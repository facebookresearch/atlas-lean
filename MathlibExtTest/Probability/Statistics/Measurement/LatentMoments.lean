/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Measurement.LatentMoments

/-!
# Latent-mixture moment tests

Two-state rational, boundary, and degenerate-prior instances.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.Measurement

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.Measurement

private theorem bind_integral_eq {Z α : Type*} [Fintype Z] [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (pi : PMF Z) (K : Z → PMF α) (f : α → ℝ) :
    ∫ x, f x ∂(pi.bind K).toMeasure
      = ∑ z, (pi z).toReal * (∫ x, f x ∂(K z).toMeasure) := by
  have hbind : ∀ x, ((pi.bind K) x).toReal
      = ∑ z, (pi z).toReal * ((K z) x).toReal := by
    intro x
    rw [PMF.bind_apply, tsum_fintype]
    rw [ENNReal.toReal_sum (fun a _ => by
      apply ENNReal.mul_ne_top
      · exact pi.apply_ne_top a
      · exact (K a).apply_ne_top x)]
    apply Finset.sum_congr rfl
    intro z _
    rw [ENNReal.toReal_mul]
  have hK : ∀ z, (∫ x, f x ∂(K z).toMeasure) = ∑ x, ((K z) x).toReal * f x := by
    intro z
    rw [PMF.integral_eq_sum _ f]
    apply Finset.sum_congr rfl
    intro x _
    rw [smul_eq_mul]
  rw [PMF.integral_eq_sum _ f]
  simp_rw [hbind, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [hK]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem pmf_sum_toReal_eq_one {Z : Type*} [Fintype Z] (pi : PMF Z) :
    ∑ z, (pi z).toReal = 1 := by
  have h1 : (∑ z, pi z) = 1 := by
    have h := pi.tsum_coe
    rwa [tsum_fintype] at h
  have h2 : (∑ z, pi z).toReal = (1 : ENNReal).toReal := by rw [h1]
  rw [ENNReal.toReal_sum (fun a _ => pi.apply_ne_top a)] at h2
  simpa using h2

private theorem memLp_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : PMF (ι → Bool)) (i : ι) :
    MemLp (fun x : ι → Bool => (if x i then (1 : ℝ) else 0)) 2 p.toMeasure := by
  refine memLp_of_bounded (a := 0) (b := 1) ?_ ?_ 2
  · filter_upwards with x
    cases h : x i <;> simp
  · exact (by measurability : Measurable (fun x : ι → Bool => (if x i then (1 : ℝ) else 0))).aestronglyMeasurable

private theorem finiteCovariance_eq {α : Type*} [Fintype α] (p X Y : α → ℝ)
    (hp : ∑ x, p x = 1) :
    MathlibExt.Probability.FiniteProbability.covariance p X Y
      = (∑ x, p x * (X x * Y x)) - (∑ x, p x * X x) * (∑ x, p x * Y x) := by
  unfold MathlibExt.Probability.FiniteProbability.covariance
    MathlibExt.Probability.FiniteProbability.expectation
  have hterm : ∀ x, p x * ((X x - (∑ y, p y * X y)) * (Y x - (∑ y, p y * Y y)))
      = p x * (X x * Y x) - (p x * X x) * (∑ y, p y * Y y)
        - (p x * Y x) * (∑ y, p y * X y)
        + p x * ((∑ y, p y * X y) * (∑ y, p y * Y y)) := by
    intro x
    ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hB : (∑ x, (p x * X x) * (∑ y, p y * Y y))
      = (∑ x, p x * X x) * (∑ y, p y * Y y) :=
    (Finset.sum_mul Finset.univ (fun x => p x * X x) _).symm
  have hC : (∑ x, (p x * Y x) * (∑ y, p y * X y))
      = (∑ x, p x * Y x) * (∑ y, p y * X y) :=
    (Finset.sum_mul Finset.univ (fun x => p x * Y x) _).symm
  have hD : (∑ x, p x * ((∑ y, p y * X y) * (∑ y, p y * Y y)))
      = (∑ x, p x) * ((∑ y, p y * X y) * (∑ y, p y * Y y)) :=
    (Finset.sum_mul Finset.univ (fun x => p x) _).symm
  rw [hB, hC, hD, hp]
  ring

/-- **Latent-mixture coordinate moments.** Let `Z` (latent states) and `ι`
(items) be finite, `pi : PMF Z` a latent law with no support restriction,
and `q z i ∈ [0, 1]` item curves (endpoints `0` and `1` allowed). Write
`K z = localIndepPMF (q z) _ _` and observe `Y : ι → Bool` from the mixture
law `pi.bind K` on the full response space. Then, with
`Y_i x = if x i then 1 else 0`:

(1) mixed first moment `E[Y_i] = E_pi[q_i]`;
(2) mixed pair moment `E[Y_i * Y_j] = E_pi[q_i * q_j]` for `i ≠ j`;
(3) observable covariance `Cov(Y_i, Y_j) = Cov_pi(q_i, q_j)` for `i ≠ j`,
where the left covariance is `ProbabilityTheory.covariance` under the
observed law and the right is the finite-sum
`FiniteProbability.covariance` under the weights `(pi z).toReal`.

No diagonal (`i = j`) covariance claim is made. -/

theorem pi_norm_rational :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h1, ite_true, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem hq0_rational_all : ∀ z i : Fin 2, 0 ≤ (if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
    else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ))) := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num

theorem hq1_rational_all : ∀ z i : Fin 2, (if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
    else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ))) ≤ 1 := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num

theorem pi_norm_boundary :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h1, ite_true, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem hq0_boundary_all : ∀ z i : Fin 2, 0 ≤ (if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
    else (if i = 0 then (1 : ℝ) else (0 : ℝ))) := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi]
  · by_cases hi : i = 0 <;> simp [hz, hi]

theorem hq1_boundary_all : ∀ z i : Fin 2, (if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
    else (if i = 0 then (1 : ℝ) else (0 : ℝ))) ≤ 1 := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi]
  · by_cases hi : i = 0 <;> simp [hz, hi]

theorem pi_norm_degenerate :
    (∑ z : Fin 2, (if z = 0 then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))) = 1 := by
  rw [Fin.sum_univ_two]
  have h1 : (1 : Fin 2) ≠ 0 := by decide
  simp only [h1, ite_true, ite_false]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem hq0_degenerate_all : ∀ z i : Fin 2, 0 ≤ (if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
    else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ))) := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num

theorem hq1_degenerate_all : ∀ z i : Fin 2, (if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
    else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ))) ≤ 1 := by
  intro z i
  by_cases hz : z = 0
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num
  · by_cases hi : i = 0 <;> simp [hz, hi] <;> norm_num

/-! ## Production result (the leaf's one new public symbol) -/

/-- **Latent-mixture coordinate moments.** Let `Z` (latent states) and `ι`
(items) be finite, `pi : PMF Z` a latent law with no support restriction,
and `q z i ∈ [0, 1]` item curves (endpoints `0` and `1` allowed). Write
`K z = localIndepPMF (q z) _ _` and observe `Y : ι → Bool` from the mixture
law `pi.bind K` on the full response space. Then, with
`Y_i x = if x i then 1 else 0`:

(1) mixed first moment `E[Y_i] = E_pi[q_i]`;
(2) mixed pair moment `E[Y_i * Y_j] = E_pi[q_i * q_j]` for `i ≠ j`;
(3) observable covariance `Cov(Y_i, Y_j) = Cov_pi(q_i, q_j)` for `i ≠ j`,
where the left covariance is `ProbabilityTheory.covariance` under the
observed law and the right is the finite-sum
`FiniteProbability.covariance` under the weights `(pi z).toReal`.

No diagonal (`i = j`) covariance claim is made. -/
theorem latentMixture_coordinate_moments {Z ι : Type*} [Fintype Z] [Fintype ι]
    [DecidableEq ι] (pi : PMF Z) (q : Z → ι → ℝ)
    (hq0 : ∀ z i, 0 ≤ q z i) (hq1 : ∀ z i, q z i ≤ 1) :
    (∀ i, ∫ x, (if x i then (1 : ℝ) else 0)
        ∂(pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
      = MathlibExt.Probability.FiniteProbability.expectation
          (fun z => (pi z).toReal) (fun z => q z i))
    ∧ (∀ i j, i ≠ j →
        ∫ x, (if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0)
          ∂(pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
        = MathlibExt.Probability.FiniteProbability.expectation
            (fun z => (pi z).toReal) (fun z => q z i * q z j))
    ∧ (∀ i j, i ≠ j →
        ProbabilityTheory.covariance (fun x : ι → Bool => if x i then (1 : ℝ) else 0)
            (fun x : ι → Bool => if x j then (1 : ℝ) else 0)
            (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
          = MathlibExt.Probability.FiniteProbability.covariance
              (fun z => (pi z).toReal) (fun z => q z i) (fun z => q z j)) := by
  have h1 : ∀ i, ∫ x, (if x i then (1 : ℝ) else 0)
        ∂(pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
      = MathlibExt.Probability.FiniteProbability.expectation
          (fun z => (pi z).toReal) (fun z => q z i) := by
    intro i
    rw [bind_integral_eq]
    simp_rw [(localIndepPMF_coordinate_moments (q _) (hq0 _) (hq1 _)).1 i]
    rfl
  have h2 : ∀ i j, i ≠ j →
        ∫ x, (if x i then (1 : ℝ) else 0) * (if x j then (1 : ℝ) else 0)
          ∂(pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
        = MathlibExt.Probability.FiniteProbability.expectation
            (fun z => (pi z).toReal) (fun z => q z i * q z j) := by
    intro i j hij
    rw [bind_integral_eq]
    simp_rw [(localIndepPMF_coordinate_moments (q _) (hq0 _) (hq1 _)).2 i j hij]
    rfl
  have h3 : ∀ i j, i ≠ j →
        ProbabilityTheory.covariance (fun x : ι → Bool => if x i then (1 : ℝ) else 0)
            (fun x : ι → Bool => if x j then (1 : ℝ) else 0)
            (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure
          = MathlibExt.Probability.FiniteProbability.covariance
              (fun z => (pi z).toReal) (fun z => q z i) (fun z => q z j) := by
    intro i j hij
    have hX : MemLp (fun x : ι → Bool => (if x i then (1 : ℝ) else 0)) 2
        (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure :=
      memLp_indicator _ i
    have hY : MemLp (fun x : ι → Bool => (if x j then (1 : ℝ) else 0)) 2
        (pi.bind fun z => localIndepPMF (q z) (hq0 z) (hq1 z)).toMeasure :=
      memLp_indicator _ j
    rw [ProbabilityTheory.covariance_eq_sub hX hY]
    simp only [Pi.mul_apply]
    rw [finiteCovariance_eq _ _ _ (pmf_sum_toReal_eq_one pi)]
    rw [h1 i, h1 j, h2 i j hij]
    rfl
  exact ⟨h1, h2, h3⟩

/-- Latent relabeling, as an instantiation of the existing `PMF.map` /
`PMF.bind` laws (leaf: "instantiate existing bind/map relabeling rather
than reprove its generic law"). Relabeling latent states by an equivalence
`e : Z ≃ Z'`, with curves transported along `e`, leaves the observed
mixture law unchanged. Kept as an `example`: no new public symbol. At
integration this follows from `PMF.map_bind` and `PMF.bind_map`. -/
example {Z Z' ι : Type*} [Fintype Z] [Fintype Z'] [Fintype ι] [DecidableEq ι]
    (e : Z ≃ Z') (pi : PMF Z) (q : Z → ι → ℝ)
    (hq0 : ∀ z i, 0 ≤ q z i) (hq1 : ∀ z i, q z i ≤ 1) :
    (pi.map e).bind (fun z' => localIndepPMF (q (e.symm z'))
        (hq0 (e.symm z')) (hq1 (e.symm z')))
      = pi.bind (fun z => localIndepPMF (q z) (hq0 z) (hq1 z)) := by
  rw [PMF.bind_map]
  congr 1
  funext z
  simp

/-! ## Test theorems (planned `MathlibExtTest/.../LatentMoments.lean`)

Each is `sorry` in this pin; at integration each is proved by instantiating
`latentMixture_coordinate_moments` at the concrete data and evaluating the
finite sums. The concrete priors use `ENNReal.ofReal` of rational weights so
`(pi z).toReal` evaluates to the stated rationals. -/

/-- Nonvacuity, two latent states with rational weights and item curves.
`Z = Fin 2` with weights `1/3, 2/3`; `ι = Fin 2` with curves
`z=0: (1/4, 1/2)`, `z=1: (3/4, 1/5)`. Then `E[Y_0] = 7/12`,
`E[Y_0 * Y_1] = 17/120`, `Cov(Y_0, Y_1) = -1/30` (negative: the curves are
oppositely ordered across states), and the observed law has total real
mass `1`. -/
theorem latentMixture_fin2_rational_moments :
    (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
            (by exact pi_norm_rational)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
              else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
            (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = 7 / 12)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
            (by exact pi_norm_rational)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
              else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
            (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = 17 / 120)
    ∧ (ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
        (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
        ((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
            (by exact pi_norm_rational)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
              else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
            (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = -1 / 30)
    ∧ (∑ x, (((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
            (by exact pi_norm_rational)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
              else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
            (by exact hq0_rational_all z) (by exact hq1_rational_all z))) x).toReal = 1) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hMom := latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
        then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ)) pi_norm_rational)
    (fun z i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
      else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
    hq0_rational_all hq1_rational_all
  have c1 : (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
          (by exact pi_norm_rational)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
            else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
          (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = 7 / 12) := by
    have h1 := hMom.1 (0 : Fin 2)
    convert h1 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/3)]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2/3)]
    norm_num
  have c2 : (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
          (by exact pi_norm_rational)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
            else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
          (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = 17 / 120) := by
    have h2 := hMom.2.1 (0 : Fin 2) (1 : Fin 2) h01
    convert h2 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/3)]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2/3)]
    norm_num
  have c3 : (ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
      (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
      ((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
          (by exact pi_norm_rational)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
            else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
          (by exact hq0_rational_all z) (by exact hq1_rational_all z))).toMeasure = -1 / 30) := by
    have h3 := hMom.2.2 (0 : Fin 2) (1 : Fin 2) h01
    convert h3 using 2
    rw [finiteCovariance_eq _ _ _ (pmf_sum_toReal_eq_one _)]
    simp only [Fin.sum_univ_two, PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/3)]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 2/3)]
    norm_num
  have c4 : (∑ x, (((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 3 : ℝ) else ENNReal.ofReal (2 / 3 : ℝ))
          (by exact pi_norm_rational)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (1 / 4 : ℝ) else (1 / 2 : ℝ))
            else (if i = 0 then (3 / 4 : ℝ) else (1 / 5 : ℝ)))
          (by exact hq0_rational_all z) (by exact hq1_rational_all z))) x).toReal = 1) :=
    pmf_sum_toReal_eq_one _
  exact ⟨c1, c2, c3, c4⟩

/-- Boundary cells: curves attain `0` and `1`. `Z = Fin 2` with equal
weights `1/2, 1/2`; curves `z=0: (0, 1)`, `z=1: (1, 0)`. Then
`E[Y_0] = 1/2`, `E[Y_0 * Y_1] = 0`, `Cov(Y_0, Y_1) = -1/4`. This pins that
closed `[0, 1]` endpoints need no strict-positivity side condition. -/
theorem latentMixture_boundary_moments :
    (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
            (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
              else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
            (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = 1 / 2)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
            (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
              else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
            (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = 0)
    ∧ (ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
        (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
        ((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
            (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
              else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
            (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = -1 / 4) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hMom := latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
        then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ)) pi_norm_boundary)
    (fun z i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
      else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
    hq0_boundary_all hq1_boundary_all
  have c1 : (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
          (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
            else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
          (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = 1 / 2) := by
    have h1 := hMom.1 (0 : Fin 2)
    convert h1 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have c2 : (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
          (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
            else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
          (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = 0) := by
    have h2 := hMom.2.1 (0 : Fin 2) (1 : Fin 2) h01
    convert h2 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  have c3 : (ProbabilityTheory.covariance (fun x : Fin 2 → Bool => if x 0 then (1 : ℝ) else 0)
      (fun x : Fin 2 → Bool => if x 1 then (1 : ℝ) else 0)
      ((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 / 2 : ℝ) else ENNReal.ofReal (1 / 2 : ℝ))
          (by exact pi_norm_boundary)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (0 : ℝ) else (1 : ℝ))
            else (if i = 0 then (1 : ℝ) else (0 : ℝ)))
          (by exact hq0_boundary_all z) (by exact hq1_boundary_all z))).toMeasure = -1 / 4) := by
    have h3 := hMom.2.2 (0 : Fin 2) (1 : Fin 2) h01
    convert h3 using 2
    rw [finiteCovariance_eq _ _ _ (pmf_sum_toReal_eq_one _)]
    simp only [Fin.sum_univ_two, PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  exact ⟨c1, c2, c3⟩

/-- Degenerate prior: weights `(1, 0)` put all mass on latent state `0`, so
the mixture collapses to that component. Curves `z=0: (2/7, 5/9)`,
`z=1: (1/3, 1/3)` (the zero-weight state's curves are irrelevant). Then
`E[Y_0] = 2/7` and `E[Y_0 * Y_1] = (2/7) * (5/9)`. This pins that `pi z = 0`
cells are allowed. -/
theorem latentMixture_degenerate_prior_moments :
    (∫ x, (if x 0 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))
            (by exact pi_norm_degenerate)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
              else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
            (by exact hq0_degenerate_all z) (by exact hq1_degenerate_all z))).toMeasure = 2 / 7)
    ∧ (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
        ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
              then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))
            (by exact pi_norm_degenerate)).bind (fun z => localIndepPMF
            (fun i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
              else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
            (by exact hq0_degenerate_all z) (by exact hq1_degenerate_all z))).toMeasure = (2 / 7 : ℝ) * (5 / 9)) := by
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have hMom := latentMixture_coordinate_moments
    (PMF.ofFintype (fun z : Fin 2 => if z = 0
        then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ)) pi_norm_degenerate)
    (fun z i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
      else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
    hq0_degenerate_all hq1_degenerate_all
  have c1 : (∫ x, (if x 0 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))
          (by exact pi_norm_degenerate)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
            else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
          (by exact hq0_degenerate_all z) (by exact hq1_degenerate_all z))).toMeasure = 2 / 7) := by
    have h1 := hMom.1 (0 : Fin 2)
    convert h1 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (1:ℝ))]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (0:ℝ))]
    norm_num
  have c2 : (∫ x, (if x 0 then (1 : ℝ) else 0) * (if x 1 then (1 : ℝ) else 0)
      ∂((PMF.ofFintype (fun z : Fin 2 => if z = 0
            then ENNReal.ofReal (1 : ℝ) else ENNReal.ofReal (0 : ℝ))
          (by exact pi_norm_degenerate)).bind (fun z => localIndepPMF
          (fun i : Fin 2 => if z = 0 then (if i = 0 then (2 / 7 : ℝ) else (5 / 9 : ℝ))
            else (if i = 0 then (1 / 3 : ℝ) else (1 / 3 : ℝ)))
          (by exact hq0_degenerate_all z) (by exact hq1_degenerate_all z))).toMeasure
        = (2 / 7 : ℝ) * (5 / 9)) := by
    have h2 := hMom.2.1 (0 : Fin 2) (1 : Fin 2) h01
    convert h2 using 2
    unfold MathlibExt.Probability.FiniteProbability.expectation
    rw [Fin.sum_univ_two]
    simp only [PMF.ofFintype_apply]
    have hne : (1 : Fin 2) ≠ 0 := by decide
    simp only [hne, ite_true, ite_false]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (1:ℝ))]
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ (0:ℝ))]
    norm_num
  exact ⟨c1, c2⟩


end MathlibExtTest.Probability.Statistics.Measurement
