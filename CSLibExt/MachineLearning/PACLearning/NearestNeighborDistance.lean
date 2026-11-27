/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.PACLearning.NearestNeighbor
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Expected nearest-neighbor distance on the unit cube

Partition the Euclidean cube into finitely many grid cells, including their boundary points.
An occupied query cell gives a distance bound by its diameter, and an empty one contributes
at most the cube diameter times its probability. This is the geometry and sampling argument
of Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*
(2014), §19.2, using a geometric sum in place of the exponential estimate for an empty cell.
-/

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory Set
open scoped BigOperators

@[expose] public section

/-- The Borel cube `[0, 1]^d` with the inherited Euclidean metric. -/
abbrev NearestNeighborCube (d : ℕ) :=
  {x : EuclideanSpace ℝ (Fin d) //
    WithLp.ofLp x ∈ Set.pi (Set.univ : Set (Fin d)) (fun _ : Fin d => unitInterval)}

private lemma dist_cube_le_of_coord {d : ℕ} {x y : NearestNeighborCube d} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ i, |x.1 i - y.1 i| ≤ r) :
    dist x y ≤ Real.sqrt d * r := by
  change dist x.1 y.1 ≤ _
  rw [EuclideanSpace.dist_eq]
  calc
    _ ≤ Real.sqrt (∑ _ : Fin d, r ^ 2) := by
      apply Real.sqrt_le_sqrt
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Real.dist_eq]
      have hi := h i
      nlinarith [abs_nonneg (x.1 i - y.1 i)]
    _ = Real.sqrt d * r := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hr]

private lemma dist_cube_le {d : ℕ} (x y : NearestNeighborCube d) :
    dist x y ≤ Real.sqrt d := by
  rw [← mul_one (Real.sqrt d)]
  refine dist_cube_le_of_coord zero_le_one fun i => abs_le.mpr ?_
  have hx := x.2 i (Set.mem_univ i)
  have hy := y.2 i (Set.mem_univ i)
  exact ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

private def cubeGridCoord (N : ℕ) [NeZero N] (k : ℕ) : Fin N :=
  ⟨min (N - 1) k, (min_le_left _ _).trans_lt (by have := NeZero.pos N; omega)⟩

private noncomputable def cubeGrid {d : ℕ} (N : ℕ) [NeZero N]
    (x : NearestNeighborCube d) (i : Fin d) : Fin N :=
  cubeGridCoord N ⌊(N : ℝ) * x.1 i⌋₊

private lemma cubeGridCoord_bounds {N : ℕ} [NeZero N] {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (cubeGridCoord N ⌊(N : ℝ) * t⌋₊ : ℕ) ≤ (N : ℝ) * t ∧
      (N : ℝ) * t ≤ ((cubeGridCoord N ⌊(N : ℝ) * t⌋₊ : ℕ) : ℝ) + 1 := by
  let u : ℝ := (N : ℝ) * t
  have hu : 0 ≤ u := mul_nonneg (Nat.cast_nonneg N) ht.1
  change ((min (N - 1) ⌊u⌋₊ : ℕ) : ℝ) ≤ u ∧
    u ≤ ((min (N - 1) ⌊u⌋₊ : ℕ) : ℝ) + 1
  refine ⟨(Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hu), ?_⟩
  rcases le_total ⌊u⌋₊ (N - 1) with h | h
  · rw [min_eq_right h]
    exact (Nat.lt_floor_add_one u).le
  · rw [min_eq_left h]
    have hN : 1 ≤ N := NeZero.pos N
    rw [Nat.cast_sub hN, Nat.cast_one, sub_add_cancel]
    exact mul_le_of_le_one_right (Nat.cast_nonneg N) ht.2

private lemma measurable_cubeGrid {d : ℕ} (N : ℕ) [NeZero N] :
    Measurable (cubeGrid (d := d) N) := by
  apply Measurable.of_eval
  intro i
  have hc : Measurable (fun x : NearestNeighborCube d => x.1 i) :=
    (PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) i).measurable.comp measurable_subtype_coe
  exact (measurable_of_countable _).comp (Nat.measurable_floor.comp (measurable_const.mul hc))

private lemma dist_cube_le_of_cubeGrid_eq {d N : ℕ} [NeZero N] {x y : NearestNeighborCube d}
    (h : cubeGrid N x = cubeGrid N y) : dist x y ≤ Real.sqrt d / N := by
  rw [div_eq_mul_inv]
  refine dist_cube_le_of_coord (inv_nonneg.mpr (Nat.cast_nonneg N)) fun i => ?_
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hx := cubeGridCoord_bounds (N := N) (x.2 i (Set.mem_univ i))
  have hy := cubeGridCoord_bounds (N := N) (y.2 i (Set.mem_univ i))
  change ((cubeGrid N x i : ℕ) : ℝ) ≤ (N : ℝ) * x.1 i ∧
    (N : ℝ) * x.1 i ≤ ((cubeGrid N x i : ℕ) : ℝ) + 1 at hx
  change ((cubeGrid N y i : ℕ) : ℝ) ≤ (N : ℝ) * y.1 i ∧
    (N : ℝ) * y.1 i ≤ ((cubeGrid N y i : ℕ) : ℝ) + 1 at hy
  rw [congrFun h i] at hx
  rw [abs_le, ← one_div]
  constructor
  · apply le_of_neg_le_neg
    rw [neg_sub, neg_neg]
    apply (le_div_iff₀ hN).mpr
    linarith [hx.1, hy.2]
  · apply (le_div_iff₀ hN).mpr
    linarith [hy.1, hx.2]

private lemma nearestNeighbor_dist_le {X : Type*} [PseudoMetricSpace X] {m : ℕ} [NeZero m]
    (points : Fin m → X) (x : X) (i : Fin m) :
    dist x (points (nearestNeighborIndex points x)) ≤ dist x (points i) :=
  ((nearestNeighborIndex_eq_iff points x _).mp rfl i).elim le_of_lt fun h => h.1.le

private lemma measurable_nearestNeighbor_dist {d m : ℕ} [NeZero m] :
    Measurable fun p : (Fin m → NearestNeighborCube d) × NearestNeighborCube d =>
      dist p.2 (p.1 (nearestNeighborIndex p.1 p.2)) := by
  let idx (p : (Fin m → NearestNeighborCube d) × NearestNeighborCube d) :=
    nearestNeighborIndex p.1 p.2
  have hi : Measurable idx := measurable_nearestNeighborIndex
    (fun i => (measurable_pi_apply i).comp measurable_fst) measurable_snd
  apply measurable_snd.dist
  intro s hs
  change MeasurableSet {p : (Fin m → NearestNeighborCube d) × NearestNeighborCube d |
    p.1 (idx p) ∈ s}
  have heq : {p | p.1 (idx p) ∈ s} = ⋃ i : Fin m, {p | idx p = i} ∩ {p | p.1 i ∈ s} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun hp => ⟨idx p, rfl, hp⟩, fun ⟨i, hi', hp⟩ => hi' ▸ hp⟩
  rw [heq]
  exact MeasurableSet.iUnion fun i => (hi (measurableSet_singleton i)).inter
    (((measurable_pi_apply i).comp measurable_fst) hs)

/-- The nearest-neighbor distance on the unit cube is integrable under independent sampling. -/
theorem integrable_nearestNeighborCube_dist {d m : ℕ} [NeZero m]
    (μ : Measure (NearestNeighborCube d)) [IsProbabilityMeasure μ] :
    Integrable (fun p : (Fin m → NearestNeighborCube d) × NearestNeighborCube d =>
      dist p.2 (p.1 (nearestNeighborIndex p.1 p.2))) ((Measure.pi fun _ : Fin m => μ).prod μ) := by
  refine Integrable.of_bound measurable_nearestNeighbor_dist.aestronglyMeasurable (Real.sqrt d)
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_of_nonneg dist_nonneg]
  exact dist_cube_le _ _

private lemma cell_mass_mul_miss_le (m : ℕ) {u : ℝ} (hu : 0 ≤ u) (hu₁ : u ≤ 1) :
    u * (1 - u) ^ m ≤ 1 / ((m : ℝ) + 1) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
  calc
    u * (1 - u) ^ m * ((m : ℝ) + 1) =
        ∑ _i ∈ Finset.range (m + 1), (1 - u) ^ m * u := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring
    _ ≤ ∑ i ∈ Finset.range (m + 1), (1 - u) ^ i * u := by
      refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ?_ hu
      exact pow_le_pow_of_le_one (sub_nonneg.mpr hu₁) (by linarith)
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    _ = 1 - (1 - u) ^ (m + 1) := by
      rw [← Finset.sum_mul, ← geom_sum_mul_neg (1 - u) (m + 1), sub_sub_cancel]
    _ ≤ 1 := sub_le_self _ (pow_nonneg (sub_nonneg.mpr hu₁) _)

private lemma measureReal_empty_cell {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {C : Set X} (hC : MeasurableSet C) (m : ℕ) :
    ((Measure.pi fun _ : Fin m => μ).prod μ).real
        ((Set.univ.pi fun _ : Fin m => Cᶜ) ×ˢ C) ≤ 1 / ((m : ℝ) + 1) := by
  have hμc : μ.real C ≤ 1 := measureReal_le_one
  rw [measureReal_prod_prod, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  change (∏ _i : Fin m, μ.real Cᶜ) * μ.real C ≤ _
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, measureReal_compl hC,
    probReal_univ, mul_comm]
  exact cell_mass_mul_miss_le m measureReal_nonneg hμc

private lemma integral_nearestNeighbor_dist_le_grid {d m : ℕ} [NeZero m]
    (μ : Measure (NearestNeighborCube d)) [IsProbabilityMeasure μ] (N : ℕ) [NeZero N] :
    (∫ p : (Fin m → NearestNeighborCube d) × NearestNeighborCube d,
        dist p.2 (p.1 (nearestNeighborIndex p.1 p.2))
        ∂((Measure.pi fun _ : Fin m => μ).prod μ)) ≤
      Real.sqrt d / N + Real.sqrt d * (N : ℝ) ^ d / ((m : ℝ) + 1) := by
  classical
  let Ω := (Fin m → NearestNeighborCube d) × NearestNeighborCube d
  let ν : Measure Ω := (Measure.pi fun _ : Fin m => μ).prod μ
  let C (k : Fin d → Fin N) : Set (NearestNeighborCube d) := {x | cubeGrid N x = k}
  let A (k : Fin d → Fin N) : Set (Fin m → NearestNeighborCube d) :=
    Set.univ.pi fun _ : Fin m => (C k)ᶜ
  let G (k : Fin d → Fin N) (p : Ω) : ℝ :=
    (A k ×ˢ C k).indicator (fun _ => Real.sqrt d) p
  have hC (k : Fin d → Fin N) : MeasurableSet (C k) :=
    (measurable_cubeGrid N) (measurableSet_singleton k)
  have hA (k : Fin d → Fin N) : MeasurableSet (A k) :=
    (measurableSet_pi Set.countable_univ).mpr (Or.inl fun _ _ => (hC k).compl)
  have hGi (k : Fin d → Fin N) : Integrable (G k) ν :=
    (integrable_const _).indicator ((hA k).prod (hC k))
  have hGi_nonneg (k : Fin d → Fin N) (p : Ω) : 0 ≤ G k p := by
    by_cases hp : p ∈ A k ×ˢ C k <;> simp [G, hp]
  have hB_nonneg : 0 ≤ Real.sqrt d / (N : ℝ) := by positivity
  have hfi : Integrable (fun p : Ω => dist p.2 (p.1 (nearestNeighborIndex p.1 p.2))) ν :=
    integrable_nearestNeighborCube_dist μ
  have hpoint (p : Ω) : dist p.2 (p.1 (nearestNeighborIndex p.1 p.2)) ≤
      Real.sqrt d / N + ∑ k : Fin d → Fin N, G k p := by
    let k := cubeGrid N p.2
    have hpC : p.2 ∈ C k := rfl
    by_cases hp : p.1 ∈ A k
    · have hg : G k p = Real.sqrt d := indicator_of_mem (show p ∈ A k ×ˢ C k from ⟨hp, hpC⟩) _
      have hsum : G k p ≤ ∑ i : Fin d → Fin N, G i p :=
        Finset.single_le_sum (fun i _ => hGi_nonneg i p) (Finset.mem_univ k)
      linarith [dist_cube_le p.2 (p.1 (nearestNeighborIndex p.1 p.2))]
    · have hex : ∃ i : Fin m, cubeGrid N (p.1 i) = k := by
        by_contra! h
        exact hp (fun i _ => h i)
      obtain ⟨i, hi⟩ := hex
      have hnear := (nearestNeighbor_dist_le p.1 p.2 i).trans
        (dist_cube_le_of_cubeGrid_eq hi.symm)
      exact hnear.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hGi_nonneg i p))
  have hterm (k : Fin d → Fin N) : ∫ p, G k p ∂ν ≤ Real.sqrt d / ((m : ℝ) + 1) := by
    rw [show G k = (A k ×ˢ C k).indicator (fun _ => Real.sqrt d) from rfl,
      integral_indicator_const _ ((hA k).prod (hC k)), smul_eq_mul, div_eq_mul_one_div,
      mul_comm (Real.sqrt d)]
    exact mul_le_mul_of_nonneg_right (measureReal_empty_cell μ (hC k) m) (Real.sqrt_nonneg _)
  calc
    _ ≤ ∫ p : Ω, Real.sqrt d / N + ∑ k : Fin d → Fin N, G k p ∂ν :=
      integral_mono hfi ((integrable_const _).add
        (integrable_finsetSum Finset.univ fun k _ => hGi k)) hpoint
    _ = Real.sqrt d / N + ∑ k : Fin d → Fin N, ∫ p, G k p ∂ν := by
      rw [integral_add (integrable_const _)
        (integrable_finsetSum Finset.univ fun k _ => hGi k), integral_const,
        probReal_univ, one_smul, integral_finsetSum _ fun k _ => hGi k]
    _ ≤ Real.sqrt d / N + ∑ _k : Fin d → Fin N, Real.sqrt d / ((m : ℝ) + 1) :=
      add_le_add_right (Finset.sum_le_sum fun k _ => hterm k) _
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ring

private lemma grid_rate_le (d m : ℕ) [NeZero m] :
    let t : ℝ := (m : ℝ) ^ (1 / ((d : ℝ) + 1))
    let N : ℕ := ⌊t⌋₊
    0 < N ∧ 1 / (N : ℝ) ≤ 2 / t ∧ (N : ℝ) ^ d / ((m : ℝ) + 1) ≤ 1 / t := by
  dsimp only
  let a : ℝ := 1 / ((d : ℝ) + 1)
  let t : ℝ := (m : ℝ) ^ a
  let N : ℕ := ⌊t⌋₊
  change 0 < N ∧ 1 / (N : ℝ) ≤ 2 / t ∧ (N : ℝ) ^ d / ((m : ℝ) + 1) ≤ 1 / t
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  have h1m : (1 : ℝ) ≤ m := by exact_mod_cast (NeZero.pos m)
  have ht : 1 ≤ t := Real.one_le_rpow h1m (by dsimp [a]; positivity)
  have htp : 0 < t := by linarith
  have hN : 1 ≤ N := Nat.le_floor (by simpa using ht)
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNt : (N : ℝ) ≤ t := Nat.floor_le htp.le
  have htfloor : t < (N : ℝ) + 1 := Nat.lt_floor_add_one t
  have ht_pow : t ^ (d + 1) = (m : ℝ) := by
    rw [← Real.rpow_natCast, show t = (m : ℝ) ^ a from rfl, ← Real.rpow_mul hm.le,
      Nat.cast_add, Nat.cast_one]
    have ha : a * ((d : ℝ) + 1) = 1 :=
      div_mul_cancel₀ 1 (by positivity : (d : ℝ) + 1 ≠ 0)
    rw [ha, Real.rpow_one]
  refine ⟨hN, (div_le_div_iff₀ hNp htp).mpr (by linarith), ?_⟩
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1) htp).mpr
  calc
    (N : ℝ) ^ d * t ≤ t ^ d * t :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hNp.le hNt _) htp.le
    _ = (m : ℝ) := (pow_succ t d).symm.trans ht_pow
    _ ≤ 1 * ((m : ℝ) + 1) := by linarith

/-- The expected Euclidean distance to the nearest among `m` independent sample points
on `[0, 1]^d` is at most `4 √d m^(-1/(d+1))` for an independent query with the same law.
The grid proof in fact bounds this distance with constant `3`. -/
theorem integral_nearestNeighborCube_dist_le {d m : ℕ} [NeZero m]
    (μ : Measure (NearestNeighborCube d)) [IsProbabilityMeasure μ] :
    (∫ p : (Fin m → NearestNeighborCube d) × NearestNeighborCube d,
        dist p.2 (p.1 (nearestNeighborIndex p.1 p.2))
        ∂((Measure.pi fun _ : Fin m => μ).prod μ)) ≤
      4 * Real.sqrt d * (m : ℝ) ^ (-(1 / ((d : ℝ) + 1))) := by
  let t : ℝ := (m : ℝ) ^ (1 / ((d : ℝ) + 1))
  let N : ℕ := ⌊t⌋₊
  obtain ⟨hN, hdiam, hmiss⟩ :
      0 < N ∧ 1 / (N : ℝ) ≤ 2 / t ∧ (N : ℝ) ^ d / ((m : ℝ) + 1) ≤ 1 / t :=
    grid_rate_le d m
  let : NeZero N := ⟨hN.ne'⟩
  have hs := Real.sqrt_nonneg (d : ℝ)
  have ht : 0 < t := Real.rpow_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos m)) _
  calc
    _ ≤ Real.sqrt d / N + Real.sqrt d * (N : ℝ) ^ d / ((m : ℝ) + 1) :=
      integral_nearestNeighbor_dist_le_grid μ N
    _ ≤ Real.sqrt d * (2 / t) + Real.sqrt d * (1 / t) := by
      rw [mul_div_assoc, div_eq_mul_one_div (Real.sqrt d) (N : ℝ)]
      exact add_le_add (mul_le_mul_of_nonneg_left hdiam hs) (mul_le_mul_of_nonneg_left hmiss hs)
    _ ≤ 4 * Real.sqrt d * t⁻¹ := by
      simp only [div_eq_mul_inv, one_mul]
      nlinarith [mul_nonneg hs (inv_nonneg.mpr ht.le)]
    _ = _ := by
      rw [Real.rpow_neg (Nat.cast_nonneg m)]

/-- The nearest-neighbor distance bound in sample-then-query integral form. -/
theorem integral_integral_nearestNeighborCube_dist_le {d m : ℕ} [NeZero m]
    (μ : Measure (NearestNeighborCube d)) [IsProbabilityMeasure μ] :
    (∫ points : Fin m → NearestNeighborCube d,
      ∫ x, dist x (points (nearestNeighborIndex points x)) ∂μ
      ∂(Measure.pi fun _ : Fin m => μ)) ≤
      4 * Real.sqrt d * (m : ℝ) ^ (-(1 / ((d : ℝ) + 1))) := by
  exact (integral_prod _ (integrable_nearestNeighborCube_dist (m := m) μ)) ▸
    integral_nearestNeighborCube_dist_le (m := m) μ

end

end Cslib.MachineLearning.PACLearning
