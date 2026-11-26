/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.RademacherComplexity

/-!
# Rademacher complexity of path-norm balls of two-layer ReLU networks

A two-layer ReLU network of width `m` without bias computes
`f(x; θ) = ∑ₖ aₖ σ(⟨wₖ, x⟩)` with `σ(t) = max t 0`, and its path norm is
`‖θ‖_P = ∑ₖ |aₖ| ‖wₖ‖₁` (W. E, C. Ma and L. Wu, *A priori estimates of the population risk for
two-layer neural networks*, Commun. Math. Sci. 17 (2019), equations (3.1) and (3.2)).
For a sample `x₁, …, xₙ ∈ [-1, 1]^d`, the set of value vectors `(f(x₁), …, f(xₙ))` of all such
networks, of any width, with path norm at most `Q` has empirical Rademacher complexity at most
`2 Q √(2 log (2d) / n)` (`rademacherComplexity_pathNormBallValues_le`); this is the bound (5.1)
of E, Ma and Wu, which they attribute to Neyshabur, Tomioka and Srebro (COLT 2015), and the
estimate behind Theorem 6 of E, Ma and Wu, *The Barron space and the flow-induced function spaces
for neural network models*, Constr. Approx. 55 (2022) (arXiv:1906.08039).

The proof is the one of §2.5.5 of the Barron-space paper, in four steps on the Rademacher
calculus of `Cslib.MachineLearning.Rademacher`:

1. positive homogeneity of the ReLU reduces the class to the single neurons
   `x ↦ σ(⟨u, x⟩)` with `‖u‖₁ ≤ 1`, each counted with both signs, at the price of the factor
   `2 Q` (the sign reversal is `sum_flipSigns`);
2. the contraction lemma (`rademacherComplexity_coordMap_le`) removes the 1-Lipschitz ReLU;
3. a linear functional over the `ℓ¹` unit ball attains its supremum at one of the `2d` signed
   coordinate vectors `± eⱼ`;
4. Massart's finite-class lemma (`rademacherComplexity_le_of_finite`) for these `2d` vectors,
   each of Euclidean norm at most `√n`.

With a bias term, `f(x) = ∑ₖ aₖ σ(⟨bₖ, x⟩ + cₖ)` and `‖θ‖_P = ∑ₖ |aₖ| (‖bₖ‖₁ + |cₖ|)`, the same
argument applied to `(x, 1) ∈ ℝ^{d+1}` gives `2 Q √(2 log (2(d+1)) / n)`
(`rademacherComplexity_pathNormBallBiasValues_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace CSLibExt.MachineLearning.GeneralizationBounds

open Finset Real
open Cslib.MachineLearning.Rademacher

variable {d n : ℕ}

/-- **Two-layer ReLU network** of width `m` without bias: `f(x; θ) = ∑ₖ aₖ max(⟨wₖ, x⟩, 0)`
for outer weights `a : Fin m → ℝ` and inner weights `w : Fin m → ℝ^d` (W. E, C. Ma and L. Wu,
*A priori estimates of the population risk for two-layer neural networks*, Commun. Math. Sci. 17
(2019), equation (3.1), with the ReLU activation). -/
def twoLayerReLU {m : ℕ} (a : Fin m → ℝ) (w : Fin m → Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ k, a k * max (∑ j, w k j * x j) 0

/-- **Path norm** of a two-layer network: `‖θ‖_P = ∑ₖ |aₖ| ‖wₖ‖₁` (E, Ma and Wu, *A priori
estimates of the population risk for two-layer neural networks*, equation (3.2)). -/
def pathNorm {m : ℕ} (a : Fin m → ℝ) (w : Fin m → Fin d → ℝ) : ℝ :=
  ∑ k, |a k| * ∑ j, |w k j|

/-- **Path-norm ball on a sample.** The value vectors `(f(x₁), …, f(xₙ))` on a sample
`x : Fin n → ℝ^d` of the two-layer ReLU networks `f = twoLayerReLU a w` of any width with
path norm at most `Q`: the set `F_Q` of E, Ma
and Wu (*A priori estimates*, §5.1) restricted to the sample. -/
def pathNormBallValues (x : Fin n → Fin d → ℝ) (Q : ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ (m : ℕ) (a : Fin m → ℝ) (w : Fin m → Fin d → ℝ), pathNorm a w ≤ Q ∧
    v = fun i => twoLayerReLU a w (x i)}

/-- **Linear functionals on the `ℓ¹` unit ball.** The value vectors on a sample of the linear
functionals `x ↦ ⟨u, x⟩` with `‖u‖₁ ≤ 1`. -/
def l1LinearValues (x : Fin n → Fin d → ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ u : Fin d → ℝ, ∑ j, |u j| ≤ 1 ∧ v = fun i => ∑ j, u j * x i j}

/-- **ReLU neurons on the `ℓ¹` unit ball.** The value vectors on a sample of the single ReLU
neurons `x ↦ max(⟨u, x⟩, 0)` with `‖u‖₁ ≤ 1`. -/
def l1NeuronValues (x : Fin n → Fin d → ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ u : Fin d → ℝ, ∑ j, |u j| ≤ 1 ∧ v = fun i => max (∑ j, u j * x i j) 0}

/-- **Signed coordinate functionals.** The `2d` value vectors on a sample of the coordinate
functionals `x ↦ ± xⱼ`. -/
def signedColumns (x : Fin n → Fin d → ℝ) : Set (Fin n → ℝ) :=
  Set.range fun p : Fin d × Bool => fun i => (if p.2 then (1 : ℝ) else -1) * x i p.1

lemma l1NeuronValues_eq_image (x : Fin n → Fin d → ℝ) :
    l1NeuronValues x = coordMap (fun _ t => max t 0) '' l1LinearValues x := by
  ext v
  simp only [l1NeuronValues, l1LinearValues, Set.mem_image]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

lemma abs_sum_mul_le_one {x : Fin n → Fin d → ℝ} (hx : ∀ i j, |x i j| ≤ 1) {u : Fin d → ℝ}
    (hu : ∑ j, |u j| ≤ 1) (i : Fin n) : |∑ j, u j * x i j| ≤ 1 := by
  calc |∑ j, u j * x i j| ≤ ∑ j, |u j * x i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |u j| := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hx i j)
    _ ≤ 1 := hu

lemma isBounded_l1LinearValues {x : Fin n → Fin d → ℝ} (hx : ∀ i j, |x i j| ≤ 1) :
    Bornology.IsBounded (l1LinearValues x) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_sum_mul_le_one hx hu i

lemma isBounded_l1NeuronValues {x : Fin n → Fin d → ℝ} (hx : ∀ i j, |x i j| ≤ 1) :
    Bornology.IsBounded (l1NeuronValues x) := by
  rw [l1NeuronValues_eq_image]
  exact isBounded_coordMap_image (isBounded_l1LinearValues hx) zero_le_one
    fun _ s t => by simpa using abs_max_sub_max_le_abs s t 0

lemma zero_mem_l1NeuronValues (x : Fin n → Fin d → ℝ) : (0 : Fin n → ℝ) ∈ l1NeuronValues x :=
  ⟨0, by simp, by funext i; simp⟩

lemma supCorr_l1NeuronValues_nonneg {x : Fin n → Fin d → ℝ} (hx : ∀ i j, |x i j| ≤ 1)
    (ε : Fin n → Bool) : 0 ≤ supCorr (l1NeuronValues x) ε := by
  have h := le_csSup (bddAbove_signCorr_image (isBounded_l1NeuronValues hx) ε)
    ⟨0, zero_mem_l1NeuronValues x, rfl⟩
  have h0 : signCorr ε (0 : Fin n → ℝ) = 0 := by simp [signCorr]
  rw [h0] at h
  exact h

/-- **Step 2: contraction.** Removing the 1-Lipschitz ReLU does not decrease the empirical
Rademacher complexity of the `ℓ¹`-ball neurons. -/
lemma rademacherComplexity_l1NeuronValues_le {x : Fin n → Fin d → ℝ}
    (hx : ∀ i j, |x i j| ≤ 1) :
    rademacherComplexity (l1NeuronValues x) ≤ rademacherComplexity (l1LinearValues x) := by
  have hlip : ∀ _i : Fin n, LipschitzWith 1 (fun t : ℝ => max t 0) := fun _ =>
    LipschitzWith.of_dist_le_mul fun s t => by
      simpa [Real.dist_eq] using abs_max_sub_max_le_abs s t 0
  have h := rademacherComplexity_coordMap_le (isBounded_l1LinearValues hx)
    (fun _ t => max t 0) hlip
  rw [l1NeuronValues_eq_image]
  simpa using h

lemma supCorr_l1LinearValues_le (hd : 0 < d) (x : Fin n → Fin d → ℝ) (ε : Fin n → Bool) :
    supCorr (l1LinearValues x) ε ≤ supCorr (signedColumns x) ε := by
  have hfin : (signedColumns x).Finite := Set.finite_range _
  have hbdd : BddAbove (signCorr ε '' signedColumns x) := (hfin.image _).bddAbove
  set c : Fin d → ℝ := fun j => signCorr ε (fun i => x i j) with hc
  have hcol : ∀ j, |c j| ≤ supCorr (signedColumns x) ε := by
    intro j
    unfold supCorr
    rcases abs_cases (c j) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]
      refine le_csSup hbdd ⟨_, ⟨(j, true), rfl⟩, ?_⟩
      simp [hc, signCorr]
    · rw [h]
      refine le_csSup hbdd ⟨_, ⟨(j, false), rfl⟩, ?_⟩
      simp [hc, signCorr, Finset.sum_neg_distrib]
  have hM : 0 ≤ supCorr (signedColumns x) ε := (abs_nonneg _).trans (hcol ⟨0, hd⟩)
  refine csSup_le (Set.Nonempty.image _ ⟨_, ⟨0, by simp, rfl⟩⟩) ?_
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  have hexp : signCorr ε (fun i => ∑ j, u j * x i j) = ∑ j, u j * c j := by
    simp only [hc, signCorr, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hexp]
  calc ∑ j, u j * c j ≤ ∑ j, |u j| * supCorr (signedColumns x) ε := by
        refine Finset.sum_le_sum fun j _ => ?_
        calc u j * c j ≤ |u j * c j| := le_abs_self _
          _ = |u j| * |c j| := abs_mul _ _
          _ ≤ |u j| * supCorr (signedColumns x) ε :=
              mul_le_mul_of_nonneg_left (hcol j) (abs_nonneg _)
    _ = (∑ j, |u j|) * supCorr (signedColumns x) ε := by rw [Finset.sum_mul]
    _ ≤ 1 * supCorr (signedColumns x) ε := mul_le_mul_of_nonneg_right hu hM
    _ = supCorr (signedColumns x) ε := one_mul _

/-- **Step 3: the `ℓ¹` ball.** A linear functional over the `ℓ¹` unit ball is at most its value
at one of the signed coordinate vectors, so the linear functionals with `‖u‖₁ ≤ 1` have at most
the empirical Rademacher complexity of the `2d` signed coordinates (`d ≥ 1`). -/
lemma rademacherComplexity_l1LinearValues_le (hd : 0 < d) (x : Fin n → Fin d → ℝ) :
    rademacherComplexity (l1LinearValues x) ≤ rademacherComplexity (signedColumns x) := by
  unfold rademacherComplexity
  gcongr with ε
  exact supCorr_l1LinearValues_le hd x ε

/-- **Step 4: Massart.** For a sample in `[-1, 1]^d` with `d ≥ 1`, the `2d` signed coordinate
vectors have empirical Rademacher complexity at most `√(2 log (2d) / n)`, by Massart's
finite-class lemma with radius `√n`. -/
lemma rademacherComplexity_signedColumns_le (hd : 0 < d) {x : Fin n → Fin d → ℝ}
    (hx : ∀ i j, |x i j| ≤ 1) :
    rademacherComplexity (signedColumns x) ≤ √(2 * log (2 * d) / n) := by
  have hfin : (signedColumns x).Finite := Set.finite_range _
  have hne : (signedColumns x).Nonempty := ⟨_, ⟨(⟨0, hd⟩, true), rfl⟩⟩
  have hnorm : ∀ a ∈ signedColumns x, ∑ i, a i ^ 2 ≤ (√(n : ℝ)) ^ 2 := by
    rintro _ ⟨⟨j, b⟩, rfl⟩
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    calc ∑ i, ((if b then (1 : ℝ) else -1) * x i j) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : ((if b then (1 : ℝ) else -1) * x i j) ^ 2 = |x i j| ^ 2 := by
            cases b <;> simp [sq_abs]
          rw [h1]
          have := hx i j
          have := abs_nonneg (x i j)
          nlinarith
      _ = n := by simp
  have hM := rademacherComplexity_le_of_finite hfin hne (Real.sqrt_nonneg _) hnorm
  have hcard : (signedColumns x).ncard ≤ 2 * d := by
    rw [signedColumns, ← Set.image_univ]
    calc _ ≤ (Set.univ : Set (Fin d × Bool)).ncard := Set.ncard_image_le Set.finite_univ
      _ = 2 * d := by rw [Set.ncard_univ]; simp [mul_comm]
  have hcard1 : 1 ≤ (signedColumns x).ncard := (Set.ncard_pos hfin).2 hne
  have hlog : log (signedColumns x).ncard ≤ log (2 * d) := by
    apply Real.log_le_log (by exact_mod_cast hcard1)
    exact_mod_cast hcard
  refine hM.trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.2 hn'
  calc √(n : ℝ) * √(2 * log (signedColumns x).ncard) / n
        ≤ √(n : ℝ) * √(2 * log (2 * d)) / n := by gcongr
    _ = √(2 * log (2 * d) / n) := by
        rw [Real.sqrt_div' _ hn'.le, eq_div_iff hs.ne', div_mul_eq_mul_div,
          mul_comm (√(n : ℝ)) (√(2 * log (2 * d))), mul_assoc, Real.mul_self_sqrt hn'.le,
          mul_div_assoc, div_self hn'.ne', mul_one]

/-- **Correlation of one neuron.** The neuron with inner weights `w` is `‖w‖₁` times a neuron
of the `ℓ¹` unit ball, so its
correlation with a sign vector is at most `‖w‖₁` times the two one-sided suprema. -/
lemma abs_signCorr_neuron_le {x : Fin n → Fin d → ℝ} (hx : ∀ i j, |x i j| ≤ 1)
    (ε : Fin n → Bool) (w : Fin d → ℝ) :
    |signCorr ε (fun i => max (∑ j, w j * x i j) 0)| ≤
      (∑ j, |w j|) * (supCorr (l1NeuronValues x) ε +
        supCorr (l1NeuronValues x) (flipSigns ε)) := by
  set r := ∑ j, |w j| with hr
  have hr0 : 0 ≤ r := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hb := bddAbove_signCorr_image (isBounded_l1NeuronValues hx)
  have hmem : ∀ u : Fin d → ℝ, ∑ j, |u j| ≤ 1 →
      |signCorr ε (fun i => max (∑ j, u j * x i j) 0)| ≤
        supCorr (l1NeuronValues x) ε + supCorr (l1NeuronValues x) (flipSigns ε) := by
    intro u hu
    have h1 : signCorr ε (fun i => max (∑ j, u j * x i j) 0) ≤ supCorr (l1NeuronValues x) ε :=
      le_csSup (hb ε) ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have h2 : signCorr (flipSigns ε) (fun i => max (∑ j, u j * x i j) 0) ≤
        supCorr (l1NeuronValues x) (flipSigns ε) :=
      le_csSup (hb _) ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    rw [signCorr_flipSigns] at h2
    have h3 := supCorr_l1NeuronValues_nonneg hx ε
    have h4 := supCorr_l1NeuronValues_nonneg hx (flipSigns ε)
    rw [abs_le]
    constructor <;> linarith
  rcases hr0.eq_or_lt with h | h
  · have hw : ∀ j, w j = 0 := fun j => abs_eq_zero.1
      ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => abs_nonneg (w j)).1 h.symm j
        (Finset.mem_univ j))
    rw [← h]
    simp [hw, signCorr]
  · set u : Fin d → ℝ := fun j => w j / r with hu_def
    have hu : ∑ j, |u j| ≤ 1 := by
      have : ∑ j, |u j| = (∑ j, |w j|) / r := by
        simp only [hu_def, abs_div, abs_of_pos h, Finset.sum_div]
      rw [this, ← hr, div_self h.ne']
    have hscale : (fun i => max (∑ j, w j * x i j) 0) =
        r • (fun i => max (∑ j, u j * x i j) 0) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      have hlin : ∑ j, u j * x i j = r⁻¹ * ∑ j, w j * x i j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by simp only [hu_def]; ring
      have hm : max (r⁻¹ * ∑ j, w j * x i j) 0 = r⁻¹ * max (∑ j, w j * x i j) 0 := by
        rw [mul_max_of_nonneg _ _ (inv_nonneg.2 hr0), mul_zero]
      rw [hlin, hm, ← mul_assoc, mul_inv_cancel₀ h.ne', one_mul]
    rw [hscale, signCorr_smul, abs_mul, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left (hmem u hu) hr0

/-- **Step 1: homogeneity.** For a sample in `[-1, 1]^d` and `Q ≥ 0`, the correlation of every
network of path norm at most `Q` with a sign vector `σ` is at most `Q` times the sum of the
suprema over the `ℓ¹`-ball neurons for `σ` and for `-σ`. -/
lemma supCorr_pathNormBallValues_le {x : Fin n → Fin d → ℝ} (hx : ∀ i j, |x i j| ≤ 1)
    {Q : ℝ} (hQ : 0 ≤ Q) (ε : Fin n → Bool) :
    supCorr (pathNormBallValues x Q) ε ≤
      Q * (supCorr (l1NeuronValues x) ε + supCorr (l1NeuronValues x) (flipSigns ε)) := by
  set S := supCorr (l1NeuronValues x) ε + supCorr (l1NeuronValues x) (flipSigns ε) with hS_def
  have hS : 0 ≤ S :=
    add_nonneg (supCorr_l1NeuronValues_nonneg hx ε) (supCorr_l1NeuronValues_nonneg hx _)
  refine csSup_le (Set.Nonempty.image _
    ⟨_, 0, Fin.elim0, Fin.elim0, by simp [pathNorm, hQ], rfl⟩) ?_
  rintro _ ⟨_, ⟨m, a, w, hpath, rfl⟩, rfl⟩
  have hexp : signCorr ε (fun i => twoLayerReLU a w (x i)) =
      ∑ k, a k * signCorr ε (fun i => max (∑ j, w k j * x i j) 0) := by
    simp only [signCorr, twoLayerReLU, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hexp]
  calc ∑ k, a k * signCorr ε (fun i => max (∑ j, w k j * x i j) 0)
        ≤ ∑ k, |a k| * ((∑ j, |w k j|) * S) := by
        refine Finset.sum_le_sum fun k _ => ?_
        calc a k * signCorr ε (fun i => max (∑ j, w k j * x i j) 0)
              ≤ |a k * signCorr ε (fun i => max (∑ j, w k j * x i j) 0)| := le_abs_self _
          _ = |a k| * |signCorr ε (fun i => max (∑ j, w k j * x i j) 0)| := abs_mul _ _
          _ ≤ |a k| * ((∑ j, |w k j|) * S) :=
              mul_le_mul_of_nonneg_left (abs_signCorr_neuron_le hx ε (w k)) (abs_nonneg _)
    _ = pathNorm a w * S := by
        rw [pathNorm, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ Q * S := mul_le_mul_of_nonneg_right hpath hS

/-- **Rademacher complexity of path-norm balls of two-layer ReLU networks.** Let `d ≥ 1`, let
`x₁, …, xₙ ∈ ℝ^d` with every coordinate in `[-1, 1]`, and let `Q ≥ 0`. The set of value
vectors `(f(x₁), …, f(xₙ))` of the two-layer ReLU networks `f(x) = ∑ₖ aₖ max(⟨wₖ, x⟩, 0)` of
any width with path norm `∑ₖ |aₖ| ‖wₖ‖₁ ≤ Q` has empirical Rademacher complexity
`R ≤ 2 Q √(2 log (2d) / n)`.
Source: W. E, C. Ma and L. Wu, *A priori estimates of the population risk for two-layer neural
networks*, Commun. Math. Sci. 17 (2019), bound (5.1) (attributed there to Neyshabur, Tomioka and
Srebro, COLT 2015), with data in `X = [-1, 1]^d`; the proof is that of Theorem 6 of E, Ma and
Wu, *The Barron space and the flow-induced function spaces for neural network models*,
Constr. Approx. 55 (2022), §2.5.5: homogeneity, symmetry of the signs, contraction, and
Massart's lemma for the `2d` signed coordinates. -/
theorem rademacherComplexity_pathNormBallValues_le (hd : 0 < d) {x : Fin n → Fin d → ℝ}
    (hx : ∀ i j, |x i j| ≤ 1) {Q : ℝ} (hQ : 0 ≤ Q) :
    rademacherComplexity (pathNormBallValues x Q) ≤ 2 * Q * √(2 * log (2 * d) / n) := by
  have h1 : rademacherComplexity (pathNormBallValues x Q) ≤
      2 * Q * rademacherComplexity (l1NeuronValues x) := by
    unfold rademacherComplexity
    have hsum : ∑ ε, supCorr (pathNormBallValues x Q) ε ≤
        ∑ ε, Q * (supCorr (l1NeuronValues x) ε + supCorr (l1NeuronValues x) (flipSigns ε)) :=
      Finset.sum_le_sum fun ε _ => supCorr_pathNormBallValues_le hx hQ ε
    have heq : ∑ ε, Q * (supCorr (l1NeuronValues x) ε +
        supCorr (l1NeuronValues x) (flipSigns ε)) =
        2 * Q * ∑ ε, supCorr (l1NeuronValues x) ε := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        sum_flipSigns (fun ε => supCorr (l1NeuronValues x) ε)]
      ring
    rw [heq] at hsum
    calc (n : ℝ)⁻¹ * (((2 : ℝ) ^ n)⁻¹ * ∑ ε, supCorr (pathNormBallValues x Q) ε)
          ≤ (n : ℝ)⁻¹ * (((2 : ℝ) ^ n)⁻¹ * (2 * Q * ∑ ε, supCorr (l1NeuronValues x) ε)) := by
          gcongr
      _ = 2 * Q * ((n : ℝ)⁻¹ * (((2 : ℝ) ^ n)⁻¹ * ∑ ε, supCorr (l1NeuronValues x) ε)) := by
          ring
  have h2Q : 0 ≤ 2 * Q := by linarith
  calc rademacherComplexity (pathNormBallValues x Q)
        ≤ 2 * Q * rademacherComplexity (l1NeuronValues x) := h1
    _ ≤ 2 * Q * rademacherComplexity (signedColumns x) :=
        mul_le_mul_of_nonneg_left ((rademacherComplexity_l1NeuronValues_le hx).trans
          (rademacherComplexity_l1LinearValues_le hd x)) h2Q
    _ ≤ 2 * Q * √(2 * log (2 * d) / n) :=
        mul_le_mul_of_nonneg_left (rademacherComplexity_signedColumns_le hd hx) h2Q

/-! ### Networks with a bias term -/

/-- **Two-layer ReLU network with bias** of width `m`:
`f(x; θ) = ∑ₖ aₖ max(⟨bₖ, x⟩ + cₖ, 0)` (W. E, C. Ma and L. Wu, *The Barron space and the
flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022), the network
`f_m` of §2.1, written here without the normalisation `1/m`, which the outer weights absorb). -/
def twoLayerReLUBias {m : ℕ} (a : Fin m → ℝ) (b : Fin m → Fin d → ℝ) (c : Fin m → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  ∑ k, a k * max (∑ j, b k j * x j + c k) 0

/-- **Path norm with bias** of a two-layer network: `∑ₖ |aₖ| (‖bₖ‖₁ + |cₖ|)` (E, Ma and Wu,
*The Barron space and the flow-induced function spaces*, Theorem 4, there with the factor
`1/m`). -/
def pathNormBias {m : ℕ} (a : Fin m → ℝ) (b : Fin m → Fin d → ℝ) (c : Fin m → ℝ) : ℝ :=
  ∑ k, |a k| * (∑ j, |b k j| + |c k|)

/-- **Path-norm ball with bias on a sample.** The value vectors on a sample `x : Fin n → ℝ^d` of
the two-layer ReLU networks with bias of any width and path norm at most `Q`. -/
def pathNormBallBiasValues (x : Fin n → Fin d → ℝ) (Q : ℝ) : Set (Fin n → ℝ) :=
  {v | ∃ (m : ℕ) (a : Fin m → ℝ) (b : Fin m → Fin d → ℝ) (c : Fin m → ℝ),
    pathNormBias a b c ≤ Q ∧ v = fun i => twoLayerReLUBias a b c (x i)}

/-- **Bias as an extra input coordinate.** Appending the constant coordinate `1` to every sample
point turns networks with bias into networks without bias in one more dimension. -/
lemma pathNormBallBiasValues_eq (x : Fin n → Fin d → ℝ) (Q : ℝ) :
    pathNormBallBiasValues x Q =
      pathNormBallValues (fun i => (Fin.snoc (x i) 1 : Fin (d + 1) → ℝ)) Q := by
  ext v
  constructor
  · rintro ⟨m, a, b, c, hpath, rfl⟩
    refine ⟨m, a, fun k => (Fin.snoc (b k) (c k) : Fin (d + 1) → ℝ), ?_, ?_⟩
    · simpa [pathNorm, pathNormBias, Fin.sum_univ_castSucc] using hpath
    · funext i
      simp [twoLayerReLU, twoLayerReLUBias, Fin.sum_univ_castSucc]
  · rintro ⟨m, a, w, hpath, rfl⟩
    refine ⟨m, a, fun k j => w k j.castSucc, fun k => w k (Fin.last d), ?_, ?_⟩
    · simpa [pathNorm, pathNormBias, Fin.sum_univ_castSucc] using hpath
    · funext i
      simp [twoLayerReLU, twoLayerReLUBias, Fin.sum_univ_castSucc]

/-- **Rademacher complexity of path-norm balls of two-layer ReLU networks with bias.** Let
`x₁, …, xₙ ∈ ℝ^d` with every coordinate in `[-1, 1]`, and let `Q ≥ 0`. The set of value vectors
of the networks `f(x) = ∑ₖ aₖ max(⟨bₖ, x⟩ + cₖ, 0)` of any width with
`∑ₖ |aₖ| (‖bₖ‖₁ + |cₖ|) ≤ Q` has empirical Rademacher complexity
`R ≤ 2 Q √(2 log (2(d + 1)) / n)`.
This is the finite-width form of Theorem 6 of W. E, C. Ma and L. Wu, *The Barron space and the
flow-induced function spaces for neural network models*, Constr. Approx. 55 (2022), by the proof
of their §2.5.5, which works with `x̃ = (x, 1) ∈ ℝ^{d+1}`; that proof yields `log (2(d + 1))`,
while their statement writes `log (2d)`. Here it follows from
`rademacherComplexity_pathNormBallValues_le` in dimension `d + 1`. -/
theorem rademacherComplexity_pathNormBallBiasValues_le {x : Fin n → Fin d → ℝ}
    (hx : ∀ i j, |x i j| ≤ 1) {Q : ℝ} (hQ : 0 ≤ Q) :
    rademacherComplexity (pathNormBallBiasValues x Q) ≤
      2 * Q * √(2 * log (2 * (d + 1)) / n) := by
  have hx' : ∀ i j, |(Fin.snoc (x i) 1 : Fin (d + 1) → ℝ) j| ≤ 1 := by
    intro i j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simpa using hx i j
  rw [pathNormBallBiasValues_eq]
  simpa using rademacherComplexity_pathNormBallValues_le (Nat.succ_pos d) hx' hQ

end CSLibExt.MachineLearning.GeneralizationBounds
