/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Basic.Real.Pointwise
public import MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype
public import MathlibExt.Combinatorics.BinomialPartialSum
public import MathlibExt.Combinatorics.SetFamily.VCDim

/-!
# Empirical Rademacher complexity of a set of vectors

For a set `A ⊆ ℝⁿ` (in learning theory, the set of value vectors
`(f(x₁), …, f(xₙ))` of a function class on a fixed sample), the empirical Rademacher
complexity is

`R(A) = (1/n) 𝔼_σ sup_{a ∈ A} ∑ᵢ σᵢ aᵢ`,

the expectation being the uniform average over the `2ⁿ` sign vectors `σ ∈ {±1}ⁿ`
(`rademacherComplexity`). This is the convention of Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, CUP 2014, Section 26.1, equation (26.5), and of Bartlett,
Foster and Telgarsky (NeurIPS 2017, Section 3.1). Bartlett and Mendelson (*Rademacher and Gaussian
complexities: risk bounds and structural results*, JMLR 3, 2002, Definition 2) instead use
`𝔼 sup |(2/n) ∑ σᵢ aᵢ|`; their structural results have counterparts in this convention, and several
inequalities become identities here because `𝔼 σᵢ = 0`.

The supremum is `sSup` in `ℝ`, so statements that need it assume `A` bounded (and
nonempty); a finite set is bounded.

Main results:

* `rademacherComplexity_mono`: monotonicity in `A` (Bartlett–Mendelson, Theorem 12.1).
* `rademacherComplexity_convexHull`: `R(conv A) = R(A)` (Theorem 12.2; Shalev-Shwartz and
  Ben-David, Lemma 26.7).
* `rademacherComplexity_smul`: `R(c • A) = |c| R(A)` (Theorem 12.3; the inequality `≤` is
  Shalev-Shwartz and Ben-David, Lemma 26.6).
* `rademacherComplexity_add`: `R(A + B) = R(A) + R(B)` for the Minkowski sum
  (Theorem 12.7 is the inequality `≤` in the absolute-value convention), and
  `rademacherComplexity_add_singleton`: translation invariance (compare Theorem 12.5).
* `rademacherComplexity_le_of_finite`: **Massart's finite-class lemma**
  `R(A) ≤ r √(2 log |A|) / n` when every `a ∈ A` has Euclidean norm at most `r`
  (Massart 2000, Lemma 5.2; Shalev-Shwartz–Ben-David, Lemma 26.8, state it with the vectors
  centred at their mean, which this uncentred form does not assume).
* `rademacherComplexity_signPatterns_le`: for the sign patterns that a family `𝒜` of
  subsets of the sample realizes, Massart's lemma and the Sauer–Shelah lemma give
  `R ≤ √(2 log (∑_{k ≤ d} C(n, k)) / n)` with `d` the VC dimension of `𝒜`, and
  `rademacherComplexity_signPatterns_le_vcDim`: `R ≤ √(2 d log (e n / d) / n)` when `d ≥ 1`
  (Shalev-Shwartz and Ben-David, Section 28.1), through `Real.sum_choose_le_exp_mul_div_pow`,
  `∑_{k ≤ d} C(n, k) ≤ (e n / d)^d`, and `Finset.vcDim_le_card`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.Rademacher

open Finset Real Pointwise
open MathlibExt.Analysis.InnerProductSpace.RademacherTypeCotype (rademacherSign card_sign_vectors
  norm_rademacherSign)

variable {n : ℕ}

/-- The correlation `∑ᵢ σᵢ aᵢ` of a vector `a ∈ ℝⁿ` with the sign vector `σ` encoded by
`ε : Fin n → Bool` (`σᵢ = 1` when `ε i` is `true`, `-1` otherwise). -/
noncomputable def signCorr (ε : Fin n → Bool) (a : Fin n → ℝ) : ℝ :=
  ∑ i, rademacherSign ℝ ε i * a i

/-- The supremum `sup_{a ∈ A} ∑ᵢ σᵢ aᵢ` of the correlations with one sign vector
(`sSup` in `ℝ`, hence `0` for an empty or unbounded-above set). -/
noncomputable def supCorr (A : Set (Fin n → ℝ)) (ε : Fin n → Bool) : ℝ :=
  sSup (signCorr ε '' A)

/-- The **empirical Rademacher complexity** `R(A) = (1/n) 𝔼_σ sup_{a ∈ A} ∑ᵢ σᵢ aᵢ` of
`A ⊆ ℝⁿ`, the expectation being the uniform average over the `2ⁿ` sign vectors
(Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Section 26.1, equation (26.5)). -/
noncomputable def rademacherComplexity (A : Set (Fin n → ℝ)) : ℝ :=
  (n : ℝ)⁻¹ * (((2 : ℝ) ^ n)⁻¹ * ∑ ε : Fin n → Bool, supCorr A ε)

/-- The sign vector with every sign reversed. -/
def flipSigns (ε : Fin n → Bool) : Fin n → Bool := fun i => !ε i

lemma flipSigns_involutive : Function.Involutive (flipSigns (n := n)) := by
  intro ε; funext i; simp [flipSigns]

lemma rademacherSign_flipSigns (ε : Fin n → Bool) (i : Fin n) :
    rademacherSign ℝ (flipSigns ε) i = -rademacherSign ℝ ε i := by
  unfold rademacherSign flipSigns
  cases ε i <;> simp

/-- Reversing every sign negates the correlation. -/
lemma signCorr_flipSigns (ε : Fin n → Bool) (a : Fin n → ℝ) :
    signCorr (flipSigns ε) a = -signCorr ε a := by
  simp [signCorr, rademacherSign_flipSigns, ← Finset.sum_neg_distrib]

/-- Averages over sign vectors are invariant under reversing every sign. -/
lemma sum_flipSigns (g : (Fin n → Bool) → ℝ) :
    ∑ ε, g (flipSigns ε) = ∑ ε, g ε :=
  Fintype.sum_equiv (flipSigns_involutive.toPerm _) _ _ (fun _ => rfl)

/-- The correlations of a fixed vector average to zero over the sign vectors. -/
lemma sum_signCorr (a : Fin n → ℝ) : ∑ ε, signCorr ε a = 0 := by
  have h := sum_flipSigns (fun ε => signCorr ε a)
  simp only [signCorr_flipSigns, Finset.sum_neg_distrib] at h
  linarith

lemma signCorr_add (ε : Fin n → Bool) (a b : Fin n → ℝ) :
    signCorr ε (a + b) = signCorr ε a + signCorr ε b := by
  simp [signCorr, mul_add, Finset.sum_add_distrib]

lemma signCorr_smul (ε : Fin n → Bool) (c : ℝ) (a : Fin n → ℝ) :
    signCorr ε (c • a) = c * signCorr ε a := by
  simp only [signCorr, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma isLinearMap_signCorr (ε : Fin n → Bool) : IsLinearMap ℝ (signCorr ε) :=
  ⟨signCorr_add ε, signCorr_smul ε⟩

lemma signCorr_le_norm (ε : Fin n → Bool) (a : Fin n → ℝ) : signCorr ε a ≤ n * ‖a‖ := by
  calc signCorr ε a ≤ ∑ _i : Fin n, ‖a‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc rademacherSign ℝ ε i * a i ≤ |rademacherSign ℝ ε i * a i| := le_abs_self _
          _ = ‖a i‖ := by
              rw [abs_mul, ← Real.norm_eq_abs (rademacherSign ℝ ε i), norm_rademacherSign,
                one_mul, Real.norm_eq_abs]
          _ ≤ ‖a‖ := norm_le_pi_norm a i
    _ = n * ‖a‖ := by simp

/-- On a bounded set the correlations with a sign vector are bounded above. -/
lemma bddAbove_signCorr_image {A : Set (Fin n → ℝ)} (hA : Bornology.IsBounded A)
    (ε : Fin n → Bool) : BddAbove (signCorr ε '' A) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hA
  refine ⟨n * C, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact (signCorr_le_norm ε a).trans (by gcongr; exact hC a ha)

/-- **Monotonicity** (Bartlett–Mendelson, Theorem 12.1): a nonempty subset of a bounded set
has smaller empirical Rademacher complexity. -/
theorem rademacherComplexity_mono {A B : Set (Fin n → ℝ)} (hAB : A ⊆ B) (hA : A.Nonempty)
    (hB : Bornology.IsBounded B) : rademacherComplexity A ≤ rademacherComplexity B := by
  unfold rademacherComplexity
  gcongr with ε
  exact csSup_le_csSup (bddAbove_signCorr_image hB ε) (hA.image _) (Set.image_mono hAB)

/-- The supremum of the correlations over the convex hull is the supremum over the set. -/
lemma supCorr_convexHull {A : Set (Fin n → ℝ)} (hne : A.Nonempty)
    (hA : Bornology.IsBounded A) (ε : Fin n → Bool) :
    supCorr (convexHull ℝ A) ε = supCorr A ε := by
  apply le_antisymm
  · refine csSup_le ((hne.mono (subset_convexHull ℝ A)).image _) ?_
    rintro _ ⟨x, hx, rfl⟩
    have hsub : convexHull ℝ A ⊆ {y | signCorr ε y ≤ supCorr A ε} :=
      convexHull_min (fun a ha => le_csSup (bddAbove_signCorr_image hA ε) ⟨a, ha, rfl⟩)
        (convex_halfSpace_le (isLinearMap_signCorr ε) _)
    exact hsub hx
  · exact csSup_le_csSup (bddAbove_signCorr_image (isBounded_convexHull.2 hA) ε)
      (hne.image _) (Set.image_mono (subset_convexHull ℝ A))

/-- **Convex hull invariance** (Bartlett–Mendelson, Theorem 12.2; Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, Lemma 26.7): a nonempty bounded set and its convex hull have
the same empirical Rademacher complexity. -/
theorem rademacherComplexity_convexHull {A : Set (Fin n → ℝ)} (hne : A.Nonempty)
    (hA : Bornology.IsBounded A) :
    rademacherComplexity (convexHull ℝ A) = rademacherComplexity A := by
  simp only [rademacherComplexity, supCorr_convexHull hne hA]

lemma signCorr_image_smul (A : Set (Fin n → ℝ)) (c : ℝ) (ε : Fin n → Bool) :
    signCorr ε '' (c • A) = c • (signCorr ε '' A) := by
  rw [← Set.image_smul, ← Set.image_smul, Set.image_image, Set.image_image]
  simp only [signCorr_smul, smul_eq_mul]

lemma supCorr_smul_of_nonneg (A : Set (Fin n → ℝ)) {c : ℝ} (hc : 0 ≤ c) (ε : Fin n → Bool) :
    supCorr (c • A) ε = c * supCorr A ε := by
  rw [supCorr, signCorr_image_smul, Real.sSup_smul_of_nonneg hc, smul_eq_mul, supCorr]

lemma supCorr_neg_smul (A : Set (Fin n → ℝ)) (c : ℝ) (ε : Fin n → Bool) :
    supCorr ((-c) • A) ε = supCorr (c • A) (flipSigns ε) := by
  unfold supCorr
  congr 1
  rw [signCorr_image_smul, signCorr_image_smul, ← Set.image_smul, ← Set.image_smul,
    Set.image_image, Set.image_image]
  simp only [signCorr_flipSigns, smul_eq_mul]
  ext x; simp only [Set.mem_image]
  constructor <;> rintro ⟨a, ha, rfl⟩ <;> exact ⟨a, ha, by ring⟩

/-- **Scaling** (Bartlett–Mendelson, Theorem 12.3; Shalev-Shwartz and Ben-David, *Understanding
Machine Learning*, Lemma 26.6, the inequality `≤`): `R(c • A) = |c| R(A)` for every real `c`
and every set `A`. -/
theorem rademacherComplexity_smul (A : Set (Fin n → ℝ)) (c : ℝ) :
    rademacherComplexity (c • A) = |c| * rademacherComplexity A := by
  have key : ∑ ε, supCorr (c • A) ε = |c| * ∑ ε, supCorr A ε := by
    rcases le_or_gt 0 c with hc | hc
    · simp [supCorr_smul_of_nonneg A hc, abs_of_nonneg hc, Finset.mul_sum]
    · have hc' : c = -|c| := by rw [abs_of_neg hc]; ring
      rw [hc']
      simp only [supCorr_neg_smul, supCorr_smul_of_nonneg A (abs_nonneg c),
        abs_neg, abs_abs, ← Finset.mul_sum]
      rw [sum_flipSigns (fun ε => supCorr A ε)]
  unfold rademacherComplexity
  rw [key]; ring

lemma signCorr_image_add (A B : Set (Fin n → ℝ)) (ε : Fin n → Bool) :
    signCorr ε '' (A + B) = signCorr ε '' A + signCorr ε '' B := by
  rw [← Set.image2_add, ← Set.image2_add]
  exact Set.image_image2_distrib (signCorr_add ε)

lemma supCorr_add {A B : Set (Fin n → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty)
    (hA' : Bornology.IsBounded A) (hB' : Bornology.IsBounded B) (ε : Fin n → Bool) :
    supCorr (A + B) ε = supCorr A ε + supCorr B ε := by
  rw [supCorr, signCorr_image_add]
  exact csSup_add (hA.image _) (bddAbove_signCorr_image hA' ε) (hB.image _)
    (bddAbove_signCorr_image hB' ε)

/-- **Minkowski sums** (compare Bartlett–Mendelson, Theorem 12.7, an inequality in their
absolute-value convention): for nonempty bounded `A` and `B`, `R(A + B) = R(A) + R(B)`. -/
theorem rademacherComplexity_add {A B : Set (Fin n → ℝ)} (hA : A.Nonempty) (hB : B.Nonempty)
    (hA' : Bornology.IsBounded A) (hB' : Bornology.IsBounded B) :
    rademacherComplexity (A + B) = rademacherComplexity A + rademacherComplexity B := by
  simp only [rademacherComplexity, supCorr_add hA hB hA' hB', Finset.sum_add_distrib]
  ring

/-- A single vector has empirical Rademacher complexity zero. -/
theorem rademacherComplexity_singleton (v : Fin n → ℝ) :
    rademacherComplexity ({v} : Set (Fin n → ℝ)) = 0 := by
  simp [rademacherComplexity, supCorr, sum_signCorr]

/-- **Translation invariance** (compare Bartlett–Mendelson, Theorem 12.5, which bounds the
change by `‖v‖_∞ / √n` in their convention, and Shalev-Shwartz and Ben-David, Lemma 26.6, the
inequality `≤`): `R(A + {v}) = R(A)` for nonempty bounded `A`. -/
theorem rademacherComplexity_add_singleton {A : Set (Fin n → ℝ)} (hA : A.Nonempty)
    (hA' : Bornology.IsBounded A) (v : Fin n → ℝ) :
    rademacherComplexity (A + {v}) = rademacherComplexity A := by
  rw [rademacherComplexity_add hA (Set.singleton_nonempty v) hA' Bornology.isBounded_singleton,
    rademacherComplexity_singleton, add_zero]

/-! ### Massart's finite-class lemma -/

/-- Averaging `exp (∑ᵢ σᵢ xᵢ)` over the sign vectors gives `∏ᵢ cosh xᵢ`. -/
lemma sum_exp_signCorr (x : Fin n → ℝ) :
    ∑ ε : Fin n → Bool, exp (signCorr ε x) = 2 ^ n * ∏ i, cosh (x i) := by
  have h1 : ∀ ε : Fin n → Bool, exp (signCorr ε x) =
      ∏ i, (fun i (b : Bool) => exp ((if b then 1 else -1) * x i)) i (ε i) := by
    intro ε
    simp only [signCorr, Real.exp_sum, rademacherSign]
  simp only [h1]
  have h3 := Fintype.prod_sum
    (fun (i : Fin n) (b : Bool) => exp ((if b then (1 : ℝ) else -1) * x i))
  rw [← h3]
  have h2 : ∀ i, ∑ b : Bool, exp ((if b then (1 : ℝ) else -1) * x i) = 2 * cosh (x i) := by
    intro i
    rw [Fintype.sum_bool, Real.cosh_eq]
    simp only [ite_true, one_mul, Bool.false_eq_true, ite_false, neg_mul]
    ring
  simp only [h2, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- The exponential moment of a Rademacher sum: the average of `exp (∑ᵢ σᵢ xᵢ)` over the sign
vectors is at most `exp (∑ᵢ xᵢ² / 2)` (`cosh x ≤ exp (x² / 2)`). -/
lemma average_exp_signCorr_le (x : Fin n → ℝ) :
    ((2 : ℝ) ^ n)⁻¹ * ∑ ε : Fin n → Bool, exp (signCorr ε x) ≤ exp ((∑ i, x i ^ 2) / 2) := by
  rw [sum_exp_signCorr, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul,
    Finset.sum_div, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun i _ => (cosh_pos _).le) (fun i _ => cosh_le_exp_half_sq _)

/-- A real number bounded by `a / λ + λ b` for every `λ > 0`, with `a, b ≥ 0`, is at most
`2 √(a b)`. -/
lemma le_two_mul_sqrt_of_forall {x a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ t : ℝ, 0 < t → x ≤ a / t + t * b) : x ≤ 2 * sqrt (a * b) := by
  rcases ha.eq_or_lt with ha0 | ha0
  · subst ha0
    simp only [zero_mul, sqrt_zero, mul_zero]
    refine le_of_forall_pos_lt_add fun d hd => ?_
    have := h (d / (b + 1)) (by positivity)
    have hlt : d / (b + 1) * b < d := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    simp only [zero_div, zero_add] at this
    linarith
  rcases hb.eq_or_lt with hb0 | hb0
  · subst hb0
    simp only [mul_zero, sqrt_zero]
    refine le_of_forall_pos_lt_add fun d hd => ?_
    have := h ((a + 1) / d) (by positivity)
    have hlt : a / ((a + 1) / d) < d := by
      rw [div_div_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
    simp only [mul_zero, add_zero] at this
    linarith
  · have ht : 0 < sqrt (a / b) := sqrt_pos.2 (div_pos ha0 hb0)
    have := h (sqrt (a / b)) ht
    have hab : sqrt (a / b) * sqrt (a / b) = a / b := mul_self_sqrt (div_pos ha0 hb0).le
    have hs : sqrt (a * b) = sqrt (a / b) * b := by
      rw [show a * b = (a / b) * b ^ 2 by field_simp, sqrt_mul (div_pos ha0 hb0).le,
        sqrt_sq hb0.le]
    have hq : a / sqrt (a / b) = sqrt (a / b) * b := by
      have h4 : sqrt (a / b) * b * sqrt (a / b) = a := by
        rw [mul_right_comm, hab]; field_simp
      rw [div_eq_iff ht.ne', h4]
    rw [hs]
    linarith

/-- **Massart's finite-class lemma** (P. Massart, *Some applications of concentration
inequalities to statistics*, Ann. Fac. Sci. Toulouse Math. 9, 2000, Lemma 5.2; Shalev-Shwartz
and Ben-David, *Understanding Machine Learning*, Lemma 26.8, state it with the vectors centred
at their mean, and their proof without the centring step gives this form): if `A ⊆ ℝⁿ` is
finite and nonempty and every `a ∈ A` has Euclidean norm at most `r`, then
`R(A) ≤ r √(2 log |A|) / n`. -/
theorem rademacherComplexity_le_of_finite {A : Set (Fin n → ℝ)} (hA : A.Finite)
    (hne : A.Nonempty) {r : ℝ} (hr : 0 ≤ r) (hnorm : ∀ a ∈ A, ∑ i, a i ^ 2 ≤ r ^ 2) :
    rademacherComplexity A ≤ r * sqrt (2 * log A.ncard) / n := by
  set w : ℝ := ((2 : ℝ) ^ n)⁻¹ with hw
  set N : ℝ := (A.ncard : ℝ) with hN
  have hNpos : 1 ≤ N := by
    rw [hN]; exact_mod_cast (Set.ncard_pos hA).2 hne
  have hlogN : 0 ≤ log N := log_nonneg hNpos
  have hcard : ∑ _ε : Fin n → Bool, w = 1 := by
    simp [hw]
  -- the attained supremum on a finite set
  have hmem : ∀ ε, ∃ a ∈ A, supCorr A ε = signCorr ε a := by
    intro ε
    obtain ⟨a, ha, h⟩ := (hne.image (signCorr ε)).csSup_mem (hA.image _)
    exact ⟨a, ha, h.symm⟩
  have key : ∀ t : ℝ, 0 < t → w * ∑ ε, supCorr A ε ≤ log N / t + t * (r ^ 2 / 2) := by
    intro t ht
    -- Jensen, then the attained supremum, then the exponential moment
    have hJ : exp (t * (w * ∑ ε, supCorr A ε)) ≤ ∑ ε : Fin n → Bool, w * exp (t * supCorr A ε) := by
      have := (convexOn_exp).map_sum_le (t := (Finset.univ : Finset (Fin n → Bool)))
        (w := fun _ => w) (p := fun ε => t * supCorr A ε) (fun _ _ => by positivity)
        (by simpa using hcard) (fun _ _ => Set.mem_univ _)
      simpa [smul_eq_mul, Finset.mul_sum, mul_left_comm] using this
    have hS : ∀ ε, exp (t * supCorr A ε) ≤ ∑ a ∈ hA.toFinset, exp (t * signCorr ε a) := by
      intro ε
      obtain ⟨a, ha, h⟩ := hmem ε
      rw [h]
      exact Finset.single_le_sum (f := fun a => exp (t * signCorr ε a))
        (fun _ _ => (exp_pos _).le) (hA.mem_toFinset.2 ha)
    have hE : ∀ a ∈ hA.toFinset, w * ∑ ε : Fin n → Bool, exp (t * signCorr ε a)
        ≤ exp (t ^ 2 * (r ^ 2 / 2)) := by
      intro a ha
      have h1 : ∀ ε, t * signCorr ε a = signCorr ε (t • a) := fun ε =>
        (signCorr_smul ε t a).symm
      simp only [h1]
      refine (average_exp_signCorr_le _).trans ?_
      gcongr
      have : ∑ i, (t • a) i ^ 2 = t ^ 2 * ∑ i, a i ^ 2 := by
        simp [mul_pow, Finset.mul_sum]
      rw [this]
      have := hnorm a (hA.mem_toFinset.1 ha)
      nlinarith [sq_nonneg t]
    have hchain : exp (t * (w * ∑ ε, supCorr A ε)) ≤ N * exp (t ^ 2 * (r ^ 2 / 2)) := by
      calc exp (t * (w * ∑ ε, supCorr A ε))
          ≤ ∑ ε : Fin n → Bool, w * exp (t * supCorr A ε) := hJ
        _ ≤ ∑ ε : Fin n → Bool, w * ∑ a ∈ hA.toFinset, exp (t * signCorr ε a) := by
            gcongr with ε; exact hS ε
        _ = ∑ a ∈ hA.toFinset, w * ∑ ε : Fin n → Bool, exp (t * signCorr ε a) := by
            simp only [Finset.mul_sum]; exact Finset.sum_comm
        _ ≤ ∑ _a ∈ hA.toFinset, exp (t ^ 2 * (r ^ 2 / 2)) := Finset.sum_le_sum hE
        _ = N * exp (t ^ 2 * (r ^ 2 / 2)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hN, Set.ncard_eq_toFinset_card A hA]
    have hlog := Real.log_le_log (exp_pos _) hchain
    rw [Real.log_exp, Real.log_mul (by positivity) (exp_pos _).ne', Real.log_exp] at hlog
    rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
    nlinarith
  have hfin := le_two_mul_sqrt_of_forall hlogN (by positivity) key
  have hsq : 2 * sqrt (log N * (r ^ 2 / 2)) = r * sqrt (2 * log N) := by
    rw [show log N * (r ^ 2 / 2) = (r / 2) ^ 2 * (2 * log N) by ring,
      sqrt_mul (sq_nonneg _), sqrt_sq (by positivity)]
    ring
  rw [hsq] at hfin
  unfold rademacherComplexity
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hfin (by positivity)

/-! ### Sign patterns of a set family and the VC dimension -/

/-- The `±1` vector of a subset `t` of the sample `Fin n`: `1` on `t`, `-1` off `t`. -/
noncomputable def signVector (t : Finset (Fin n)) : Fin n → ℝ := fun i => if i ∈ t then 1 else -1

lemma signVector_injective : Function.Injective (signVector (n := n)) := by
  intro s t h
  ext i
  have := congrFun h i
  unfold signVector at this
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all <;> norm_num at this

/-- The sign patterns realized by a family `𝒜` of subsets of the sample: for a binary
hypothesis class, `𝒜` is the family of sets `{i | h(xᵢ) = 1}`, one per hypothesis `h`. -/
noncomputable def signPatterns (𝒜 : Finset (Finset (Fin n))) : Set (Fin n → ℝ) :=
  signVector '' (𝒜 : Set (Finset (Fin n)))

lemma ncard_signPatterns (𝒜 : Finset (Finset (Fin n))) : (signPatterns 𝒜).ncard = #𝒜 := by
  rw [signPatterns, Set.ncard_image_of_injective _ signVector_injective, Set.ncard_coe_finset]

/-- **Rademacher complexity of a VC class** (Massart's lemma combined with the Sauer–Shelah
lemma; Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Lemma 26.8 and
Lemma 6.10): the sign patterns of a nonempty family `𝒜` of subsets of an `n`-point sample,
`n ≥ 1`, have empirical Rademacher complexity at most
`√(2 log (∑_{k ≤ d} C(n, k)) / n)`, where `d = 𝒜.vcDim` is the VC dimension of `𝒜`. -/
theorem rademacherComplexity_signPatterns_le {𝒜 : Finset (Finset (Fin n))} (h𝒜 : 𝒜.Nonempty)
    (hn : 0 < n) :
    rademacherComplexity (signPatterns 𝒜) ≤
      sqrt (2 * log (∑ k ∈ Iic 𝒜.vcDim, n.choose k : ℕ) / n) := by
  have hfin : (signPatterns 𝒜).Finite := (𝒜.finite_toSet).image _
  have hne : (signPatterns 𝒜).Nonempty := (Finset.coe_nonempty.2 h𝒜).image _
  have hnorm : ∀ a ∈ signPatterns 𝒜, ∑ i, a i ^ 2 ≤ sqrt n ^ 2 := by
    rintro _ ⟨t, -, rfl⟩
    rw [sq_sqrt (Nat.cast_nonneg n)]
    simp [signVector, apply_ite (· ^ 2)]
  have hM := rademacherComplexity_le_of_finite hfin hne (sqrt_nonneg _) hnorm
  rw [ncard_signPatterns] at hM
  have hcard : (#𝒜 : ℝ) ≤ (∑ k ∈ Iic 𝒜.vcDim, n.choose k : ℕ) := by
    have h' : #𝒜 ≤ ∑ k ∈ Iic 𝒜.vcDim, n.choose k := by
      simpa using (card_le_card_shatterer 𝒜).trans card_shatterer_le_sum_vcDim
    exact_mod_cast h'
  have hpos : (0 : ℝ) < #𝒜 := by exact_mod_cast h𝒜.card_pos
  have hlog : log (#𝒜 : ℝ) ≤ log (∑ k ∈ Iic 𝒜.vcDim, n.choose k : ℕ) :=
    log_le_log hpos hcard
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine hM.trans ?_
  have hL : 0 ≤ log (#𝒜 : ℝ) := log_nonneg (by exact_mod_cast h𝒜.card_pos)
  calc sqrt n * sqrt (2 * log (#𝒜 : ℝ)) / n
      = sqrt (2 * log (#𝒜 : ℝ) / n) := by
        rw [sqrt_div' _ hnR.le, div_eq_div_iff hnR.ne' (sqrt_pos.2 hnR).ne', mul_right_comm,
          mul_self_sqrt hnR.le, mul_comm]
    _ ≤ sqrt (2 * log (∑ k ∈ Iic 𝒜.vcDim, n.choose k : ℕ) / n) := by
        gcongr

/-- **Rademacher complexity of a VC class, explicit rate** (Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, Section 28.1, from Lemma 26.8 and Lemma 6.10): for a nonempty
family `𝒜` of subsets of an `n`-point sample with VC dimension `d ≥ 1`, the sign patterns
have empirical Rademacher complexity at most `√(2 d log (e n / d) / n)`. -/
theorem rademacherComplexity_signPatterns_le_vcDim {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : 𝒜.Nonempty) (hd : 1 ≤ 𝒜.vcDim) :
    rademacherComplexity (signPatterns 𝒜) ≤
      sqrt (2 * 𝒜.vcDim * log (exp 1 * n / 𝒜.vcDim) / n) := by
  have hdn : 𝒜.vcDim ≤ n := by simpa using Finset.vcDim_le_card 𝒜
  have hn : 0 < n := lt_of_lt_of_le hd hdn
  refine (rademacherComplexity_signPatterns_le h𝒜 hn).trans ?_
  have hrange : (∑ k ∈ Iic 𝒜.vcDim, n.choose k : ℕ) = ∑ k ∈ range (𝒜.vcDim + 1), n.choose k := by
    congr 1; ext k; simp
  have hS : ((∑ k ∈ Iic 𝒜.vcDim, n.choose k : ℕ) : ℝ) ≤ (exp 1 * n / 𝒜.vcDim) ^ 𝒜.vcDim := by
    rw [hrange, Nat.cast_sum]
    exact Real.sum_choose_le_exp_mul_div_pow hd hdn
  have hpos : (0 : ℝ) < ((∑ k ∈ Iic 𝒜.vcDim, n.choose k : ℕ) : ℝ) := by
    have : 1 ≤ ∑ k ∈ Iic 𝒜.vcDim, n.choose k :=
      le_trans (by simp) (Finset.single_le_sum (f := fun k => n.choose k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_Iic.2 (Nat.zero_le _)))
    exact_mod_cast this
  have hlog := log_le_log hpos hS
  rw [Real.log_pow] at hlog
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply Real.sqrt_le_sqrt
  gcongr ?_ / _
  rw [mul_assoc]
  linarith

/-! ### The contraction lemma -/

/-- Apply a function `φ i` to each coordinate `i` of a vector. -/
def coordMap (φ : Fin n → ℝ → ℝ) (a : Fin n → ℝ) : Fin n → ℝ := fun i => φ i (a i)

/-- Reverse the sign of coordinate `j` only. -/
def flipAt (j : Fin n) (ε : Fin n → Bool) : Fin n → Bool := Function.update ε j (!ε j)

lemma flipAt_involutive (j : Fin n) : Function.Involutive (flipAt j) := by
  intro ε; simp [flipAt]

lemma rademacherSign_flipAt_self (j : Fin n) (ε : Fin n → Bool) :
    rademacherSign ℝ (flipAt j ε) j = -rademacherSign ℝ ε j := by
  unfold rademacherSign flipAt
  cases ε j <;> simp

lemma rademacherSign_flipAt_of_ne {i j : Fin n} (h : i ≠ j) (ε : Fin n → Bool) :
    rademacherSign ℝ (flipAt j ε) i = rademacherSign ℝ ε i := by
  simp [rademacherSign, flipAt, Function.update_of_ne h]

/-- The correlation with a coordinate map, with coordinate `j` split off. -/
lemma signCorr_coordMap_update (ε : Fin n → Bool) (g : Fin n → ℝ → ℝ) (j : Fin n)
    (h : ℝ → ℝ) (a : Fin n → ℝ) :
    signCorr ε (coordMap (Function.update g j h) a) = rademacherSign ℝ ε j * h (a j) +
      ∑ i ∈ univ.erase j, rademacherSign ℝ ε i * g i (a i) := by
  rw [signCorr, ← Finset.add_sum_erase _ _ (mem_univ j)]
  congr 1
  · simp [coordMap]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp [coordMap, Function.update_of_ne (ne_of_mem_erase hi)]

/-- Coordinatewise `L`-Lipschitz maps send bounded sets to bounded sets. -/
lemma isBounded_coordMap_image {A : Set (Fin n → ℝ)} (hA : Bornology.IsBounded A)
    {g : Fin n → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : ∀ i x y, |g i x - g i y| ≤ L * |x - y|) :
    Bornology.IsBounded (coordMap g '' A) := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hA
  set M : ℝ := ∑ i, |g i 0|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine isBounded_iff_forall_norm_le.2 ⟨M + L * max C 0, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  change |g i (a i)| ≤ _
  have h1 : |g i (a i)| ≤ |g i 0| + L * |a i| := by
    have := hg i (a i) 0
    rw [sub_zero] at this
    have := abs_sub_abs_le_abs_sub (g i (a i)) (g i 0)
    linarith
  have h2 : |g i 0| ≤ M :=
    Finset.single_le_sum (f := fun i => |g i 0|) (fun _ _ => abs_nonneg _) (mem_univ i)
  have h3 : |a i| ≤ max C 0 :=
    ((Real.norm_eq_abs (a i)).symm ▸ norm_le_pi_norm a i).trans ((hC a ha).trans (le_max_left _ _))
  nlinarith [mul_le_mul_of_nonneg_left h3 hL]

/-- One step of the contraction argument: replacing the `L`-Lipschitz coordinate map `g j` by
`x ↦ L x` does not decrease the summed suprema of the correlations. -/
lemma sum_supCorr_le_update {A : Set (Fin n → ℝ)} (hA : Bornology.IsBounded A)
    (hne : A.Nonempty) {g : Fin n → ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ i x y, |g i x - g i y| ≤ L * |x - y|) (j : Fin n) :
    ∑ ε, supCorr (coordMap g '' A) ε ≤
      ∑ ε, supCorr (coordMap (Function.update g j fun x => L * x) '' A) ε := by
  set g' := Function.update g j fun x => L * x with hg'
  have hg'L : ∀ i x y, |g' i x - g' i y| ≤ L * |x - y| := by
    intro i x y
    by_cases hij : i = j
    · subst hij; simp only [hg', Function.update_self]
      rw [← mul_sub, abs_mul, abs_of_nonneg hL]
    · simp only [hg', Function.update_of_ne hij]; exact hg i x y
  have hB' := isBounded_coordMap_image hA hL hg'L
  set F : (Fin n → Bool) → ℝ := fun ε => supCorr (coordMap g '' A) ε
  set G : (Fin n → Bool) → ℝ := fun ε => supCorr (coordMap g' '' A) ε
  -- the pointwise inequality for a pair of sign vectors differing at `j`, sign `+` at `j`
  have pair : ∀ ε : Fin n → Bool, ε j = true → F ε + F (flipAt j ε) ≤ G ε + G (flipAt j ε) := by
    intro ε hεj
    set U : (Fin n → ℝ) → ℝ := fun a => ∑ i ∈ univ.erase j, rademacherSign ℝ ε i * g i (a i)
    have hU : ∀ a, ∑ i ∈ univ.erase j, rademacherSign ℝ (flipAt j ε) i * g i (a i) = U a :=
      fun a => Finset.sum_congr rfl fun i hi => by
        rw [rademacherSign_flipAt_of_ne (ne_of_mem_erase hi)]
    have hsj : rademacherSign ℝ ε j = 1 := by simp [rademacherSign, hεj]
    have hsj' : rademacherSign ℝ (flipAt j ε) j = -1 := by
      rw [rademacherSign_flipAt_self, hsj]
    have hgg : g = Function.update g j (g j) := (Function.update_eq_self j g).symm
    have eF : ∀ a, signCorr ε (coordMap g a) = g j (a j) + U a := fun a => by
      conv_lhs => rw [hgg]
      rw [signCorr_coordMap_update, hsj, one_mul]
    have eF' : ∀ a, signCorr (flipAt j ε) (coordMap g a) = -g j (a j) + U a := fun a => by
      conv_lhs => rw [hgg]
      rw [signCorr_coordMap_update, hsj', hU, neg_one_mul]
    have eG : ∀ a, signCorr ε (coordMap g' a) = L * a j + U a := fun a => by
      rw [hg', signCorr_coordMap_update, hsj, one_mul]
    have eG' : ∀ a, signCorr (flipAt j ε) (coordMap g' a) = -(L * a j) + U a := fun a => by
      rw [hg', signCorr_coordMap_update, hsj', hU, neg_one_mul]
    have hGle : ∀ a ∈ A, L * a j + U a ≤ G ε := fun a ha => by
      rw [← eG]
      exact le_csSup (bddAbove_signCorr_image hB' ε) ⟨coordMap g' a, ⟨a, ha, rfl⟩, rfl⟩
    have hGle' : ∀ a ∈ A, -(L * a j) + U a ≤ G (flipAt j ε) := fun a ha => by
      rw [← eG']
      exact le_csSup (bddAbove_signCorr_image hB' _) ⟨coordMap g' a, ⟨a, ha, rfl⟩, rfl⟩
    have key : ∀ a ∈ A, ∀ a' ∈ A,
        (g j (a j) + U a) + (-g j (a' j) + U a') ≤ G ε + G (flipAt j ε) := by
      intro a ha a' ha'
      have hlip := hg j (a j) (a' j)
      rcases le_total (a' j) (a j) with h | h
      · rw [abs_of_nonneg (sub_nonneg.2 h)] at hlip
        have := le_abs_self (g j (a j) - g j (a' j))
        linarith [hGle a ha, hGle' a' ha']
      · rw [abs_of_nonpos (sub_nonpos.2 h)] at hlip
        have := le_abs_self (g j (a j) - g j (a' j))
        linarith [hGle a' ha', hGle' a ha]
    set C := G ε + G (flipAt j ε)
    have hFimg : ∀ ε', F ε' = sSup ((fun a => signCorr ε' (coordMap g a)) '' A) := fun ε' => by
      simp only [F, supCorr, Set.image_image]
    have h1 : ∀ a' ∈ A, F ε ≤ C - (-g j (a' j) + U a') := by
      intro a' ha'
      rw [hFimg]
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨a, ha, rfl⟩
      dsimp only; rw [eF]; linarith [key a ha a' ha']
    have h2 : F (flipAt j ε) ≤ C - F ε := by
      rw [hFimg]
      refine csSup_le (hne.image _) ?_
      rintro _ ⟨a', ha', rfl⟩
      dsimp only; rw [eF']; linarith [h1 a' ha']
    linarith
  have pair' : ∀ ε, F ε + F (flipAt j ε) ≤ G ε + G (flipAt j ε) := by
    intro ε
    cases hε : ε j
    · have hτ : flipAt j ε j = true := by simp [flipAt, hε]
      have := pair (flipAt j ε) hτ
      rw [flipAt_involutive j ε] at this
      linarith
    · exact pair ε hε
  have hsumF : ∑ ε, F (flipAt j ε) = ∑ ε, F ε :=
    Fintype.sum_equiv ((flipAt_involutive j).toPerm _) _ _ (fun _ => rfl)
  have hsumG : ∑ ε, G (flipAt j ε) = ∑ ε, G ε :=
    Fintype.sum_equiv ((flipAt_involutive j).toPerm _) _ _ (fun _ => rfl)
  have := Finset.sum_le_sum fun ε (_ : ε ∈ univ) => pair' ε
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsumF, hsumG] at this
  change ∑ ε, F ε ≤ ∑ ε, G ε
  linarith

/-- **The contraction lemma** (Shalev-Shwartz and Ben-David, *Understanding Machine Learning*,
Lemma 26.9, which states exactly this form): if each `φ i : ℝ → ℝ` is `L`-Lipschitz and `A` is
bounded, then `R({(φ₁(a₁), …, φₙ(aₙ)) : a ∈ A}) ≤ L R(A)`. No condition `φ i 0 = 0` is needed
in this convention. The absolute-value versions assume `φ i 0 = 0`: Bartlett–Mendelson,
Theorem 12.4 (with the factor `2 L`), and cf. the comparison principle for contractions of
Ledoux and Talagrand, *Probability in Banach Spaces*, 1991, §4.5, stated with an absolute
value for contractions vanishing at `0`. -/
theorem rademacherComplexity_coordMap_le {A : Set (Fin n → ℝ)} (hA : Bornology.IsBounded A)
    (φ : Fin n → ℝ → ℝ) {L : NNReal} (hφ : ∀ i, LipschitzWith L (φ i)) :
    rademacherComplexity (coordMap φ '' A) ≤ L * rademacherComplexity A := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp [rademacherComplexity, supCorr]
  have hφ' : ∀ i x y, |φ i x - φ i y| ≤ (L : ℝ) * |x - y| := fun i x y => by
    simpa [Real.dist_eq] using (hφ i).dist_le_mul x y
  set ψ : Finset (Fin n) → Fin n → ℝ → ℝ :=
    fun s i => if i ∈ s then (fun x => (L : ℝ) * x) else φ i with hψ
  have hψL : ∀ s i x y, |ψ s i x - ψ s i y| ≤ (L : ℝ) * |x - y| := by
    intro s i x y
    by_cases hi : i ∈ s
    · simp only [hψ, hi, ↓reduceIte]; rw [← mul_sub, abs_mul, NNReal.abs_eq]
    · simp only [hψ, hi, ↓reduceIte]; exact hφ' i x y
  have step : ∀ s : Finset (Fin n), ∑ ε, supCorr (coordMap φ '' A) ε ≤
      ∑ ε, supCorr (coordMap (ψ s) '' A) ε := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hψ]
    | insert j s hj ih =>
      have hupd : ψ (insert j s) = Function.update (ψ s) j fun x => (L : ℝ) * x := by
        funext i
        by_cases hij : i = j
        · subst hij; simp [hψ]
        · simp [hψ, hij]
      rw [hupd]
      exact ih.trans (sum_supCorr_le_update hA hne L.coe_nonneg (hψL s) j)
  have huniv : coordMap (ψ univ) '' A = (L : ℝ) • A := by
    rw [← Set.image_smul]
    congr 1
    funext a i
    simp [coordMap, hψ]
  have hfin := step univ
  rw [huniv] at hfin
  have hR := rademacherComplexity_smul A (L : ℝ)
  rw [NNReal.abs_eq] at hR
  rw [← hR]
  unfold rademacherComplexity
  gcongr

end Cslib.MachineLearning.Rademacher
