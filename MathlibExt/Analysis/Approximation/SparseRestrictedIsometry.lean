/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.InformationTheory.Hamming
public import MathlibExt.Probability.Statistics.BasisPursuit

/-!
# The restricted isometry property for sparse vectors

Let `Φ` be a real `m × n` matrix. A vector `x ∈ ℝⁿ` is `s`-sparse if it has at most `s` nonzero
entries; here this is `hammingNorm x ≤ s`, Mathlib's count of the nonzero entries of `x`. The
isometry constant `δ_s` of `Φ` is the least `δ` such that
`(1 - δ) ‖x‖₂² ≤ ‖Φ x‖₂² ≤ (1 + δ) ‖x‖₂²` for every `s`-sparse `x` (E. J. Candès, *The restricted
isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I
346 (2008) 589–592, doi:10.1016/j.crma.2008.03.014, Definition 1.1). Following that Note:

* `HasRIP Φ s δ`: the inequality of Definition 1.1 with the constant `δ`, for all `s`-sparse
  vectors; `HasRIP.mono` is its monotonicity in `s` and `δ`, and `HasRIP.nonneg` shows that
  `δ ≥ 0` when `s ≥ 1` and `ι` is nonempty.
* `abs_dotProduct_mulVec_le`: Lemma 2.1, `|⟪Φ x, Φ x'⟫| ≤ δ_{s+s'} ‖x‖₂ ‖x'‖₂` for `x`, `x'`
  supported on disjoint sets of sizes at most `s` and `s'`.
* `eq_of_mulVec_eq`: if `δ_{2s} < 1`, two `s`-sparse vectors with the same image are equal, so
  the `ℓ₀` problem has a unique `s`-sparse solution (the remark after Theorem 1.2).
* `sum_abs_le_of_mulVec_eq_zero`: Lemma 2.2, the null-space property
  `‖h_{T₀}‖₁ ≤ ρ ‖h_{T₀ᶜ}‖₁` for `Φ h = 0`, with `ρ = √2 δ_{2s} / (1 - δ_{2s})`.
* `restrictedNullspace_of_hasRIP`: consequently, if `δ_{2s} < √2 - 1` then `Φ` has the restricted
  nullspace property `BasisPursuit.RestrictedNullspace Φ S` over every `S` with `#S ≤ s`, and
  `eq_of_sum_abs_le_of_hasRIP`: basis pursuit recovers every `s`-sparse vector exactly (the last
  sentence of Theorem 1.2).

Norms are written in coordinates, as in `BasisPursuit`: `‖x‖₂² = ∑ j, x j ^ 2`,
`‖x‖₁ = ∑ j, |x j|`, `‖Φ x‖₂² = ∑ i, (Φ *ᵥ x) i ^ 2`, and `⟪Φ x, Φ x'⟫ = (Φ *ᵥ x) ⬝ᵥ (Φ *ᵥ x')`.

The restricted isometry property here uses **squared** norms, as in Candès (2008). It differs
from `MathlibExt.LinearAlgebra.Matrix.LowRankRecovery.IsRestrictedIsometry`, the restricted
isometry property of Recht, Fazel and Parrilo for linear maps on matrices and rank-`r` matrices,
which bounds the unsquared norm `‖𝒜 X‖` between `(1 - δ) ‖X‖_F` and `(1 + δ) ‖X‖_F`.
-/

open Finset Matrix

namespace MathlibExt.Analysis.Approximation.SparseRestrictedIsometry

open MathlibExt.Probability.Statistics.BasisPursuit
  MathlibExt.Probability.Statistics.LassoRestrictedEigenvalue

@[expose] public section

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- **The restricted isometry property of order `s` with constant `δ`** (E. J. Candès, *The
restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci.
Paris, Ser. I 346 (2008) 589–592, Definition 1.1): every `s`-sparse vector `x`, that is every `x`
with at most `s` nonzero entries (`hammingNorm x ≤ s`), satisfies
`(1 - δ) ‖x‖₂² ≤ ‖Φ x‖₂² ≤ (1 + δ) ‖x‖₂²`.

Candès's isometry constant `δ_s` is the least such `δ`. The set of admissible `δ` is an up-set
(`HasRIP.mono`), nonempty, closed (an intersection of closed half-lines) and, for `s ≥ 1` and
nonempty `ι`, bounded below by `0` (`HasRIP.nonneg`), so it has a least element and "`δ_s < c`"
means `HasRIP Φ s δ` for some `δ < c`; the results below are stated in that form. (The existence
of the least element is a remark, not formalized here.) The norms are squared, unlike
`MathlibExt.LinearAlgebra.Matrix.LowRankRecovery.IsRestrictedIsometry` (Recht, Fazel and
Parrilo), which bounds unsquared norms. -/
def HasRIP (Φ : Matrix (Fin m) ι ℝ) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x : ι → ℝ, hammingNorm x ≤ s →
    (1 - δ) * ∑ j, x j ^ 2 ≤ ∑ i, (Φ *ᵥ x) i ^ 2 ∧ ∑ i, (Φ *ᵥ x) i ^ 2 ≤ (1 + δ) * ∑ j, x j ^ 2

/-- **Monotonicity of the restricted isometry property** (E. J. Candès, C. R. Acad. Sci. Paris,
Ser. I 346 (2008), Definition 1.1): the restricted isometry property of order `s` with constant
`δ` implies it for every smaller order `s' ≤ s` and every larger constant `δ' ≥ δ`; in particular
`δ_{s'} ≤ δ_s`. -/
theorem HasRIP.mono {Φ : Matrix (Fin m) ι ℝ} {s s' : ℕ} {δ δ' : ℝ} (hΦ : HasRIP Φ s δ)
    (hs : s' ≤ s) (hδ : δ ≤ δ') : HasRIP Φ s' δ' := by
  intro x hx
  obtain ⟨h1, h2⟩ := hΦ x (hx.trans hs)
  have h0 : 0 ≤ ∑ j, x j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
  constructor <;> nlinarith

/-- **A vector supported on `T` is `#T`-sparse** (the notion of sparsity in E. J. Candès, C. R.
Acad. Sci. Paris, Ser. I 346 (2008), Definition 1.1): if `x` vanishes off `T`, then `x` has at
most `#T` nonzero entries. -/
theorem hammingNorm_le_card {x : ι → ℝ} {T : Finset ι} (hx : ∀ j ∉ T, x j = 0) :
    hammingNorm x ≤ #T := by
  unfold hammingNorm
  refine card_le_card fun j hj => ?_
  by_contra hjT
  exact (mem_filter.mp hj).2 (hx j hjT)

/-- **Isometry constants are nonnegative** (E. J. Candès, C. R. Acad. Sci. Paris, Ser. I 346
(2008), Definition 1.1): if `ι` is nonempty, `s ≥ 1` and `Φ` has the restricted isometry property
of order `s` with constant `δ`, then `0 ≤ δ` (apply the definition to a standard basis vector). -/
theorem HasRIP.nonneg [Nonempty ι] {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ} (hΦ : HasRIP Φ s δ)
    (hs : 1 ≤ s) : 0 ≤ δ := by
  classical
  obtain ⟨j⟩ := ‹Nonempty ι›
  have hsp : hammingNorm (Pi.single j (1 : ℝ)) ≤ s :=
    (hammingNorm_le_card (T := {j}) fun k hk =>
      Pi.single_eq_of_ne (mt mem_singleton.mpr hk) _).trans (by simpa using hs)
  have h1 : ∑ k, (Pi.single j (1 : ℝ) : ι → ℝ) k ^ 2 = 1 := by
    simp [Pi.single_apply]
  obtain ⟨hl, hu⟩ := hΦ _ hsp
  rw [h1] at hl hu
  linarith

private lemma eq_zero_of_sum_sq_eq_zero {x : ι → ℝ} (h : ∑ j, x j ^ 2 = 0) : x = 0 := by
  funext j
  have := (sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (x j))).mp h j (mem_univ j)
  simpa using this

/-- **Near-orthogonality of disjointly supported sparse vectors** (E. J. Candès, *The restricted
isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I
346 (2008) 589–592, Lemma 2.1): if `Φ` has the restricted isometry property of order `s + s'`
with constant `δ`, and `x`, `x'` are supported on disjoint sets `T`, `T'` with `#T ≤ s` and
`#T' ≤ s'`, then `|⟪Φ x, Φ x'⟫| ≤ δ ‖x‖₂ ‖x'‖₂`. -/
theorem abs_dotProduct_mulVec_le {Φ : Matrix (Fin m) ι ℝ} {s s' : ℕ} {δ : ℝ}
    (hΦ : HasRIP Φ (s + s') δ) {T T' : Finset ι} (hT : #T ≤ s) (hT' : #T' ≤ s')
    (hdisj : Disjoint T T') {x x' : ι → ℝ} (hx : ∀ j ∉ T, x j = 0)
    (hx' : ∀ j ∉ T', x' j = 0) :
    |(Φ *ᵥ x) ⬝ᵥ (Φ *ᵥ x')| ≤ δ * √(∑ j, x j ^ 2) * √(∑ j, x' j ^ 2) := by
  classical
  have hA : 0 ≤ ∑ j, x j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
  have hB : 0 ≤ ∑ j, x' j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
  have ha2 := Real.sq_sqrt hA
  have hb2 := Real.sq_sqrt hB
  -- The zero cases.
  rcases (Real.sqrt_nonneg (∑ j, x j ^ 2)).eq_or_lt with ha0 | ha0
  · have : x = 0 := eq_zero_of_sum_sq_eq_zero (by rw [← ha2, ← ha0]; ring)
    simp [this]
  rcases (Real.sqrt_nonneg (∑ j, x' j ^ 2)).eq_or_lt with hb0 | hb0
  · have : x' = 0 := eq_zero_of_sum_sq_eq_zero (by rw [← hb2, ← hb0]; ring)
    simp [this]
  -- The parallelogram identity applied to `b • x ± a • x'`, with `a = ‖x‖₂` and `b = ‖x'‖₂`.
  set a := √(∑ j, x j ^ 2)
  set b := √(∑ j, x' j ^ 2)
  have hprod : ∀ j, x j * x' j = 0 := by
    intro j
    by_cases hj : j ∈ T
    · rw [hx' j (disjoint_left.mp hdisj hj), mul_zero]
    · rw [hx j hj, zero_mul]
  have hsp : ∀ c d : ℝ, hammingNorm (c • x + d • x') ≤ s + s' := by
    intro c d
    refine (hammingNorm_le_card (T := T ∪ T') fun j hj => ?_).trans
      ((card_union_le _ _).trans (add_le_add hT hT'))
    rw [mem_union, not_or] at hj
    simp [hx j hj.1, hx' j hj.2]
  have hnorm : ∀ c d : ℝ, ∑ j, (c • x + d • x') j ^ 2 =
      c ^ 2 * ∑ j, x j ^ 2 + d ^ 2 * ∑ j, x' j ^ 2 := by
    intro c d
    simp only [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (2 * c * d) * hprod j
  have himg : ∀ c d : ℝ, ∑ i, (Φ *ᵥ (c • x + d • x')) i ^ 2 =
      c ^ 2 * ∑ i, (Φ *ᵥ x) i ^ 2 + d ^ 2 * ∑ i, (Φ *ᵥ x') i ^ 2 +
        2 * c * d * ((Φ *ᵥ x) ⬝ᵥ (Φ *ᵥ x')) := by
    intro c d
    simp only [mulVec_add, mulVec_smul, dotProduct, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨hpl, hpu⟩ := hΦ _ (hsp b a)
  obtain ⟨hml, hmu⟩ := hΦ _ (hsp b (-a))
  rw [hnorm, himg] at hpl hpu hml hmu
  rw [← ha2, ← hb2] at hpl hpu hml hmu
  have hab : 0 < 4 * (a * b) := by positivity
  rw [abs_le]
  constructor
  · have : 4 * (a * b) * (-(δ * (a * b))) ≤ 4 * (a * b) * ((Φ *ᵥ x) ⬝ᵥ (Φ *ᵥ x')) := by
      linear_combination hmu + hpl
    have := le_of_mul_le_mul_left this hab
    linarith
  · have : 4 * (a * b) * ((Φ *ᵥ x) ⬝ᵥ (Φ *ᵥ x')) ≤ 4 * (a * b) * (δ * (a * b)) := by
      linear_combination hpu + hml
    have := le_of_mul_le_mul_left this hab
    linarith

/-- **Uniqueness of sparse solutions under `δ_{2s} < 1`** (E. J. Candès, *The restricted isometry
property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008)
589–592, remark after Theorem 1.2: "if `δ_{2s} < 1`, the `ℓ₀` problem has a unique `s`-sparse
solution"): if `Φ` has the restricted isometry property of order `2 s` with a constant `δ < 1`,
then two `s`-sparse vectors `x`, `x'` with `Φ x = Φ x'` are equal. -/
theorem eq_of_mulVec_eq {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ} (hΦ : HasRIP Φ (2 * s) δ)
    (hδ : δ < 1) {x x' : ι → ℝ} (hx : hammingNorm x ≤ s) (hx' : hammingNorm x' ≤ s)
    (h : Φ *ᵥ x = Φ *ᵥ x') : x = x' := by
  have hsp : hammingNorm (x - x') ≤ 2 * s := by
    rw [← neg_add_eq_sub, ← hammingDist_eq_hammingNorm, two_mul]
    calc hammingDist x' x ≤ hammingDist x' 0 + hammingDist 0 x := hammingDist_triangle _ _ _
      _ = hammingNorm x' + hammingNorm x := by
        rw [hammingDist_zero_right, hammingDist_zero_left]
      _ ≤ s + s := add_le_add hx' hx
  obtain ⟨h1, -⟩ := hΦ _ hsp
  rw [mulVec_sub, h, sub_self] at h1
  have h0 : 0 ≤ ∑ j, (x - x') j ^ 2 := sum_nonneg fun j _ => sq_nonneg _
  have hpos : 0 < 1 - δ := by linarith
  have hle : ∑ j, (x - x') j ^ 2 ≤ 0 := by
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sum_const_zero] at h1
    nlinarith
  exact sub_eq_zero.mp (eq_zero_of_sum_sq_eq_zero (le_antisymm hle h0))

section NullSpace

variable [DecidableEq ι]

/-- The vector equal to `h` on `W` and zero elsewhere (Candès's `h_W`). -/
private def restr (h : ι → ℝ) (W : Finset ι) : ι → ℝ := fun j => if j ∈ W then h j else 0

omit [Fintype ι] in
private lemma restr_of_notMem {h : ι → ℝ} {W : Finset ι} {j : ι} (hj : j ∉ W) :
    restr h W j = 0 := by
  simp [restr, hj]

private lemma sum_restr_sq (h : ι → ℝ) (W : Finset ι) :
    ∑ j, restr h W j ^ 2 = ∑ j ∈ W, h j ^ 2 := by
  simp [restr, ite_pow, sum_ite_mem]

omit [Fintype ι] in
/-- Among the indices of `R`, a set `T` of `min s #R` indices carrying the largest entries of
`|h|`. -/
private lemma exists_top (h : ι → ℝ) (R : Finset ι) (s : ℕ) :
    ∃ T ⊆ R, #T = min s #R ∧ ∀ j ∈ T, ∀ k ∈ R \ T, |h k| ≤ |h j| := by
  obtain ⟨T, hT, hmax⟩ := (R.powersetCard (min s #R)).exists_max_image
    (fun T => ∑ j ∈ T, |h j|) (powersetCard_nonempty.mpr (min_le_right _ _))
  rw [mem_powersetCard] at hT
  refine ⟨T, hT.1, hT.2, fun j hj k hk => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  rw [mem_sdiff] at hk
  have hkT : k ∉ T.erase j := fun h => hk.2 (mem_of_mem_erase h)
  have hT' : insert k (T.erase j) ∈ R.powersetCard (min s #R) := by
    rw [mem_powersetCard]
    refine ⟨insert_subset hk.1 ((erase_subset _ _).trans hT.1), ?_⟩
    rw [card_insert_of_notMem hkT, card_erase_of_mem hj, hT.2]
    have := card_pos.mpr ⟨j, hj⟩
    omega
  have hle := hmax _ hT'
  have hsum : ∑ i ∈ insert k (T.erase j), |h i| = ∑ i ∈ T, |h i| - |h j| + |h k| := by
    rw [sum_insert hkT, ← add_sum_erase T _ hj]
    ring
  linarith

/-- The `ℓ₂` norm of `h_W` is at most `M / √s` when `#W ≤ s` and `s |h j| ≤ s t ≤ M` on `W`. -/
private lemma sqrt_sum_restr_sq_le {h : ι → ℝ} {W : Finset ι} {s : ℕ} (hs : 1 ≤ s)
    (hW : #W ≤ s) {t M : ℝ} (ht : 0 ≤ t) (hbound : ∀ j ∈ W, |h j| ≤ t) (hM : s * t ≤ M) :
    √(∑ j, restr h W j ^ 2) ≤ M / √s := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.mpr hs0
  rw [sum_restr_sq]
  have h1 : ∑ j ∈ W, h j ^ 2 ≤ s * t ^ 2 := by
    calc ∑ j ∈ W, h j ^ 2 ≤ ∑ _j ∈ W, t ^ 2 := sum_le_sum fun j hj => by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbound j hj) 2
      _ = #W * t ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ s * t ^ 2 := by gcongr
  calc √(∑ j ∈ W, h j ^ 2) ≤ √(s * t ^ 2) := Real.sqrt_le_sqrt h1
    _ = √s * t := by rw [Real.sqrt_mul hs0.le, Real.sqrt_sq ht]
    _ ≤ M / √s := by
      rw [le_div_iff₀ hsq, mul_comm, ← mul_assoc, Real.mul_self_sqrt hs0.le]
      exact hM

/-- The blockwise estimate of Candès (2008), (10) with Lemma 2.1: for `u` supported on `U` with
`#U ≤ s` and `W` disjoint from `U`, if `|h| ≤ t` on `W` and `s t ≤ M`, then
`|⟪Φ u, Φ h_W⟫| ≤ δ ‖u‖₂ (M + ‖h_W‖₁) / √s`. Proved by peeling off the `s` largest entries of
`h` on `W` (Candès's blocks `T₂, T₃, …`). -/
private lemma abs_dotProduct_restr_le {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ} (hs : 1 ≤ s)
    (hΦ : HasRIP Φ (s + s) δ) (hδ : 0 ≤ δ) (h u : ι → ℝ) {U : Finset ι} (hU : #U ≤ s)
    (hu : ∀ j ∉ U, u j = 0) :
    ∀ (n : ℕ) (W : Finset ι), #W ≤ n → Disjoint U W → ∀ t M : ℝ, 0 ≤ t →
      (∀ j ∈ W, |h j| ≤ t) → s * t ≤ M →
      |(Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ restr h W)| ≤
        δ * √(∑ j, u j ^ 2) * ((M + ∑ j ∈ W, |h j|) / √s) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.mpr hs0
  have hδu : 0 ≤ δ * √(∑ j, u j ^ 2) := mul_nonneg hδ (Real.sqrt_nonneg _)
  have hW1 : ∀ W : Finset ι, 0 ≤ ∑ j ∈ W, |h j| := fun W => sum_nonneg fun j _ => abs_nonneg _
  -- The base case `#W ≤ s`, by Lemma 2.1.
  have base : ∀ W : Finset ι, #W ≤ s → Disjoint U W → ∀ t M : ℝ, 0 ≤ t →
      (∀ j ∈ W, |h j| ≤ t) → s * t ≤ M →
      |(Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ restr h W)| ≤ δ * √(∑ j, u j ^ 2) * (M / √s) := by
    intro W hW hUW t M ht hbound hM
    refine (abs_dotProduct_mulVec_le hΦ hU hW hUW hu fun j hj => restr_of_notMem hj).trans ?_
    exact mul_le_mul_of_nonneg_left (sqrt_sum_restr_sq_le hs hW ht hbound hM) hδu
  intro n
  induction n with
  | zero =>
    intro W hW hUW t M ht hbound hM
    refine (base W (hW.trans (Nat.zero_le _)) hUW t M ht hbound hM).trans ?_
    gcongr
    exact le_add_of_nonneg_right (hW1 W)
  | succ n ih =>
    intro W hW hUW t M ht hbound hM
    by_cases hWs : #W ≤ s
    · refine (base W hWs hUW t M ht hbound hM).trans ?_
      gcongr
      exact le_add_of_nonneg_right (hW1 W)
    rw [not_le] at hWs
    obtain ⟨T, hTW, hTcard, htop⟩ := exists_top h W s
    rw [min_eq_left hWs.le] at hTcard
    have hsplit : restr h W = restr h T + restr h (W \ T) := by
      funext j
      by_cases hjT : j ∈ T
      · simp [restr, hjT, hTW hjT]
      · by_cases hjW : j ∈ W <;> simp [restr, hjT, hjW]
    have hT := base T hTcard.le (disjoint_of_subset_right hTW hUW) t M ht
      (fun j hj => hbound j (hTW hj)) hM
    have hrest := ih (W \ T) (by rw [card_sdiff_of_subset hTW]; omega)
      (disjoint_of_subset_right sdiff_subset hUW) ((∑ j ∈ T, |h j|) / s) (∑ j ∈ T, |h j|)
      (div_nonneg (hW1 T) hs0.le)
      (fun k hk => by
        rw [le_div_iff₀ hs0]
        calc |h k| * s = ∑ _j ∈ T, |h k| := by rw [sum_const, hTcard, nsmul_eq_mul, mul_comm]
          _ ≤ ∑ j ∈ T, |h j| := sum_le_sum fun j hj => htop j hj k hk)
      (by rw [mul_div_cancel₀ _ hs0.ne'])
    have hsum : ∑ j ∈ T, |h j| + ∑ j ∈ W \ T, |h j| = ∑ j ∈ W, |h j| := by
      rw [add_comm, sum_sdiff hTW]
    rw [hsplit, mulVec_add, dotProduct_add]
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ δ * √(∑ j, u j ^ 2) * (M / √s) +
          δ * √(∑ j, u j ^ 2) * ((∑ j ∈ T, |h j| + ∑ j ∈ W \ T, |h j|) / √s) :=
          add_le_add hT hrest
      _ = δ * √(∑ j, u j ^ 2) * ((M + ∑ j ∈ W, |h j|) / √s) := by
          rw [hsum]; ring

/-- **The null-space property under restricted isometry**, assuming `0 ≤ δ`. -/
private lemma sum_abs_le_of_mulVec_eq_zero_aux {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ}
    (hs : 1 ≤ s)
    (hΦ : HasRIP Φ (2 * s) δ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {h : ι → ℝ} (hh : Φ *ᵥ h = 0)
    {T₀ : Finset ι} (hT₀ : #T₀ ≤ s) :
    ∑ j ∈ T₀, |h j| ≤ √2 * δ / (1 - δ) * ∑ j ∈ T₀ᶜ, |h j| := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq : 0 < √(s : ℝ) := Real.sqrt_pos.mpr hs0
  have hΦ' : HasRIP Φ (s + s) δ := by rwa [← two_mul]
  -- `T₁`: the `s` largest entries of `|h|` off `T₀`; `W`: the remaining indices.
  obtain ⟨T₁, hT₁R, hT₁card, htop⟩ := exists_top h T₀ᶜ s
  set W := T₀ᶜ \ T₁ with hWdef
  set M := ∑ j ∈ T₁, |h j| with hMdef
  have hT₁s : #T₁ ≤ s := hT₁card.trans_le (min_le_left _ _)
  have hdisj01 : Disjoint T₀ T₁ := disjoint_of_subset_right hT₁R disjoint_compl_right
  have hdisj0W : Disjoint T₀ W := disjoint_of_subset_right sdiff_subset disjoint_compl_right
  have hdisj1W : Disjoint T₁ W := disjoint_sdiff
  have hM0 : 0 ≤ M := sum_nonneg fun j _ => abs_nonneg _
  have hbound : ∀ k ∈ W, |h k| ≤ M / s := by
    intro k hk
    have hcard : #T₁ = s := by
      by_contra hne
      have hlt : #T₀ᶜ < s := by
        rcases le_total s #T₀ᶜ with hle | hle
        · rw [min_eq_left hle] at hT₁card; exact absurd hT₁card hne
        · rw [min_eq_right hle] at hT₁card; omega
      have : T₁ = T₀ᶜ := eq_of_subset_of_card_le hT₁R (by
        rw [hT₁card]; exact (min_eq_right hlt.le).ge)
      rw [hWdef, this, sdiff_self] at hk
      exact absurd hk (notMem_empty k)
    rw [le_div_iff₀ hs0]
    calc |h k| * s = ∑ _j ∈ T₁, |h k| := by rw [sum_const, hcard, nsmul_eq_mul, mul_comm]
      _ ≤ M := sum_le_sum fun j hj => htop j hj k hk
  -- The tail estimate (10)–(11) combined with Lemma 2.1, for `h_{T₀}` and `h_{T₁}`.
  set K := (M + ∑ j ∈ W, |h j|) / √s with hK
  have hKL : M + ∑ j ∈ W, |h j| = ∑ j ∈ T₀ᶜ, |h j| := by
    rw [add_comm, hMdef, hWdef, sum_sdiff hT₁R]
  have hK0 : 0 ≤ K := div_nonneg (by rw [hKL]; exact sum_nonneg fun j _ => abs_nonneg _) hsq.le
  have hb0 := abs_dotProduct_restr_le hs hΦ' hδ0 h (restr h T₀) hT₀
    (fun j hj => restr_of_notMem hj) _ W le_rfl hdisj0W (M / s) M
    (div_nonneg hM0 hs0.le) hbound (by rw [mul_div_cancel₀ _ hs0.ne'])
  have hb1 := abs_dotProduct_restr_le hs hΦ' hδ0 h (restr h T₁) hT₁s
    (fun j hj => restr_of_notMem hj) _ W le_rfl hdisj1W (M / s) M
    (div_nonneg hM0 hs0.le) hbound (by rw [mul_div_cancel₀ _ hs0.ne'])
  rw [← hK] at hb0 hb1
  -- `h = h_{T₀} + h_{T₁} + h_W`, so `Φ (h_{T₀} + h_{T₁}) = - Φ h_W`.
  have hdecomp : h = restr h T₀ + restr h T₁ + restr h W := by
    funext j
    by_cases h0 : j ∈ T₀
    · have h1 : j ∉ T₁ := disjoint_left.mp hdisj01 h0
      have h2 : j ∉ W := disjoint_left.mp hdisj0W h0
      simp [restr, h0, h1, h2]
    · by_cases h1 : j ∈ T₁
      · have h2 : j ∉ W := disjoint_left.mp hdisj1W h1
        simp [restr, h0, h1, h2]
      · have h2 : j ∈ W := by rw [hWdef, mem_sdiff, mem_compl]; exact ⟨h0, h1⟩
        simp [restr, h0, h1, h2]
  set u := restr h T₀ + restr h T₁ with hu
  have hΦu : Φ *ᵥ u = -(Φ *ᵥ restr h W) := by
    have : Φ *ᵥ u + Φ *ᵥ restr h W = 0 := by rw [← mulVec_add, ← hdecomp, hh]
    exact eq_neg_of_add_eq_zero_left this
  -- The restricted isometry property on the `2 s`-sparse vector `u`.
  have husp : hammingNorm u ≤ 2 * s := by
    refine (hammingNorm_le_card (T := T₀ ∪ T₁) fun j hj => ?_).trans
      ((card_union_le _ _).trans (by omega))
    rw [mem_union, not_or] at hj
    simp [hu, restr, hj.1, hj.2]
  set A := ∑ j ∈ T₀, h j ^ 2 with hA
  set B := ∑ j ∈ T₁, h j ^ 2 with hB
  have hA0 : 0 ≤ A := sum_nonneg fun j _ => sq_nonneg _
  have hB0 : 0 ≤ B := sum_nonneg fun j _ => sq_nonneg _
  have hunorm : ∑ j, u j ^ 2 = A + B := by
    have : u = restr h (T₀ ∪ T₁) := by
      funext j
      by_cases h0 : j ∈ T₀
      · have h1 : j ∉ T₁ := disjoint_left.mp hdisj01 h0
        simp [hu, restr, h0, h1]
      · by_cases h1 : j ∈ T₁ <;> simp [hu, restr, h0, h1]
    rw [this, sum_restr_sq, sum_union hdisj01]
  obtain ⟨hlow, -⟩ := hΦ u husp
  have hΦu2 : ∑ i, (Φ *ᵥ u) i ^ 2 =
      -((Φ *ᵥ restr h T₀) ⬝ᵥ (Φ *ᵥ restr h W)) - (Φ *ᵥ restr h T₁) ⬝ᵥ (Φ *ᵥ restr h W) := by
    have : ∑ i, (Φ *ᵥ u) i ^ 2 = (Φ *ᵥ u) ⬝ᵥ (Φ *ᵥ u) := by
      simp only [dotProduct, sq]
    conv_lhs => rw [this]
    nth_rw 2 [hΦu]
    rw [dotProduct_neg, hu, mulVec_add, add_dotProduct]
    ring
  rw [sum_restr_sq] at hb0 hb1
  rw [hunorm, hΦu2] at hlow
  set a := √A with ha
  set b := √B with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0' : 0 ≤ b := Real.sqrt_nonneg _
  -- `(1 - δ) (a² + b²) ≤ δ (a + b) K` and `a + b ≤ √2 N` with `N = ‖u‖₂`.
  have hmain : (1 - δ) * (A + B) ≤ δ * (a + b) * K := by
    have h0 := neg_abs_le ((Φ *ᵥ restr h T₀) ⬝ᵥ (Φ *ᵥ restr h W))
    have h1 := neg_abs_le ((Φ *ᵥ restr h T₁) ⬝ᵥ (Φ *ᵥ restr h W))
    nlinarith
  set N := √(A + B) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hN2 : N ^ 2 = A + B := Real.sq_sqrt (by positivity)
  have hab : a + b ≤ √2 * N := by
    have h2 : (a + b) ^ 2 ≤ 2 * (A + B) := by
      have := Real.sq_sqrt hA0
      have := Real.sq_sqrt hB0
      nlinarith [sq_nonneg (a - b)]
    calc a + b = √((a + b) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(2 * (A + B)) := Real.sqrt_le_sqrt h2
      _ = √2 * N := by rw [Real.sqrt_mul (by norm_num)]
  have hpos : 0 < 1 - δ := by linarith
  have hNle : N ≤ √2 * δ / (1 - δ) * K := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
    rcases hN0.eq_or_lt with hN00 | hN00
    · rw [← hN00]; simp only [zero_mul]; positivity
    · have : (1 - δ) * N * N ≤ √2 * δ * K * N := by
        have := mul_le_mul_of_nonneg_left hab (mul_nonneg hδ0 hK0)
        nlinarith
      nlinarith
  have haN : a ≤ N := Real.sqrt_le_sqrt (by linarith)
  -- Cauchy–Schwarz: `‖h_{T₀}‖₁ ≤ √s ‖h_{T₀}‖₂`.
  have hcs : ∑ j ∈ T₀, |h j| ≤ √s * a := by
    have h1 : (∑ j ∈ T₀, |h j|) ^ 2 ≤ s * A := by
      calc (∑ j ∈ T₀, |h j|) ^ 2 ≤ #T₀ * ∑ j ∈ T₀, |h j| ^ 2 := sq_sum_le_card_mul_sum_sq
        _ = #T₀ * A := by simp only [sq_abs, hA]
        _ ≤ s * A := by gcongr
    calc ∑ j ∈ T₀, |h j| ≤ √(s * A) := (le_abs_self _).trans (Real.abs_le_sqrt h1)
      _ = √s * a := Real.sqrt_mul hs0.le _
  calc ∑ j ∈ T₀, |h j| ≤ √s * a := hcs
    _ ≤ √s * (√2 * δ / (1 - δ) * K) := by gcongr; exact haN.trans hNle
    _ = √2 * δ / (1 - δ) * ∑ j ∈ T₀ᶜ, |h j| := by
      rw [hK, hKL]; field_simp

/-- **The null-space property under restricted isometry** (E. J. Candès, *The restricted isometry
property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346 (2008)
589–592, Lemma 2.2, eq. (15)): let `s ≥ 1` and let `Φ` have the restricted isometry property of
order `2 s` with a constant `δ < 1`. For every `h` in the nullspace of `Φ` and every set `T₀` of at
most `s` indices, `‖h_{T₀}‖₁ ≤ ρ ‖h_{T₀ᶜ}‖₁` with `ρ = √2 δ / (1 - δ)`.

Candès states the lemma for `#T₀ = s`; the proof covers `#T₀ ≤ s` unchanged. -/
theorem sum_abs_le_of_mulVec_eq_zero {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ} (hs : 1 ≤ s)
    (hΦ : HasRIP Φ (2 * s) δ) (hδ1 : δ < 1) {h : ι → ℝ} (hh : Φ *ᵥ h = 0)
    {T₀ : Finset ι} (hT₀ : #T₀ ≤ s) :
    ∑ j ∈ T₀, |h j| ≤ √2 * δ / (1 - δ) * ∑ j ∈ T₀ᶜ, |h j| := by
  cases isEmpty_or_nonempty ι with
  | inl hι => simp [Finset.univ_eq_empty, Finset.eq_empty_of_isEmpty T₀]
  | inr hι =>
    exact sum_abs_le_of_mulVec_eq_zero_aux hs hΦ (hΦ.nonneg (by omega)) hδ1 hh hT₀

/-- **Restricted isometry implies the restricted nullspace property** (E. J. Candès, *The
restricted isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris,
Ser. I 346 (2008) 589–592, Lemma 2.2 with `ρ < 1`): let `s ≥ 1` and let `Φ` have the restricted
isometry property of order `2 s` with a constant `δ < √2 - 1` (that is, `δ_{2s} < √2 - 1`). Then
`Φ` has the restricted nullspace property `BasisPursuit.RestrictedNullspace Φ S` over every set `S`
of at most `s` indices. Indeed `δ < √2 - 1` is equivalent to `ρ = √2 δ / (1 - δ) < 1`. -/
theorem restrictedNullspace_of_hasRIP {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ} (hs : 1 ≤ s)
    (hΦ : HasRIP Φ (2 * s) δ) (hδ : δ < √2 - 1) {S : Finset ι} (hS : #S ≤ s) :
    RestrictedNullspace Φ S := by
  intro Δ hΔ hcone
  have h2 : √2 < 2 := by
    rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2sq : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hδ1 : δ < 1 := by linarith
  have hlem := sum_abs_le_of_mulVec_eq_zero hs hΦ hδ1 hΔ hS
  have hρ : √2 * δ / (1 - δ) < 1 := by
    rw [div_lt_one (by linarith)]
    nlinarith [mul_pos (sub_pos.mpr hδ) (show (0 : ℝ) < √2 + 1 by positivity)]
  simp only [cone, Set.mem_ofPred_eq, one_mul] at hcone
  have hS0 : 0 ≤ ∑ j ∈ S, |Δ j| := sum_nonneg fun j _ => abs_nonneg _
  have hSc0 : 0 ≤ ∑ j ∈ Sᶜ, |Δ j| := sum_nonneg fun j _ => abs_nonneg _
  have hSzero : ∑ j ∈ S, |Δ j| = 0 := by
    by_contra hne
    have hpos : 0 < ∑ j ∈ S, |Δ j| := lt_of_le_of_ne hS0 (Ne.symm hne)
    have : ∑ j ∈ S, |Δ j| ≤ √2 * δ / (1 - δ) * ∑ j ∈ S, |Δ j| := by
      refine hlem.trans ?_
      rcases le_total 0 (√2 * δ / (1 - δ)) with hρ0 | hρ0
      · exact mul_le_mul_of_nonneg_left hcone hρ0
      · nlinarith
    nlinarith
  have hSczero : ∑ j ∈ Sᶜ, |Δ j| = 0 := le_antisymm (hSzero ▸ hcone) hSc0
  have htot : ∑ j, |Δ j| = 0 := by rw [← sum_add_sum_compl S, hSzero, hSczero, add_zero]
  funext j
  have := (sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (Δ j))).mp htot j (mem_univ j)
  simpa using this

end NullSpace

/-- **Exact recovery of sparse vectors by `ℓ₁` minimization** (E. J. Candès, *The restricted
isometry property and its implications for compressed sensing*, C. R. Acad. Sci. Paris, Ser. I 346
(2008) 589–592, Theorem 1.2, last sentence: "if `x` is `s`-sparse, the recovery is exact"): let
`s ≥ 1` and let `Φ` have the restricted isometry property of order `2 s` with a constant
`δ < √2 - 1`. If `x` is `s`-sparse, then every `xhat` with `Φ xhat = Φ x` and
`‖xhat‖₁ ≤ ‖x‖₁` equals `x`; so `x` is the unique solution of `min {‖x̃‖₁ | Φ x̃ = Φ x}`. -/
theorem eq_of_sum_abs_le_of_hasRIP {Φ : Matrix (Fin m) ι ℝ} {s : ℕ} {δ : ℝ} (hs : 1 ≤ s)
    (hΦ : HasRIP Φ (2 * s) δ) (hδ : δ < √2 - 1) {x : ι → ℝ} (hx : hammingNorm x ≤ s)
    {xhat : ι → ℝ} (hfeas : Φ *ᵥ xhat = Φ *ᵥ x) (hle : ∑ j, |xhat j| ≤ ∑ j, |x j|) :
    xhat = x := by
  classical
  have hRN := restrictedNullspace_of_hasRIP hs hΦ hδ (S := {j | x j ≠ 0}) hx
  exact (basisPursuit_unique_iff_restrictedNullspace Φ _).mpr hRN x
    (fun j hj => by simpa using hj) xhat hfeas hle

end

end MathlibExt.Analysis.Approximation.SparseRestrictedIsometry
