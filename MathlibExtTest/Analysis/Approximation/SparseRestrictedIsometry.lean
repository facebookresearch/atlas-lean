/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Approximation.SparseRestrictedIsometry

@[expose] public section

open Finset Matrix MathlibExt.Analysis.Approximation.SparseRestrictedIsometry
  MathlibExt.Probability.Statistics.BasisPursuit

namespace MathlibExtTest.Analysis.Approximation.SparseRestrictedIsometry

/-- The identity matrix has the restricted isometry property of every order with constant `0`. -/
lemma hasRIP_one (n s : ℕ) : HasRIP (1 : Matrix (Fin n) (Fin n) ℝ) s 0 := by
  intro x _
  simp

/-- Lemma 2.1 on the identity: disjointly supported vectors have orthogonal images. -/
example (n : ℕ) {T T' : Finset (Fin n)} (hdisj : Disjoint T T') {x x' : Fin n → ℝ}
    (hx : ∀ j ∉ T, x j = 0) (hx' : ∀ j ∉ T', x' j = 0) :
    |((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x) ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x')| ≤
      0 * √(∑ j, x j ^ 2) * √(∑ j, x' j ^ 2) :=
  abs_dotProduct_mulVec_le (hasRIP_one n (#T + #T')) le_rfl le_rfl hdisj hx hx'

/-- `ℓ₀` uniqueness on the identity, for `1`-sparse vectors. -/
example (n : ℕ) {x x' : Fin n → ℝ} (hx : hammingNorm x ≤ 1) (hx' : hammingNorm x' ≤ 1)
    (h : (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ x = 1 *ᵥ x') : x = x' :=
  eq_of_mulVec_eq (hasRIP_one n (2 * 1)) (by norm_num) hx hx' h

/-- The standard basis vector `e₀ ∈ ℝ²` is `1`-sparse, so the hypotheses above are satisfiable. -/
example : hammingNorm (Pi.single 0 1 : Fin 2 → ℝ) ≤ 1 :=
  hammingNorm_le_card (T := {0}) fun j hj => by simp_all

/-- Lemma 2.2 on the identity, whose nullspace is trivial. -/
example (n : ℕ) {h : Fin n → ℝ} (hh : (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ h = 0)
    {T₀ : Finset (Fin n)} (hT₀ : #T₀ ≤ 1) :
    ∑ j ∈ T₀, |h j| ≤ √2 * 0 / (1 - 0) * ∑ j ∈ T₀ᶜ, |h j| :=
  sum_abs_le_of_mulVec_eq_zero le_rfl (hasRIP_one n (2 * 1)) (by norm_num) hh hT₀

/-- The identity has the restricted nullspace property over every set of at most `s ≥ 1`
indices, through `restrictedNullspace_of_hasRIP` with `δ = 0 < √2 - 1`. -/
example (n s : ℕ) (hs : 1 ≤ s) {S : Finset (Fin n)} (hS : #S ≤ s) :
    RestrictedNullspace (1 : Matrix (Fin n) (Fin n) ℝ) S :=
  restrictedNullspace_of_hasRIP hs (hasRIP_one n (2 * s)) (by
    have : (1 : ℝ) < √2 := by
      rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith) hS

/-- The all-ones row `Φ₁ = (1 1)`, a `1 × 2` matrix. -/
def Φ₁ : Matrix (Fin 1) (Fin 2) ℝ := !![1, 1]

/-- `Φ₁` is an isometry on `1`-sparse vectors: it has the restricted isometry property of order
`1` with constant `0`. -/
lemma hasRIP_Φ₁ : HasRIP Φ₁ 1 0 := by
  intro x hx
  -- A `1`-sparse vector of `ℝ²` has a zero entry.
  have hzero : x 0 = 0 ∨ x 1 = 0 := by
    by_contra hne
    rw [not_or] at hne
    have : hammingNorm x = 2 := by
      unfold hammingNorm
      rw [show ({i | x i ≠ 0} : Finset (Fin 2)) = univ by
        ext i; fin_cases i <;> simp [hne.1, hne.2]]
      rfl
    omega
  rcases hzero with h0 | h1 <;>
    simp [Φ₁, mulVec, dotProduct, Fin.sum_univ_two, *]

/-- Boundary probe for `eq_of_mulVec_eq`: `Φ₁` has no restricted isometry property of order `2`
with a constant `δ < 1`, as its nullspace contains the `2`-sparse vector `(1, -1)`. -/
lemma not_hasRIP_Φ₁_two {δ : ℝ} (hδ : δ < 1) : ¬ HasRIP Φ₁ 2 δ := by
  intro h
  have := (h ![1, -1] hammingNorm_le_card_fintype).1
  simp [Φ₁, mulVec, dotProduct, Fin.sum_univ_two] at this
  linarith

/-- Without `δ_{2s} < 1`, `s`-sparse solutions need not be unique: the distinct `1`-sparse
vectors `(1, 0)` and `(0, 1)` have the same image under `Φ₁`. -/
example : Φ₁ *ᵥ ![1, 0] = Φ₁ *ᵥ ![0, 1] ∧ (![1, 0] : Fin 2 → ℝ) ≠ ![0, 1] := by
  refine ⟨?_, fun h => by simpa using congrFun h 0⟩
  funext i
  fin_cases i
  simp [Φ₁, mulVec, dotProduct, Fin.sum_univ_two]

end MathlibExtTest.Analysis.Approximation.SparseRestrictedIsometry
