/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_
of_transitionStable_degree_le_two.lean`
and
`P2M/Sol/S_LanglandsTunnell_CubicInduction_compactPicture_bottom_mem_of_
transitionStable_degree_le_two.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.

The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Stability of the bottom harmonic components in three variables

For polynomials in three complex variables, the operator `cubicXi ν` packages
a diagonal weight term and the three rotation-type terms
`X_i ∂_j - X_j ∂_i`. The lowering operators `cubicLowerTwo`, `cubicLowerOne`
and the same-degree operator `cubicSameTwo` are second-order contractions of
that matrix. On the two-dimensional space of diagonal quadratics
`X_0^2 - X_2^2`, `X_1^2 - X_2^2` and on the mixed quadratics `X_0 X_1`,
`X_0 X_2`, these operators act by explicit scalar matrices (the
characterization lemmas below). For the two weight parameters `cubicNu12` and
`cubicNu13` the relevant scalar factors have nonzero real part, so any
transition-stable pair of subspaces either is trivial or already contains
the expected bottom vector (`1`, `X_2`, or `X_1`).
-/

@[expose] public section

open MvPolynomial

/-- Polynomials in three complex variables. -/
public abbrev CubicPoly := MvPolynomial (Fin 3) ℂ

/-- The rotation-and-weight operator on a polynomial: diagonal weight part
plus the three terms `-(X_{max} ∂_{min} - X_{min} ∂_{max})`. -/
public noncomputable def cubicXi (ν : Fin 3 → ℂ) (p : CubicPoly) :
    Matrix (Fin 3) (Fin 3) CubicPoly :=
  Matrix.of fun c d =>
    if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
    else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
      MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)

/-- The full second-derivative contraction of a matrix of polynomials. -/
public noncomputable def cubicLowerTwo (M : Matrix (Fin 3) (Fin 3) CubicPoly) : CubicPoly :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))

/-- The cubic-weighted second-derivative contraction. -/
public noncomputable def cubicLowerOne (M : Matrix (Fin 3) (Fin 3) CubicPoly) : CubicPoly :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
      (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))

/-- The Euler-type contraction `∑ X_c ∂_d (M c d)`. -/
public noncomputable def cubicQSum (M : Matrix (Fin 3) (Fin 3) CubicPoly) : CubicPoly :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)

/-- The same-degree operator `6 • qsum - (X_0^2+X_1^2+X_2^2) • Δ(qsum)`. -/
public noncomputable def cubicSameTwo (M : Matrix (Fin 3) (Fin 3) CubicPoly) : CubicPoly :=
  MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3,
      MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
    (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))

/-- The first weight parameter, with weights `(-1/2 + τi, 1/2 + τi, τ₃i)`. -/
public noncomputable def cubicNu12 (τ τ₃ : ℝ) : Fin 3 → ℂ :=
  ![-1 / 2 + τ * Complex.I, 1 / 2 + τ * Complex.I, τ₃ * Complex.I]

/-- The second weight parameter, with the last two weights swapped. -/
public noncomputable def cubicNu13 (τ τ₃ : ℝ) : Fin 3 → ℂ :=
  ![-1 / 2 + τ * Complex.I, τ₃ * Complex.I, 1 / 2 + τ * Complex.I]

/-- Characterization of `cubicSameTwo` through `cubicQSum`. -/
public theorem cubicSameTwo_eq (M : Matrix (Fin 3) (Fin 3) CubicPoly) :
    cubicSameTwo M = C 6 * cubicQSum M - (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2) *
      (pderiv 0 (pderiv 0 (cubicQSum M)) + pderiv 1 (pderiv 1 (cubicQSum M)) +
        pderiv 2 (pderiv 2 (cubicQSum M))) := by
  simp only [cubicSameTwo, cubicQSum, Fin.sum_univ_three]

private lemma c10 (f : CubicPoly) : pderiv 1 (pderiv 0 f) = pderiv 0 (pderiv 1 f) :=
  MvPolynomial.pderiv_comm 1 0 f
private lemma c20 (f : CubicPoly) : pderiv 2 (pderiv 0 f) = pderiv 0 (pderiv 2 f) :=
  MvPolynomial.pderiv_comm 2 0 f
private lemma c21 (f : CubicPoly) : pderiv 2 (pderiv 1 f) = pderiv 1 (pderiv 2 f) :=
  MvPolynomial.pderiv_comm 2 1 f

private lemma max01 : max (0 : Fin 3) 1 = 1 := by decide
private lemma max02 : max (0 : Fin 3) 2 = 2 := by decide
private lemma max12 : max (1 : Fin 3) 2 = 2 := by decide
private lemma max10 : max (1 : Fin 3) 0 = 1 := by decide
private lemma max20 : max (2 : Fin 3) 0 = 2 := by decide
private lemma max21 : max (2 : Fin 3) 1 = 2 := by decide
private lemma min01 : min (0 : Fin 3) 1 = 0 := by decide
private lemma min02 : min (0 : Fin 3) 2 = 0 := by decide
private lemma min12 : min (1 : Fin 3) 2 = 1 := by decide
private lemma min10 : min (1 : Fin 3) 0 = 0 := by decide
private lemma min20 : min (2 : Fin 3) 0 = 0 := by decide
private lemma min21 : min (2 : Fin 3) 1 = 1 := by decide

private lemma pdX (i j : Fin 3) : pderiv i (X j : CubicPoly) = if j = i then 1 else 0 := by
  classical
  rw [pderiv_X]; simp [Pi.single_apply]

private lemma pdXsq (i j : Fin 3) :
    pderiv i (X j ^ 2 : CubicPoly) = if j = i then C 2 * X j else 0 := by
  rw [sq, pderiv_mul, pdX]
  split_ifs
  · simp only [map_ofNat]; ring
  · ring

private lemma pd_ofNat (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (no_index (OfNat.ofNat n) : CubicPoly) = 0 := by
  rw [← map_ofNat (C : ℂ →+* CubicPoly) n]; exact pderiv_C

/-- Explicit formula for `cubicLowerTwo (cubicXi ν p)`. -/
public theorem cubicLowerTwo_cubicXi (ν : Fin 3 → ℂ) (p : CubicPoly) :
    cubicLowerTwo (cubicXi ν p) = C 2 * ((C (ν 0) - 1) * pderiv 0 (pderiv 0 p) +
      C (ν 1) * pderiv 1 (pderiv 1 p) + (C (ν 2) + 1) * pderiv 2 (pderiv 2 p)
      + X 0 * pderiv 0 (pderiv 1 (pderiv 1 p)) + X 0 * pderiv 0 (pderiv 2 (pderiv 2 p))
      - X 1 * pderiv 1 (pderiv 0 (pderiv 0 p)) + X 1 * pderiv 1 (pderiv 2 (pderiv 2 p))
      - X 2 * pderiv 2 (pderiv 0 (pderiv 0 p)) -
        X 2 * pderiv 2 (pderiv 1 (pderiv 1 p))) := by
  simp only [cubicLowerTwo, cubicXi, Fin.sum_univ_three, Matrix.of_apply, Fin.isValue,
    Fin.reduceEq, if_true, if_false, max01, max02, max12, max10, max20, max21, min01,
    min02, min12, min10, min20, min21, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_neg,
    pderiv_mul, pderiv_C, pdX, zero_mul, add_zero, zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

/-- Explicit expansion of `cubicLowerOne`. -/
public theorem cubicLowerOne_eq (M : Matrix (Fin 3) (Fin 3) CubicPoly) :
    cubicLowerOne M =
      (X 1 * pderiv 0 (pderiv 2 (M 0 0)) + X 1 * pderiv 1 (pderiv 2 (M 0 1)) +
        X 1 * pderiv 2 (pderiv 2 (M 0 2)))
      - (X 2 * pderiv 0 (pderiv 1 (M 0 0)) + X 2 * pderiv 1 (pderiv 1 (M 0 1)) +
        X 2 * pderiv 1 (pderiv 2 (M 0 2)))
      + (X 2 * pderiv 0 (pderiv 0 (M 1 0)) + X 2 * pderiv 0 (pderiv 1 (M 1 1)) +
        X 2 * pderiv 0 (pderiv 2 (M 1 2)))
      - (X 0 * pderiv 0 (pderiv 2 (M 1 0)) + X 0 * pderiv 1 (pderiv 2 (M 1 1)) +
        X 0 * pderiv 2 (pderiv 2 (M 1 2)))
      + (X 0 * pderiv 0 (pderiv 1 (M 2 0)) + X 0 * pderiv 1 (pderiv 1 (M 2 1)) +
        X 0 * pderiv 1 (pderiv 2 (M 2 2)))
      - (X 1 * pderiv 0 (pderiv 0 (M 2 0)) + X 1 * pderiv 0 (pderiv 1 (M 2 1)) +
        X 1 * pderiv 0 (pderiv 2 (M 2 2))) := by
  simp only [cubicLowerOne, Fin.sum_univ_three, Fin.isValue, Fin.val_zero, Fin.val_one,
    Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, c10, c20, c21]
  norm_num
  ring

/-- Explicit formula for `cubicLowerOne (cubicXi ν p)`. -/
public theorem cubicLowerOne_cubicXi (ν : Fin 3 → ℂ) (p : CubicPoly) :
    cubicLowerOne (cubicXi ν p) = C 2 * (C (ν 1 - ν 0 + 1) * (X 2 * pderiv 0 (pderiv 1 p))
      + C (ν 0 - ν 2 - 1) * (X 1 * pderiv 0 (pderiv 2 p))
      + C (ν 2 - ν 1 + 1) * (X 0 * pderiv 1 (pderiv 2 p))
      + X 2 * (X 1 * pderiv 1 (pderiv 0 (pderiv 1 p)))
      - X 1 * (X 1 * pderiv 1 (pderiv 0 (pderiv 2 p)))
      - X 0 * (X 2 * pderiv 1 (pderiv 1 (pderiv 1 p)))
      + X 0 * (X 1 * pderiv 1 (pderiv 1 (pderiv 2 p)))) := by
  rw [cubicLowerOne_eq]
  simp only [cubicXi, Matrix.of_apply, Fin.isValue, Fin.reduceEq, if_true, if_false,
    max01, max02, max12, max10, max20, max21, min01, min02, min12, min10, min20, min21,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_add, map_sub, map_neg, pderiv_mul, pderiv_C, pdX, zero_mul,
    add_zero, zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

/-- Explicit formula for `cubicQSum (cubicXi ν p)`. -/
public theorem cubicQSum_cubicXi (ν : Fin 3 → ℂ) (p : CubicPoly) :
    cubicQSum (cubicXi ν p) = C 2 * (C (ν 0) * (X 0 * pderiv 0 p) +
      C (ν 1) * (X 1 * pderiv 1 p) + C (ν 2) * (X 2 * pderiv 2 p))
      + X 0 ^ 2 * (pderiv 1 (pderiv 1 p) + pderiv 2 (pderiv 2 p))
      + X 1 ^ 2 * (pderiv 2 (pderiv 2 p) - pderiv 0 (pderiv 0 p))
      - X 2 ^ 2 * (pderiv 0 (pderiv 0 p) + pderiv 1 (pderiv 1 p)) := by
  simp only [cubicQSum, cubicXi, Fin.sum_univ_three, Matrix.of_apply, Fin.isValue,
    Fin.reduceEq, if_true, if_false, max01, max02, max12, max10, max20, max21, min01,
    min02, min12, min10, min20, min21, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_neg,
    pderiv_mul, pderiv_C, pdX, zero_mul, add_zero, zero_add, one_mul, c10, c20, c21]
  simp only [map_add, map_mul, map_neg, map_one, map_ofNat]
  ring

/-- `cubicLowerTwo ∘ cubicXi ν` on diagonal quadratics is a constant. -/
public theorem cubicLowerTwo_cubicXi_diagQuad (ν : Fin 3 → ℂ) (α β : ℂ) :
    cubicLowerTwo (cubicXi ν (C α * (X 0 ^ 2 - X 2 ^ 2) + C β * (X 1 ^ 2 - X 2 ^ 2))) =
      C (4 * (α * (ν 0 - ν 2 - 2) + β * (ν 1 - ν 2 - 1))) := by
  rw [cubicLowerTwo_cubicXi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C,
    pd_ofNat, pdXsq, pdX, pderiv_mul, pderiv_one, map_zero, Fin.reduceEq,
    eq_self_iff_true, if_true, if_false, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

/-- `cubicSameTwo ∘ cubicXi ν` preserves the diagonal-quadratic plane, with the
explicit scalar action below. -/
public theorem cubicSameTwo_cubicXi_diagQuad (ν : Fin 3 → ℂ) (α β : ℂ) :
    cubicSameTwo (cubicXi ν (C α * (X 0 ^ 2 - X 2 ^ 2) + C β * (X 1 ^ 2 - X 2 ^ 2))) =
      C (16 * α * ν 0 + 8 * α * ν 2 + 4 * α - 8 * β * ν 1 + 8 * β * ν 2 + 8 * β) *
        (X 0 ^ 2 - X 2 ^ 2)
      + C (-8 * α * ν 0 + 8 * α * ν 2 - 8 * α + 16 * β * ν 1 + 8 * β * ν 2 - 4 * β) *
        (X 1 ^ 2 - X 2 ^ 2) := by
  rw [cubicSameTwo_eq, cubicQSum_cubicXi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C,
    pd_ofNat, pdXsq, pdX, pderiv_mul, pderiv_one, map_zero, Fin.reduceEq,
    eq_self_iff_true, if_true, if_false, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, map_neg, mul_neg, neg_mul, neg_zero, mul_one]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

/-- `cubicLowerOne ∘ cubicXi ν` sends `X_0 X_1` to a multiple of `X_2`. -/
public theorem cubicLowerOne_cubicXi_X01 (ν : Fin 3 → ℂ) (z : ℂ) :
    cubicLowerOne (cubicXi ν (C z * (X 0 * X 1))) = C (-2 * z * (ν 0 - ν 1 - 1)) * X 2 := by
  rw [cubicLowerOne_cubicXi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C,
    pd_ofNat, pdX, pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true,
    if_true, if_false, mul_zero, zero_mul, add_zero, zero_add, sub_zero, map_neg,
    mul_neg, neg_mul, neg_zero, mul_one, one_mul]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

/-- `cubicLowerOne ∘ cubicXi ν` sends `X_0 X_2` to a multiple of `X_1`. -/
public theorem cubicLowerOne_cubicXi_X02 (ν : Fin 3 → ℂ) (z : ℂ) :
    cubicLowerOne (cubicXi ν (C z * (X 0 * X 2))) = C (2 * z * (ν 0 - ν 2 - 1)) * X 1 := by
  rw [cubicLowerOne_cubicXi]
  simp only [Fin.isValue, map_add, map_sub, mul_add, mul_sub, pderiv_C_mul, pderiv_C,
    pd_ofNat, pdX, pderiv_mul, pderiv_one, map_zero, Fin.reduceEq, eq_self_iff_true,
    if_true, if_false, mul_zero, zero_mul, add_zero, zero_add, sub_zero, map_neg,
    mul_neg, neg_mul, neg_zero, mul_one, one_mul]
  simp only [map_add, map_sub, map_mul, map_neg, map_one, map_ofNat]
  ring

private lemma mem_of_C_mul_mem (S : Submodule ℂ CubicPoly) (v : CubicPoly) (L : ℂ)
    (hL : L ≠ 0) (h : C L * v ∈ S) : v ∈ S := by
  have := S.smul_mem L⁻¹ h
  rwa [smul_eq_C_mul, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hL, map_one, one_mul] at this

private theorem one_mem_of_stable (ν : Fin 3 → ℂ)
    (h01 : ν 0 - ν 1 - 1 ≠ 0) (h02 : ν 0 - ν 2 - 1 ≠ 0) (h12 : ν 1 - ν 2 - 1 ≠ 0)
    (S₀ S₂ : Submodule ℂ CubicPoly)
    (hS₀ : S₀ ≤ Submodule.span ℂ {(1 : CubicPoly)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 ^ 2 - X 2 ^ 2 : CubicPoly), X 1 ^ 2 - X 2 ^ 2})
    (hst : ∀ p ∈ S₂, cubicLowerTwo (cubicXi ν p) ∈ S₀ ∧ cubicSameTwo (cubicXi ν p) ∈ S₂)
    (hne : S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) : (1 : CubicPoly) ∈ S₀ := by
  have key : ∀ L : ℂ, C L ∈ S₀ → L = 0 ∨ (1 : CubicPoly) ∈ S₀ := by
    intro L hmem
    rcases eq_or_ne L 0 with hL | hL
    · exact Or.inl hL
    · exact Or.inr (mem_of_C_mul_mem S₀ 1 L hL (by rwa [mul_one]))
  rcases hne with h0 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h0
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₀ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul, mul_one] at hs
    exact (key z hs).resolve_left hz
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.1 (hS₂ hp)
    rw [smul_eq_C_mul, smul_eq_C_mul] at hp hp0
    obtain ⟨hL1, hS⟩ := hst _ hp
    obtain ⟨hL2, -⟩ := hst _ hS
    rw [cubicLowerTwo_cubicXi_diagQuad] at hL1
    rw [cubicSameTwo_cubicXi_diagQuad, cubicLowerTwo_cubicXi_diagQuad] at hL2
    rcases key _ hL1 with hz1 | h
    swap; · exact h
    rcases key _ hL2 with hz2 | h
    swap; · exact h
    exfalso
    apply hp0
    have hdet : (ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h01 h02) h12
    have hα : α = 0 := by
      have e : α * ((ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1)) = 0 := by
        linear_combination
          (-(-2 * ν 0 * ν 1 + 2 * ν 0 * ν 2 + 2 * ν 0 + 4 * ν 1 ^ 2 - ν 1 -
            4 * ν 2 ^ 2 - 7 * ν 2 - 3) / 24) * hz1
          + ((ν 1 - ν 2 - 1) / 96) * hz2
      exact (mul_eq_zero.1 e).resolve_right hdet
    have hβ : β = 0 := by
      have e : β * ((ν 0 - ν 1 - 1) * (ν 0 - ν 2 - 1) * (ν 1 - ν 2 - 1)) = 0 := by
        linear_combination
          ((4 * ν 0 ^ 2 - 2 * ν 0 * ν 1 - 5 * ν 0 + 2 * ν 1 * ν 2 - 2 * ν 1 -
            4 * ν 2 ^ 2 - 5 * ν 2) / 24) * hz1
          + (-(ν 0 - ν 2 - 2) / 96) * hz2
      exact (mul_eq_zero.1 e).resolve_right hdet
    simp [hα, hβ]

private theorem X_two_mem_of_stable (ν : Fin 3 → ℂ) (h01 : ν 0 - ν 1 - 1 ≠ 0)
    (S₁ S₂ : Submodule ℂ CubicPoly)
    (hS₁ : S₁ ≤ Submodule.span ℂ {(X 2 : CubicPoly)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 * X 1 : CubicPoly)})
    (hst : ∀ p ∈ S₂, cubicLowerOne (cubicXi ν p) ∈ S₁)
    (hne : S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) : (X 2 : CubicPoly) ∈ S₁ := by
  rcases hne with h1 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h1
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₁ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hs
    exact mem_of_C_mul_mem S₁ _ z hz hs
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₂ hp)
    have hz : z ≠ 0 := by rintro rfl; exact hp0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hp
    have h := hst _ hp
    rw [cubicLowerOne_cubicXi_X01] at h
    refine mem_of_C_mul_mem S₁ _ _ ?_ h
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz) h01

private theorem X_one_mem_of_stable (ν : Fin 3 → ℂ) (h02 : ν 0 - ν 2 - 1 ≠ 0)
    (S₁ S₂ : Submodule ℂ CubicPoly)
    (hS₁ : S₁ ≤ Submodule.span ℂ {(X 1 : CubicPoly)})
    (hS₂ : S₂ ≤ Submodule.span ℂ {(X 0 * X 2 : CubicPoly)})
    (hst : ∀ p ∈ S₂, cubicLowerOne (cubicXi ν p) ∈ S₁)
    (hne : S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) : (X 1 : CubicPoly) ∈ S₁ := by
  rcases hne with h1 | h2
  · obtain ⟨s, hs, hs0⟩ := (Submodule.ne_bot_iff _).1 h1
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₁ hs)
    have hz : z ≠ 0 := by rintro rfl; exact hs0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hs
    exact mem_of_C_mul_mem S₁ _ z hz hs
  · obtain ⟨p, hp, hp0⟩ := (Submodule.ne_bot_iff _).1 h2
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 (hS₂ hp)
    have hz : z ≠ 0 := by rintro rfl; exact hp0 (zero_smul _ _)
    rw [smul_eq_C_mul] at hp
    have h := hst _ hp
    rw [cubicLowerOne_cubicXi_X02] at h
    refine mem_of_C_mul_mem S₁ _ _ ?_ h
    exact mul_ne_zero (mul_ne_zero (by norm_num) hz) h02

private lemma ne_zero_of_re_ne_zero {z : ℂ} (h : z.re ≠ 0) : z ≠ 0 :=
  fun hz => h (by simp [hz])

/-- Transition stability at the two weight parameters forces the bottom
vectors into the stable subspaces: a stable pair on constants and diagonal
quadratics contains `1`; a stable pair on `X_2` and `X_0 X_1` contains `X_2`;
and the swapped parameter gives `1` and `X_1` in the same way. -/
public theorem cubicBottom_mem_of_transitionStable_degree_le_two (τ τ₃ : ℝ) :
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, cubicLowerTwo (cubicXi (cubicNu12 τ τ₃) p) ∈ S₀ ∧
        cubicSameTwo (cubicXi (cubicNu12 τ τ₃) p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 1 :
        MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, cubicLowerOne (cubicXi (cubicNu12 τ τ₃) p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 2 : MvPolynomial (Fin 3) ℂ) ∈ S₁) ∧
    (∀ S₀ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₀ ≤ Submodule.span ℂ {(1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {MvPolynomial.X 0 ^ 2 - MvPolynomial.X 2 ^ 2,
        MvPolynomial.X 1 ^ 2 - MvPolynomial.X 2 ^ 2} →
      (∀ p ∈ S₂, cubicLowerTwo (cubicXi (cubicNu13 τ τ₃) p) ∈ S₀ ∧
        cubicSameTwo (cubicXi (cubicNu13 τ τ₃) p) ∈ S₂) →
      (S₀ ≠ ⊥ ∨ S₂ ≠ ⊥) → (1 : MvPolynomial (Fin 3) ℂ) ∈ S₀) ∧
    (∀ S₁ S₂ : Submodule ℂ (MvPolynomial (Fin 3) ℂ),
      S₁ ≤ Submodule.span ℂ {(MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ)} →
      S₂ ≤ Submodule.span ℂ {(MvPolynomial.X 0 * MvPolynomial.X 2 :
        MvPolynomial (Fin 3) ℂ)} →
      (∀ p ∈ S₂, cubicLowerOne (cubicXi (cubicNu13 τ τ₃) p) ∈ S₁) →
      (S₁ ≠ ⊥ ∨ S₂ ≠ ⊥) → (MvPolynomial.X 1 : MvPolynomial (Fin 3) ℂ) ∈ S₁) := by
  have A01 : cubicNu12 τ τ₃ 0 - cubicNu12 τ τ₃ 1 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [cubicNu12]; norm_num
  have A02 : cubicNu12 τ τ₃ 0 - cubicNu12 τ τ₃ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [cubicNu12]; norm_num
  have A12 : cubicNu12 τ τ₃ 1 - cubicNu12 τ τ₃ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [cubicNu12]; norm_num
  have B01 : cubicNu13 τ τ₃ 0 - cubicNu13 τ τ₃ 1 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [cubicNu13]; norm_num
  have B02 : cubicNu13 τ τ₃ 0 - cubicNu13 τ τ₃ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [cubicNu13]; norm_num
  have B12 : cubicNu13 τ τ₃ 1 - cubicNu13 τ τ₃ 2 - 1 ≠ 0 := by
    apply ne_zero_of_re_ne_zero; simp [cubicNu13]; norm_num
  refine ⟨fun S₀ S₂ h0 h2 hst hne => ?_, fun S₁ S₂ h1 h2 hst hne => ?_,
    fun S₀ S₂ h0 h2 hst hne => ?_, fun S₁ S₂ h1 h2 hst hne => ?_⟩
  · exact one_mem_of_stable _ A01 A02 A12 S₀ S₂ h0 h2 hst hne
  · exact X_two_mem_of_stable _ A01 S₁ S₂ h1 h2 hst hne
  · exact one_mem_of_stable _ B01 B02 B12 S₀ S₂ h0 h2 hst hne
  · exact X_one_mem_of_stable _ B02 S₁ S₂ h1 h2 hst hne
