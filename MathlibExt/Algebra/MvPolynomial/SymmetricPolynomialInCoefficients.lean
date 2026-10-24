/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.Polynomial.Vieta
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.MvPolynomial.Basic

open scoped BigOperators

/-!
# Symmetric polynomials in the roots are polynomials in the coefficients

Source: `v1/Atlas/AlgebraNotes/code/GaloisTheory.lean`
(`GaloisTheory.symmetric_polynomial_in_esymm`, fully proved there),
formalizing the book's corollary (Subsection: Symmetric Polynomials):
"A symmetric polynomial in the roots of `P` can be written as a polynomial
in the coefficients of `P`."

More precisely, if `P` is a monic split polynomial of degree `n` with roots
`α : Fin n → F`, and `f` is a symmetric polynomial in `n` variables, then
`f` evaluated at the roots equals some polynomial `q` evaluated at the
signed coefficients `(-1)^(i+1) * P.coeff (n - (i+1))` of `P`, the
elementary symmetric polynomials in the roots, by Vieta's formulas.
-/

@[expose] public section

namespace Polynomial

/-- A symmetric polynomial evaluated at the roots of a monic split polynomial
`P` equals some polynomial evaluated at the signed coefficients of `P`.
This is the book's corollary that a symmetric polynomial in the roots of `P`
can be written as a polynomial in the coefficients of `P`; the signed
coefficients are the elementary symmetric polynomials in the roots, by
Vieta's formulas. -/
theorem symmetric_polynomial_in_esymm
    {F : Type*} [Field F] {P : Polynomial F} (hP : P.Monic) (hsplit : P.Splits)
    (n : ℕ) (hn : P.natDegree = n)
    (f : MvPolynomial (Fin n) F) (hf : f.IsSymmetric)
    (α : Fin n → F) (hα : P = ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i))) :
    ∃ q : MvPolynomial (Fin n) F,
      MvPolynomial.eval α f =
        MvPolynomial.eval
          (fun i : Fin n => (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1))) q := by
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  set q := (MvPolynomial.esymmAlgEquiv (Fin n) F hcard).symm ⟨f, hf⟩
  refine ⟨q, ?_⟩
  have hfq : f = (MvPolynomial.aeval
      (fun i : Fin n => MvPolynomial.esymm (Fin n) F (i.val + 1))) q := by
    have h1 : ((MvPolynomial.esymmAlgEquiv (Fin n) F hcard) q).val = f := by
      simp [q, AlgEquiv.apply_symm_apply]
    rw [← h1]
    change ((MvPolynomial.esymmAlgHom (Fin n) F n) q).val = _
    exact MvPolynomial.esymmAlgHom_apply (σ := Fin n) q
  suffices h : ∀ i : Fin n,
      MvPolynomial.eval α (MvPolynomial.esymm (Fin n) F (i.val + 1)) =
        (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1)) by
    rw [hfq]
    have key : (MvPolynomial.eval α).comp (MvPolynomial.aeval
        (fun i : Fin n => MvPolynomial.esymm (Fin n) F (i.val + 1))).toRingHom =
        MvPolynomial.eval
          (fun i : Fin n => (-1 : F) ^ (i.val + 1) * P.coeff (n - (i.val + 1))) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [MvPolynomial.eval_C]
      · intro i
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MvPolynomial.aeval_X, MvPolynomial.eval_X]
        exact h i
    exact RingHom.congr_fun key q
  intro i
  have hesymm : MvPolynomial.eval α (MvPolynomial.esymm (Fin n) F (i.val + 1)) =
      (Finset.univ.val.map α).esymm (i.val + 1) := by
    have := MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) F (i.val + 1) α
    rwa [MvPolynomial.aeval_def] at this
  rw [hesymm]
  have hroots : P.roots = Finset.univ.val.map α := by
    rw [hα, Finset.prod_eq_multiset_prod]
    conv_lhs =>
      rw [show Multiset.map (fun i => Polynomial.X - Polynomial.C (α i)) Finset.univ.val =
        Multiset.map (fun a => Polynomial.X - Polynomial.C a) (Finset.univ.val.map α) from by
          rw [Multiset.map_map]; rfl]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  rw [← hroots]
  have hi_le : n - (i.val + 1) ≤ P.natDegree := by omega
  have hvieta := Polynomial.coeff_eq_esymm_roots_of_splits hsplit hi_le
  rw [hP.leadingCoeff, one_mul] at hvieta
  have hsub : P.natDegree - (n - (i.val + 1)) = i.val + 1 := by omega
  rw [hsub] at hvieta
  rw [hvieta, ← mul_assoc, ← pow_add]
  simp

end Polynomial
