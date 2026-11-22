/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
Canonical evaluation, maximal polynomial ideals and symmetric generators. Quotient common-zero
bijections and Vieta substitutions are not asserted.
-/

set_option autoImplicit false
noncomputable section

example (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    I.IsMaximal ↔ ∃ a : Fin n → ℂ, I = MvPolynomial.vanishingIdeal ℂ {a} :=
  MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton

example (n : ℕ) (a : Fin n → ℂ) :
    (MvPolynomial.vanishingIdeal ℂ {a} : Ideal (MvPolynomial (Fin n) ℂ)) =
      RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ) := by
  ext p
  exact MvPolynomial.mem_vanishingIdeal_singleton_iff a p

example (σ R : Type*) [Fintype σ] [CommRing R] (n : ℕ) (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) R ≃ₐ[R] MvPolynomial.symmetricSubalgebra σ R :=
  MvPolynomial.esymmAlgEquiv σ R hn

example {R S σ : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : σ → S) :
    MvPolynomial σ R →+* S := MvPolynomial.eval₂Hom f a

example {R S σ : Type*} [CommRing R] [CommRing S]
    (f g : MvPolynomial σ R →+* S)
    (hC : ∀ r, f (MvPolynomial.C r) = g (MvPolynomial.C r))
    (hX : ∀ i, f (MvPolynomial.X i) = g (MvPolynomial.X i)) : f = g :=
  MvPolynomial.ringHom_ext hC hX

#print axioms MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton
#print axioms MvPolynomial.mem_vanishingIdeal_singleton_iff
#print axioms MvPolynomial.esymmAlgEquiv
#print axioms MvPolynomial.eval₂Hom
#print axioms MvPolynomial.ringHom_ext

end
