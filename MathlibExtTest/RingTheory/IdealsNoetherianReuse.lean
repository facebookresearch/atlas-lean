/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
Canonical ideal, Noetherian and finite-presentation APIs. The finite-free presentation witness
construction is not reproduced.
-/

set_option autoImplicit false
noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (I : Ideal R) (hI : I ≠ ⊤) : ∃ J : Ideal R, J.IsMaximal ∧ I ≤ J :=
  Ideal.exists_le_maximal I hI

example (I : Ideal R) : I.IsMaximal ↔ IsCoatom I := Ideal.isMaximal_def
example (I : Ideal R) : CommRing (R ⧸ I) := inferInstance
example (a : R) : a ∈ Ideal.span ({a} : Set R) := Ideal.subset_span (Set.mem_singleton a)

example [IsNoetherianRing R] [Module.Finite R M] : IsNoetherian R M := inferInstance
example [IsNoetherianRing R] [Module.Finite R M] : Module.FinitePresentation R M :=
  Module.finitePresentation_of_finite R M
example [IsNoetherianRing R] : IsNoetherianRing (Polynomial R) := Polynomial.isNoetherianRing

example : IsNoetherianRing R ↔ IsNoetherian R R := isNoetherianRing_iff
example :
    (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M :=
  monotone_stabilizes_iff_noetherian

example {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R M]
    [Module.FinitePresentation R N] (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    (LinearMap.ker f).FG := Module.FinitePresentation.fg_ker f hf

example (n : ℕ) (f : (Fin n → R) →ₗ[R] M) (hf : Function.Surjective f)
    (hk : (LinearMap.ker f).FG) : Module.FinitePresentation R M :=
  Module.finitePresentation_of_free_of_surjective f hf hk

example [IsBezout R] (a b : R) : Ideal.span {IsBezout.gcd a b} = Ideal.span {a, b} :=
  IsBezout.span_gcd a b

#print axioms Ideal.exists_le_maximal
#print axioms Ideal.isMaximal_def
#print axioms Ideal.Quotient.commRing
#print axioms Ideal.span
#print axioms isNoetherian_of_isNoetherianRing_of_finite
#print axioms Module.finitePresentation_of_finite
#print axioms Polynomial.isNoetherianRing
#print axioms isNoetherianRing_iff
#print axioms monotone_stabilizes_iff_noetherian
#print axioms Module.FinitePresentation.fg_ker
#print axioms Module.finitePresentation_of_free_of_surjective
#print axioms IsBezout.span_gcd

end
