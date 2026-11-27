/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Algebra.Ring.Equiv

/-!
# Coefficients as continuous functions on a singleton

For a topological space `X` with exactly one point and a topological
semiring `R`, the constant-function map is a semiring equivalence
`R ≃ C(X,R)`. Its inverse evaluates at the unique point. The forward
and inverse maps are identified both pointwise and as whole bundled
homomorphisms.

For topological semirings `R,S` in independent universes, these
equivalences commute with every continuous coefficient semiring homomorphism
`R→S`. With commutative coefficients, their maps are also the standard
constant and evaluation algebra homomorphisms. The singleton hypothesis is
`Unique X`, so the point exists; no norm, compactness assumption or additive
inverses are required.
-/

public section

noncomputable section

universe uX uR uS

namespace ContinuousMap

section Semiring

variable (X : Type uX) (R : Type uR) [Unique X] [TopologicalSpace X]
  [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

private theorem singletonEvaluation_bijective :
    Function.Bijective
      ((Pi.evalRingHom (fun _ : X => R) (default : X)).comp
        (coeFnRingHom : C(X, R) →+* (X → R))) := by
  constructor
  · intro f g h
    apply ContinuousMap.ext
    intro x
    change f (default : X) = g (default : X) at h
    exact (congrArg f (Subsingleton.elim x (default : X))).trans
      (h.trans (congrArg g (Subsingleton.elim (default : X) x)))
  · intro r
    exact ⟨ContinuousMap.const X r, rfl⟩

/-- The semiring equivalence sending a coefficient to its constant function on the one-point
domain, with evaluation as inverse.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent. -/
def constRingEquiv : R ≃+* C(X, R) :=
  (RingEquiv.ofBijective
    ((Pi.evalRingHom (fun _ : X => R) (default : X)).comp
      (coeFnRingHom : C(X, R) →+* (X → R)))
    (singletonEvaluation_bijective X R)).symm

/-- The inverse coefficient is the function value at the unique domain point.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent.

```lean
theorem constRingEquiv_symm_apply (f : C(X, R)) :
    (constRingEquiv X R).symm f = f (default : X)
``` -/
@[simp]
theorem constRingEquiv_symm_apply (f : C(X, R)) :
    (constRingEquiv X R).symm f = f (default : X) := by
  change RingEquiv.ofBijective _ (singletonEvaluation_bijective X R) f = _
  exact RingEquiv.ofBijective_apply _ _ f

/-- The forward value is exactly the constant continuous function.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent.

```lean
theorem constRingEquiv_apply (r : R) :
    constRingEquiv X R r = ContinuousMap.const X r
``` -/
@[simp]
theorem constRingEquiv_apply (r : R) :
    constRingEquiv X R r = ContinuousMap.const X r := by
  apply (constRingEquiv X R).symm.injective
  rw [RingEquiv.symm_apply_apply, constRingEquiv_symm_apply]
  rfl

/-- The whole forward function is the constant-function constructor.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent.

```lean
theorem coe_constRingEquiv :
    (constRingEquiv X R : R → C(X, R)) = ContinuousMap.const X
``` -/
theorem coe_constRingEquiv :
    (constRingEquiv X R : R → C(X, R)) = ContinuousMap.const X := by
  funext r
  exact constRingEquiv_apply X R r

/-- The inverse semiring homomorphism is evaluation at the unique point after taking the underlying
function.

`X` has exactly one point and `R` is a topological semiring. Their universes are independent.

```lean
theorem constRingEquiv_symm_toRingHom :
    (constRingEquiv X R).symm.toRingHom =
      (Pi.evalRingHom (fun _ : X => R) (default : X)).comp
        (coeFnRingHom : C(X, R) →+* (X → R))
``` -/
theorem constRingEquiv_symm_toRingHom :
    (constRingEquiv X R).symm.toRingHom =
      (Pi.evalRingHom (fun _ : X => R) (default : X)).comp
        (coeFnRingHom : C(X, R) →+* (X → R)) := by
  apply RingHom.ext
  intro f
  exact constRingEquiv_symm_apply X R f

end Semiring

section Coefficients

variable (X : Type uX) [Unique X] [TopologicalSpace X]
  {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]
  [TopologicalSpace R] [TopologicalSpace S] [IsTopologicalSemiring R] [IsTopologicalSemiring S]

/-- Singleton coefficient equivalences commute with continuous semiring-homomorphism
postcomposition, in independent coefficient universes.

`X` has exactly one point; `R,S` are topological semirings and the displayed semiring homomorphism
is continuous.

```lean
theorem constRingEquiv_compLeftContinuous (f : R →+* S) (hf : Continuous f) :
    (f.compLeftContinuous X hf).comp (constRingEquiv X R).toRingHom =
      (constRingEquiv X S).toRingHom.comp f
``` -/
theorem constRingEquiv_compLeftContinuous (f : R →+* S) (hf : Continuous f) :
    (f.compLeftContinuous X hf).comp (constRingEquiv X R).toRingHom =
      (constRingEquiv X S).toRingHom.comp f := by
  apply RingHom.ext
  intro r
  apply ContinuousMap.ext
  intro x
  change f ((constRingEquiv X R r) x) = (constRingEquiv X S (f r)) x
  simp only [constRingEquiv_apply, const_apply]

end Coefficients

section Commutative

variable (X : Type uX) (R : Type uR) [Unique X] [TopologicalSpace X]
  [CommSemiring R] [TopologicalSpace R] [IsTopologicalSemiring R]

/-- For commutative semiring coefficients, the forward map is the constant algebra homomorphism
viewed as a semiring homomorphism.

`X` has exactly one point and `R` is a topological commutative semiring.

```lean
theorem constRingEquiv_toRingHom :
    (constRingEquiv X R).toRingHom = ContinuousMap.C (α := X) (R := R) (A := R)
``` -/
theorem constRingEquiv_toRingHom :
    (constRingEquiv X R).toRingHom = ContinuousMap.C (α := X) (R := R) (A := R) := by
  apply RingHom.ext
  intro r
  apply ContinuousMap.ext
  intro x
  change (constRingEquiv X R r) x = (ContinuousMap.C r) x
  rw [constRingEquiv_apply, const_apply, C_apply]
  rfl

/-- For commutative semiring coefficients, the inverse map is evaluation at the unique point viewed
as a semiring homomorphism.

`X` has exactly one point and `R` is a topological commutative semiring.

```lean
theorem constRingEquiv_symm_toEvalAlgHom :
    (constRingEquiv X R).symm.toRingHom =
      (ContinuousMap.evalAlgHom R R (default : X)).toRingHom
``` -/
theorem constRingEquiv_symm_toEvalAlgHom :
    (constRingEquiv X R).symm.toRingHom =
      (ContinuousMap.evalAlgHom R R (default : X)).toRingHom := by
  apply RingHom.ext
  intro f
  exact constRingEquiv_symm_apply X R f

end Commutative

end ContinuousMap
