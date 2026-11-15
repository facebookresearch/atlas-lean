/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AdicDerivedCompactSupports

/-!
# Native scope, cohomology covariance and trace normalization

The coefficient is an arbitrary topological commutative ring. Relative
support allows a scheme base; the absolute RΓ_c test has an explicit
structural map to a field's spectrum. The coefficient needs no field,
torsion or smoothness hypothesis. A zero counit cannot stand in for the
trace when its right-adjoint object is nonzero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AdicRingedSiteOperations
open MathlibExt.AlgebraicGeometry.AdicDerivedCompactSupports

attribute [local instance] HasDerivedCategory.standard

variable (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]

/-- The identity model is a valid relative compactification over any scheme. -/
example (X : Scheme) : Compactification (𝟙 X) := Compactification.identity X

example {X : Scheme} {K L M : Derived E X} (a : K ⟶ L) (b : L ⟶ M) (n : ℤ) :
    unitCohomologyMap E (a ≫ b) n =
      (unitCohomologyMap E b n).comp (unitCohomologyMap E a n) :=
  unitCohomologyMap_comp E a b n

example {X : Scheme} (K : Derived E X) (n : ℤ) :
    unitCohomologyMap E (𝟙 K) n = AddMonoidHom.id _ :=
  unitCohomologyMap_id E K n

section Trace

variable {X Y : Scheme} (p : X ⟶ Y) [IsProper p] [ModuleInjectives E]
  [(derivedPushforward E p).IsLeftAdjoint]

/-- The canonical unit excludes a constant-zero trace on nonzero objects. -/
example (K : Derived E Y) (hK : ¬ IsZero ((properExceptionalPullback E p).obj K)) :
    (properTrace E p).app K ≠ 0 := by
  intro hzero
  have h := properTrace_unit E p K
  rw [hzero, Functor.map_zero, comp_zero] at h
  exact hK ((IsZero.iff_id_eq_zero _).mpr h.symm)

end Trace

section Compactification

variable {X S : Scheme} {f : X ⟶ S} (c : Compactification f) [ModuleInjectives E]
  [(pushforward E c.openMap).IsRightAdjoint]
  [(pullback E c.openMap).IsRightAdjoint]
  [PreservesFiniteLimits (extensionByZero E c.openMap)]

/-- The relative proper-support carrier is the actual derived module category. -/
example : Derived E X ⥤ DerivedCategory.Plus (ModuleCat.{1} E) :=
  derivedRelativeCompactSections E c

/-- The compactification supplies the exact geometric factorization. -/
example : c.openMap ≫ c.properMap = f := c.factorization

end Compactification

section Absolute

variable {k : Type} [Field k] {X : Scheme} {f : X ⟶ Spec (.of k)}
  (c : Compactification f) [ModuleInjectives E]
  [(pushforward E c.openMap).IsRightAdjoint]
  [(pullback E c.openMap).IsRightAdjoint]
  [PreservesFiniteLimits (extensionByZero E c.openMap)]

/-- Absolute RΓ_c has the structural/proper ambient base in its actual type. -/
example : Derived E X ⥤ DerivedCategory.Plus (ModuleCat.{1} E) :=
  derivedCompactSections E c

end Absolute
