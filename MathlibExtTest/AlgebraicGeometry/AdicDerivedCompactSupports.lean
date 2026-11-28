/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AdicDerivedCompactSupports

/-!
# Tests for derived compact supports

Compactifications, covariance of cohomology, the trace triangle (a zero trace is excluded on
nonzero objects), the derived unit of an exact extension by zero, and the derived refinement
pasting with its normalization.
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

section Constructed

/-- An exact extension by zero has invertible derived unit, by instance search. -/
example {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j] [(pushforward E j).IsRightAdjoint]
    [(pullback E j).IsRightAdjoint] [ModuleInjectives E]
    [PreservesFiniteLimits (extensionByZero E j)] (K : Cochains E X) :
    IsIso ((extensionByZero E j).rightDerivedFunctorPlusUnit.app K) := inferInstance

variable {X S : Scheme} {f : X ⟶ S} {c d : Compactification f} (r : Refinement c d)
  [(pushforward E c.openMap).IsRightAdjoint] [(pushforward E d.openMap).IsRightAdjoint]
  [(pushforward E r.map).IsRightAdjoint] [RingedRefinementPasting E r] [ModuleInjectives E]
  [PreservesFiniteLimits (pullback E c.openMap)] [PreservesFiniteLimits (pullback E d.openMap)]
  [PreservesFiniteLimits (pullback E r.map)]

/-- The derived refinement pasting exists, by instance search. -/
example : DerivedRefinementPasting E r := inferInstance

/-- It is compatible with the pasting on complexes. -/
example (K : Cochains E c.ambient) :
    refinementCompositeUnit E r K ≫
        (derivedRefinementPasting E r).comparison.hom.app
          (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map (refinementCochainPasting E r K).hom ≫
        (pullback E c.openMap).rightDerivedFunctorPlusUnit.app K :=
  (derivedRefinementPasting E r).unit_normalization K

end Constructed

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
