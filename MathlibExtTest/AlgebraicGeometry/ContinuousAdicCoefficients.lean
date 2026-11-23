/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

/-! # Tests for continuous coefficient sheaves on the pro-étale site

Sections of the continuous coefficient presheaf are continuous maps and its restriction maps are
precomposition; forgetting the module structure gives Mathlib's presheaf of continuous maps; the
lattice inclusion is the inclusion of continuous lattice-valued maps.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.ContinuousAdicCoefficients

open CategoryTheory Opposite _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients

universe u

section ContinuousModules

variable (R : Type) [Ring R] (M : Type (u + 1))
  [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

example (U : Scheme.{u}) : ((continuousModulePresheaf R M).obj (op U) : Type (u + 1)) = C(U, M) :=
  rfl

/-- Restriction is precomposition with the underlying continuous map. -/
example {U V : Scheme.{u}} (f : V ⟶ U) (a : C(U, M)) (x : V) :
    (show C(V, M) from (continuousModulePresheaf R M).map f.op a) x = a (f.base x) :=
  rfl

/-- Restriction is `R`-linear. -/
example {U V : Scheme.{u}} (f : V ⟶ U) (r : R) (a : C(U, M)) :
    (continuousModulePresheaf R M).map f.op (r • a) =
      r • (continuousModulePresheaf R M).map f.op a :=
  map_smul _ r a

example : continuousModulePresheaf R M ⋙ forget (ModuleCat.{u + 1} R) =
    continuousMapPresheaf.{u + 1, u} M := rfl

example (X : Scheme.{u}) : CoefficientSheaf X R := continuousModuleSheaf R M X

end ContinuousModules

section Lattices

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (V : Type (u + 1)) [TopologicalSpace V] [AddCommGroup V] [Module S V]
  [IsTopologicalAddGroup V] [ContinuousConstSMul S V]
  (L : Submodule R (restrictedVector R S V))

/-- Scalars of `R` act on the restricted coefficient module through `algebraMap R S`. -/
example (r : R) (v : restrictedVector R S V) :
    r • v = (algebraMap R S r • (v : V) : V) := rfl

example (X : Scheme.{u}) :
    (scalarExtension R S X).obj (continuousModuleSheaf R L X) ⟶ continuousModuleSheaf S V X :=
  latticeScalarComparison R S V L X

end Lattices

end MathlibExtTest.AlgebraicGeometry.ContinuousAdicCoefficients
