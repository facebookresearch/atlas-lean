/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.ConstructionFactorization
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.Factorization

/-!
# Exact original source cardinal data under caller-bottom transport

Both named source data use the same native generator cardinal and actual
carrier inverse. The original constructed bottom is unique. These comparisons
retain both whole packets, whole intermediate functors and dependent i/p/maps.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation.Construction

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The whole original source packet retains its actual caller-bottom value. -/
theorem cofibrantFactorizationData_heq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HEq (cofibrantFactorizationData e) (NativePresentation.cofibrantFactorizationData e) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete original source middle functor is unchanged. -/
theorem cofibrantFactorizationData_Z_eq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (cofibrantFactorizationData e).Z = (NativePresentation.cofibrantFactorizationData e).Z := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The whole original first natural map is unchanged. -/
theorem cofibrantFactorizationData_i_heq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HEq (cofibrantFactorizationData e).i (NativePresentation.cofibrantFactorizationData e).i := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The whole original second natural map is unchanged. -/
theorem cofibrantFactorizationData_p_heq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HEq (cofibrantFactorizationData e).p (NativePresentation.cofibrantFactorizationData e).p := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every full original Arrow square retains its dependent middle map. -/
theorem cofibrantFactorizationData_Z_map_heq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {f g : CategoryTheory.Arrow C} (φ : f ⟶ g) :
    HEq ((cofibrantFactorizationData e).Z.map φ)
      ((NativePresentation.cofibrantFactorizationData e).Z.map φ) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The whole original source packet retains its actual caller-bottom value. -/
theorem fibrantFactorizationData_heq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HEq (fibrantFactorizationData e) (NativePresentation.fibrantFactorizationData e) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete original source middle functor is unchanged. -/
theorem fibrantFactorizationData_Z_eq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    (fibrantFactorizationData e).Z = (NativePresentation.fibrantFactorizationData e).Z := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The whole original first natural map is unchanged. -/
theorem fibrantFactorizationData_i_heq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HEq (fibrantFactorizationData e).i (NativePresentation.fibrantFactorizationData e).i := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The whole original second natural map is unchanged. -/
theorem fibrantFactorizationData_p_heq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) :
    HEq (fibrantFactorizationData e).p (NativePresentation.fibrantFactorizationData e).p := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every full original Arrow square retains its dependent middle map. -/
theorem fibrantFactorizationData_Z_map_heq_existing
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A)
    {f g : CategoryTheory.Arrow C} (φ : f ⟶ g) :
    HEq ((fibrantFactorizationData e).Z.map φ)
      ((NativePresentation.fibrantFactorizationData e).Z.map φ) := by
  have hB : B = Native.Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

end HomotopicalAlgebra.EnrichedProjective.NativePresentation.Construction
