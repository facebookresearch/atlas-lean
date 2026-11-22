/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeConstruction

/-!
# Explicit original-cardinal data under caller-bottom transport

The convenience constructor and the given-bottom factory both use the same
original cardinal and full generator family. The least-point dictionary is
unique, so the explicit full functorial data agree after its transport.
The heterogeneous statements retain their dependent endpoint types.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.Construction

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The whole explicit original-cardinal data agree under the actual caller bottom. -/
theorem cofibrantFactorizationData_heq_native :
    HEq (cofibrantFactorizationData (A := A)) (Native.cofibrantFactorizationData (B := B) (A :=
      A)) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The entire intermediate functor agrees with the actual caller-bottom functor. -/
theorem cofibrantFactorizationData_Z_eq_native :
    (cofibrantFactorizationData (A := A)).Z = (Native.cofibrantFactorizationData (B := B) (A :=
      A)).Z := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete original first natural arrow is retained under caller-bottom transport. -/
theorem cofibrantFactorizationData_i_heq_native :
    HEq (cofibrantFactorizationData (A := A)).i (Native.cofibrantFactorizationData (B := B) (A
      := A)).i := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete original second natural arrow is retained under caller-bottom transport. -/
theorem cofibrantFactorizationData_p_heq_native :
    HEq (cofibrantFactorizationData (A := A)).p (Native.cofibrantFactorizationData (B := B) (A
      := A)).p := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every intermediate map of the caller's full Arrow square is retained. -/
theorem cofibrantFactorizationData_Z_map_heq_native
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (φ : f ⟶ g) :
    HEq ((cofibrantFactorizationData (A := A)).Z.map φ) ((Native.cofibrantFactorizationData (B
      := B) (A := A)).Z.map φ) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The whole explicit original-cardinal data agree under the actual caller bottom. -/
theorem fibrantFactorizationData_heq_native :
    HEq (fibrantFactorizationData (A := A)) (Native.fibrantFactorizationData (B := B) (A := A))
      := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The entire intermediate functor agrees with the actual caller-bottom functor. -/
theorem fibrantFactorizationData_Z_eq_native :
    (fibrantFactorizationData (A := A)).Z = (Native.fibrantFactorizationData (B := B) (A :=
      A)).Z := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete original first natural arrow is retained under caller-bottom transport. -/
theorem fibrantFactorizationData_i_heq_native :
    HEq (fibrantFactorizationData (A := A)).i (Native.fibrantFactorizationData (B := B) (A :=
      A)).i := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- The complete original second natural arrow is retained under caller-bottom transport. -/
theorem fibrantFactorizationData_p_heq_native :
    HEq (fibrantFactorizationData (A := A)).p (Native.fibrantFactorizationData (B := B) (A :=
      A)).p := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

/-- Every intermediate map of the caller's full Arrow square is retained. -/
theorem fibrantFactorizationData_Z_map_heq_native
    {f g : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} A)} (φ : f ⟶ g) :
    HEq ((fibrantFactorizationData (A := A)).Z.map φ) ((Native.fibrantFactorizationData (B := B)
      (A := A)).Z.map φ) := by
  have hB : B = generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  rfl

end HomotopicalAlgebra.EnrichedProjective.Native.Construction
