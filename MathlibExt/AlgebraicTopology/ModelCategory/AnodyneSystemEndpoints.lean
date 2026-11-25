/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.AnodyneSystem
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Endpoint membership in an anodyne system

For an exact functorial precylinder, the endpoint corner of an initial-to-object
monomorphism is isomorphic to the actual endpoint. Initial preservation makes
the endpoint at the initial object an isomorphism; the specified pushout's first
coprojection is then an isomorphism. An1 and native left-orthogonal closure give
membership of both endpoints in the specified anodyne class.

This is the initial-object consequence of Cisinski, *Higher Categories and
Homotopical Algebra*, July 30, 2026, Definitions 2.4.8 and 2.4.11, used in
Lemma 2.4.28. The generic statement displays the initial-monomorphism hypothesis
and requires no terminal object, model structure or object fibrancy.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits

universe w v u

namespace HomotopicalAlgebra.Precylinder.IsAnodyneSystem

variable {C : Type u} [Category.{v} C]
  [HasBinaryCoproducts C] [HasPushouts C] [HasInitial C] [InitialMonoClass C]
  (P : Precylinder (𝟭 C)) [P.IsExact.{w}]
  (An : MorphismProperty C) [P.IsAnodyneSystem.{w} An]

/-- Both actual endpoints belong to the specified anodyne class, using the
initial-object corner and its genuine source isomorphism. -/
theorem endpoint_mem_anodyne (X : C) (ε : Fin 2) : An ((P.app X).endpoint ε) := by
  let : PreservesColimitsOfSize.{0, 0} P.I :=
    preservesSmallestColimits_of_preservesColimits P.I
  have hI₀ : IsInitial (P.I.obj (⊥_ C)) :=
    IsInitial.isInitialObj (G := P.I) (X := (⊥_ C)) initialIsInitial
  let i : (⊥_ C) ⟶ X := initial.to X
  let a : (⊥_ C) ⟶ P.I.obj (⊥_ C) := (P.app (⊥_ C)).endpoint ε
  have : Mono i := by dsimp only [i]; infer_instance
  have : IsIso a := isIso_of_isInitial initialIsInitial hI₀ a
  let u : X ⟶ pushout i a := pushout.inl i a
  have : IsIso u := by dsimp only [u]; infer_instance
  have hκ : An (P.endpointCorner i ε) := endpoint_corner (P := P) (An := An) i ε
  have hκ' : An.rlp.llp (P.endpointCorner i ε) := by
    simpa only [llp_rlp_eq P An] using hκ
  have hu : An.rlp.llp u := MorphismProperty.llp_of_isIso An.rlp u
  have h := (An.rlp.llp).comp_mem u (P.endpointCorner i ε) hu hκ'
  simpa only [u, a, inl_endpointCorner, llp_rlp_eq P An] using h

end HomotopicalAlgebra.Precylinder.IsAnodyneSystem
