/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.NatIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import MathlibExt.CategoryTheory.NerveHomotopy

/-!
# Unpointed nerve of the Quillen Q-construction

For an exact category `C`, `NQ C` is `CategoryTheory.nerve (QuillenQ C)`,
an unpointed simplicial set (not a K-theory space). Exact functors act by
`CategoryTheory.nerveMap (QuillenQ.map F)`, with identity and composition
laws transported from the `nerveMap` and `QuillenQ.map` lemmas.

Source and target share one object universe and one morphism universe,
because `CategoryTheory.nerveMap` in the pinned Mathlib is same-universe.
A zero vertex is given by `ComposableArrows.mk₀` at `⟨0⟩`; strict
preservation by arbitrary exact functors is not claimed. A natural
isomorphism of exact functors induces a simplicial homotopy via
`CategoryTheory.NatTrans.nerveHomotopy`.

The simplicial maps are induced by the original exact-functor maps on Quillen
spans, and natural isomorphisms retain their original component maps.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type u} [Category.{v} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable {E : Type u} [Category.{v} E] [Preadditive E]
  [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]

/-- Unpointed nerve of `QuillenQ C`. Same-universe in source and target. -/
noncomputable abbrev NQ (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :=
  CategoryTheory.nerve (QuillenQ C)

/-- Exact-functor action on nerves, via `nerveMap (QuillenQ.map F)`. -/
noncomputable def NQ.map (F : C ⥤ D) [F.Additive] [F.IsExact] :
    NQ C ⟶ NQ D :=
  CategoryTheory.nerveMap (QuillenQ.map F)

@[simp]
theorem NQ.map_id : NQ.map (𝟭 C) = 𝟙 (NQ C) := by
  unfold NQ.map
  rw [QuillenQ.map_id]
  exact CategoryTheory.nerveMap_id

@[simp]
theorem NQ.map_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] :
    NQ.map F ≫ NQ.map G = NQ.map (F ⋙ G) := by
  unfold NQ.map
  rw [CategoryTheory.nerveMap_comp, QuillenQ.map_comp]

/-- Zero vertex of the Q-nerve, from the zero object of `C`. -/
noncomputable def NQ.zeroVertex (C : Type u) [Category.{v} C]
    [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    [ExactCategory C] :
    (NQ C).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀ (⟨0⟩ : QuillenQ C)

@[simp]
theorem NQ.map_app_mk₀ (F : C ⥤ D) [F.Additive] [F.IsExact]
    (X : QuillenQ C) :
    (NQ.map F).app (op ⦋0⦌) (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀ ((QuillenQ.map F).obj X) :=
  CategoryTheory.nerveMap_app_mk₀ _ _

@[simp]
theorem NQ.map_app_mk₁ (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : QuillenQ C} (f : X ⟶ Y) :
    (NQ.map F).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ ((QuillenQ.map F).map f) :=
  CategoryTheory.nerveMap_app_mk₁ _ _

@[simp]
theorem NQ.map_app_mk₁_mkHom (F : C ⥤ D) [F.Additive] [F.IsExact]
    {X Y : QuillenQ C} (S : QuillenSpan X.obj Y.obj) :
    (NQ.map F).app (op ⦋1⦌)
        (ComposableArrows.mk₁ (QuillenQ.mkHom S)) =
      ComposableArrows.mk₁
        (QuillenQ.mkHom (QuillenSpan.map F S)) := by
  rw [NQ.map_app_mk₁, QuillenQ.map_mk]
  rfl

/-- A natural isomorphism of exact functors induces a simplicial homotopy
between the maps on Q-nerves. -/
noncomputable def NQ.mapNatIsoHomotopy (F G : C ⥤ D)
    [F.Additive] [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    SSet.Homotopy (NQ.map F) (NQ.map G) :=
  CategoryTheory.NatTrans.nerveHomotopy (QuillenQ.mapNatIso F G e).hom

end AlgebraicKTheory
