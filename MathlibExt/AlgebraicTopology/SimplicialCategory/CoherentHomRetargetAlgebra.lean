/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornMapAlgebra

/-!
# Exact source and target retargeting of original enriched Hom maps

The actual enriched map commutes with source equality transports and
successive target endpoint transports. These equations retain the same
original objects and whole scalar Hom maps. No object quotient or
coherence outcome is introduced.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomRetargetAlgebra
open SimplicialEnrichment HornHomFaces

/-- Source retargeting of an actual whole enriched Hom map keeps its exact original target
endpoints. -/
theorem source_reindex {A B : Carrier.{u}} (F : A ⟶ B) {a b a' b' : A}
    (ha : a = a') (hb : b = b') {x y : B} (hx : F.obj a' = x) (hy : F.obj b' = y) :
    eqToHom (congrArg₂ (fun a b : A => a ⟶[SSet.{u}] b) ha hb) ≫ retargetMap F a' b' hx hy =
      retargetMap F a b ((congrArg F.obj ha).trans hx) ((congrArg F.obj hb).trans hy) := by
  subst a'
  subst b'
  change 𝟙 _ ≫ retargetMap F a b hx hy = retargetMap F a b hx hy
  exact Category.id_comp _

/-- Successive original target equality transports are the same whole retargeted enriched
Hom map. -/
theorem target_trans {A B : Carrier.{u}} (F : A ⟶ B) (a b : A) {x y x' y' : B}
    (ha : F.obj a = x) (hb : F.obj b = y) (hx : x = x') (hy : y = y') :
    retargetMap F a b ha hb ≫ eqToHom (congrArg₂ (fun x y : B => x ⟶[SSet.{u}] y) hx hy) =
      retargetMap F a b (ha.trans hx) (hb.trans hy) := by
  rw [retargetMap, retargetMap, Category.assoc, eqToHom_trans]

/-- The actual source restriction and its two original source endpoint equations read back the whole
  composite enriched functor map. -/
theorem restriction_reindex {A B C : Carrier.{u}} (F : A ⟶ B) (G : B ⟶ C) (a b : A)
    {a' b' : B} (ha : F.obj a = a') (hb : F.obj b = b') {x y : C}
    (hx : G.obj a' = x) (hy : G.obj b' = y) :
    F.map a b ≫ eqToHom (congrArg₂ (fun a b : B => a ⟶[SSet.{u}] b) ha hb) ≫
      retargetMap G a' b' hx hy =
    retargetMap (F ≫ G) a b ((congrArg G.obj ha).trans hx) ((congrArg G.obj hb).trans hy) :=
  (congrArg (fun h => F.map a b ≫ h) (source_reindex G ha hb hx hy)).trans
    (HornMapAlgebra.retargetMap_precomp F G a b _ _)

end CategoryTheory.CoherentRealization.HomRetargetAlgebra
