/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornHomFaces

/-!
# Original identity and composition of the actual coherent horn face maps

The actual enriched face functors preserve whole original identities and
union composition. Both endpoint transports use the same individual
horn vertices. A coherent face restriction precomposes its original whole
Hom map; this permits common-face equalities to be used without replacing
any original source or target.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornMapAlgebra
open SimplicialEnrichment HornHomFaces

/-- The retargeted original enriched Hom map preserves the actual entire enriched identity. -/
theorem retargetMap_id {C D : Carrier.{u}} (F : C ⟶ D) (a : C) {x : D} (ha : F.obj a = x) :
    eId SSet.{u} a ≫ retargetMap F a a ha ha = eId SSet.{u} x := by
  subst x
  change eId SSet.{u} a ≫ (F.map a a ≫ 𝟙 _) = eId SSet.{u} (F.obj a)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g => g ≫ 𝟙 _) (F.map_id a)).trans (Category.comp_id _))

/-- The retargeted original enriched Hom maps preserve the actual entire composition map
with all three
  original vertices. -/
theorem retargetMap_comp {C D : Carrier.{u}} (F : C ⟶ D) (a b c : C) {x y z : D}
    (ha : F.obj a = x) (hb : F.obj b = y) (hc : F.obj c = z) :
    eComp SSet.{u} a b c ≫ retargetMap F a c ha hc =
      (retargetMap F a b ha hb ⊗ₘ retargetMap F b c hb hc) ≫ eComp SSet.{u} x y z := by
  subst x
  subst y
  subst z
  change eComp SSet.{u} a b c ≫ (F.map a c ≫ 𝟙 _) =
    ((F.map a b ≫ 𝟙 _) ⊗ₘ (F.map b c ≫ 𝟙 _)) ≫
      eComp SSet.{u} (F.obj a) (F.obj b) (F.obj c)
  simpa only [Category.comp_id] using F.map_comp a b c

/-- Actual restriction of a retargeted coherent face precomposes precisely its original
whole Hom map. -/
theorem retargetMap_precomp {A B C : Carrier.{u}} (F : A ⟶ B) (G : B ⟶ C) (a b : A)
    {x y : C} (ha : G.obj (F.obj a) = x) (hb : G.obj (F.obj b) = y) :
    F.map a b ≫ retargetMap G (F.obj a) (F.obj b) ha hb = retargetMap (F ≫ G) a b ha hb :=
  (Category.assoc _ _ _).symm

variable {C : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)

/-- The supplied original horn face preserves its actual identity at the same individual
horn vertex. -/
theorem faceMap_id (j : Fin (n + 3)) (hj : j ≠ i) (a : coherentSimplex.{u} ⦋n + 1⦌) :
    eId SSet.{u} a ≫ HornHomFaces.faceMap f j hj a a =
      eId SSet.{u} (HornFaces.object f (j.succAbove a.as.down)) :=
  retargetMap_id (HornFaces.faceFunctor f j hj) a (HornFaces.faceFunctor_obj f j hj a)

/-- The supplied original horn face preserves its whole actual composition with the same
three original horn
  vertices. -/
theorem faceMap_comp (j : Fin (n + 3)) (hj : j ≠ i) (a b c : coherentSimplex.{u} ⦋n + 1⦌) :
    eComp SSet.{u} a b c ≫ HornHomFaces.faceMap f j hj a c =
      (HornHomFaces.faceMap f j hj a b ⊗ₘ HornHomFaces.faceMap f j hj b c) ≫
        eComp SSet.{u} (HornFaces.object f (j.succAbove a.as.down))
          (HornFaces.object f (j.succAbove b.as.down)) (HornFaces.object f (j.succAbove
            c.as.down)) :=
  retargetMap_comp (HornFaces.faceFunctor f j hj) a b c
    (HornFaces.faceFunctor_obj f j hj a) (HornFaces.faceFunctor_obj f j hj b)
    (HornFaces.faceFunctor_obj f j hj c)

end CategoryTheory.CoherentRealization.HornMapAlgebra
