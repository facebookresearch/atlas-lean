/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeBoundaryCellScalarReadbacks
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarFreeFilteredColimit
import MathlibExt.AlgebraicTopology.SimplicialCategory.InitialScalarFreePresentation
import Mathlib.CategoryTheory.Functor.OfSequence
import MathlibExt.CategoryTheory.Category.QuiverHomDictionary
import MathlibExt.CategoryTheory.Functor.SequenceMapProperty

/-!
# Compatible actual scalar generators along original sequential boundary cells

The whole original boundary-cell diagram is retained. Its scalar free
presentation is constructed recursively using the actual successor
attachments. The generator diagram consists of the SAME old-generator
inclusions, with full original path-evaluation naturality at every stage.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.SequentialBoundaryScalarPresentation
open RelativeWords

variable {O : Type u} (F : ℕ ⥤ FixedObjects O)
  (a : ∀ n : ℕ, AttachCells.{u} (boundaryFamily O).homFamily (F.map (homOfLE (n.le_add_right 1))))
  (q : SimplexCategoryᵒᵖ)
  (P0 : FreePresentation.{u,u,u} (scalarCategory (F.obj 0) q))

/-- Every original full scalar stage is presented by its actual original boundary generators. -/
def stage : (n : ℕ) → FreePresentation.{u,u,u} (scalarCategory (F.obj n) q)
  | 0 => P0
  | n + 1 => FreeBoundaryCells.scalarPresentation (a n) q (stage n)

/-- The actual old-generator inclusion at one original successor stage. -/
def generatorMap (n : ℕ) {x y : O} : (stage F a q P0 n).quiver.Hom x y →
    (stage F a q P0 (n + 1)).quiver.Hom x y :=
  FreeBoundaryCells.generatorInclusion (a n) q (stage F a q P0 n)

/-- The entire original generator diagram keeps all original stages and their literal old inclusions. -/
def generators (x y : O) : ℕ ⥤ Type u :=
  Functor.ofSequence (fun n => ↾(@generatorMap O F a q P0 n x y))

/-- Every complete original path in a successor retains the SAME original diagram Hom map. -/
theorem stage_natural_succ (n : ℕ) {x y : O}
    (p : @Quiver.Path O (stage F a q P0 n).quiver x y) :
    (stage F a q P0 (n + 1)).map
      (FixedLabelPathMaps.mapPath (stage F a q P0 n).quiver
        (stage F a q P0 (n + 1)).quiver (generatorMap F a q P0 n) p) =
      (homMap (F.map (homOfLE (n.le_add_right 1))) x y).app q
        ((stage F a q P0 n).map p) :=
  FreeBoundaryCells.scalarPresentation_oldPath (a n) q (stage F a q P0 n) p


/-- The complete original Hom-family quiver dictionary of one actual scalar stage. -/
theorem stageQuiver_eq (n : ℕ) :
    FixedLabelPathMaps.FilteredColimit.stageQuiver (generators F a q P0) n =
      Quiver.mk (stage F a q P0 n).quiver.Hom := rfl

/-- Read the SAME complete original stage path through its native Hom-family dictionary. -/
def stageEvaluation (n : ℕ) {x y : O}
    (p : @Quiver.Path O
      (FixedLabelPathMaps.FilteredColimit.stageQuiver (generators F a q P0) n) x y) :
    (hom (F.obj n) x y).obj q :=
  (stage F a q P0 n).map (FixedLabelPathMaps.fromHomDictionary (stage F a q P0 n).quiver p)

/-- The actual generator diagram maps are genuinely injective at every original arrow. -/
theorem generators_map_injective {n m : ℕ} (f : n ⟶ m) (x y : O) :
    Function.Injective ((generators F a q P0 x y).map f) := by
  have hstep (n : ℕ) : Mono (↾(@generatorMap O F a q P0 n x y)) :=
    (mono_iff_injective _).mpr (FreeBoundaryCells.generatorInclusion_injective
      (a n) q (stage F a q P0 n) x y)
  have h := Functor.ofSequence_map_property
    (fun n => ↾(@generatorMap O F a q P0 n x y)) (MorphismProperty.monomorphisms (Type u)) hstep f
  exact (mono_iff_injective _).mp h


/-- Each actual successor keeps the whole original path evaluation. -/
theorem stageEvaluation_succ (n : ℕ) {x y : O}
    (p : @Quiver.Path O
      (FixedLabelPathMaps.FilteredColimit.stageQuiver (generators F a q P0) n) x y) :
    stageEvaluation F a q P0 (n+1)
        (FixedLabelPathMaps.FilteredColimit.stageMap (generators F a q P0)
          (homOfLE (n.le_add_right 1)) p) =
      (homMap (F.map (homOfLE (n.le_add_right 1))) x y).app q
        (stageEvaluation F a q P0 n p) := by
  change (stage F a q P0 (n+1)).map
    (FixedLabelPathMaps.fromHomDictionary (stage F a q P0 (n+1)).quiver
      (FixedLabelPathMaps.mapPath (Quiver.mk (stage F a q P0 n).quiver.Hom)
        (Quiver.mk (stage F a q P0 (n+1)).quiver.Hom)
        (fun {x y} e => (generators F a q P0 x y).map (homOfLE (n.le_add_right 1)) e) p)) = _
  have hm : (fun {x y} (e : (stage F a q P0 n).quiver.Hom x y) =>
      (generators F a q P0 x y).map (homOfLE (n.le_add_right 1)) e) =
        @generatorMap O F a q P0 n := by
    funext x y e
    exact congr($(Functor.ofSequence_map_homOfLE_succ
      (fun n => ↾(@generatorMap O F a q P0 n x y)) n) e)
  have hh := FixedLabelPathMaps.fromHomDictionary_map (stage F a q P0 n).quiver
    (stage F a q P0 (n+1)).quiver (generatorMap F a q P0 n) p
  have hmap := congrArg (fun m => FixedLabelPathMaps.mapPath
    (Quiver.mk (stage F a q P0 n).quiver.Hom)
    (Quiver.mk (stage F a q P0 (n+1)).quiver.Hom) m p) hm
  exact (congrArg (fun p => (stage F a q P0 (n+1)).map
    (FixedLabelPathMaps.fromHomDictionary (stage F a q P0 (n+1)).quiver p)) hmap).trans
    ((congrArg (stage F a q P0 (n+1)).map hh).trans (stage_natural_succ F a q P0 n _))

/-- The full actual original path evaluations give a natural transformation on every original stage arrow. -/
def stageNatural (x y : O) :
    FixedLabelPathMaps.FilteredColimit.pathDiagram (generators F a q P0) x y ⟶
      ScalarFreeColimit.homDiagram F q x y :=
  NatTrans.ofSequence (fun n => ↾(@stageEvaluation O F a q P0 n x y))
    (fun n => by
      ext p
      exact stageEvaluation_succ F a q P0 n p)

/-- Every whole original stage map keeps the complete original path-evaluation naturality. -/
theorem stageEvaluation_natural {i j : ℕ} (f : i ⟶ j) {x y : O}
    (p : @Quiver.Path O
      (FixedLabelPathMaps.FilteredColimit.stageQuiver (generators F a q P0) i) x y) :
    stageEvaluation F a q P0 j
        (FixedLabelPathMaps.FilteredColimit.stageMap (generators F a q P0) f p) =
      (homMap (F.map f) x y).app q (stageEvaluation F a q P0 i p) :=
  congr($((stageNatural F a q P0 x y).naturality f) p)


/-- The original complete path stage evaluations are the actual compatible scalar free presentations. -/
def stagePresentation : ScalarFreeColimit.StagePresentation F q (generators F a q P0) where
  map := stageEvaluation F a q P0
  map_id n x :=
    (congrArg (stage F a q P0 n).map
      (FixedLabelPathMaps.fromHomDictionary_nil (stage F a q P0 n).quiver x)).trans
        ((stage F a q P0 n).map_id x)
  map_comp n {x y z} p r :=
    (congrArg (stage F a q P0 n).map
      (FixedLabelPathMaps.fromHomDictionary_comp (stage F a q P0 n).quiver p r)).trans
        ((stage F a q P0 n).map_comp _ _)
  bijective n x y := by
    have h : Function.Bijective (FixedLabelPathMaps.fromHomDictionary
      (stage F a q P0 n).quiver (a := x) (b := y)) :=
      ⟨Function.LeftInverse.injective (FixedLabelPathMaps.to_fromHomDictionary _),
        Function.RightInverse.surjective (FixedLabelPathMaps.from_toHomDictionary _)⟩
    exact ((stage F a q P0 n).bijective x y).comp h
  naturality {i j} f {x y} p := stageEvaluation_natural F a q P0 f p

/-- Construct the full free scalar presentation of the SAME actual original terminal enriched colimit. -/
def terminalPresentation (s : Cocone F) (hs : IsColimit s) :
    FreePresentation.{u,u,u} (scalarCategory s.pt q) :=
  ScalarFreeColimit.presentation F s hs q (generators F a q P0)
    (fun x y => colimit.cocone (generators F a q P0 x y))
    (fun x y => colimit.isColimit (generators F a q P0 x y))
    (generators_map_injective F a q P0) (stagePresentation F a q P0)

end CategoryTheory.SimplicialEnrichment.FixedObjects.SequentialBoundaryScalarPresentation
