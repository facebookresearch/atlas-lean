/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningMonoCells
import Mathlib.CategoryTheory.LiftingProperties.Adjunction
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Actual native straightening preserves every original marked cofibration

All original marked mono generators have their proved actual native
projective images. The original fixed-base mono right and left classes
and actual native adjunction therefore prove preservation of every
whole original marked mono. This gives actual coherent-model
cofibrations, projective mono-right preservation by native Un and
cofibrancy of the original whole straightening objects. Weak-class
preservation and the full Quillen statement remain separate.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Every original whole marked mono over the actual fixed base straightens into the genuine projective left class
by its original small mono generators and actual native adjunction. -/
theorem nativeStraightening_mono_projectiveLeft (B : SSet.{u}) {X Y : Over (max B)} (i : X ⟶ Y) [Mono i] :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp.llp ((nativeStraightening B).map i) := by
  let I := overCells monoCell.{u} (max B)
  have hi : I.rlp.llp i := by
    rw [fixedBaseMonoCells_left_eq B]
    exact (inferInstance : Mono i)
  intro F G p hp
  have hU : I.rlp ((nativeUnstraightening B).map p) := by
    intro A D j hj
    exact (Adjunction.hasLiftingProperty_iff (nativeStraighteningAdjunction B) j p).mp
      ((nativeStraightening_monoCells_projectiveLeft B j hj) p hp)
  exact (Adjunction.hasLiftingProperty_iff (nativeStraighteningAdjunction B) i p).mpr
    (hi ((nativeUnstraightening B).map p) hU)

/-- Actual native straightening retains monicity of the same original whole marked source map as its full enriched
target map. -/
instance nativeStraightening_map_mono (B : SSet.{u}) {X Y : Over (max B)} (i : X ⟶ Y) [Mono i] :
    Mono ((nativeStraightening B).map i) :=
  coherentDiagram_projectiveLeft_mono B ((nativeStraightening B).map i) (nativeStraightening_mono_projectiveLeft B i)

/-- The same actual native straightening map preserves every cofibration of the original marked-mono source
structure as a cofibration in the genuinely constructed original coherent diagram model. -/
theorem nativeStraightening_preservesCofibrations (B : SSet.{u}) {X Y : Over (max B)} (i : X ⟶ Y) :
    let _ := markedCofibrationStructure (max B)
    let _ := coherentDiagramModelCategory B
    Cofibration i → Cofibration ((nativeStraightening B).map i) := by
  let _ := markedCofibrationStructure (max B)
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hi
  rw [cofibration_iff] at hi
  change Mono i at hi
  have : Mono i := hi
  rw [cofibration_iff, coherentDiagramModel_cofibrations B]
  exact nativeStraightening_mono_projectiveLeft B i

/-- The actual native unstraightening image of every genuine projective mono-right map has the right lifting
property against all original marked monos over the unchanged base. -/
theorem nativeUnstraightening_projectiveMonoRight (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (p : F ⟶ G)
    (hp : (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos).rlp p) :
    (monomorphisms (Over (max B))).rlp ((nativeUnstraightening B).map p) := by
  intro X Y i hi
  have : Mono i := hi
  exact (Adjunction.hasLiftingProperty_iff (nativeStraighteningAdjunction B) i p).mp
    ((nativeStraightening_mono_projectiveLeft B i) p hp)

/-- The original actual coherent-model trivial fibration is sent by the same native Un functor to a genuine
mono-right map on the original whole marked total spaces. -/
theorem nativeUnstraightening_trivialFibration_monoRight (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (p : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    trivialFibrations (EnrichedDiagram (realization B)ᵒᵖ) p →
      (monomorphisms (Over (max B))).rlp ((nativeUnstraightening B).map p) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hp
  let I := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos
  have hI : I.rlp p := by
    rw [← cofibrations_rlp (EnrichedDiagram (realization B)ᵒᵖ)] at hp
    intro A D j hj
    apply hp j
    rw [coherentDiagramModel_cofibrations B]
    exact I.le_llp_rlp j hj
  exact nativeUnstraightening_projectiveMonoRight B p hI

/-- The unchanged actual straightening object of every original marked total space is cofibrant in the genuinely
constructed original coherent diagram model. -/
theorem nativeStraightening_object_isCofibrant (B : SSet.{u}) (X : Over (max B)) :
    let _ := coherentDiagramModelCategory B
    IsCofibrant ((nativeStraightening B).obj X) := by
  let _ := coherentDiagramModelCategory B
  let _ : InitialMonoClass (Over (max B)) := over_initialMonoClass (max B)
  let T := nativeStraightening B
  let _ : PreservesColimitsOfSize.{0, 0} T := (nativeStraighteningAdjunction B).leftAdjoint_preservesColimits
  let i : (⊥_ (Over (max B))) ⟶ X := initial.to X
  have : Mono i := inferInstance
  let hI := initialIsInitial.isInitialObj T (⊥_ (Over (max B)))
  let e := initialIsInitial.uniqueUpToIso hI
  let G := enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingMonos
  have h := G.rlp.llp.comp_mem e.hom (T.map i)
    (G.rlp.llp_of_isIso e.hom) (nativeStraightening_mono_projectiveLeft B i)
  have he : e.hom ≫ T.map i = initial.to (T.obj X) := initialIsInitial.hom_ext _ _
  rw [isCofibrant_iff, cofibration_iff, coherentDiagramModel_cofibrations B]
  change G.rlp.llp (initial.to (T.obj X))
  exact he ▸ h

end SSet.Marked
