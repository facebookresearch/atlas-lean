/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningCriticalParameterWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.InnerCellParameterLifting

/-!
# Original inner-horn parameter cells have actual native weak images

The actual native Un map of a coherent-model fibration is an inner
fibration. The original inner-anodyne parameter corner and its complete
mark coverage therefore give a marked lift for arbitrary source and
target diagrams, over every original base. The same native adjunction
proves the actual target projective weak left class, model trivial
cofibration and every original marked coefficient trivial cofibration.
Both original model structures and both whole parameter-side maps are
retained. No diagram fibrancy, Kan parameter, weak image or native
filler is an input to the proof.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- The same original minimally marked horn over its entire prescribed base simplex is a mono on the original marked
slice carrier. -/
theorem innerCellOver_nativeMono (B : SSet.{u}) (n : ℕ) (i : Fin (n + 3))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) : Mono (innerCellOver n i r) := by
  have : Mono (innerCellOver n i r).left := innerCell_mono n i
  exact Over.mono_of_mono_left _

/-- Every original inner-horn/maximal-scalar-mono corner lifts the same native Un map of an actual coherent-model
fibration, without fibrancy of either diagram or base. -/
theorem nativeUnstraightening_map_innerMonoParameterLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ (n : ℕ) (i : Fin (n + 3)) (_hi : 0 < i) (_hi' : i < Fin.last (n + 2))
      (r : (Δ[n + 2] : SSet.{u}) ⟶ B), ∀ {A D : SSet.{u}} (a : A ⟶ D), Mono a →
        HasLiftingProperty (overParameterPushoutProduct a (innerCellOver n i r))
          ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq n i hi hi' r A D a ha
  let _ : Mono a := ha
  let _ : InnerFibration ((nativeUnstraightening B).map q).left.hom :=
    nativeUnstraightening_map_innerFibration B q hq
  exact innerCellOver_parameter_lifting a n i hi hi' r ((nativeUnstraightening B).map q)

/-- Every same original inner-horn/maximal-parameter corner has its genuine native projective weak left image over
an arbitrary original base. -/
theorem nativeStraightening_innerParameterCell_projectiveWeakLeft (B : SSet.{u}) (n : ℕ)
    (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (overParameterPushoutProduct a (innerCellOver n i r))) := by
  let _ := coherentDiagramModelCategory B
  intro F G q hq
  have hq' : Fibration q := (fibration_iff q).mpr hq
  exact ((nativeStraighteningAdjunction B).hasLiftingProperty_iff
    (overParameterPushoutProduct a (innerCellOver n i r)) q).mpr
      (nativeUnstraightening_map_innerMonoParameterLifting B q hq' n i hi hi' r a inferInstance)

/-- The same physical original inner-horn parameter image is a trivial cofibration in the actual coherent target
model, for every original base and scalar mono. -/
theorem nativeStraightening_innerParameterCell_trivialCofibration (B : SSet.{u}) (n : ℕ)
    (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      ((nativeStraightening B).map (overParameterPushoutProduct a (innerCellOver n i r))) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeStraightening_innerParameterCell_projectiveWeakLeft B n i hi hi' r a

/-- Every same original marked evaluation coefficient of the native inner-horn parameter map is an actual
coefficient-model trivial cofibration. -/
theorem nativeStraightening_innerParameterCell_evaluation_trivialCofibration (B : SSet.{u}) (n : ℕ)
    (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a]
    (x : (realization B)ᵒᵖ) :
    trivialCofibrations Marked.{u}
      (((nativeStraightening B).map (overParameterPushoutProduct a (innerCellOver n i r))).app x) := by
  let _ := coherentDiagramModelCategory B
  let _ : Mono (innerCellOver n i r) := innerCellOver_nativeMono B n i r
  have hc := nativeStraightening_parameterCell_evaluation_cofibration B a (innerCellOver n i r) x
  have hw : coherentDiagramWeakEquivalences B
      ((nativeStraightening B).map (overParameterPushoutProduct a (innerCellOver n i r))) :=
    coherentDiagramGeneratingWeakMonos_left_weak B _
      (nativeStraightening_innerParameterCell_projectiveWeakLeft B n i hi hi' r a)
  exact ⟨hc, (EvaluationTransfer.evaluationProperty_iff _ _ _).mp hw x⟩

/-- Both actual original models retain the same whole inner-horn parameter cell and its same native weak image over
every quasicategory base. -/
theorem nativeStraightening_innerParameterCell_bothModels (B : SSet.{u}) [Quasicategory B] (n : ℕ)
    (i : Fin (n + 3)) (hi : 0 < i) (hi' : i < Fin.last (n + 2))
    (r : (Δ[n + 2] : SSet.{u}) ⟶ B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (Over (max B)) (overParameterPushoutProduct a (innerCellOver n i r)) ∧
      trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
        ((nativeStraightening B).map (overParameterPushoutProduct a (innerCellOver n i r))) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  have hs : cartesianTestingTrivialCofibrations B (innerCellOver n i r) :=
    ⟨innerCellOver_nativeMono B n i r, innerCellOver_cartesian_weak n i hi hi' r⟩
  exact ⟨cartesianWeakMono_parameter_closed (innerCellOver n i r) hs a,
    nativeStraightening_innerParameterCell_trivialCofibration B n i hi hi' r a⟩

end SSet.Marked
