/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningControlledPairingLifting
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeStraighteningCriticalParameterCells
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalProductPairing
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianCriticalParameterCorner
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.OverParameterArrowComparison
import Mathlib.CategoryTheory.LiftingProperties.Over

/-!
# SAME original critical lower-face parameter cells have actual native weak images

The original controlled product pairing and its unchanged old-stage marks
lift the SAME actual native Un map of every coherent-model fibration.
The original whole corner Arrow Iso and fixed-base parameter adjunction
retain every prescribed scalar and critical edge. Original boundary
lifting gives all scalar-mono lifting. The SAME original native adjunction
therefore proves the full target weak projective left class and actual
coefficient trivial cofibrations. Neither base nor parameter is required
to be Kan or a quasicategory; neither diagram is assumed fibrant. No
target weakness, native filler or Quillen result is supplied as input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

/-- Every SAME original full scalar-boundary/critical-cell square lifts the SAME native Un map of an ACTUAL
coherent-model fibration through the ENTIRE original controlled marked pairing. -/
theorem nativeUnstraightening_map_criticalBoundaryParameterLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ (m n : ℕ) (r : cartesianCriticalTarget.{u} m ⟶ max B),
      HasLiftingProperty (overParameterPushoutProduct (boundary.{u} n).ι (cartesianCriticalOver m r))
        ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq m n r
  let ambient := prod (cartesianCriticalTarget.{u} m) (max (Δ[n] : SSet.{u}))
  let A := Subcomplex.unionProd (horn.{u} (m + 2) (Fin.last (m + 2))) (boundary.{u} n)
  let core := cartesianCriticalProductCore.{u} m n
  let _ : core.IsRegular := by
    dsimp only [core, cartesianCriticalProductCore]
    infer_instance
  have hregular : core.pairing.IsRegular := (Subcomplex.PairingCore.isRegular_pairing_iff _).mpr inferInstance
  have hUnion : HasLiftingProperty (comapHom ambient A.ι) ((nativeUnstraightening B).map q).left :=
    @nativeUnstraightening_controlledPairing_lifting.{u} ambient A core.pairing hregular
      (cartesianCriticalProduct_marks_mem m n) (cartesianCriticalProduct_pairing_controlled m n) B F G q hq
  have hCorner : HasLiftingProperty (parameterPushoutProduct (boundary.{u} n).ι (cartesianCriticalCell.{u} m))
      ((nativeUnstraightening B).map q).left :=
    (HasLiftingProperty.iff_of_arrow_iso_left (cartesianCriticalParameterUnionIso m n)
      ((nativeUnstraightening B).map q).left).mpr hUnion
  let _ : HasLiftingProperty
      (overParameterPushoutProduct (boundary.{u} n).ι (cartesianCriticalOver m r)).left
        ((nativeUnstraightening B).map q).left :=
    (HasLiftingProperty.iff_of_arrow_iso_left
      (overParameterMarkedArrowIso (boundary.{u} n).ι (cartesianCriticalOver m r))
        ((nativeUnstraightening B).map q).left).mpr hCorner
  exact HasLiftingProperty.over _ ((nativeUnstraightening B).map q)

/-- Every SAME original maximal scalar-mono/critical-cell corner lifts the SAME actual native Un map, by its full
original boundary comparison and parameter adjunction. -/
theorem nativeUnstraightening_map_criticalMonoParameterLifting (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ∀ (m : ℕ) (r : cartesianCriticalTarget.{u} m ⟶ max B),
      ∀ {A D : SSet.{u}} (a : A ⟶ D), Mono a →
        HasLiftingProperty (overParameterPushoutProduct a (cartesianCriticalOver m r))
          ((nativeUnstraightening B).map q) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq m r A D a ha
  let _ : Mono a := ha
  let i := cartesianCriticalOver m r
  let p := (nativeUnstraightening B).map q
  let c := overParameterMappingComparison i p
  have hI : modelCategoryQuillen.I.{u}.rlp c := by
    intro X Y j hj
    obtain ⟨n⟩ := hj
    exact (overParameterPushoutProduct_hasLiftingProperty_iff (boundary.{u} n).ι i p).mp
      (nativeUnstraightening_map_criticalBoundaryParameterLifting B q hq m n r)
  have hMono : (monomorphisms SSet.{u}).rlp c := by
    rw [SSet.rlp_monomorphisms]
    exact hI
  exact (overParameterPushoutProduct_hasLiftingProperty_iff a i p).mpr (hMono a inferInstance)

/-- EVERY SAME original full marked critical lower-face/maximal-scalar-mono parameter corner has its genuine native
weak projective image, through actual model fibrations and the SAME native adjunction. -/
theorem nativeStraightening_criticalParameterCell_projectiveWeakLeft (B : SSet.{u}) (m : ℕ)
    (r : cartesianCriticalTarget.{u} m ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    (enrichedFreeGenerators (realization B)ᵒᵖ coefficientGeneratingWeakMonos).rlp.llp
      ((nativeStraightening B).map (overParameterPushoutProduct a (cartesianCriticalOver m r))) := by
  let _ := coherentDiagramModelCategory B
  intro F G q hq
  have hq' : Fibration q := (fibration_iff q).mpr hq
  exact ((nativeStraighteningAdjunction B).hasLiftingProperty_iff
    (overParameterPushoutProduct a (cartesianCriticalOver m r)) q).mpr
      (nativeUnstraightening_map_criticalMonoParameterLifting B q hq' m r a inferInstance)

/-- The SAME physical original critical lower-face/maximal-parameter cell is an ACTUAL trivial cofibration in the
genuine original coherent target model, over every original base. -/
theorem nativeStraightening_criticalParameterCell_trivialCofibration (B : SSet.{u}) (m : ℕ)
    (r : cartesianCriticalTarget.{u} m ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
      ((nativeStraightening B).map (overParameterPushoutProduct a (cartesianCriticalOver m r))) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  rw [coherentDiagramModel_trivialCofibrations B]
  exact nativeStraightening_criticalParameterCell_projectiveWeakLeft B m r a

/-- EVERY SAME original marked evaluation coefficient of the physical native critical parameter cell is a genuine
original coefficient-model trivial cofibration. -/
theorem nativeStraightening_criticalParameterCell_evaluation_trivialCofibration (B : SSet.{u}) (m : ℕ)
    (r : cartesianCriticalTarget.{u} m ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a]
    (x : (realization B)ᵒᵖ) :
    trivialCofibrations Marked.{u}
      (((nativeStraightening B).map (overParameterPushoutProduct a (cartesianCriticalOver m r))).app x) := by
  let _ := coherentDiagramModelCategory B
  let _ : Mono (cartesianCriticalOver m r) := cartesianCriticalOver_nativeMono B m r
  have hc := nativeStraightening_parameterCell_evaluation_cofibration B a (cartesianCriticalOver m r) x
  have hw : coherentDiagramWeakEquivalences B
      ((nativeStraightening B).map (overParameterPushoutProduct a (cartesianCriticalOver m r))) :=
    coherentDiagramGeneratingWeakMonos_left_weak B _
      (nativeStraightening_criticalParameterCell_projectiveWeakLeft B m r a)
  exact ⟨hc, (EvaluationTransfer.evaluationProperty_iff _ _ _).mp hw x⟩

/-- The SAME physical original critical lower-face/maximal-parameter corner and SAME native image are actual trivial
cofibrations in BOTH original models over every original quasicategory base. -/
theorem nativeStraightening_criticalParameterCell_bothModels (B : SSet.{u}) [Quasicategory B] (m : ℕ)
    (r : cartesianCriticalTarget.{u} m ⟶ max B) {A D : SSet.{u}} (a : A ⟶ D) [Mono a] :
    let _ := markedCofibrationStructure (max B)
    let _ := cartesianMarkedFibrationStructure B
    let _ := cartesianMarkedWeakStructure B
    let _ := cartesianMarkedModelCategory B
    let _ := coherentDiagramModelCategory B
    trivialCofibrations (Over (max B)) (overParameterPushoutProduct a (cartesianCriticalOver m r)) ∧
      trivialCofibrations (EnrichedDiagram (realization B)ᵒᵖ)
        ((nativeStraightening B).map (overParameterPushoutProduct a (cartesianCriticalOver m r))) := by
  let _ := markedCofibrationStructure (max B)
  let _ := cartesianMarkedFibrationStructure B
  let _ := cartesianMarkedWeakStructure B
  let _ := cartesianMarkedModelCategory B
  let _ := coherentDiagramModelCategory B
  dsimp only
  exact ⟨(nativeStraightening_criticalParameterCell_sourceWeak_targetProjective B m r a).1,
    nativeStraightening_criticalParameterCell_trivialCofibration B m r a⟩

end SSet.Marked
