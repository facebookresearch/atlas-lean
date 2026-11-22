/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CartesianWeakEquivalences
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterModelObstruction

/-!
# The full original local-testing trivial-cofibration classes

Use all original marked monomorphisms satisfying every intrinsic target
mapping-space weak test, rather than the unchanged auxiliary cell-left
class. The two original vertical interval endpoints belong to these
classes, and their right classes must lift them. In particular the proved
auxiliary counterexample is excluded from the corrected right class.
These are actual class definitions and lifting laws, not a claimed model
or a supplied recognition certificate.
-/

noncomputable section
universe u
open CategoryTheory MorphismProperty
open scoped Simplicial

namespace SSet.Marked

/-- All original Cartesian mapping-weak marked monomorphisms, with no restriction to an auxiliary family. -/
def cartesianTestingTrivialCofibrations (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  monomorphisms (Over (max B)) ⊓ cartesianWeakEquivalences B

/-- The corresponding full original cocartesian local-testing class. -/
def cocartesianTestingTrivialCofibrations (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  monomorphisms (Over (max B)) ⊓ cocartesianWeakEquivalences B

/-- Actual Cartesian testing fibrations lift all original weak marked monomorphisms. -/
def cartesianTestingFibrations (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  (cartesianTestingTrivialCofibrations B).rlp

/-- Actual dual testing fibrations use all original cocartesian weak marked monomorphisms. -/
def cocartesianTestingFibrations (B : SSet.{u}) : MorphismProperty (Over (max B)) :=
  (cocartesianTestingTrivialCofibrations B).rlp

/-- The full Cartesian class respects the same original arrow isomorphisms. -/
theorem cartesianTestingTrivialCofibrations_respectsIso (B : SSet.{u}) :
    (cartesianTestingTrivialCofibrations B).RespectsIso := by
  unfold cartesianTestingTrivialCofibrations cartesianWeakEquivalences
  infer_instance

/-- The corresponding dual full class also retains arrow-isomorphism transport. -/
theorem cocartesianTestingTrivialCofibrations_respectsIso (B : SSet.{u}) :
    (cocartesianTestingTrivialCofibrations B).RespectsIso := by
  unfold cocartesianTestingTrivialCofibrations cocartesianWeakEquivalences
  infer_instance

/-- Every original vertical interval endpoint is in the full Cartesian testing trivial-cofibration class. -/
theorem pointEndpoint_cartesianTestingTrivialCofibration (ε : Fin 2) :
    cartesianTestingTrivialCofibrations (Δ[0] : SSet.{u}) (pointEndpoint.{u} ε) := by
  refine ⟨pointEndpoint_mono ε, ?_⟩
  fin_cases ε
  · exact pointTargetEndpoint_cartesian_weak
  · exact pointSourceEndpoint_cartesian_weak

/-- Both whole original vertical endpoints are also genuine dual testing weak monomorphisms. -/
theorem pointEndpoint_cocartesianTestingTrivialCofibration (ε : Fin 2) :
    cocartesianTestingTrivialCofibrations (Δ[0] : SSet.{u}) (pointEndpoint.{u} ε) := by
  refine ⟨pointEndpoint_mono ε, ?_⟩
  fin_cases ε
  · exact pointTargetEndpoint_cocartesian_weak
  · exact pointSourceEndpoint_cocartesian_weak

/-- Corrected Cartesian right maps must lift the actual vertical source endpoint. -/
theorem cartesianTestingFibration_lifts_pointEndpoint {X Y : Over (max (Δ[0] : SSet.{u}))}
    (p : X ⟶ Y) (hp : cartesianTestingFibrations (Δ[0] : SSet.{u}) p) (ε : Fin 2) :
    HasLiftingProperty (pointEndpoint.{u} ε) p :=
  hp _ (pointEndpoint_cartesianTestingTrivialCofibration ε)

/-- The corresponding actual right class obeys both native dual endpoint lifting laws. -/
theorem cocartesianTestingFibration_lifts_pointEndpoint {X Y : Over (max (Δ[0] : SSet.{u}))}
    (p : X ⟶ Y) (hp : cocartesianTestingFibrations (Δ[0] : SSet.{u}) p) (ε : Fin 2) :
    HasLiftingProperty (pointEndpoint.{u} ε) p :=
  hp _ (pointEndpoint_cocartesianTestingTrivialCofibration ε)

/-- The actual auxiliary Cartesian counterexample is excluded from the full corrected right class. -/
theorem pointEndpoint_not_cartesianTestingFibration (ε : Fin 2) :
    ¬ cartesianTestingFibrations (Δ[0] : SSet.{u}) (pointEndpoint.{u} ε) := by
  intro h
  exact pointEndpoint_not_self_lifting ε (cartesianTestingFibration_lifts_pointEndpoint _ h ε)

/-- The same obstruction is excluded from the full dual testing right class. -/
theorem pointEndpoint_not_cocartesianTestingFibration (ε : Fin 2) :
    ¬ cocartesianTestingFibrations (Δ[0] : SSet.{u}) (pointEndpoint.{u} ε) := by
  intro h
  exact pointEndpoint_not_self_lifting ε (cocartesianTestingFibration_lifts_pointEndpoint _ h ε)

end SSet.Marked
