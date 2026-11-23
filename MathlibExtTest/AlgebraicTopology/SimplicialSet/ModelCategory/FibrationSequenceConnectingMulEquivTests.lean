/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceConnectingMulEquiv

/-!
# Tests for multiplicative connecting-map equivalences

The matrix checks the generic and based-loop contracts, both inverse
cancellations, degrees zero and one, naturality, and universes zero, one, and
symbolic.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Simplicial
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
namespace FibrationSequenceConnectingMulEquivTests

section Generic

variable (S : SSet.FibrationSequence.{u})
  (hE : ∀ k, Subsingleton (SSet.KanComplex.π k S.E S.e))

example (n : ℕ) :
    SSet.KanComplex.π (n + 2) S.B S.b ≃*
      SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint :=
  S.connectingMapMulEquivOfSubsingletonTotal hE n

example (n : ℕ) (q : SSet.KanComplex.π (n + 2) S.B S.b) :
    S.connectingMapMulEquivOfSubsingletonTotal hE n q =
      S.connectingMap (n + 1) q :=
  SSet.FibrationSequence.connectingMapMulEquivOfSubsingletonTotal_apply
    S hE n q

example (n : ℕ) (q : SSet.KanComplex.π (n + 2) S.B S.b) :
    (S.connectingMapMulEquivOfSubsingletonTotal hE n).symm
        (S.connectingMapMulEquivOfSubsingletonTotal hE n q) = q :=
  (S.connectingMapMulEquivOfSubsingletonTotal hE n).symm_apply_apply q

example (n : ℕ) (q : SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint) :
    S.connectingMapMulEquivOfSubsingletonTotal hE n
        ((S.connectingMapMulEquivOfSubsingletonTotal hE n).symm q) = q :=
  (S.connectingMapMulEquivOfSubsingletonTotal hE n).apply_symm_apply q

example :
    SSet.KanComplex.π 2 S.B S.b ≃*
      SSet.KanComplex.π 1 S.fiber S.fiberPoint :=
  S.connectingMapMulEquivOfSubsingletonTotal hE 0

example :
    SSet.KanComplex.π 3 S.B S.b ≃*
      SSet.KanComplex.π 2 S.fiber S.fiberPoint :=
  S.connectingMapMulEquivOfSubsingletonTotal hE 1

variable {T : SSet.FibrationSequence.{u}}
  (f : SSet.FibrationSequenceHom S T)
  (hT : ∀ k, Subsingleton (SSet.KanComplex.π k T.E T.e))

example (n : ℕ) (q : SSet.KanComplex.π (n + 2) S.B S.b) :
    SSet.KanComplex.π.mapHom f.fiberMap
        f.fiberMap_app_basePoint n
        (S.connectingMapMulEquivOfSubsingletonTotal hE n q) =
      T.connectingMapMulEquivOfSubsingletonTotal hT n
        (SSet.KanComplex.π.mapHom f.baseMap f.base_pt (n + 1) q) :=
  SSet.FibrationSequence.connectingMapMulEquivOfSubsingletonTotal_naturality
    f hE hT n q

end Generic

section Loops

variable {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
  (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌}
  (h : f.app _ x = y)

example (n : ℕ) :
    let z : SSet.loopSpace X x _⦋0⦌ :=
      (SSet.loopFibrationSequence X x).fiberPoint
    SSet.KanComplex.π (n + 2) X x ≃*
      SSet.KanComplex.π (n + 1) (SSet.loopSpace X x) z :=
  SSet.loopConnectingMulEquiv n X x

example (n : ℕ) (q : SSet.KanComplex.π (n + 2) X x) :
    SSet.loopConnectingMulEquiv n X x q =
      (SSet.loopFibrationSequence X x).connectingMap (n + 1) q :=
  SSet.loopConnectingMulEquiv_apply n X x q

example (n : ℕ) (q : SSet.KanComplex.π (n + 2) X x) :
    SSet.KanComplex.π.mapHom (SSet.loopSpaceMap f h)
        (SSet.loopSpaceMap_app_point f h) n
        (SSet.loopConnectingMulEquiv n X x q) =
      SSet.loopConnectingMulEquiv n Y y
        (SSet.KanComplex.π.mapHom f h (n + 1) q) :=
  SSet.loopConnectingMulEquiv_naturality f h n q

example :
    let z : SSet.loopSpace X x _⦋0⦌ :=
      (SSet.loopFibrationSequence X x).fiberPoint
    SSet.KanComplex.π 2 X x ≃*
      SSet.KanComplex.π 1 (SSet.loopSpace X x) z :=
  SSet.loopConnectingMulEquiv 0 X x

example :
    let z : SSet.loopSpace X x _⦋0⦌ :=
      (SSet.loopFibrationSequence X x).fiberPoint
    SSet.KanComplex.π 3 X x ≃*
      SSet.KanComplex.π 2 (SSet.loopSpace X x) z :=
  SSet.loopConnectingMulEquiv 1 X x

end Loops

section UniverseZero

variable (X : SSet.{0}) [SSet.KanComplex X] (x : X _⦋0⦌)

example (n : ℕ) :
    let z : SSet.loopSpace X x _⦋0⦌ :=
      (SSet.loopFibrationSequence X x).fiberPoint
    SSet.KanComplex.π (n + 2) X x ≃*
      SSet.KanComplex.π (n + 1) (SSet.loopSpace X x) z :=
  SSet.loopConnectingMulEquiv n X x

end UniverseZero

section UniverseOne

variable (X : SSet.{1}) [SSet.KanComplex X] (x : X _⦋0⦌)

example (n : ℕ) :
    let z : SSet.loopSpace X x _⦋0⦌ :=
      (SSet.loopFibrationSequence X x).fiberPoint
    SSet.KanComplex.π (n + 2) X x ≃*
      SSet.KanComplex.π (n + 1) (SSet.loopSpace X x) z :=
  SSet.loopConnectingMulEquiv n X x

end UniverseOne

#print axioms SSet.FibrationSequence.connectingMapMulEquivOfSubsingletonTotal
#print axioms SSet.FibrationSequence.connectingMapMulEquivOfSubsingletonTotal_apply
#print axioms SSet.FibrationSequence.connectingMapMulEquivOfSubsingletonTotal_naturality
#print axioms SSet.loopConnectingMulEquiv
#print axioms SSet.loopConnectingMulEquiv_apply
#print axioms SSet.loopConnectingMulEquiv_naturality

end FibrationSequenceConnectingMulEquivTests
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory
