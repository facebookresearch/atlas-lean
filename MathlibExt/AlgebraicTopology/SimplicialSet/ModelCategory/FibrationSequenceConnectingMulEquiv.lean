/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceContractible
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopSpaceWeakEquivalence

/-!
# Multiplicative connecting-map equivalences

The connecting map of a simplicial fibration sequence is a multiplicative
equivalence in positive target degrees when every homotopy group of the total
space is subsingleton.  For the based-path fibration sequence this gives the
canonical multiplicative shift between the homotopy groups of a Kan complex
and those of its strict loop space.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Simplicial
open scoped Simplicial

namespace SSet.FibrationSequence

/-- The connecting map, from homotopy of the base to homotopy of the strict
fiber, as a multiplicative equivalence when the total space has subsingleton
homotopy groups. -/
noncomputable def connectingMapMulEquivOfSubsingletonTotal
    (S : SSet.FibrationSequence.{u})
    (hE : ∀ k, Subsingleton (SSet.KanComplex.π k S.E S.e))
    (n : ℕ) :
    SSet.KanComplex.π (n + 2) S.B S.b ≃*
      SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint :=
  MulEquiv.ofBijective
    ({ toFun := S.connectingMap (n + 1)
       map_mul' := S.connectingMap_mul n } :
      SSet.KanComplex.π (n + 2) S.B S.b →ₙ*
        SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint)
    (S.connectingMap_bijective_of_subsingleton_total hE (n + 1))

/-- The forward map of `connectingMapMulEquivOfSubsingletonTotal` is the
connecting map. -/
@[simp]
theorem connectingMapMulEquivOfSubsingletonTotal_apply
    (S : SSet.FibrationSequence.{u})
    (hE : ∀ k, Subsingleton (SSet.KanComplex.π k S.E S.e))
    (n : ℕ) (q : SSet.KanComplex.π (n + 2) S.B S.b) :
    connectingMapMulEquivOfSubsingletonTotal S hE n q =
      S.connectingMap (n + 1) q := by
  exact MulEquiv.ofBijective_apply _ _ _

/-- The multiplicative connecting equivalence is natural under morphisms of
fibration sequences. -/
theorem connectingMapMulEquivOfSubsingletonTotal_naturality
    {S T : SSet.FibrationSequence.{u}}
    (f : SSet.FibrationSequenceHom S T)
    (hS : ∀ k, Subsingleton (SSet.KanComplex.π k S.E S.e))
    (hT : ∀ k, Subsingleton (SSet.KanComplex.π k T.E T.e))
    (n : ℕ) (q : SSet.KanComplex.π (n + 2) S.B S.b) :
    SSet.KanComplex.π.mapHom f.fiberMap
        f.fiberMap_app_basePoint n
        (connectingMapMulEquivOfSubsingletonTotal S hS n q) =
      connectingMapMulEquivOfSubsingletonTotal T hT n
        (SSet.KanComplex.π.mapHom f.baseMap f.base_pt (n + 1) q) := by
  simpa only [connectingMapMulEquivOfSubsingletonTotal_apply,
    SSet.KanComplex.π.mapHom_apply] using
    SSet.FibrationSequence.connectingMap_naturality (n := n + 1) f q

end SSet.FibrationSequence

namespace SSet

/-- The multiplicative connecting equivalence for the based-path fibration
sequence, from homotopy of a Kan complex to homotopy of its strict loop
space. -/
noncomputable def loopConnectingMulEquiv
    (n : ℕ) (X : SSet.{u}) [SSet.KanComplex X]
    (x : X _⦋0⦌) :
    let z : SSet.loopSpace X x _⦋0⦌ :=
      (SSet.loopFibrationSequence X x).fiberPoint
    SSet.KanComplex.π (n + 2) X x ≃*
      SSet.KanComplex.π (n + 1) (SSet.loopSpace X x) z := by
  dsimp only
  exact FibrationSequence.connectingMapMulEquivOfSubsingletonTotal
    (SSet.loopFibrationSequence X x)
    (SSet.subsingleton_pi_basedPath X x) n

/-- The forward map of `loopConnectingMulEquiv` is the connecting map of the
based-path fibration sequence. -/
@[simp]
theorem loopConnectingMulEquiv_apply
    (n : ℕ) (X : SSet.{u}) [SSet.KanComplex X]
    (x : X _⦋0⦌) (q : SSet.KanComplex.π (n + 2) X x) :
    loopConnectingMulEquiv n X x q =
      (SSet.loopFibrationSequence X x).connectingMap (n + 1) q :=
  FibrationSequence.connectingMapMulEquivOfSubsingletonTotal_apply
    (SSet.loopFibrationSequence X x)
    (SSet.subsingleton_pi_basedPath X x) n q

/-- The loop connecting equivalence is natural under strictly pointed maps
of Kan complexes. -/
theorem loopConnectingMulEquiv_naturality
    {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌}
    (h : f.app _ x = y) (n : ℕ)
    (q : SSet.KanComplex.π (n + 2) X x) :
    SSet.KanComplex.π.mapHom (SSet.loopSpaceMap f h)
        (SSet.loopSpaceMap_app_point f h) n
        (loopConnectingMulEquiv n X x q) =
      loopConnectingMulEquiv n Y y
        (SSet.KanComplex.π.mapHom f h (n + 1) q) := by
  change
    SSet.KanComplex.π.mapHom
        (SSet.loopFibrationSequenceHom f h).fiberMap
        (SSet.loopFibrationSequenceHom f h).fiberMap_app_basePoint n
        (FibrationSequence.connectingMapMulEquivOfSubsingletonTotal
          (SSet.loopFibrationSequence X x)
          (SSet.subsingleton_pi_basedPath X x) n q) =
      FibrationSequence.connectingMapMulEquivOfSubsingletonTotal
        (SSet.loopFibrationSequence Y y)
        (SSet.subsingleton_pi_basedPath Y y) n
        (SSet.KanComplex.π.mapHom
          (SSet.loopFibrationSequenceHom f h).baseMap
          (SSet.loopFibrationSequenceHom f h).base_pt (n + 1) q)
  exact
    FibrationSequence.connectingMapMulEquivOfSubsingletonTotal_naturality
      (SSet.loopFibrationSequenceHom f h)
      (SSet.subsingleton_pi_basedPath X x)
      (SSet.subsingleton_pi_basedPath Y y) n q

end SSet
