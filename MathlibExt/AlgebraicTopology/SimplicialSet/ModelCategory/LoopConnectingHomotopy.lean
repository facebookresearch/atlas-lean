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
# Every actual degree of the original based-path connecting equivalence

The original based-path fibration and the already-proved contractibility of
its total space give the connecting equivalence in every literal degree,
including the entire degree-zero loop component set. Its exact original
forward function, both constant classes, both naturality directions and
the genuine positive multiplicative comparison are retained.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Simplicial
open scoped Simplicial

namespace SSet.LoopShiftOriginalGeometry

/-- The exact original based-path fiber point, with its literal strict-loop vertex type. -/
def originalLoopPoint (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    loopSpace X x _⦋0⦌ :=
  (loopFibrationSequence X x).fiberPoint

/-- The explicitly typed vertex is the unchanged original sequence fiber point. -/
theorem originalLoopPoint_eq (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    originalLoopPoint X x = (loopFibrationSequence X x).fiberPoint := rfl

/-- The actual original based-path connecting equivalence in every degree. -/
def loopConnectingEquiv (n : ℕ) (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    KanComplex.π (n + 1) X x ≃
      KanComplex.π n (loopSpace X x) (originalLoopPoint X x) :=
  Equiv.ofBijective ((loopFibrationSequence X x).connectingMap n)
    ((loopFibrationSequence X x).connectingMap_bijective_of_subsingleton_total
      (subsingleton_pi_basedPath X x) n)

/-- The whole forward function is the exact original based-path connecting function. -/
theorem loopConnectingEquiv_apply (n : ℕ) (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) (q : KanComplex.π (n + 1) X x) :
    loopConnectingEquiv n X x q = (loopFibrationSequence X x).connectingMap n q := rfl

/-- The original equivalence preserves the actual constant class in every degree. -/
theorem loopConnectingEquiv_one (n : ℕ) (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    loopConnectingEquiv n X x (1 : KanComplex.π (n + 1) X x) = 1 := by
  let S := loopFibrationSequence X x
  have h := S.connectingMap_map_eq_one (n := n)
    (1 : KanComplex.π (n + 1) S.E S.e)
  exact (congrArg (S.connectingMap n) (KanComplex.π.map_one S.p S.hb (n + 1))).symm.trans h

/-- The actual inverse equivalence preserves the same original constant class as well. -/
theorem loopConnectingEquiv_symm_one (n : ℕ) (X : SSet.{u}) [KanComplex X]
    (x : X _⦋0⦌) :
    (loopConnectingEquiv n X x).symm
      (1 : KanComplex.π n (loopSpace X x) (originalLoopPoint X x)) = 1 := by
  apply (loopConnectingEquiv n X x).injective
  exact ((loopConnectingEquiv n X x).apply_symm_apply 1).trans
    (loopConnectingEquiv_one n X x).symm

/-- Every entire strictly pointed source map preserves the original connecting equivalence. -/
theorem loopConnectingEquiv_naturality {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) (n : ℕ)
    (q : KanComplex.π (n + 1) X x) :
    KanComplex.π.map (loopSpaceMap f h) (loopSpaceMap_app_point f h) n
        (loopConnectingEquiv n X x q) =
      loopConnectingEquiv n Y y (KanComplex.π.map f h (n + 1) q) :=
  FibrationSequence.connectingMap_naturality (n := n) (loopFibrationSequenceHom f h) q

/-- The whole original forward naturality retains the entire pointed source function. -/
theorem loopConnectingEquiv_naturality_function
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) (n : ℕ) :
    KanComplex.π.map (loopSpaceMap f h) (loopSpaceMap_app_point f h) n ∘
        loopConnectingEquiv n X x =
      loopConnectingEquiv n Y y ∘ KanComplex.π.map f h (n + 1) :=
  funext (fun q => loopConnectingEquiv_naturality f h n q)

/-- Every entire inverse comparison retains the forced opposite original map naturality. -/
theorem loopConnectingEquiv_symm_naturality
    {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) {x : X _⦋0⦌} {y : Y _⦋0⦌} (h : f.app _ x = y) (n : ℕ)
    (q : KanComplex.π n (loopSpace X x) (originalLoopPoint X x)) :
    KanComplex.π.map f h (n + 1) ((loopConnectingEquiv n X x).symm q) =
      (loopConnectingEquiv n Y y).symm
        (KanComplex.π.map (loopSpaceMap f h) (loopSpaceMap_app_point f h) n q) := by
  apply (loopConnectingEquiv n Y y).injective
  exact (loopConnectingEquiv_naturality f h n ((loopConnectingEquiv n X x).symm q)).symm.trans
    ((congrArg (KanComplex.π.map (loopSpaceMap f h) (loopSpaceMap_app_point f h) n)
        ((loopConnectingEquiv n X x).apply_symm_apply q)).trans
      ((loopConnectingEquiv n Y y).apply_symm_apply _).symm)

/-- In every positive target degree this is the existing genuine multiplicative connecting Iso. -/
theorem loopConnectingEquiv_positive (n : ℕ) (X : SSet.{u}) [KanComplex X] (x : X _⦋0⦌) :
    loopConnectingEquiv (n + 1) X x =
      @MulEquiv.toEquiv (KanComplex.π (n + 2) X x)
        (KanComplex.π (n + 1) (loopSpace X x) (originalLoopPoint X x))
        (inferInstance : Group (KanComplex.π (n + 2) X x)).toMul
        (inferInstance : Group (KanComplex.π (n + 1) (loopSpace X x)
          (originalLoopPoint X x))).toMul (SSet.loopConnectingMulEquiv n X x) := by
  apply Equiv.ext
  intro q
  exact (SSet.loopConnectingMulEquiv_apply n X x q).symm

end SSet.LoopShiftOriginalGeometry
