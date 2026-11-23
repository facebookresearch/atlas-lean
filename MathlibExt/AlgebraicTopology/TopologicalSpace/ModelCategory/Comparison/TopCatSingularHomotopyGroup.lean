/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.Homology.DegreeTwoHurewiczMap

public import MathlibExt.Topology.Homotopy.HomotopyGroupLoopShift
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidActionMul
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidPiOne
public import MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoidPath
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceConnectingMulEquiv
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularLoopComparisonIso
public import MathlibExt.Topology.Homotopy.TopCat.Singular.SingularKanPolymorphic

/-!
# Cube-to-singular homotopy groups

This file compares the positive cube-based homotopy groups of a topological
space with the simplicial homotopy groups of its singular Kan complex.  The
comparison is multiplicative, natural, and compatible with change of
basepoint along paths.

The degree-one statements retain the noncommutative conjugation convention.
No weak-equivalence, derived-loop, spectrum, or unpointed degree-zero result
is asserted here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Simplicial
open scoped Simplicial Topology

namespace TopCat

private theorem piOneMulEquivFundamentalGroup_naturality
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
        (HomotopyGroup.map f a) =
      (_root_.FundamentalGroupoid.map f).mapEnd (_root_.FundamentalGroupoid.mk x)
        (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
  obtain ⟨p, rfl⟩ := HomotopyGroup.mk_surjective a
  rfl

private theorem singularFundamentalGroupoidEndMulEquiv_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (q : CategoryTheory.End
      (SSet.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv.symm x))) :
    TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
        ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).mapEnd
          (SSet.FundamentalGroupoid.mk (TopCat.toSSetObj₀Equiv.symm x)) q) =
      (_root_.FundamentalGroupoid.map f.hom).mapEnd (_root_.FundamentalGroupoid.mk x)
        (TopCat.singularFundamentalGroupoidEndMulEquiv X x q) := by
  let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
    TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex Y
  rcases q with ⟨q⟩
  obtain ⟨e, rfl⟩ := SSet.FundamentalGroupoid.homMk_surjective q
  let p := TopCat.pathEquiv
    ((TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)) e)
  have he :
      (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)).symm
          ((TopCat.pathEquiv (X := X) (x := x) (y := x)).symm p) = e := by
    dsimp only [p]
    rw [(TopCat.pathEquiv (X := X) (x := x) (y := x)).symm_apply_apply,
      (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := x)).symm_apply_apply]
  rw [← he]
  change
    TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
        (End.of ((SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).map
          (TopCat.singularPathHom X p))) = _
  rw [TopCat.singularPathHom_map]
  simp only [TopCat.singularPathHom,
    TopCat.singularFundamentalGroupoidEndMulEquiv_homMk,
    (TopCat.toSSetObjEdgeEquiv (X := X)
      (x := x) (y := x)).apply_symm_apply,
    (TopCat.pathEquiv (X := X) (x := x) (y := x)).apply_symm_apply,
    (TopCat.toSSetObjEdgeEquiv (X := Y)
      (x := f x) (y := f x)).apply_symm_apply,
    (TopCat.pathEquiv (X := Y)
      (x := f x) (y := f x)).apply_symm_apply]
  apply End.ext
  change Path.Homotopic.Quotient.mk (p.map f.hom.continuous) =
    (Path.Homotopic.Quotient.mk p).map f.hom
  exact Path.Homotopic.Quotient.mk_map p f.hom

private noncomputable def singularLoopHomotopyGroupMulEquiv
    (n : ℕ) (X : TopCat.{u}) (x : X) :
    let K := TopCat.toSSet.obj X
    let KL := TopCat.toSSet.obj (TopCat.of (LoopSpace X x))
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    letI : SSet.KanComplex KL :=
      TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace X x))
    let sx := TopCat.toSSetObj₀Equiv.symm x
    let z : SSet.loopSpace K sx _⦋0⦌ :=
      (SSet.loopFibrationSequence K sx).fiberPoint
    SSet.KanComplex.π (n + 1) KL
        (TopCat.toSSetObj₀Equiv.symm (Path.refl x)) ≃*
      SSet.KanComplex.π (n + 1) (SSet.loopSpace K sx) z := by
  dsimp only
  let K := TopCat.toSSet.obj X
  let KL := TopCat.toSSet.obj (TopCat.of (LoopSpace X x))
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KL :=
    TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace X x))
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sr := (TopCat.toSSetObj₀Equiv
    (X := TopCat.of (LoopSpace X x))).symm (Path.refl x)
  let z : SSet.loopSpace K sx _⦋0⦌ :=
    (SSet.loopFibrationSequence K sx).fiberPoint
  let _ : SSet.KanComplex (SSet.loopSpace K sx) :=
    SSet.loopSpace_kanComplex K sx
  let _ : Group (SSet.KanComplex.π (n + 1) KL sr) :=
    SSet.KanComplex.π.group
  let _ : Group (SSet.KanComplex.π (n + 1)
      (SSet.loopSpace K sx) z) :=
    SSet.KanComplex.π.group
  let e := SSet.singularLoopIso (X : Type u) x
  have hLoop : e.hom.app _
      (TopCat.toSSetObj₀Equiv.symm (Path.refl x)) =
      (SSet.loopFibrationSequence (TopCat.toSSet.obj X)
        (TopCat.toSSetObj₀Equiv.symm x)).fiberPoint := by
    dsimp only [e]
    rw [SSet.singularLoopIso_hom]
    exact SSet.singularLoopComparison_refl (X : Type u) x
  exact
    { toEquiv := SSet.KanComplex.π.equivOfIso e hLoop (n + 1)
      map_mul' := SSet.KanComplex.π.map_mul e.hom hLoop n }

@[simp]
private theorem singularLoopHomotopyGroupMulEquiv_apply
    (n : ℕ) (X : TopCat.{u}) (x : X) :
    let K := TopCat.toSSet.obj X
    let KL := TopCat.toSSet.obj (TopCat.of (LoopSpace X x))
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    letI : SSet.KanComplex KL :=
      TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace X x))
    ∀ a : SSet.KanComplex.π (n + 1) KL
        (TopCat.toSSetObj₀Equiv.symm (Path.refl x)),
      singularLoopHomotopyGroupMulEquiv n X x a =
        SSet.KanComplex.π.map
          (SSet.singularLoopIso (X : Type u) x).hom
          (by
            rw [SSet.singularLoopIso_hom]
            exact SSet.singularLoopComparison_refl (X : Type u) x)
          (n + 1) a := by
  dsimp only
  let K := TopCat.toSSet.obj X
  let KL := TopCat.toSSet.obj (TopCat.of (LoopSpace X x))
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KL :=
    TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace X x))
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sr := (TopCat.toSSetObj₀Equiv
    (X := TopCat.of (LoopSpace X x))).symm (Path.refl x)
  let z : SSet.loopSpace K sx _⦋0⦌ :=
    (SSet.loopFibrationSequence K sx).fiberPoint
  let _ : SSet.KanComplex (SSet.loopSpace K sx) :=
    SSet.loopSpace_kanComplex K sx
  let _ : Group (SSet.KanComplex.π (n + 1) KL sr) :=
    SSet.KanComplex.π.group
  let _ : Group (SSet.KanComplex.π (n + 1)
      (SSet.loopSpace K sx) z) :=
    SSet.KanComplex.π.group
  intro a
  rfl

/-- The multiplicative comparison from positive cube-based homotopy groups to
the homotopy groups of the singular Kan complex. -/
noncomputable def homotopyGroupSingularMulEquiv
    (n : ℕ) (X : TopCat.{u}) (x : X) :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    HomotopyGroup.Pi (n + 1) X x ≃*
      SSet.KanComplex.π (n + 1) K
        (TopCat.toSSetObj₀Equiv.symm x) :=
  match n with
  | 0 => by
      dsimp only
      let K := TopCat.toSSet.obj X
      let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
      exact HomotopyGroup.pi1MulEquivFundamentalGroup.trans
        ((TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm.trans
          (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd
            (TopCat.toSSetObj₀Equiv.symm x)).symm)
  | n + 1 => by
      dsimp only
      let K := TopCat.toSSet.obj X
      let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
      let KL := TopCat.toSSet.obj (TopCat.of (LoopSpace X x))
      let _ : SSet.KanComplex KL :=
        TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace X x))
      let sx := TopCat.toSSetObj₀Equiv.symm x
      let sr := (TopCat.toSSetObj₀Equiv
        (X := TopCat.of (LoopSpace X x))).symm (Path.refl x)
      let z : SSet.loopSpace K sx _⦋0⦌ :=
        (SSet.loopFibrationSequence K sx).fiberPoint
      let _ : SSet.KanComplex (SSet.loopSpace K sx) :=
        SSet.loopSpace_kanComplex K sx
      let _ : Group (SSet.KanComplex.π (n + 1) KL sr) :=
        SSet.KanComplex.π.group
      let _ : Group (SSet.KanComplex.π (n + 1)
          (SSet.loopSpace K sx) z) :=
        SSet.KanComplex.π.group
      let e := SSet.singularLoopIso (X : Type u) x
      have hLoop : e.hom.app _ sr = z := by
        dsimp only [e, sr, z]
        rw [SSet.singularLoopIso_hom]
        exact SSet.singularLoopComparison_refl (X : Type u) x
      let loopEquiv : SSet.KanComplex.π (n + 1) KL sr ≃*
          SSet.KanComplex.π (n + 1) (SSet.loopSpace K sx) z :=
        { toEquiv := SSet.KanComplex.π.equivOfIso e hLoop (n + 1)
          map_mul' := SSet.KanComplex.π.map_mul e.hom hLoop n }
      exact
        (HomotopyGroup.loopShiftMulEquiv n (X : Type u) x).symm
          |>.trans
            (homotopyGroupSingularMulEquiv n
              (TopCat.of (LoopSpace X x)) (Path.refl x))
          |>.trans loopEquiv
          |>.trans (SSet.loopConnectingMulEquiv n K sx).symm

/-- In degree one, the comparison agrees with the fundamental-groupoid
description, including its inverse-edge convention. -/
theorem homotopyGroupSingularMulEquiv_piOne
    (X : TopCat.{u}) (x : X) (a : HomotopyGroup.Pi 1 X x) :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    TopCat.singularFundamentalGroupoidEndMulEquiv X x
      (SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd
        (TopCat.toSSetObj₀Equiv.symm x)
        (homotopyGroupSingularMulEquiv 0 X x a)) =
      HomotopyGroup.pi1MulEquivFundamentalGroup a := by
  dsimp only
  let K := TopCat.toSSet.obj X
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  change
    (TopCat.singularFundamentalGroupoidEndMulEquiv X x)
      ((SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd
        (TopCat.toSSetObj₀Equiv.symm x))
        ((SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd
          (TopCat.toSSetObj₀Equiv.symm x)).symm
          ((TopCat.singularFundamentalGroupoidEndMulEquiv X x).symm
            (HomotopyGroup.pi1MulEquivFundamentalGroup a)))) = _
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]

private theorem homotopyGroupSingularMulEquiv_naturality_zero
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (a : HomotopyGroup.Pi 1 X x) :
    let KX := TopCat.toSSet.obj X
    let KY := TopCat.toSSet.obj Y
    let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
    let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
    let h₀ : (TopCat.toSSet.map f).app _
        (TopCat.toSSetObj₀Equiv.symm x) =
        TopCat.toSSetObj₀Equiv.symm (f x) := by
      rfl
    homotopyGroupSingularMulEquiv 0 Y (f x)
        (HomotopyGroup.map f.hom a) =
      SSet.KanComplex.π.map (TopCat.toSSet.map f) h₀ 1
        (homotopyGroupSingularMulEquiv 0 X x a) := by
  dsimp only
  let KX := TopCat.toSSet.obj X
  let KY := TopCat.toSSet.obj Y
  let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sy := TopCat.toSSetObj₀Equiv.symm (f x)
  let h₀ : (TopCat.toSSet.map f).app _ sx = sy := by
    rfl
  cases h₀
  let SX := SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd sx
  let SY := SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd sy
  let EX := TopCat.singularFundamentalGroupoidEndMulEquiv X x
  let EY := TopCat.singularFundamentalGroupoidEndMulEquiv Y (f x)
  have hπ (b : SSet.KanComplex.π 1 KX sx) :
      SY (SSet.KanComplex.π.map (TopCat.toSSet.map f) h₀ 1 b) =
        (SSet.mapFundamentalGroupoid (TopCat.toSSet.map f)).mapEnd
          (SSet.FundamentalGroupoid.mk sx) (SX b) := by
    exact SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_naturality
      (TopCat.toSSet.map f) sx b
  apply SY.injective
  apply EY.injective
  rw [hπ]
  rw [singularFundamentalGroupoidEndMulEquiv_naturality]
  rw [homotopyGroupSingularMulEquiv_piOne,
    homotopyGroupSingularMulEquiv_piOne]
  exact piOneMulEquivFundamentalGroup_naturality f.hom x a

private theorem singularStrictLoopMap_refl
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    (TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.strictLoopMap f.hom x))).app _
        (TopCat.toSSetObj₀Equiv.symm (Path.refl x)) =
      TopCat.toSSetObj₀Equiv.symm (Path.refl (f x)) := by
  change (TopCat.toSSetObj₀Equiv
    (X := TopCat.of (LoopSpace Y (f x)))).symm
      (ContinuousMap.strictLoopMap f.hom x (Path.refl x)) =
    (TopCat.toSSetObj₀Equiv
      (X := TopCat.of (LoopSpace Y (f x)))).symm (Path.refl (f x))
  exact congrArg _ (ContinuousMap.strictLoopMap_refl f.hom x)

private theorem singularLoopIso_hom_app_refl
    (X : TopCat.{u}) (x : X) :
    let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
      TopCat.toSSet_obj_kanComplex X
    (SSet.singularLoopIso (X : Type u) x).hom.app _
        (TopCat.toSSetObj₀Equiv.symm (Path.refl x)) =
      (SSet.loopFibrationSequence (TopCat.toSSet.obj X)
        (TopCat.toSSetObj₀Equiv.symm x)).fiberPoint := by
  dsimp only
  let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
    TopCat.toSSet_obj_kanComplex X
  rw [SSet.singularLoopIso_hom]
  exact SSet.singularLoopComparison_refl (X : Type u) x

private theorem singularLoopIso_left_comp_app_refl
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
      TopCat.toSSet_obj_kanComplex Y
    ((TopCat.toSSet.map
      (TopCat.ofHom (ContinuousMap.strictLoopMap f.hom x))) ≫
        (SSet.singularLoopIso (Y : Type u) (f x)).hom).app _
          (TopCat.toSSetObj₀Equiv.symm (Path.refl x)) =
      (SSet.loopFibrationSequence (TopCat.toSSet.obj Y)
        (TopCat.toSSetObj₀Equiv.symm (f x))).fiberPoint := by
  dsimp only
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex Y
  change (SSet.singularLoopIso (Y : Type u) (f x)).hom.app _
      ((TopCat.toSSet.map
        (TopCat.ofHom (ContinuousMap.strictLoopMap f.hom x))).app _
          (TopCat.toSSetObj₀Equiv.symm (Path.refl x))) = _
  rw [singularStrictLoopMap_refl,
    singularLoopIso_hom_app_refl]

private theorem singularLoopIso_right_comp_app_refl
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
      TopCat.toSSet_obj_kanComplex X
    let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
      TopCat.toSSet_obj_kanComplex Y
    ((SSet.singularLoopIso (X : Type u) x).hom ≫
        SSet.loopSpaceMap (TopCat.toSSet.map f) rfl).app _
          (TopCat.toSSetObj₀Equiv.symm (Path.refl x)) =
      (SSet.loopFibrationSequence (TopCat.toSSet.obj Y)
        (TopCat.toSSetObj₀Equiv.symm (f x))).fiberPoint := by
  dsimp only
  let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
    TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
    TopCat.toSSet_obj_kanComplex Y
  change (SSet.loopSpaceMap (TopCat.toSSet.map f) rfl).app _
      ((SSet.singularLoopIso (X : Type u) x).hom.app _
        (TopCat.toSSetObj₀Equiv.symm (Path.refl x))) = _
  rw [singularLoopIso_hom_app_refl]
  exact SSet.loopSpaceMap_app_point (TopCat.toSSet.map f)
    (x := TopCat.toSSetObj₀Equiv.symm x)
    (y := TopCat.toSSetObj₀Equiv.symm (f x)) rfl

private theorem singularLoopHomotopyGroupMulEquiv_naturality
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X) (n : ℕ)
    (a : SSet.KanComplex.π (n + 1)
      (TopCat.toSSet.obj (TopCat.of (LoopSpace X x)))
      (TopCat.toSSetObj₀Equiv.symm (Path.refl x))) :
    let _ : SSet.KanComplex (TopCat.toSSet.obj X) :=
      TopCat.toSSet_obj_kanComplex X
    let _ : SSet.KanComplex (TopCat.toSSet.obj Y) :=
      TopCat.toSSet_obj_kanComplex Y
    let _ : SSet.KanComplex
        (TopCat.toSSet.obj (TopCat.of (LoopSpace X x))) :=
      TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace X x))
    let _ : SSet.KanComplex
        (TopCat.toSSet.obj (TopCat.of (LoopSpace Y (f x)))) :=
      TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace Y (f x)))
    singularLoopHomotopyGroupMulEquiv n Y (f x)
        (SSet.KanComplex.π.map
          (TopCat.toSSet.map
            (TopCat.ofHom (ContinuousMap.strictLoopMap f.hom x)))
          (singularStrictLoopMap_refl f x) (n + 1) a) =
      SSet.KanComplex.π.map
        (SSet.loopSpaceMap (TopCat.toSSet.map f) rfl)
        (SSet.loopSpaceMap_app_point (TopCat.toSSet.map f) rfl)
        (n + 1) (singularLoopHomotopyGroupMulEquiv n X x a) := by
  dsimp only
  let KX := TopCat.toSSet.obj X
  let KY := TopCat.toSSet.obj Y
  let KLX := TopCat.toSSet.obj (TopCat.of (LoopSpace X x))
  let KLY := TopCat.toSSet.obj (TopCat.of (LoopSpace Y (f x)))
  let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
  let _ : SSet.KanComplex KLX :=
    TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace X x))
  let _ : SSet.KanComplex KLY :=
    TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace Y (f x)))
  let sx := TopCat.toSSetObj₀Equiv.symm x
  let sy := TopCat.toSSetObj₀Equiv.symm (f x)
  let srX := (TopCat.toSSetObj₀Equiv
    (X := TopCat.of (LoopSpace X x))).symm (Path.refl x)
  let srY := (TopCat.toSSetObj₀Equiv
    (X := TopCat.of (LoopSpace Y (f x)))).symm (Path.refl (f x))
  let zX : SSet.loopSpace KX sx _⦋0⦌ :=
    (SSet.loopFibrationSequence KX sx).fiberPoint
  let zY : SSet.loopSpace KY sy _⦋0⦌ :=
    (SSet.loopFibrationSequence KY sy).fiberPoint
  let _ : SSet.KanComplex (SSet.loopSpace KX sx) :=
    SSet.loopSpace_kanComplex KX sx
  let _ : SSet.KanComplex (SSet.loopSpace KY sy) :=
    SSet.loopSpace_kanComplex KY sy
  let s := TopCat.toSSet.map
    (TopCat.ofHom (ContinuousMap.strictLoopMap f.hom x))
  let hs : s.app _ srX = srY := singularStrictLoopMap_refl f x
  let lmap := SSet.loopSpaceMap (TopCat.toSSet.map f)
    (x := sx) (y := sy) rfl
  let hl : lmap.app _ zX = zY :=
    SSet.loopSpaceMap_app_point (TopCat.toSSet.map f) rfl
  let eX := SSet.singularLoopIso (X : Type u) x
  let eY := SSet.singularLoopIso (Y : Type u) (f x)
  have hX : eX.hom.app _ srX = zX :=
    singularLoopIso_hom_app_refl X x
  have hY : eY.hom.app _ srY = zY :=
    singularLoopIso_hom_app_refl Y (f x)
  have hcomp : (s ≫ eY.hom).app _ srX = zY :=
    singularLoopIso_left_comp_app_refl f x
  have hcomp' : (eX.hom ≫ lmap).app _ srX = zY :=
    singularLoopIso_right_comp_app_refl f x
  rw [singularLoopHomotopyGroupMulEquiv_apply,
    singularLoopHomotopyGroupMulEquiv_apply]
  calc
    SSet.KanComplex.π.map eY.hom hY (n + 1)
        (SSet.KanComplex.π.map s hs (n + 1) a) =
      SSet.KanComplex.π.map (s ≫ eY.hom) hcomp (n + 1) a :=
        (SSet.KanComplex.π.map_comp_apply s eY.hom hs hY hcomp a).symm
    _ = SSet.KanComplex.π.map (eX.hom ≫ lmap) hcomp' (n + 1) a := by
      have hnat : s ≫ eY.hom = eX.hom ≫ lmap :=
        SSet.singularLoopIso_hom_naturality f.hom x
      have map_eq (F G : KLX ⟶ SSet.loopSpace KY sy)
          (hF : F.app _ srX = zY) (hG : G.app _ srX = zY)
          (hFG : F = G) :
          SSet.KanComplex.π.map F hF (n + 1) a =
            SSet.KanComplex.π.map G hG (n + 1) a := by
        subst G
        cases Subsingleton.elim hF hG
        rfl
      exact map_eq (s ≫ eY.hom) (eX.hom ≫ lmap)
        hcomp hcomp' hnat
    _ = SSet.KanComplex.π.map lmap hl (n + 1)
        (SSet.KanComplex.π.map eX.hom hX (n + 1) a) :=
      SSet.KanComplex.π.map_comp_apply eX.hom lmap hX hl hcomp' a

private theorem homotopyGroupSingularMulEquiv_naturality_image
    {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y) (x : X)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    let KX := TopCat.toSSet.obj X
    let KY := TopCat.toSSet.obj Y
    let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
    let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
    homotopyGroupSingularMulEquiv n Y (f x)
        (HomotopyGroup.map f.hom a) =
      SSet.KanComplex.π.map (TopCat.toSSet.map f) rfl (n + 1)
        (homotopyGroupSingularMulEquiv n X x a) := by
  induction n generalizing X Y with
  | zero =>
      exact homotopyGroupSingularMulEquiv_naturality_zero f x a
  | succ n ih =>
      dsimp only
      let KX := TopCat.toSSet.obj X
      let KY := TopCat.toSSet.obj Y
      let KLX := TopCat.toSSet.obj (TopCat.of (LoopSpace X x))
      let KLY := TopCat.toSSet.obj (TopCat.of (LoopSpace Y (f x)))
      let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
      let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
      let _ : SSet.KanComplex KLX :=
        TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace X x))
      let _ : SSet.KanComplex KLY :=
        TopCat.toSSet_obj_kanComplex (TopCat.of (LoopSpace Y (f x)))
      let sx := TopCat.toSSetObj₀Equiv.symm x
      let sy := TopCat.toSSetObj₀Equiv.symm (f x)
      let srX := (TopCat.toSSetObj₀Equiv
        (X := TopCat.of (LoopSpace X x))).symm (Path.refl x)
      let srY := (TopCat.toSSetObj₀Equiv
        (X := TopCat.of (LoopSpace Y (f x)))).symm (Path.refl (f x))
      let zX : SSet.loopSpace KX sx _⦋0⦌ :=
        (SSet.loopFibrationSequence KX sx).fiberPoint
      let zY : SSet.loopSpace KY sy _⦋0⦌ :=
        (SSet.loopFibrationSequence KY sy).fiberPoint
      let _ : SSet.KanComplex (SSet.loopSpace KX sx) :=
        SSet.loopSpace_kanComplex KX sx
      let _ : SSet.KanComplex (SSet.loopSpace KY sy) :=
        SSet.loopSpace_kanComplex KY sy
      let _ : Group (SSet.KanComplex.π (n + 1) KLX srX) :=
        SSet.KanComplex.π.group
      let _ : Group (SSet.KanComplex.π (n + 1) KLY srY) :=
        SSet.KanComplex.π.group
      let _ : Group (SSet.KanComplex.π (n + 1)
          (SSet.loopSpace KX sx) zX) :=
        SSet.KanComplex.π.group
      let _ : Group (SSet.KanComplex.π (n + 1)
          (SSet.loopSpace KY sy) zY) :=
        SSet.KanComplex.π.group
      let LX := HomotopyGroup.loopShiftMulEquiv n (X : Type u) x
      let LY := HomotopyGroup.loopShiftMulEquiv n (Y : Type u) (f x)
      let g : TopCat.of (LoopSpace X x) ⟶
          TopCat.of (LoopSpace Y (f x)) :=
        TopCat.ofHom (ContinuousMap.strictLoopMap f.hom x)
      let hb : g (Path.refl x) = Path.refl (f x) :=
        ContinuousMap.strictLoopMap_refl f.hom x
      let s := TopCat.toSSet.map g
      let hs : s.app _ srX = srY := singularStrictLoopMap_refl f x
      let lmap := SSet.loopSpaceMap (TopCat.toSSet.map f)
        (x := sx) (y := sy) rfl
      let hl : lmap.app _ zX = zY :=
        SSet.loopSpaceMap_app_point (TopCat.toSSet.map f) rfl
      let DX := SSet.loopConnectingMulEquiv n KX sx
      let DY := SSet.loopConnectingMulEquiv n KY sy
      have hA :
          LY.symm (HomotopyGroup.map f.hom a) =
            HomotopyGroup.mapHomOfEq
              (ContinuousMap.strictLoopMap f.hom x) hb n (LX.symm a) := by
        apply LY.injective
        rw [LY.apply_symm_apply]
        rw [HomotopyGroup.loopShiftMulEquiv_naturality]
        rw [LX.apply_symm_apply]
      have ihEq {A B : TopCat.{u}} (k : A ⟶ B)
          (a₀ : A) (b₀ : B) (h₀ : k a₀ = b₀)
          (q : HomotopyGroup.Pi (n + 1) A a₀) :
          let KA := TopCat.toSSet.obj A
          let KB := TopCat.toSSet.obj B
          let _ : SSet.KanComplex KA := TopCat.toSSet_obj_kanComplex A
          let _ : SSet.KanComplex KB := TopCat.toSSet_obj_kanComplex B
          let hs₀ : (TopCat.toSSet.map k).app _
              (TopCat.toSSetObj₀Equiv.symm a₀) =
              TopCat.toSSetObj₀Equiv.symm b₀ := by
            exact congrArg (TopCat.toSSetObj₀Equiv (X := B)).symm h₀
          homotopyGroupSingularMulEquiv n B b₀
              (HomotopyGroup.mapHomOfEq k.hom h₀ n q) =
            SSet.KanComplex.π.map (TopCat.toSSet.map k) hs₀ (n + 1)
              (homotopyGroupSingularMulEquiv n A a₀ q) := by
        cases h₀
        dsimp only
        rw [HomotopyGroup.mapHomOfEq_apply]
        exact ih k a₀ q
      have hB :
          homotopyGroupSingularMulEquiv n
              (TopCat.of (LoopSpace Y (f x))) (Path.refl (f x))
              (HomotopyGroup.mapHomOfEq
                (ContinuousMap.strictLoopMap f.hom x) hb n (LX.symm a)) =
            SSet.KanComplex.π.map s hs (n + 1)
              (homotopyGroupSingularMulEquiv n
                (TopCat.of (LoopSpace X x)) (Path.refl x) (LX.symm a)) :=
        ihEq g (Path.refl x) (Path.refl (f x)) hb (LX.symm a)
      have hD (r : SSet.KanComplex.π (n + 1)
          (SSet.loopSpace KX sx) zX) :
          DY.symm (SSet.KanComplex.π.map lmap hl (n + 1) r) =
            SSet.KanComplex.π.map (TopCat.toSSet.map f) rfl (n + 2)
              (DX.symm r) := by
        apply DY.injective
        rw [DY.apply_symm_apply]
        change SSet.KanComplex.π.mapHom lmap hl n r =
          DY (SSet.KanComplex.π.mapHom
            (TopCat.toSSet.map f) rfl (n + 1) (DX.symm r))
        calc
          SSet.KanComplex.π.mapHom lmap hl n r =
              SSet.KanComplex.π.mapHom lmap hl n
                (DX (DX.symm r)) := by rw [DX.apply_symm_apply]
          _ = DY (SSet.KanComplex.π.mapHom
              (TopCat.toSSet.map f) rfl (n + 1) (DX.symm r)) :=
            SSet.loopConnectingMulEquiv_naturality
              (TopCat.toSSet.map f) rfl n (DX.symm r)
      simp only [homotopyGroupSingularMulEquiv]
      calc
        DY.symm
            (singularLoopHomotopyGroupMulEquiv n Y (f x)
              (homotopyGroupSingularMulEquiv n
                (TopCat.of (LoopSpace Y (f x))) (Path.refl (f x))
                (LY.symm (HomotopyGroup.map f.hom a)))) =
          DY.symm
            (singularLoopHomotopyGroupMulEquiv n Y (f x)
              (homotopyGroupSingularMulEquiv n
                (TopCat.of (LoopSpace Y (f x))) (Path.refl (f x))
                (HomotopyGroup.mapHomOfEq
                  (ContinuousMap.strictLoopMap f.hom x) hb n (LX.symm a)))) := by
            rw [hA]
        _ = DY.symm
            (singularLoopHomotopyGroupMulEquiv n Y (f x)
              (SSet.KanComplex.π.map s hs (n + 1)
                (homotopyGroupSingularMulEquiv n
                  (TopCat.of (LoopSpace X x)) (Path.refl x)
                  (LX.symm a)))) := by
            rw [hB]
        _ = DY.symm
            (SSet.KanComplex.π.map lmap hl (n + 1)
              (singularLoopHomotopyGroupMulEquiv n X x
                (homotopyGroupSingularMulEquiv n
                  (TopCat.of (LoopSpace X x)) (Path.refl x)
                  (LX.symm a)))) := by
            apply congrArg DY.symm
            exact singularLoopHomotopyGroupMulEquiv_naturality
              f x n _
        _ = _ := by
          exact hD
            (singularLoopHomotopyGroupMulEquiv n X x
              (homotopyGroupSingularMulEquiv n
                (TopCat.of (LoopSpace X x)) (Path.refl x)
                (LX.symm a)))

/-- Change basepoint in positive cube-based homotopy groups along a path. -/
noncomputable def homotopyGroupBasepointChangeMulEquiv
    (n : ℕ) (X : TopCat.{u}) {x y : X} (p : _root_.Path x y) :
    HomotopyGroup.Pi (n + 1) X x ≃*
      HomotopyGroup.Pi (n + 1) X y := by
  let K := TopCat.toSSet.obj X
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  exact (homotopyGroupSingularMulEquiv n X x).trans
    ((SSet.KanComplex.π.actionMulEquiv (m := n)
      (TopCat.singularPathHom X p)).trans
        (homotopyGroupSingularMulEquiv n X y).symm)

/-- The cube-to-singular comparison identifies topological basepoint change
with the fundamental-groupoid action on simplicial homotopy groups. -/
theorem homotopyGroupSingularMulEquiv_basepointChange
    (n : ℕ) (X : TopCat.{u}) {x y : X} (p : _root_.Path x y)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    let K := TopCat.toSSet.obj X
    letI : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
    homotopyGroupSingularMulEquiv n X y
        (homotopyGroupBasepointChangeMulEquiv n X p a) =
      SSet.KanComplex.π.action (TopCat.singularPathHom X p)
        (homotopyGroupSingularMulEquiv n X x a) := by
  dsimp only
  let K := TopCat.toSSet.obj X
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  simp only [homotopyGroupBasepointChangeMulEquiv,
    MulEquiv.trans_apply, SSet.KanComplex.π.actionMulEquiv_apply,
    MulEquiv.apply_symm_apply]

/-- Change of basepoint along the reflexive path is the identity. -/
@[simp]
theorem homotopyGroupBasepointChangeMulEquiv_refl
    (n : ℕ) (X : TopCat.{u}) (x : X) :
    homotopyGroupBasepointChangeMulEquiv n X (_root_.Path.refl x) =
      MulEquiv.refl (HomotopyGroup.Pi (n + 1) X x) := by
  ext a
  let K := TopCat.toSSet.obj X
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  simp only [homotopyGroupBasepointChangeMulEquiv,
    TopCat.singularPathHom_refl,
    SSet.KanComplex.π.actionMulEquiv_id,
    MulEquiv.trans_apply, MulEquiv.refl_apply,
    MulEquiv.symm_apply_apply]

/-- Change of basepoint preserves source-first path composition. -/
theorem homotopyGroupBasepointChangeMulEquiv_trans
    (n : ℕ) (X : TopCat.{u}) {x y z : X}
    (p : _root_.Path x y) (q : _root_.Path y z) :
    homotopyGroupBasepointChangeMulEquiv n X (p.trans q) =
      (homotopyGroupBasepointChangeMulEquiv n X p).trans
        (homotopyGroupBasepointChangeMulEquiv n X q) := by
  ext a
  let K := TopCat.toSSet.obj X
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  simp only [homotopyGroupBasepointChangeMulEquiv,
    TopCat.singularPathHom_trans,
    SSet.KanComplex.π.actionMulEquiv_comp,
    MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

/-- The cube-to-singular comparison is natural for a map preserving the
selected basepoint by a specified equality. -/
theorem homotopyGroupSingularMulEquiv_naturality
    {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y)
    {x : X} {y : Y} (h : f x = y)
    (a : HomotopyGroup.Pi (n + 1) X x) :
  let KX := TopCat.toSSet.obj X
  let KY := TopCat.toSSet.obj Y
  let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
  let hs : (TopCat.toSSet.map f).app _
      (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm y := by
    change (TopCat.toSSetObj₀Equiv (X := Y)).symm (f x) =
      (TopCat.toSSetObj₀Equiv (X := Y)).symm y
    exact congrArg (TopCat.toSSetObj₀Equiv (X := Y)).symm h
  homotopyGroupSingularMulEquiv n Y y
      (HomotopyGroup.mapHomOfEq f.hom h n a) =
    SSet.KanComplex.π.map (TopCat.toSSet.map f) hs (n + 1)
      (homotopyGroupSingularMulEquiv n X x a) := by
  cases h
  dsimp only
  rw [HomotopyGroup.mapHomOfEq_apply]
  exact homotopyGroupSingularMulEquiv_naturality_image n f x a

/-- Naturality of the comparison for the identity map. -/
theorem homotopyGroupSingularMulEquiv_id
    (n : ℕ) (X : TopCat.{u}) (x : X)
    (a : HomotopyGroup.Pi (n + 1) X x) :
  let K := TopCat.toSSet.obj X
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  homotopyGroupSingularMulEquiv n X x
      (HomotopyGroup.mapHomOfEq (ContinuousMap.id X) rfl n a) =
    SSet.KanComplex.π.map (TopCat.toSSet.map (𝟙 X)) rfl (n + 1)
      (homotopyGroupSingularMulEquiv n X x a) := by
  exact homotopyGroupSingularMulEquiv_naturality n (𝟙 X) rfl a

/-- Naturality of the comparison for source-first composition. -/
theorem homotopyGroupSingularMulEquiv_comp
    {X Y Z : TopCat.{u}} (n : ℕ)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z)
    (hfg : (g.hom.comp f.hom) x = z)
    (a : HomotopyGroup.Pi (n + 1) X x) :
  let KX := TopCat.toSSet.obj X
  let KZ := TopCat.toSSet.obj Z
  let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KZ := TopCat.toSSet_obj_kanComplex Z
  let hsfg : (TopCat.toSSet.map f ≫ TopCat.toSSet.map g).app _
      (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm z := by
    change (TopCat.toSSetObj₀Equiv (X := Z)).symm (g (f x)) =
      (TopCat.toSSetObj₀Equiv (X := Z)).symm z
    exact congrArg (TopCat.toSSetObj₀Equiv (X := Z)).symm hfg
  homotopyGroupSingularMulEquiv n Z z
      (HomotopyGroup.mapHomOfEq (g.hom.comp f.hom) hfg n a) =
    SSet.KanComplex.π.map
      (TopCat.toSSet.map f ≫ TopCat.toSSet.map g) hsfg (n + 1)
      (homotopyGroupSingularMulEquiv n X x a) := by
  dsimp only
  let KX := TopCat.toSSet.obj X
  let KY := TopCat.toSSet.obj Y
  let KZ := TopCat.toSSet.obj Z
  let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
  let _ : SSet.KanComplex KZ := TopCat.toSSet_obj_kanComplex Z
  let hsf : (TopCat.toSSet.map f).app _
      (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm y := by
    exact congrArg (TopCat.toSSetObj₀Equiv (X := Y)).symm hf
  let hsg : (TopCat.toSSet.map g).app _
      (TopCat.toSSetObj₀Equiv.symm y) =
      TopCat.toSSetObj₀Equiv.symm z := by
    exact congrArg (TopCat.toSSetObj₀Equiv (X := Z)).symm hg
  let hsfg : (TopCat.toSSet.map f ≫ TopCat.toSSet.map g).app _
      (TopCat.toSSetObj₀Equiv.symm x) =
      TopCat.toSSetObj₀Equiv.symm z := by
    change (TopCat.toSSetObj₀Equiv (X := Z)).symm (g (f x)) =
      (TopCat.toSSetObj₀Equiv (X := Z)).symm z
    exact congrArg (TopCat.toSSetObj₀Equiv (X := Z)).symm hfg
  rw [HomotopyGroup.mapHomOfEq_comp f.hom g.hom hf hg hfg]
  rw [homotopyGroupSingularMulEquiv_naturality n g hg]
  rw [homotopyGroupSingularMulEquiv_naturality n f hf]
  exact (SSet.KanComplex.π.map_comp_apply
    (TopCat.toSSet.map f) (TopCat.toSSet.map g)
    hsf hsg hsfg (homotopyGroupSingularMulEquiv n X x a)).symm

/-- Change of basepoint commutes with continuous maps. -/
theorem homotopyGroupBasepointChangeMulEquiv_naturality
    {X Y : TopCat.{u}} (n : ℕ) (f : X ⟶ Y)
    {x y : X} (p : _root_.Path x y)
    (a : HomotopyGroup.Pi (n + 1) X x) :
  HomotopyGroup.map f.hom
      (homotopyGroupBasepointChangeMulEquiv n X p a) =
    homotopyGroupBasepointChangeMulEquiv n Y
      (p.map f.hom.continuous) (HomotopyGroup.map f.hom a) := by
  let KX := TopCat.toSSet.obj X
  let KY := TopCat.toSSet.obj Y
  let _ : SSet.KanComplex KX := TopCat.toSSet_obj_kanComplex X
  let _ : SSet.KanComplex KY := TopCat.toSSet_obj_kanComplex Y
  apply (homotopyGroupSingularMulEquiv n Y (f y)).injective
  rw [homotopyGroupSingularMulEquiv_naturality_image]
  rw [homotopyGroupSingularMulEquiv_basepointChange]
  rw [homotopyGroupSingularMulEquiv_basepointChange]
  rw [homotopyGroupSingularMulEquiv_naturality_image]
  rw [← TopCat.singularPathHom_map]
  exact SSet.KanComplex.π.action_naturality
    (TopCat.toSSet.map f) (TopCat.singularPathHom X p)
    (homotopyGroupSingularMulEquiv n X x a)

/-- In degree one, change of basepoint is conjugation by the ordinary path
class in the fundamental groupoid. -/
theorem homotopyGroupBasepointChangeMulEquiv_piOne
    (X : TopCat.{u}) {x y : X} (p : _root_.Path x y)
    (a : HomotopyGroup.Pi 1 X x) :
  HomotopyGroup.pi1MulEquivFundamentalGroup
      (homotopyGroupBasepointChangeMulEquiv 0 X p a) =
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
      (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
  let K := TopCat.toSSet.obj X
  let _ : SSet.KanComplex K := TopCat.toSSet_obj_kanComplex X
  have hconj
      (r : CategoryTheory.End
        (SSet.FundamentalGroupoid.mk
          (TopCat.toSSetObj₀Equiv.symm x))) :
      TopCat.singularFundamentalGroupoidEndMulEquiv X y
          ((CategoryTheory.asIso (TopCat.singularPathHom X p)).conj r) =
        FundamentalGroup.fundamentalGroupMulEquivOfPath p
          (TopCat.singularFundamentalGroupoidEndMulEquiv X x r) := by
    let sx := TopCat.toSSetObj₀Equiv.symm x
    let sy := TopCat.toSSetObj₀Equiv.symm y
    let F := TopCat.singularFundamentalGroupoidFunctor X
    let Ax := SSet.FundamentalGroupoid.mk sx
    let Ay := SSet.FundamentalGroupoid.mk sy
    let hx : F.obj Ax = _root_.FundamentalGroupoid.mk x :=
      (TopCat.singularFundamentalGroupoidFunctor_obj_mk X sx).trans
        (congrArg _root_.FundamentalGroupoid.mk
          ((TopCat.toSSetObj₀Equiv (X := X)).apply_symm_apply x))
    let hy : F.obj Ay = _root_.FundamentalGroupoid.mk y :=
      (TopCat.singularFundamentalGroupoidFunctor_obj_mk X sy).trans
        (congrArg _root_.FundamentalGroupoid.mk
          ((TopCat.toSSetObj₀Equiv (X := X)).apply_symm_apply y))
    let q := TopCat.singularPathHom X p
    let e := (TopCat.toSSetObjEdgeEquiv
      (X := X) (x := x) (y := y)).symm
        ((TopCat.pathEquiv (X := X) (x := x) (y := y)).symm p)
    have hp (t) : TopCat.pathEquiv (TopCat.singularEdgePath e) t = p t := by
      have he :
          (TopCat.toSSetObjEdgeEquiv (X := X) (x := x) (y := y)) e =
            (TopCat.pathEquiv (X := X) (x := x) (y := y)).symm p :=
        (TopCat.toSSetObjEdgeEquiv (X := X)
          (x := x) (y := y)).apply_symm_apply _
      have hpCat : TopCat.singularEdgePath e =
          (TopCat.pathEquiv (X := X) (x := x) (y := y)).symm p :=
        (TopCat.singularEdgePath_of_canonical
          (x := x) (y := y) e).trans he
      calc
        TopCat.pathEquiv (TopCat.singularEdgePath e) t =
            TopCat.pathEquiv
              ((TopCat.pathEquiv
                (X := X) (x := x) (y := y)).symm p) t :=
          congrArg (fun z : X.Path x y => TopCat.pathEquiv z t) hpCat
        _ = p t := congrArg (fun z : _root_.Path x y => z t)
          ((TopCat.pathEquiv (X := X)
            (x := x) (y := y)).apply_symm_apply p)
    have hMap :=
      TopCat.singularFundamentalGroupoidFunctor_map_homMk X e
    rw [Path.Homotopic.Quotient.mk_cast] at hMap
    have hCast := Path.Homotopic.Quotient.cast_heq
      (TopCat.counit_realizedVertex sx)
      (TopCat.counit_realizedVertex sy)
      (γ := Path.Homotopic.Quotient.mk
        (TopCat.pathEquiv (TopCat.singularEdgePath e)))
    have hq : F.map q ≍ Path.Homotopic.Quotient.mk p := by
      dsimp only [q, TopCat.singularPathHom]
      exact (heq_of_eq hMap).trans
        (hCast.trans (_root_.Path.Homotopic.hpath_hext hp))
    have hbridge :
        eqToHom hx.symm ≫ F.map q ≫ eqToHom hy =
          Path.Homotopic.Quotient.mk p := by
      symm
      apply (CategoryTheory.conj_eqToHom_iff_heq
        (Path.Homotopic.Quotient.mk p) (F.map q)
        hx.symm hy.symm).2
      exact hq.symm
    let α : _root_.FundamentalGroupoid.mk x ≅
        _root_.FundamentalGroupoid.mk y :=
      ((eqToIso hx).symm.trans
        (F.mapIso (CategoryTheory.asIso q))).trans (eqToIso hy)
    have hα : α =
        (CategoryTheory.Groupoid.isoEquivHom
          (_root_.FundamentalGroupoid.mk x)
          (_root_.FundamentalGroupoid.mk y)).symm
            (Path.Homotopic.Quotient.mk p) := by
      apply CategoryTheory.Iso.ext
      dsimp only [α, CategoryTheory.Iso.trans_hom,
        CategoryTheory.Iso.symm_hom,
        CategoryTheory.Functor.mapIso_hom,
        CategoryTheory.Groupoid.isoEquivHom]
      change (eqToHom hx.symm ≫ F.map q) ≫ eqToHom hy =
        Path.Homotopic.Quotient.mk p
      rw [CategoryTheory.Category.assoc]
      exact hbridge
    change TopCat.singularFundamentalGroupoidEndMulEquiv X y
        ((CategoryTheory.asIso q).conj r) =
      ((CategoryTheory.Groupoid.isoEquivHom
        (_root_.FundamentalGroupoid.mk x)
        (_root_.FundamentalGroupoid.mk y)).symm
          (Path.Homotopic.Quotient.mk p)).conj
        (TopCat.singularFundamentalGroupoidEndMulEquiv X x r)
    rw [← hα]
    change (eqToIso hy).conj
        (F.mapEnd Ay ((CategoryTheory.asIso q).conj r)) =
      α.conj ((eqToIso hx).conj (F.mapEnd Ax r))
    have hMapConj :
        F.mapEnd Ay ((CategoryTheory.asIso q).conj r) =
          (F.mapIso (CategoryTheory.asIso q)).conj (F.mapEnd Ax r) := by
      apply End.ext
      exact F.map_conj (CategoryTheory.asIso q) r
    rw [hMapConj]
    dsimp only [α]
    simp only [CategoryTheory.Iso.trans_conj,
      CategoryTheory.Iso.symm_self_conj]
  rw [← homotopyGroupSingularMulEquiv_piOne X y]
  rw [homotopyGroupSingularMulEquiv_basepointChange]
  rw [SSet.KanComplex.piOneMulEquivFundamentalGroupoidEnd_action]
  rw [hconj]
  rw [homotopyGroupSingularMulEquiv_piOne]

end TopCat

/-!
# The universal transported degree-two Hurewicz homomorphism

The forward composite uses the original cube-to-native singular homotopy
comparison, the original native normalized Hurewicz homomorphism, and the
original normalization inclusion on homology. Integral singular chains of
`Y` are definitionally the unnormalized integral chains of `TopCat.toSSet.obj Y`.

The four declarations below concern the constructed forward map, its actual
native representative formula and pointed naturality. Equality with the fixed
sphere-generator formula is a separate geometric calibration obligation.
-/


open CategoryTheory.Limits

attribute [local instance] TopCat.toSSet_obj_kanComplex

namespace TopCat

/-- The actual transported forward homomorphism for every based topological
space, using the original normalized-to-singular homology inclusion. -/
noncomputable def transportedDegreeTwoHurewiczMulHom
    (Y : TopCat.{u}) (y : Y) :
    HomotopyGroup.Pi 2 Y y →*
      Multiplicative (AlgebraicTopology.singularIntegralHomology 2 Y) :=
  (((TopCat.toSSet.obj Y).normalizedHomologyIso (C := AddCommGrpCat.{u})
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})
      2).hom.hom.toMultiplicative).comp
    ((SSet.degreeTwoHurewiczElementMulHom (TopCat.toSSetObj₀Equiv.symm y)).comp
      (TopCat.homotopyGroupSingularMulEquiv 1 Y y).toMonoidHom)

/-- Exact forward-map triangle with the original cube/singular comparison,
the original native Hurewicz map and the actual normalization inclusion. -/
@[simp]
theorem transportedDegreeTwoHurewiczMulHom_apply
    (Y : TopCat.{u}) (y : Y) (a : HomotopyGroup.Pi 2 Y y) :
    Multiplicative.toAdd (transportedDegreeTwoHurewiczMulHom Y y a) =
      HomologicalComplex.homologyMap
        ((TopCat.toSSet.obj Y).fromNormalizedChainComplex
          (C := AddCommGrpCat.{u})
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2
        (Multiplicative.toAdd
          (SSet.degreeTwoHurewiczElementMulHom (TopCat.toSSetObj₀Equiv.symm y)
            (TopCat.homotopyGroupSingularMulEquiv 1 Y y a))) :=
  rfl

/-- An original native pointed singular representative has its original
positive normalized class carried through the actual normalization inclusion. -/
theorem transportedDegreeTwoHurewiczMulHom_singular_mk
    (Y : TopCat.{u}) (y : Y)
    (p : (TopCat.toSSet.obj Y).PtSimplex 2 (TopCat.toSSetObj₀Equiv.symm y)) :
    Multiplicative.toAdd
        (transportedDegreeTwoHurewiczMulHom Y y
          ((TopCat.homotopyGroupSingularMulEquiv 1 Y y).symm
            (SSet.KanComplex.π.mk p))) =
      HomologicalComplex.homologyMap
        ((TopCat.toSSet.obj Y).fromNormalizedChainComplex
          (C := AddCommGrpCat.{u})
          (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2
        (SSet.pointedTwoHomologyClass p (ULift.up (1 : ℤ))) := by
  rw [transportedDegreeTwoHurewiczMulHom_apply,
    MulEquiv.apply_symm_apply, SSet.degreeTwoHurewiczElementMulHom_mk]
  rfl

/-- Pointed naturality of the constructed forward homomorphism, using a
literal equality relating the original selected source and target points. -/
theorem transportedDegreeTwoHurewiczMulHom_naturality
    {Y Z : TopCat.{u}} (f : Y ⟶ Z) {y : Y} {z : Z} (h : f y = z)
    (a : HomotopyGroup.Pi 2 Y y) :
    Multiplicative.toAdd
        (transportedDegreeTwoHurewiczMulHom Z z
          (HomotopyGroup.mapHomOfEq f.hom h 1 a)) =
      (AlgebraicTopology.singularIntegralHomologyFunctor 2).map f
        (Multiplicative.toAdd (transportedDegreeTwoHurewiczMulHom Y y a)) := by
  let hs : (TopCat.toSSet.map f).app _ (TopCat.toSSetObj₀Equiv.symm y) =
      TopCat.toSSetObj₀Equiv.symm z := by
    change (TopCat.toSSetObj₀Equiv (X := Z)).symm (f y) =
      (TopCat.toSSetObj₀Equiv (X := Z)).symm z
    exact congrArg (TopCat.toSSetObj₀Equiv (X := Z)).symm h
  let q := TopCat.homotopyGroupSingularMulEquiv 1 Y y a
  have htop :
      TopCat.homotopyGroupSingularMulEquiv 1 Z z
          (HomotopyGroup.mapHomOfEq f.hom h 1 a) =
        SSet.KanComplex.π.map (TopCat.toSSet.map f) hs 2 q :=
    TopCat.homotopyGroupSingularMulEquiv_naturality 1 f h a
  have hnative := ConcreteCategory.congr_hom
    (SSet.degreeTwoHurewiczFn_naturality (TopCat.toSSet.map f) hs q)
    (ULift.up (1 : ℤ))
  change Multiplicative.toAdd
      (SSet.degreeTwoHurewiczElementMulHom (TopCat.toSSetObj₀Equiv.symm z)
        (SSet.KanComplex.π.map (TopCat.toSSet.map f) hs 2 q)) =
    HomologicalComplex.homologyMap
      (SSet.normalizedChainComplexMap (TopCat.toSSet.map f)
        (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2
      (Multiplicative.toAdd
        (SSet.degreeTwoHurewiczElementMulHom (TopCat.toSSetObj₀Equiv.symm y) q)) at hnative
  have hnormalization :
      HomologicalComplex.homologyMap
          (SSet.normalizedChainComplexMap (TopCat.toSSet.map f)
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2 ≫
        HomologicalComplex.homologyMap
          ((TopCat.toSSet.obj Z).fromNormalizedChainComplex
            (C := AddCommGrpCat.{u})
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2 =
      HomologicalComplex.homologyMap
          ((TopCat.toSSet.obj Y).fromNormalizedChainComplex
            (C := AddCommGrpCat.{u})
            (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u})) 2 ≫
        (AlgebraicTopology.singularIntegralHomologyFunctor 2).map f :=
    (SSet.homologyNatIso_fromNormalizedChainComplex (C := AddCommGrpCat.{u})
      (AlgebraicTopology.singularIntegralCoefficients : AddCommGrpCat.{u}) 2).hom.naturality
        (TopCat.toSSet.map f)
  rw [transportedDegreeTwoHurewiczMulHom_apply, htop,
    hnative, transportedDegreeTwoHurewiczMulHom_apply]
  exact ConcreteCategory.congr_hom hnormalization
    (Multiplicative.toAdd
      (SSet.degreeTwoHurewiczElementMulHom (TopCat.toSSetObj₀Equiv.symm y) q))

end TopCat
