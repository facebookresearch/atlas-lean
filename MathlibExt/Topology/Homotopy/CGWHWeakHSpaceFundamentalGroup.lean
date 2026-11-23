/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Homotopy.CGWHHSpaceFundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Fundamental groups of weak-unit native CGWH H-spaces

A categorical CGWH multiplication need not send the selected unit pair
strictly to the selected unit.  This file allows the product point to be
joined to the unit by a chosen root path.  Left and right unit homotopies are
required to trace that root path at the unit, up to endpoint-fixed path
homotopy.

Pointwise multiplication first lands in the fundamental group at the product
point and is then transported to the selected unit along the root path.
Naturality of evaluated homotopies supplies the unit laws, while the
basepoint-change equivalence preserves multiplication; Eckmann--Hilton then
gives a named commutative-group structure.  No global instance or ordinary
raw-product `HSpace` is installed.  No classifying-space, additive
`S⁻¹S`, kernel, homology, plus-construction, or `Q = +` claim is made.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits unitInterval

universe u v

namespace CGWH

/-- The path traced by a left unit homotopy at the selected point, cast to
start at the categorical product of the unit with itself. -/
noncomputable def hspaceLeftUnitPath (X : CGWH.{u, v})
    (mul : X ⨯ X ⟶ X) (e : X)
    (H : ContinuousMap.Homotopy
      (CGWH.cgwhToTop.map (hspaceLeftUnitMap X mul e)).hom
      (ContinuousMap.id X)) :
    Path (mul (prodPoint X X e e)) e :=
  (H.evalAt e).cast (hspaceLeftUnitMap_apply X mul e e).symm rfl

/-- The path traced by a right unit homotopy at the selected point, cast to
start at the categorical product of the unit with itself. -/
noncomputable def hspaceRightUnitPath (X : CGWH.{u, v})
    (mul : X ⨯ X ⟶ X) (e : X)
    (H : ContinuousMap.Homotopy
      (CGWH.cgwhToTop.map (hspaceRightUnitMap X mul e)).hom
      (ContinuousMap.id X)) :
    Path (mul (prodPoint X X e e)) e :=
  (H.evalAt e).cast (hspaceRightUnitMap_apply X mul e e).symm rfl

/-- Native CGWH H-space data with a weak unit.  The chosen root path joins
the categorical product of the unit pair to the selected unit, and both unit
homotopies trace that same path class at the unit. -/
structure WeakHSpaceData (X : CGWH.{u, v}) where
  /-- Native categorical multiplication. -/
  mul : X ⨯ X ⟶ X
  /-- Selected unit point. -/
  e : X
  /-- Root path from the categorical product of the unit pair to the unit. -/
  rootPath : Path (mul (prodPoint X X e e)) e
  /-- Left unit homotopy on the underlying space. -/
  leftUnit : ContinuousMap.Homotopy
    (CGWH.cgwhToTop.map (hspaceLeftUnitMap X mul e)).hom
    (ContinuousMap.id X)
  /-- Right unit homotopy on the underlying space. -/
  rightUnit : ContinuousMap.Homotopy
    (CGWH.cgwhToTop.map (hspaceRightUnitMap X mul e)).hom
    (ContinuousMap.id X)
  /-- At the unit, the left unit homotopy represents the chosen root path. -/
  leftUnit_root :
    (hspaceLeftUnitPath X mul e leftUnit).Homotopic rootPath
  /-- At the unit, the right unit homotopy represents the chosen root path. -/
  rightUnit_root :
    (hspaceRightUnitPath X mul e rightUnit).Homotopic rootPath

namespace WeakHSpaceData

variable {X : CGWH.{u, v}} (H : WeakHSpaceData X)

/-- The product point of the two selected units. -/
abbrev mulUnit : X := H.mul (prodPoint X X H.e H.e)

/-- A loop at the selected unit regarded as a CGWH morphism from the lifted
compact interval. -/
def pathHom (p : Path H.e H.e) :
    HSpaceData.liftedUnitInterval.{u, v} ⟶ X :=
  ConcreteCategory.ofHom
    ⟨fun t ↦ p t.down, p.continuous.comp continuous_uliftDown⟩

/-- Pair two selected-unit loops through the categorical CGWH product. -/
noncomputable def pathPair (p q : Path H.e H.e) :
    HSpaceData.liftedUnitInterval.{u, v} ⟶ X ⨯ X :=
  Limits.prod.lift (pathHom H p) (pathHom H q)

@[simp]
theorem pathPair_apply (p q : Path H.e H.e) (t : unitInterval) :
    pathPair H p q (ULift.up t) = prodPoint X X (p t) (q t) := by
  rw [pathPair, prod_lift_apply]
  rfl

/-- Raw pointwise multiplication of selected-unit loops; its basepoint is
the categorical product point `mulUnit`. -/
noncomputable def rawPathMul (p q : Path H.e H.e) :
    Path H.mulUnit H.mulUnit where
  toFun t := (pathPair H p q ≫ H.mul) (ULift.up t)
  continuous_toFun :=
    (ConcreteCategory.hom (pathPair H p q ≫ H.mul)).continuous.comp
      continuous_uliftUp
  source' := by
    rw [CategoryTheory.comp_apply, pathPair_apply, p.source, q.source]
  target' := by
    rw [CategoryTheory.comp_apply, pathPair_apply, p.target, q.target]

@[simp]
theorem rawPathMul_apply (p q : Path H.e H.e) (t : unitInterval) :
    rawPathMul H p q t = H.mul (prodPoint X X (p t) (q t)) := by
  change (pathPair H p q ≫ H.mul) (ULift.up t) = _
  rw [CategoryTheory.comp_apply, pathPair_apply]

/-- A selected-unit path homotopy regarded as a CGWH morphism from the
lifted compact square. -/
def pathHomotopyHom
    {p₀ p₁ : Path H.e H.e} (P : Path.Homotopy p₀ p₁) :
    HSpaceData.liftedUnitSquare.{u, v} ⟶ X :=
  ConcreteCategory.ofHom
    ⟨fun st ↦ P st.down, P.continuous.comp continuous_uliftDown⟩

/-- Pair two selected-unit path homotopies through the categorical product. -/
noncomputable def pathHomotopyPair
    {p₀ p₁ q₀ q₁ : Path H.e H.e}
    (P : Path.Homotopy p₀ p₁) (Q : Path.Homotopy q₀ q₁) :
    HSpaceData.liftedUnitSquare.{u, v} ⟶ X ⨯ X :=
  Limits.prod.lift (pathHomotopyHom H P) (pathHomotopyHom H Q)

@[simp]
theorem pathHomotopyPair_apply
    {p₀ p₁ q₀ q₁ : Path H.e H.e}
    (P : Path.Homotopy p₀ p₁) (Q : Path.Homotopy q₀ q₁)
    (st : unitInterval × unitInterval) :
    pathHomotopyPair H P Q (ULift.up st) =
      prodPoint X X (P st) (Q st) := by
  rw [pathHomotopyPair, prod_lift_apply]
  rfl

/-- Raw pointwise multiplication respects based path homotopies. -/
noncomputable def rawPathMulHomotopy
    {p₀ p₁ q₀ q₁ : Path H.e H.e}
    (P : Path.Homotopy p₀ p₁) (Q : Path.Homotopy q₀ q₁) :
    Path.Homotopy (rawPathMul H p₀ q₀) (rawPathMul H p₁ q₁) where
  toFun st := (pathHomotopyPair H P Q ≫ H.mul) (ULift.up st)
  continuous_toFun :=
    (ConcreteCategory.hom (pathHomotopyPair H P Q ≫ H.mul)).continuous.comp
      continuous_uliftUp
  map_zero_left t := by
    change (pathHomotopyPair H P Q ≫ H.mul) (ULift.up (0, t)) =
      rawPathMul H p₀ q₀ t
    rw [CategoryTheory.comp_apply, pathHomotopyPair_apply,
      P.apply_zero, Q.apply_zero, rawPathMul_apply]
    rfl
  map_one_left t := by
    change (pathHomotopyPair H P Q ≫ H.mul) (ULift.up (1, t)) =
      rawPathMul H p₁ q₁ t
    rw [CategoryTheory.comp_apply, pathHomotopyPair_apply,
      P.apply_one, Q.apply_one, rawPathMul_apply]
    rfl
  prop' s t ht := by
    rcases ht with rfl | rfl
    · change (pathHomotopyPair H P Q ≫ H.mul) (ULift.up (s, 0)) =
        rawPathMul H p₀ q₀ 0
      rw [CategoryTheory.comp_apply, pathHomotopyPair_apply,
        P.source, Q.source]
      exact (rawPathMul H p₀ q₀).source.symm
    · change (pathHomotopyPair H P Q ≫ H.mul) (ULift.up (s, 1)) =
        rawPathMul H p₀ q₀ 1
      rw [CategoryTheory.comp_apply, pathHomotopyPair_apply,
        P.target, Q.target]
      exact (rawPathMul H p₀ q₀).target.symm

/-- Raw pointwise multiplication descended to path classes, before
basepoint transport. -/
noncomputable def rawFundamentalMul
    (p q : FundamentalGroup X H.e) : FundamentalGroup X H.mulUnit :=
  FundamentalGroup.fromPath (Quotient.map₂ (rawPathMul H)
    (fun _ _ hp _ _ hq ↦ Nonempty.map2 (rawPathMulHomotopy H) hp hq) p.asHom q.asHom)

@[simp]
theorem rawFundamentalMul_mk (p q : Path H.e H.e) :
    rawFundamentalMul H
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (rawPathMul H p q)) :=
  rfl

/-- Basepoint change from the categorical product point to the selected
unit. -/
noncomputable def basepointMulEquiv :
    FundamentalGroup X H.mulUnit ≃* FundamentalGroup X H.e :=
  FundamentalGroup.fundamentalGroupMulEquivOfPath H.rootPath

/-- Pointwise multiplication transported to the selected basepoint. -/
noncomputable def fundamentalMul
    (p q : FundamentalGroup X H.e) : FundamentalGroup X H.e :=
  H.basepointMulEquiv (rawFundamentalMul H p q)

/-- Representative formula: raw multiplication is conjugated by the chosen
root path. -/
@[simp]
theorem fundamentalMul_mk (p q : Path H.e H.e) :
    fundamentalMul H
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk
        (H.rootPath.symm.trans ((rawPathMul H p q).trans H.rootPath))) :=
  rfl

/-- The left unit map sends the selected point to `mulUnit`. -/
theorem leftUnitMap_unit :
    hspaceLeftUnitMap X H.mul H.e H.e = H.mulUnit :=
  hspaceLeftUnitMap_apply X H.mul H.e H.e

/-- The right unit map sends the selected point to `mulUnit`. -/
theorem rightUnitMap_unit :
    hspaceRightUnitMap X H.mul H.e H.e = H.mulUnit :=
  hspaceRightUnitMap_apply X H.mul H.e H.e

/-- The loop obtained by left multiplying a loop by the selected point. -/
noncomputable def leftMappedPath (p : Path H.e H.e) :
    Path H.mulUnit H.mulUnit :=
  (p.map (CGWH.cgwhToTop.map
    (hspaceLeftUnitMap X H.mul H.e)).hom.continuous).cast
      H.leftUnitMap_unit.symm H.leftUnitMap_unit.symm

/-- The loop obtained by right multiplying a loop by the selected point. -/
noncomputable def rightMappedPath (p : Path H.e H.e) :
    Path H.mulUnit H.mulUnit :=
  (p.map (CGWH.cgwhToTop.map
    (hspaceRightUnitMap X H.mul H.e)).hom.continuous).cast
      H.rightUnitMap_unit.symm H.rightUnitMap_unit.symm

/-- Raw multiplication by the constant selected point is the mapped loop
for the left unit map. -/
theorem rawPathMul_refl_left (p : Path H.e H.e) :
    rawPathMul H (Path.refl H.e) p = leftMappedPath H p := by
  apply Path.ext
  funext t
  rw [rawPathMul_apply]
  change H.mul (prodPoint X X H.e (p t)) =
    hspaceLeftUnitMap X H.mul H.e (p t)
  rw [hspaceLeftUnitMap_apply]

/-- Raw multiplication by the constant selected point is the mapped loop
for the right unit map. -/
theorem rawPathMul_refl_right (p : Path H.e H.e) :
    rawPathMul H p (Path.refl H.e) = rightMappedPath H p := by
  apply Path.ext
  funext t
  rw [rawPathMul_apply]
  change H.mul (prodPoint X X (p t) H.e) =
    hspaceRightUnitMap X H.mul H.e (p t)
  rw [hspaceRightUnitMap_apply]

/-- The left-unit naturality square after correcting its source endpoint. -/
theorem rawPathMul_refl_left_trans_leftUnitPath
    (p : Path H.e H.e) :
    ((rawPathMul H (Path.refl H.e) p).trans
      (hspaceLeftUnitPath X H.mul H.e H.leftUnit)).Homotopic
      ((hspaceLeftUnitPath X H.mul H.e H.leftUnit).trans p) := by
  let f := (CGWH.cgwhToTop.map
    (hspaceLeftUnitMap X H.mul H.e)).hom
  let unitPath := hspaceLeftUnitPath X H.mul H.e H.leftUnit
  have hs : H.mulUnit = f H.e := H.leftUnitMap_unit.symm
  have h := Path.Homotopic.map_trans_evalAt H.leftUnit p
  have h' := h.pathCast hs rfl
  have hLeft :
      (((p.map f.continuous).trans (H.leftUnit.evalAt H.e)).cast hs rfl) =
        (rawPathMul H (Path.refl H.e) p).trans unitPath := by
    rw [rawPathMul_refl_left]
    apply Path.ext
    rfl
  have hRight :
      (((H.leftUnit.evalAt H.e).trans
        (p.map (ContinuousMap.id X).continuous)).cast hs rfl) =
        unitPath.trans p := by
    apply Path.ext
    rfl
  exact Nonempty.map (fun F ↦ Path.Homotopy.cast F hLeft hRight) h'

/-- The right-unit naturality square after correcting its source endpoint. -/
theorem rawPathMul_refl_right_trans_rightUnitPath
    (p : Path H.e H.e) :
    ((rawPathMul H p (Path.refl H.e)).trans
      (hspaceRightUnitPath X H.mul H.e H.rightUnit)).Homotopic
      ((hspaceRightUnitPath X H.mul H.e H.rightUnit).trans p) := by
  let f := (CGWH.cgwhToTop.map
    (hspaceRightUnitMap X H.mul H.e)).hom
  let unitPath := hspaceRightUnitPath X H.mul H.e H.rightUnit
  have hs : H.mulUnit = f H.e := H.rightUnitMap_unit.symm
  have h := Path.Homotopic.map_trans_evalAt H.rightUnit p
  have h' := h.pathCast hs rfl
  have hLeft :
      (((p.map f.continuous).trans (H.rightUnit.evalAt H.e)).cast hs rfl) =
        (rawPathMul H p (Path.refl H.e)).trans unitPath := by
    rw [rawPathMul_refl_right]
    apply Path.ext
    rfl
  have hRight :
      (((H.rightUnit.evalAt H.e).trans
        (p.map (ContinuousMap.id X).continuous)).cast hs rfl) =
        unitPath.trans p := by
    apply Path.ext
    rfl
  exact Nonempty.map (fun F ↦ Path.Homotopy.cast F hLeft hRight) h'

private theorem transported_left_unit_path (p : Path H.e H.e) :
    (H.rootPath.symm.trans
      ((rawPathMul H (Path.refl H.e) p).trans H.rootPath)).Homotopic p := by
  let raw := rawPathMul H (Path.refl H.e) p
  let unitPath := hspaceLeftUnitPath X H.mul H.e H.leftUnit
  have hNat : (raw.trans unitPath).Homotopic (unitPath.trans p) :=
    H.rawPathMul_refl_left_trans_leftUnitPath p
  have hCore : (raw.trans H.rootPath).Homotopic (H.rootPath.trans p) :=
    (((Path.Homotopic.refl raw).hcomp H.leftUnit_root).symm.trans hNat).trans
      (H.leftUnit_root.hcomp (Path.Homotopic.refl p))
  have hWhisker := (Path.Homotopic.refl H.rootPath.symm).hcomp hCore
  have hAssoc :=
    (Path.Homotopic.trans_assoc H.rootPath.symm H.rootPath p).symm
  have hCancel :=
    (Path.Homotopic.symm_trans H.rootPath).hcomp (Path.Homotopic.refl p)
  exact (hWhisker.trans hAssoc).trans
    (hCancel.trans (Path.Homotopic.refl_trans p))

private theorem transported_right_unit_path (p : Path H.e H.e) :
    (H.rootPath.symm.trans
      ((rawPathMul H p (Path.refl H.e)).trans H.rootPath)).Homotopic p := by
  let raw := rawPathMul H p (Path.refl H.e)
  let unitPath := hspaceRightUnitPath X H.mul H.e H.rightUnit
  have hNat : (raw.trans unitPath).Homotopic (unitPath.trans p) :=
    H.rawPathMul_refl_right_trans_rightUnitPath p
  have hCore : (raw.trans H.rootPath).Homotopic (H.rootPath.trans p) :=
    (((Path.Homotopic.refl raw).hcomp H.rightUnit_root).symm.trans hNat).trans
      (H.rightUnit_root.hcomp (Path.Homotopic.refl p))
  have hWhisker := (Path.Homotopic.refl H.rootPath.symm).hcomp hCore
  have hAssoc :=
    (Path.Homotopic.trans_assoc H.rootPath.symm H.rootPath p).symm
  have hCancel :=
    (Path.Homotopic.symm_trans H.rootPath).hcomp (Path.Homotopic.refl p)
  exact (hWhisker.trans hAssoc).trans
    (hCancel.trans (Path.Homotopic.refl_trans p))

@[simp]
theorem fundamentalMul_one_left (p : FundamentalGroup X H.e) :
    fundamentalMul H 1 p = p := by
  rcases p with ⟨p⟩
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
      apply End.ext
      change Path.Homotopic.Quotient.mk
          (H.rootPath.symm.trans
            ((rawPathMul H (Path.refl H.e) p).trans H.rootPath)) =
        Path.Homotopic.Quotient.mk p
      exact Path.Homotopic.Quotient.eq.mpr (H.transported_left_unit_path p)

@[simp]
theorem fundamentalMul_one_right (p : FundamentalGroup X H.e) :
    fundamentalMul H p 1 = p := by
  rcases p with ⟨p⟩
  induction p using Path.Homotopic.Quotient.ind with
  | mk p =>
      apply End.ext
      change Path.Homotopic.Quotient.mk
          (H.rootPath.symm.trans
            ((rawPathMul H p (Path.refl H.e)).trans H.rootPath)) =
        Path.Homotopic.Quotient.mk p
      exact Path.Homotopic.Quotient.eq.mpr (H.transported_right_unit_path p)

/-- Raw pointwise multiplication commutes strictly with path
concatenation. -/
theorem rawPathMul_trans
    (p₀ p₁ q₀ q₁ : Path H.e H.e) :
    rawPathMul H (p₀.trans p₁) (q₀.trans q₁) =
      (rawPathMul H p₀ q₀).trans (rawPathMul H p₁ q₁) := by
  ext t
  simp only [rawPathMul_apply, Path.trans_apply]
  split_ifs <;> rfl

/-- Raw quotient-level interchange in path-concatenation order. -/
theorem rawFundamentalMul_trans
    (p₀ p₁ q₀ q₁ : FundamentalGroup X H.e) :
    rawFundamentalMul H
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans p₀.asHom p₁.asHom))
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans q₀.asHom q₁.asHom)) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.trans
        (rawFundamentalMul H p₀ q₀).asHom
        (rawFundamentalMul H p₁ q₁).asHom) := by
  rcases p₀ with ⟨p₀⟩
  rcases p₁ with ⟨p₁⟩
  rcases q₀ with ⟨q₀⟩
  rcases q₁ with ⟨q₁⟩
  induction p₀ using Path.Homotopic.Quotient.ind with
  | mk p₀ =>
    induction p₁ using Path.Homotopic.Quotient.ind with
    | mk p₁ =>
      induction q₀ using Path.Homotopic.Quotient.ind with
      | mk q₀ =>
        induction q₁ using Path.Homotopic.Quotient.ind with
        | mk q₁ =>
          apply End.ext
          change Path.Homotopic.Quotient.mk
              (rawPathMul H (p₀.trans p₁) (q₀.trans q₁)) =
            Path.Homotopic.Quotient.mk
              ((rawPathMul H p₀ q₀).trans (rawPathMul H p₁ q₁))
          exact congrArg Path.Homotopic.Quotient.mk
            (rawPathMul_trans H p₀ p₁ q₀ q₁)

/-- Raw Eckmann--Hilton interchange, before basepoint transport. -/
theorem rawFundamentalMul_interchange
    (a b c d : FundamentalGroup X H.e) :
    rawFundamentalMul H (a * b) (c * d) =
      rawFundamentalMul H a c * rawFundamentalMul H b d := by
  rw [FundamentalGroup.mul_def, FundamentalGroup.mul_def,
    FundamentalGroup.mul_def]
  exact rawFundamentalMul_trans H b a d c

/-- Basepoint transport preserves raw interchange. -/
theorem fundamentalMul_interchange
    (a b c d : FundamentalGroup X H.e) :
    fundamentalMul H (a * b) (c * d) =
      fundamentalMul H a c * fundamentalMul H b d := by
  change H.basepointMulEquiv (rawFundamentalMul H (a * b) (c * d)) = _
  rw [rawFundamentalMul_interchange, map_mul]
  rfl

/-- Transported pointwise multiplication is unital. -/
theorem fundamentalMul_isUnital :
    EckmannHilton.IsUnital
      (fun p q : FundamentalGroup X H.e ↦ fundamentalMul H p q) 1 :=
  EckmannHilton.IsUnital.mk
    { left_id := fundamentalMul_one_left H
      right_id := fundamentalMul_one_right H }

/-- Named commutative-group structure on the fundamental group at the weak
H-space unit.  It is deliberately not a global instance. -/
@[instance_reducible]
noncomputable def fundamentalGroupCommGroup :
    CommGroup (FundamentalGroup X H.e) :=
  EckmannHilton.commGroup (fundamentalMul_isUnital H)
    (fundamentalMul_interchange H)

/-- Fundamental-group multiplication at the selected weak H-space unit is
commutative. -/
theorem fundamentalGroup_mul_comm
    (p q : FundamentalGroup X H.e) : p * q = q * p := by
  let _ : CommGroup (FundamentalGroup X H.e) :=
    fundamentalGroupCommGroup H
  exact mul_comm p q

end WeakHSpaceData
end CGWH

end
