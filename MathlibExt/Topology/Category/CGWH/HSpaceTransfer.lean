/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.ProductHomotopy
public import MathlibExt.Topology.Category.CGWH.RealizedProductPoint
public import MathlibExt.Topology.CWComplex.NativeSingularModel
public import MathlibExt.Topology.Homotopy.CGWHWeakHSpaceFundamentalGroup
public import Mathlib.Topology.Homotopy.HSpaces

/-!
# Both whole unit families transferred through the actual pointed model

The multiplication uses the genuine inverse of the ORIGINAL native
product comparison and the actual inverse of the pointed singular
model. Its two unit homotopies use the product inverse family, the
original native unit family, and the original-space inverse family.
All three families retain the original marked point. No continuous
inverse to a raw product comparison is assumed.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory

universe u

namespace CGWH

/-- Point-relative native unit families give weak-unit data with their
actual constant root path. Both traced paths are proved equal to that
root; no further trace witness is supplied. The output records the
original multiplication and original unit as properties. -/
public def HSpaceData.toWeakData {M : CGWH.{u, u}} (H : HSpaceData M) :
    { W : WeakHSpaceData M // W.mul = H.mul ∧ W.e = H.e } := by
  let root : Path (H.mul (prodPoint M M H.e H.e)) H.e :=
    (Path.refl H.e).cast H.mul_e_e rfl
  have hLeft : hspaceLeftUnitPath M H.mul H.e H.left_unit.toHomotopy = root := by
    apply Path.ext
    funext t
    change H.left_unit (t, H.e) = H.e
    exact H.left_unit.eq_snd t (Set.mem_singleton H.e)
  have hRight : hspaceRightUnitPath M H.mul H.e H.right_unit.toHomotopy = root := by
    apply Path.ext
    funext t
    change H.right_unit (t, H.e) = H.e
    exact H.right_unit.eq_snd t (Set.mem_singleton H.e)
  let W : WeakHSpaceData M :=
    { mul := H.mul
      e := H.e
      rootPath := root
      leftUnit := H.left_unit.toHomotopy
      rightUnit := H.right_unit.toHomotopy
      leftUnit_root := by rw [hLeft]
      rightUnit_root := by rw [hRight] }
  exact ⟨W, rfl, rfl⟩

/-- The actual ordinary multiplication obtained from the actual native
operation and the specified genuine product-comparison inverse. -/
public def transferredNativeHSpaceMul
    {X : TopCat.{u}} {x : X} (N : TopCat.NativeSingularPointModel X x)
    (H : HSpaceData (TopCat.nativeSingularSpace X))
    (E : (TopCat.nativeSingularSpace X ⊗ TopCat.nativeSingularSpace X : CGWH.{u, u}) ≃ₕ
      (TopCat.nativeSingularSpace X × TopCat.nativeSingularSpace X)) : C(X × X, X) :=
  N.equiv.toFun.comp ((cgwhToTop.map H.mul).hom.comp
    (E.invFun.comp (N.equiv.invFun.prodMap N.equiv.invFun)))

private def leftNativeAxis (M : CGWH.{u, u}) (m : M) : C(M, (M ⨯ M : CGWH.{u, u})) :=
  (cgwhToTop.map (Limits.prod.lift (constMap M M m) (𝟙 M))).hom

private def rightNativeAxis (M : CGWH.{u, u}) (m : M) : C(M, (M ⨯ M : CGWH.{u, u})) :=
  (cgwhToTop.map (Limits.prod.lift (𝟙 M) (constMap M M m))).hom

private theorem leftNativeAxis_apply (M : CGWH.{u, u}) (m z : M) :
    leftNativeAxis M m z = prodPoint M M m z :=
  prod_lift_apply (constMap M M m) (𝟙 M) z

private theorem rightNativeAxis_apply (M : CGWH.{u, u}) (m z : M) :
    rightNativeAxis M m z = prodPoint M M z m :=
  prod_lift_apply (𝟙 M) (constMap M M m) z

private def transferredLeftUnit
    {X : TopCat.{u}} {x : X} (N : TopCat.NativeSingularPointModel X x)
    (H : HSpaceData (TopCat.nativeSingularSpace X))
    (he : H.e = TopCat.nativeSingularPoint X x)
    (E : (TopCat.nativeSingularSpace X ⊗ TopCat.nativeSingularSpace X : CGWH.{u, u}) ≃ₕ
      (TopCat.nativeSingularSpace X × TopCat.nativeSingularSpace X))
    (hE : E.toFun = (prodComparisonToTop (TopCat.nativeSingularSpace X)
      (TopCat.nativeSingularSpace X)).hom)
    (LE : ContinuousMap.HomotopyRel (E.invFun.comp E.toFun)
      (ContinuousMap.id (TopCat.nativeSingularSpace X ⊗
        TopCat.nativeSingularSpace X : CGWH.{u, u})) {tensorMk H.e H.e}) :
    ContinuousMap.HomotopyRel
      ((transferredNativeHSpaceMul N H E).comp
        ((ContinuousMap.const X x).prodMk (ContinuousMap.id X)))
      (ContinuousMap.id X) {x} := by
  let M := TopCat.nativeSingularSpace X
  let r : C(X, M) := N.equiv.invFun
  let s : C(M, X) := N.equiv.toFun
  let mu : C((M ⨯ M : CGWH.{u, u}), M) := (cgwhToTop.map H.mul).hom
  let a : C(X, (M ⨯ M : CGWH.{u, u})) := (leftNativeAxis M H.e).comp r
  let b : C(X, X × X) := (ContinuousMap.const X x).prodMk (ContinuousMap.id X)
  have hr : r x = H.e := N.backwardPoint.trans he.symm
  have ha : a x = tensorMk H.e H.e :=
    (congrArg (leftNativeAxis M H.e) hr).trans
      ((leftNativeAxis_apply M H.e H.e).trans (tensorMk_eq_prodPoint H.e H.e).symm)
  have hAxis : E.toFun.comp a = (r.prodMap r).comp b := by
    apply ContinuousMap.ext
    intro z
    change E.toFun (leftNativeAxis M H.e (r z)) = (r x, r z)
    exact (congrArg (fun f : C((M ⊗ M : CGWH.{u, u}), M × M) =>
      f (leftNativeAxis M H.e (r z))) hE).trans
      ((congrArg (prodComparisonToTop M M) (leftNativeAxis_apply M H.e (r z))).trans
        ((prodComparisonToTop_prodPoint M M H.e (r z)).trans
          (congrArg (fun p : M => (p, r z)) hr.symm)))
  let P : ContinuousMap.HomotopyRel
      ((s.comp mu).comp ((E.invFun.comp E.toFun).comp a))
      ((s.comp mu).comp a) {x} :=
    (LE.precomposePointRelative a x ha).compContinuousMap (s.comp mu)
  have hstart : (s.comp mu).comp ((E.invFun.comp E.toFun).comp a) =
      (transferredNativeHSpaceMul N H E).comp b := by
    unfold transferredNativeHSpaceMul
    apply ContinuousMap.ext
    intro z
    change s (mu (E.invFun (E.toFun (a z)))) = s (mu (E.invFun ((r.prodMap r) (b z))))
    exact congrArg (fun p : M × M => s (mu (E.invFun p)))
      (congrArg (fun f : C(X, M × M) => f z) hAxis)
  have hend : (s.comp mu).comp a =
      s.comp ((cgwhToTop.map (hspaceLeftUnitMap M H.mul H.e)).hom.comp r) := by
    apply ContinuousMap.ext
    intro z
    change s (H.mul (leftNativeAxis M H.e (r z))) =
      s ((hspaceLeftUnitMap M H.mul H.e) (r z))
    exact congrArg s ((congrArg H.mul (leftNativeAxis_apply M H.e (r z))).trans
      (hspaceLeftUnitMap_apply M H.mul H.e (r z)).symm)
  let U : ContinuousMap.HomotopyRel
      (s.comp ((cgwhToTop.map (hspaceLeftUnitMap M H.mul H.e)).hom.comp r))
      (s.comp r) {x} :=
    (H.left_unit.precomposePointRelative r x hr).compContinuousMap s
  let U' : ContinuousMap.HomotopyRel
      (s.comp ((cgwhToTop.map (hspaceLeftUnitMap M H.mul H.e)).hom.comp r))
      (s.comp r) {x} :=
    U.cast rfl (by apply ContinuousMap.ext; intro z; rfl)
  exact (P.cast hstart hend).trans (U'.trans N.rightFamily)

private def transferredRightUnit
    {X : TopCat.{u}} {x : X} (N : TopCat.NativeSingularPointModel X x)
    (H : HSpaceData (TopCat.nativeSingularSpace X))
    (he : H.e = TopCat.nativeSingularPoint X x)
    (E : (TopCat.nativeSingularSpace X ⊗ TopCat.nativeSingularSpace X : CGWH.{u, u}) ≃ₕ
      (TopCat.nativeSingularSpace X × TopCat.nativeSingularSpace X))
    (hE : E.toFun = (prodComparisonToTop (TopCat.nativeSingularSpace X)
      (TopCat.nativeSingularSpace X)).hom)
    (LE : ContinuousMap.HomotopyRel (E.invFun.comp E.toFun)
      (ContinuousMap.id (TopCat.nativeSingularSpace X ⊗
        TopCat.nativeSingularSpace X : CGWH.{u, u})) {tensorMk H.e H.e}) :
    ContinuousMap.HomotopyRel
      ((transferredNativeHSpaceMul N H E).comp
        ((ContinuousMap.id X).prodMk (ContinuousMap.const X x)))
      (ContinuousMap.id X) {x} := by
  let M := TopCat.nativeSingularSpace X
  let r : C(X, M) := N.equiv.invFun
  let s : C(M, X) := N.equiv.toFun
  let mu : C((M ⨯ M : CGWH.{u, u}), M) := (cgwhToTop.map H.mul).hom
  let a : C(X, (M ⨯ M : CGWH.{u, u})) := (rightNativeAxis M H.e).comp r
  let b : C(X, X × X) := (ContinuousMap.id X).prodMk (ContinuousMap.const X x)
  have hr : r x = H.e := N.backwardPoint.trans he.symm
  have ha : a x = tensorMk H.e H.e :=
    (congrArg (rightNativeAxis M H.e) hr).trans
      ((rightNativeAxis_apply M H.e H.e).trans (tensorMk_eq_prodPoint H.e H.e).symm)
  have hAxis : E.toFun.comp a = (r.prodMap r).comp b := by
    apply ContinuousMap.ext
    intro z
    change E.toFun (rightNativeAxis M H.e (r z)) = (r z, r x)
    exact (congrArg (fun f : C((M ⊗ M : CGWH.{u, u}), M × M) =>
      f (rightNativeAxis M H.e (r z))) hE).trans
      ((congrArg (prodComparisonToTop M M) (rightNativeAxis_apply M H.e (r z))).trans
        ((prodComparisonToTop_prodPoint M M (r z) H.e).trans
          (congrArg (fun p : M => (r z, p)) hr.symm)))
  let P : ContinuousMap.HomotopyRel
      ((s.comp mu).comp ((E.invFun.comp E.toFun).comp a))
      ((s.comp mu).comp a) {x} :=
    (LE.precomposePointRelative a x ha).compContinuousMap (s.comp mu)
  have hstart : (s.comp mu).comp ((E.invFun.comp E.toFun).comp a) =
      (transferredNativeHSpaceMul N H E).comp b := by
    unfold transferredNativeHSpaceMul
    apply ContinuousMap.ext
    intro z
    change s (mu (E.invFun (E.toFun (a z)))) = s (mu (E.invFun ((r.prodMap r) (b z))))
    exact congrArg (fun p : M × M => s (mu (E.invFun p)))
      (congrArg (fun f : C(X, M × M) => f z) hAxis)
  have hend : (s.comp mu).comp a =
      s.comp ((cgwhToTop.map (hspaceRightUnitMap M H.mul H.e)).hom.comp r) := by
    apply ContinuousMap.ext
    intro z
    change s (H.mul (rightNativeAxis M H.e (r z))) =
      s ((hspaceRightUnitMap M H.mul H.e) (r z))
    exact congrArg s ((congrArg H.mul (rightNativeAxis_apply M H.e (r z))).trans
      (hspaceRightUnitMap_apply M H.mul H.e (r z)).symm)
  let U : ContinuousMap.HomotopyRel
      (s.comp ((cgwhToTop.map (hspaceRightUnitMap M H.mul H.e)).hom.comp r))
      (s.comp r) {x} :=
    (H.right_unit.precomposePointRelative r x hr).compContinuousMap s
  let U' : ContinuousMap.HomotopyRel
      (s.comp ((cgwhToTop.map (hspaceRightUnitMap M H.mul H.e)).hom.comp r))
      (s.comp r) {x} :=
    U.cast rfl (by apply ContinuousMap.ext; intro z; rfl)
  exact (P.cast hstart hend).trans (U'.trans N.rightFamily)

/-- The actual pointed native model, a native multiplication, and its
two actual unit families transfer to an ordinary H-space on the SAME
original space. The result records its literal unit and actual recipe.
The product equivalence used here is supplied by the genuine CW product
comparison theorem in the final construction. -/
public def HSpaceData.transferOfNativeSingularPointModel
    {X : TopCat.{u}} {x : X} (N : TopCat.NativeSingularPointModel X x)
    (H : HSpaceData (TopCat.nativeSingularSpace X))
    (he : H.e = TopCat.nativeSingularPoint X x)
    (E : (TopCat.nativeSingularSpace X ⊗ TopCat.nativeSingularSpace X : CGWH.{u, u}) ≃ₕ
      (TopCat.nativeSingularSpace X × TopCat.nativeSingularSpace X))
    (hE : E.toFun = (prodComparisonToTop (TopCat.nativeSingularSpace X)
      (TopCat.nativeSingularSpace X)).hom)
    (hInv : E.invFun (H.e, H.e) = tensorMk H.e H.e)
    (LE : ContinuousMap.HomotopyRel (E.invFun.comp E.toFun)
      (ContinuousMap.id (TopCat.nativeSingularSpace X ⊗
        TopCat.nativeSingularSpace X : CGWH.{u, u})) {tensorMk H.e H.e}) :
    { J : HSpace X // J.e = x ∧ J.hmul = transferredNativeHSpaceMul N H E } := by
  let M := TopCat.nativeSingularSpace X
  let r := N.equiv.invFun
  let s := N.equiv.toFun
  let mu := (cgwhToTop.map H.mul).hom
  have hr : r x = H.e := N.backwardPoint.trans he.symm
  have hs : s H.e = x := (congrArg s he).trans N.forwardPoint
  have hpair : (r.prodMap r) (x, x) = (H.e, H.e) := Prod.ext hr hr
  have hpoint : transferredNativeHSpaceMul N H E (x, x) = x := by
    unfold transferredNativeHSpaceMul
    change s (mu (E.invFun ((r.prodMap r) (x, x)))) = x
    exact (congrArg (fun p : M × M => s (mu (E.invFun p))) hpair).trans
      ((congrArg (s.comp mu) (hInv.trans (tensorMk_eq_prodPoint H.e H.e))).trans
        ((congrArg s H.mul_e_e).trans hs))
  let J : HSpace X :=
    { hmul := transferredNativeHSpaceMul N H E
      e := x
      hmul_e_e := hpoint
      eHmul := transferredLeftUnit N H he E hE LE
      hmulE := transferredRightUnit N H he E hE LE }
  exact ⟨J, rfl, rfl⟩

/-- The transferred multiplication retains the ORIGINAL whole native
source triangle. Its first comparison family is the actual product
inverse family; its last is the actual original-space inverse family.
Every family fixes the original pair point. -/
public def transferredNativeHSpaceSourceTriangle
    {X : TopCat.{u}} {x : X} (N : TopCat.NativeSingularPointModel X x)
    (H : HSpaceData (TopCat.nativeSingularSpace X))
    (E : (TopCat.nativeSingularSpace X ⊗ TopCat.nativeSingularSpace X : CGWH.{u, u}) ≃ₕ
      (TopCat.nativeSingularSpace X × TopCat.nativeSingularSpace X))
    (hE : E.toFun = (prodComparisonToTop (TopCat.nativeSingularSpace X)
      (TopCat.nativeSingularSpace X)).hom)
    (LE : ContinuousMap.HomotopyRel (E.invFun.comp E.toFun)
      (ContinuousMap.id (TopCat.nativeSingularSpace X ⊗
        TopCat.nativeSingularSpace X : CGWH.{u, u})) {tensorMk H.e H.e})
    (A : CGWH.{u, u}) (a : A) (f : C(A, X)) (hf : f a = x)
    (q : A ⟶ TopCat.nativeSingularSpace X)
    (hq : (cgwhToTop.map q).hom = N.equiv.invFun.comp f)
    (hqa : q a = H.e)
    (muA : A ⨯ A ⟶ A) (hmuA : muA (tensorMk a a) = a)
    (K : ContinuousMap.HomotopyRel (cgwhToTop.map ((q ⊗ₘ q) ≫ H.mul)).hom
      (cgwhToTop.map (muA ≫ q)).hom {tensorMk a a}) :
    ContinuousMap.HomotopyRel
      ((transferredNativeHSpaceMul N H E).comp
        ((f.prodMap f).comp (prodComparisonToTop A A).hom))
      (f.comp (cgwhToTop.map muA).hom) {tensorMk a a} := by
  let M := TopCat.nativeSingularSpace X
  let r : C(X, M) := N.equiv.invFun
  let s : C(M, X) := N.equiv.toFun
  let mu : C((M ⨯ M : CGWH.{u, u}), M) := (cgwhToTop.map H.mul).hom
  let p : C((A ⊗ A : CGWH.{u, u}), (M ⊗ M : CGWH.{u, u})) :=
    (cgwhToTop.map (q ⊗ₘ q)).hom
  let b : C((A ⊗ A : CGWH.{u, u}), X × X) :=
    (f.prodMap f).comp (prodComparisonToTop A A).hom
  have hp : p (tensorMk a a) = tensorMk H.e H.e :=
    (tensorMk_map q q a a).trans (congrArg (fun z : M => tensorMk z z) hqa)
  have hInput : E.toFun.comp p = (r.prodMap r).comp b := by
    apply ContinuousMap.ext
    intro z
    have hFirst : (show (cgwhToTop.obj M) × (cgwhToTop.obj M) from E.toFun (p z)) =
        prodComparisonToTop M M ((q ⊗ₘ q) z) :=
      congrArg (fun k : C((M ⊗ M : CGWH.{u, u}),
        (cgwhToTop.obj M) × (cgwhToTop.obj M)) => k (p z)) hE
    have hComparison : (show (cgwhToTop.obj M) × (cgwhToTop.obj M) from
        tensorEquivProd M M ((q ⊗ₘ q) z)) = prodComparisonToTop M M ((q ⊗ₘ q) z) :=
      tensorEquivProd_eq_prodComparisonToTop M M _
    have hTensor : (show (cgwhToTop.obj M) × (cgwhToTop.obj M) from
        tensorEquivProd M M ((q ⊗ₘ q) z)) =
        (cgwhToTop.map q (tensorEquivProd A A z).1,
          cgwhToTop.map q (tensorEquivProd A A z).2) :=
      tensorEquivProd_map q q z
    have hA : (show (cgwhToTop.obj A) × (cgwhToTop.obj A) from tensorEquivProd A A z) =
        prodComparisonToTop A A z := tensorEquivProd_eq_prodComparisonToTop A A z
    have hPair : (cgwhToTop.map q (tensorEquivProd A A z).1,
        cgwhToTop.map q (tensorEquivProd A A z).2) =
        (cgwhToTop.map q (prodComparisonToTop A A z).1,
          cgwhToTop.map q (prodComparisonToTop A A z).2) :=
      congrArg (fun t : (cgwhToTop.obj A) × (cgwhToTop.obj A) =>
        (cgwhToTop.map q t.1, cgwhToTop.map q t.2)) hA
    have hFinish : (cgwhToTop.map q (prodComparisonToTop A A z).1,
        cgwhToTop.map q (prodComparisonToTop A A z).2) =
        (show (cgwhToTop.obj M) × (cgwhToTop.obj M) from (r.prodMap r) (b z)) := by
      apply Prod.ext
      · exact congrArg (fun k : C(cgwhToTop.obj A, cgwhToTop.obj M) =>
          k (prodComparisonToTop A A z).1) hq
      · exact congrArg (fun k : C(cgwhToTop.obj A, cgwhToTop.obj M) =>
          k (prodComparisonToTop A A z).2) hq
    exact hFirst.trans (hComparison.symm.trans (hTensor.trans (hPair.trans hFinish)))
  let P := (LE.precomposePointRelative p (tensorMk a a) hp).compContinuousMap (s.comp mu)
  have hstart : (s.comp mu).comp ((E.invFun.comp E.toFun).comp p) =
      (transferredNativeHSpaceMul N H E).comp b := by
    unfold transferredNativeHSpaceMul
    apply ContinuousMap.ext
    intro z
    change s (mu (E.invFun (E.toFun (p z)))) = s (mu (E.invFun ((r.prodMap r) (b z))))
    exact congrArg (fun t : M × M => s (mu (E.invFun t)))
      (congrArg (fun k : C((A ⊗ A : CGWH.{u, u}), M × M) => k z) hInput)
  have hend : (s.comp mu).comp p = s.comp (cgwhToTop.map ((q ⊗ₘ q) ≫ H.mul)).hom := by
    apply ContinuousMap.ext
    intro z
    rfl
  let Q := K.compContinuousMap s
  have hSource : s.comp (cgwhToTop.map (muA ≫ q)).hom =
      (s.comp r).comp (f.comp (cgwhToTop.map muA).hom) := by
    apply ContinuousMap.ext
    intro z
    change s (q (muA z)) = s (r (f (muA z)))
    exact congrArg s (congrArg (fun k : C(A, M) => k (muA z)) hq)
  have hf0 : (f.comp (cgwhToTop.map muA).hom) (tensorMk a a) = x :=
    (congrArg f hmuA).trans hf
  let R := N.rightFamily.precomposePointRelative (f.comp (cgwhToTop.map muA).hom)
    (tensorMk a a) hf0
  exact (P.cast hstart hend).trans ((Q.cast rfl hSource).trans R)

end CGWH

end
