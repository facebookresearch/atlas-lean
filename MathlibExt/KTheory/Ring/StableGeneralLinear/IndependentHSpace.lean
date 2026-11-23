/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentNativeMultiplication
public import MathlibExt.Topology.Category.CGWH.HSpaceTransfer

/-!
# An actual H-space on the independently constructed BGL plus

For every unital associative ring, the original block-sum functor first
gives the whole native source multiplication. The actual product-plus
map and point-relative uniqueness derive the native target operation
and both unit families. The genuine product comparison and the derived
pointed singular inverse transfer that operation to the SAME original
two/three-cell target. Its unit is the ORIGINAL cell point, and its
whole source triangle is the ORIGINAL block-sum map.

No H-space structure, multiplication, product model, source-family
nullity, all-system comparison, or desired inverse is a caller input.
-/

noncomputable section

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory

universe u

namespace AlgebraicKTheory.StableGL

private local instance originalCellPointCofibrant (R : Type u) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{u + 1} ⟶ independentBGLCellTarget R) :=
  independentBGLCellPoint_cofibration R

/-- The same original plus target model has weak H-space data with
derived root traces and the ORIGINAL whole block-sum source triangle.
The root and both unit families come from the already derived
point-relative operation, without new hypotheses. -/
public theorem exists_independentBGLNativeWeakHSpace (R : Type u) [Ring R] :
    let M := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let m := TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R)
    let q := independentBGLNativeInclusion R
    ∃ H : CGWH.WeakHSpaceData M, H.e = m ∧
      Nonempty (ContinuousMap.HomotopyRel
        (CGWH.cgwhToTop.map ((q ⊗ₘ q) ≫ H.mul)).hom
        (CGWH.cgwhToTop.map (nativeBGLBlockSum R ≫ q)).hom
          {CGWH.tensorMk (BGLBasepoint R) (BGLBasepoint R)}) := by
  let q := independentBGLNativeInclusion R
  obtain ⟨H, he, ⟨K⟩⟩ := exists_independentBGLNativeMultiplication R
  let V := CGWH.HSpaceData.toWeakData H
  exact ⟨V.val, V.property.2.trans he, ⟨K.cast
    (congrArg (fun mu => (CGWH.cgwhToTop.map ((q ⊗ₘ q) ≫ mu)).hom)
      V.property.1.symm) rfl⟩⟩

/-- The SAME actual independently constructed cell plus carries a
continuous multiplication with BOTH whole unit homotopies relative to
its original point. The full original native block-sum source triangle
is point relative too, over every unchanged ring and every source point. -/
public theorem exists_independentBGLCellHSpace (R : Type u) [Ring R] :
    let A := BGL.{u} R
    let Y := independentBGLCellTarget R
    let f : C(A, Y) := (independentBGLCellInclusion R).hom.comp
      (BGLToOrdinaryTopIso.{u} R).hom.hom
    ∃ J : HSpace Y, J.e = independentBGLCellPoint R ∧
      Nonempty (ContinuousMap.HomotopyRel
        (J.hmul.comp ((f.prodMap f).comp (CGWH.prodComparisonToTop A A).hom))
        (f.comp (CGWH.cgwhToTop.map (nativeBGLBlockSum R)).hom)
          {CGWH.tensorMk (BGLBasepoint R) (BGLBasepoint R)}) := by
  let A := BGL.{u} R
  let Y := independentBGLCellTarget R
  let y := independentBGLCellPoint R
  let M := TopCat.nativeSingularSpace Y
  let m := TopCat.nativeSingularPoint Y y
  let N := TopCat.nativeSingularPointModelOfCofibrantPoint Y y
  let q := independentBGLNativeInclusion R
  let f : C(A, Y) := (independentBGLCellInclusion R).hom.comp
    (BGLToOrdinaryTopIso.{u} R).hom.hom
  have hf : f (BGLBasepoint R) = y :=
    (congrArg (independentBGLCellInclusion R) (BGLToOrdinaryTopIso_hom_basepoint R)).trans
      (independentBGLCellInclusion_point R)
  obtain ⟨H, he, ⟨K⟩⟩ := exists_independentBGLNativeMultiplication R
  letI : Cofibration (TopCat.const H.e : TopCat.of PUnit.{u + 1} ⟶ M.toTop) := by
    have hc : (TopCat.const H.e : TopCat.of PUnit.{u + 1} ⟶ M.toTop) =
        TopCat.const m := congrArg (fun p : M =>
          (TopCat.const p : TopCat.of PUnit.{u + 1} ⟶ M.toTop)) he
    rw [hc]
    exact TopCat.nativeSingularPoint_cofibration Y y
  obtain ⟨E, hE, hInv, ⟨LE⟩, _⟩ :=
    CGWH.prodComparisonToTop_homotopyEquiv_of_cofibrant_points M M H.e H.e
  let J := CGWH.HSpaceData.transferOfNativeSingularPointModel N H he E hE hInv LE
  have hq : (CGWH.cgwhToTop.map q).hom = N.equiv.invFun.comp f := rfl
  have hqa : q (BGLBasepoint R) = H.e :=
    (independentBGLNativeInclusion_point R).trans he.symm
  let T := CGWH.transferredNativeHSpaceSourceTriangle N H E hE LE
    A (BGLBasepoint R) f hf q hq hqa (nativeBGLBlockSum R) (nativeBGLBlockSum_point R) K
  refine ⟨J.val, J.property.1, ?_⟩
  exact ⟨T.cast
    (congrArg (fun k : C(Y × Y, Y) =>
      k.comp ((f.prodMap f).comp (CGWH.prodComparisonToTop A A).hom)) J.property.2.symm) rfl⟩

/-- The concrete H-space data on the SAME independent cell target,
with its original unit and original whole block-sum source triangle
recorded as properties of the constructed value. -/
public def independentBGLCellHSpace (R : Type u) [Ring R] :
    let A := BGL.{u} R
    let Y := independentBGLCellTarget R
    let f : C(A, Y) := (independentBGLCellInclusion R).hom.comp
      (BGLToOrdinaryTopIso.{u} R).hom.hom
    { J : HSpace Y // J.e = independentBGLCellPoint R ∧
      Nonempty (ContinuousMap.HomotopyRel
        (J.hmul.comp ((f.prodMap f).comp (CGWH.prodComparisonToTop A A).hom))
        (f.comp (CGWH.cgwhToTop.map (nativeBGLBlockSum R)).hom)
          {CGWH.tensorMk (BGLBasepoint R) (BGLBasepoint R)}) } :=
  ⟨Classical.choose (exists_independentBGLCellHSpace R),
    Classical.choose_spec (exists_independentBGLCellHSpace R)⟩

end AlgebraicKTheory.StableGL

end
