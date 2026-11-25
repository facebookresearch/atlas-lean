/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalStageOneCounit

/-!
# Arbitrary-edge normalization in the weak-stage diagonal

An arbitrary diagonal edge is represented by a morphism between degree-one
weak stages.  The generic Stage-one source degeneracy triangle removes that
inner morphism, coherent Stage-zero connector naturality cancels its target
face, and the Stage-one counit then normalizes the remaining identity-stage
edge to the canonical object edge of the source stage's `(0, 1)` evaluation.

The result is solely an equality in the simplicial fundamental groupoid.  No
generation, realization, K-zero, additivity, spectrum, or Q/S claim is made.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

private theorem fundamentalGroupoid_homMk_ofEq
    {X : SSet.{u}} {x₀ x₁ y₀ y₁ : X.obj (op ⦋0⦌)}
    (e : SSet.Edge x₀ x₁) (h₀ : x₀ = y₀) (h₁ : x₁ = y₁) :
    SSet.FundamentalGroupoid.homMk (e.ofEq h₀ h₁) =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk h₀).symm ≫
        SSet.FundamentalGroupoid.homMk e ≫
        eqToHom (congrArg SSet.FundamentalGroupoid.mk h₁) := by
  cases h₀
  cases h₁
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  congr 1

private theorem stageWeakDiagonalZeroToObj_homMk_transport
    {S T : StageWeakCategory C 0} (h : S = T) :
    SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToObjEdge C S) ≫
        eqToHom (congrArg
          (fun U : StageWeakCategory C 0 =>
            SSet.FundamentalGroupoid.mk (X := stageWeakDiagonal C)
              (ComposableArrows.mk₀ U)) h) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C T) := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The source endpoint of an arbitrary diagonal edge is the source face of
the left degree-one weak stage recovered from its underlying nerve simplex. -/
theorem stageWeakDiagonalEdge_source_eq
    {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    (e : (stageWeakDiagonal C).Edge x y) :
    ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 1)).obj
          (ComposableArrows.left e.edge)) = x := by
  let A : StageWeakCategory C 1 := ComposableArrows.left e.edge
  let B : StageWeakCategory C 1 := ComposableArrows.right e.edge
  let φ : A ⟶ B := ComposableArrows.hom e.edge
  let g := stageWeakDiagonalStageOneMapEdge C φ
  have hs : g.edge = e.edge := by
    change ComposableArrows.mk₁ (ComposableArrows.hom e.edge) = e.edge
    exact ComposableArrows.mk₁_hom e.edge
  change ComposableArrows.mk₀
    ((reindexStageWeak C (SimplexCategory.δ 1)).obj A) = x
  calc
    ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 1)).obj A) =
      (stageWeakDiagonal C).δ 1 g.edge := (SSet.Edge.src_eq g).symm
    _ = (stageWeakDiagonal C).δ 1 e.edge :=
      congrArg (fun s => (stageWeakDiagonal C).δ 1 s) hs
    _ = x := e.src_eq

set_option backward.isDefEq.respectTransparency false in
/-- The target endpoint of an arbitrary diagonal edge is the target face of
the right degree-one weak stage recovered from its underlying nerve simplex. -/
theorem stageWeakDiagonalEdge_target_eq
    {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    (e : (stageWeakDiagonal C).Edge x y) :
    ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 0)).obj
          (ComposableArrows.right e.edge)) = y := by
  let A : StageWeakCategory C 1 := ComposableArrows.left e.edge
  let B : StageWeakCategory C 1 := ComposableArrows.right e.edge
  let φ : A ⟶ B := ComposableArrows.hom e.edge
  let g := stageWeakDiagonalStageOneMapEdge C φ
  have hs : g.edge = e.edge := by
    change ComposableArrows.mk₁ (ComposableArrows.hom e.edge) = e.edge
    exact ComposableArrows.mk₁_hom e.edge
  change ComposableArrows.mk₀
    ((reindexStageWeak C (SimplexCategory.δ 0)).obj B) = y
  calc
    ComposableArrows.mk₀
        ((reindexStageWeak C (SimplexCategory.δ 0)).obj B) =
      (stageWeakDiagonal C).δ 0 g.edge := (SSet.Edge.tgt_eq g).symm
    _ = (stageWeakDiagonal C).δ 0 e.edge :=
      congrArg (fun s => (stageWeakDiagonal C).δ 0 s) hs
    _ = y := e.tgt_eq

set_option backward.isDefEq.respectTransparency false in
/-- After transporting the generic Stage-one map edge to the stored endpoints,
it is the original arbitrary diagonal edge. -/
theorem stageWeakDiagonalEdge_stageOneMapEdge_ofEq
    {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    (e : (stageWeakDiagonal C).Edge x y) :
    (stageWeakDiagonalStageOneMapEdge C
        (ComposableArrows.hom e.edge)).ofEq
          (stageWeakDiagonalEdge_source_eq C e)
          (stageWeakDiagonalEdge_target_eq C e) = e := by
  apply SSet.Edge.ext
  change ComposableArrows.mk₁ (ComposableArrows.hom e.edge) = e.edge
  exact ComposableArrows.mk₁_hom e.edge

private theorem stageWeakDiagonalStageOneMapEdge_normalization
    {A B : StageWeakCategory C 1} (φ : A ⟶ B) :
    (SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToObjEdge C
          ((reindexStageWeak C (SimplexCategory.δ 1)).obj A)) ≫
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalStageOneMapEdge C φ)) ≫
        inv (SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToObjEdge C
            ((reindexStageWeak C (SimplexCategory.δ 0)).obj B))) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalObjectEdge C ((stageOneEval C).obj A.obj)) := by
  let S : StageWeakCategory C 0 :=
    (reindexStageWeak C (SimplexCategory.δ 1)).obj A
  let T_A : StageWeakCategory C 0 :=
    (reindexStageWeak C (SimplexCategory.δ 0)).obj A
  let T_B : StageWeakCategory C 0 :=
    (reindexStageWeak C (SimplexCategory.δ 0)).obj B
  let kS := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C S)
  let kT_A := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C T_A)
  let kT_B := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C T_B)
  let iA := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalStageOneIdentityEdge C A)
  let m := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalStageZeroMapEdge C
      ((reindexStageWeak C (SimplexCategory.δ 0)).map φ))
  let g := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalStageOneMapEdge C φ)
  let oA := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalObjectEdge C ((stageOneEval C).obj A.obj))
  have hsource : iA ≫ m = g := by
    simpa only [iA, m, g] using
      (stageWeakDiagonalStageOneSource_homMk_comp C φ)
  have hconnector : kT_A ≫ m = kT_B := by
    simpa only [kT_A, m, kT_B, T_A, T_B] using
      (stageWeakDiagonalZeroConnector_homMk_comp C
        ((reindexStageWeak C (SimplexCategory.δ 0)).map φ))
  have hcancel : m ≫ inv kT_B = inv kT_A := by
    rw [← cancel_epi kT_A]
    rw [← Category.assoc, hconnector, IsIso.hom_inv_id,
      IsIso.hom_inv_id]
  have hidentity : (kS ≫ iA) ≫ inv kT_A = oA := by
    simpa only [kS, iA, kT_A, oA, S, T_A] using
      (stageWeakDiagonalStageOneIdentityEdge_normalization C A)
  change (kS ≫ g) ≫ inv kT_B = oA
  calc
    (kS ≫ g) ≫ inv kT_B =
        (kS ≫ (iA ≫ m)) ≫ inv kT_B := by rw [hsource]
    _ = (kS ≫ iA) ≫ (m ≫ inv kT_B) := by
      simp only [Category.assoc]
    _ = (kS ≫ iA) ≫ inv kT_A := by rw [hcancel]
    _ = oA := hidentity

set_option backward.isDefEq.respectTransparency false in
/-- Every edge in the weak-stage diagonal is conjugate, through the coherent
zero-to-vertex connectors, to the canonical object edge of the `(0, 1)`
evaluation of its recovered source Stage-one object. -/
theorem stageWeakDiagonalEdge_normalization
    {x y : (stageWeakDiagonal C).obj (op ⦋0⦌)}
    (e : (stageWeakDiagonal C).Edge x y) :
    (SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalZeroToVertexEdge C x) ≫
      SSet.FundamentalGroupoid.homMk e) ≫
        inv (SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToVertexEdge C y)) =
      SSet.FundamentalGroupoid.homMk
        (stageWeakDiagonalObjectEdge C
          ((stageOneEval C).obj (ComposableArrows.left e.edge).obj)) := by
  let A : StageWeakCategory C 1 := ComposableArrows.left e.edge
  let B : StageWeakCategory C 1 := ComposableArrows.right e.edge
  let φ : A ⟶ B := ComposableArrows.hom e.edge
  let S : StageWeakCategory C 0 :=
    (reindexStageWeak C (SimplexCategory.δ 1)).obj A
  let T : StageWeakCategory C 0 :=
    (reindexStageWeak C (SimplexCategory.δ 0)).obj B
  let g := stageWeakDiagonalStageOneMapEdge C φ
  have hx : ComposableArrows.mk₀ S = x := by
    simpa only [S, A] using stageWeakDiagonalEdge_source_eq C e
  have hy : ComposableArrows.mk₀ T = y := by
    simpa only [T, B] using stageWeakDiagonalEdge_target_eq C e
  have hg : g.ofEq hx hy = e := by
    simpa only [g, φ] using
      (stageWeakDiagonalEdge_stageOneMapEdge_ofEq C e)
  have hSX : CategoryTheory.nerveEquiv x = S := by
    apply CategoryTheory.nerveEquiv.symm.injective
    exact (CategoryTheory.nerveEquiv.left_inv x).trans hx.symm
  have hTY : CategoryTheory.nerveEquiv y = T := by
    apply CategoryTheory.nerveEquiv.symm.injective
    exact (CategoryTheory.nerveEquiv.left_inv y).trans hy.symm
  let zx := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToVertexEdge C x)
  let zy := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToVertexEdge C y)
  let kS := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C S)
  let kT := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalZeroToObjEdge C T)
  let ge := SSet.FundamentalGroupoid.homMk g
  let he := SSet.FundamentalGroupoid.homMk e
  let oA := SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalObjectEdge C ((stageOneEval C).obj A.obj))
  have hHom := fundamentalGroupoid_homMk_ofEq g hx hy
  rw [hg] at hHom
  have hHom' :
      he = eqToHom (congrArg SSet.FundamentalGroupoid.mk hx).symm ≫
        ge ≫ eqToHom (congrArg SSet.FundamentalGroupoid.mk hy) := by
    simpa only [he, ge] using hHom
  have hzeroX := fundamentalGroupoid_homMk_ofEq
    (stageWeakDiagonalZeroToObjEdge C (CategoryTheory.nerveEquiv x)) rfl
      (CategoryTheory.nerveEquiv.left_inv x)
  have hzeroY := fundamentalGroupoid_homMk_ofEq
    (stageWeakDiagonalZeroToObjEdge C (CategoryTheory.nerveEquiv y)) rfl
      (CategoryTheory.nerveEquiv.left_inv y)
  have hzeroX' :
      zx = SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToObjEdge C
            (CategoryTheory.nerveEquiv x)) ≫
        eqToHom (congrArg SSet.FundamentalGroupoid.mk
          (CategoryTheory.nerveEquiv.left_inv x)) := by
    simpa only [zx, stageWeakDiagonalZeroToVertexEdge,
      eqToHom_refl, Category.id_comp] using hzeroX
  have hzeroY' :
      zy = SSet.FundamentalGroupoid.homMk
          (stageWeakDiagonalZeroToObjEdge C
            (CategoryTheory.nerveEquiv y)) ≫
        eqToHom (congrArg SSet.FundamentalGroupoid.mk
          (CategoryTheory.nerveEquiv.left_inv y)) := by
    simpa only [zy, stageWeakDiagonalZeroToVertexEdge,
      eqToHom_refl, Category.id_comp] using hzeroY
  have hsourceTransport :
      zx ≫ eqToHom (congrArg SSet.FundamentalGroupoid.mk hx).symm = kS := by
    rw [hzeroX']
    rw [Category.assoc, eqToHom_trans]
    exact stageWeakDiagonalZeroToObj_homMk_transport C hSX
  have htargetTransport :
      zy ≫ eqToHom (congrArg SSet.FundamentalGroupoid.mk hy).symm = kT := by
    rw [hzeroY']
    rw [Category.assoc, eqToHom_trans]
    exact stageWeakDiagonalZeroToObj_homMk_transport C hTY
  have htargetCancel :
      eqToHom (congrArg SSet.FundamentalGroupoid.mk hy) ≫ inv zy =
        inv kT := by
    have hinv :
        inv (zy ≫ eqToHom
          (congrArg SSet.FundamentalGroupoid.mk hy).symm) = inv kT :=
      congrArg (fun f => inv f) htargetTransport
    simpa only [IsIso.inv_comp, inv_eqToHom] using hinv
  have hstage : (kS ≫ ge) ≫ inv kT = oA := by
    simpa only [kS, ge, kT, oA, g, φ, S, T, A, B] using
      (stageWeakDiagonalStageOneMapEdge_normalization C φ)
  change (zx ≫ he) ≫ inv zy = oA
  calc
    (zx ≫ he) ≫ inv zy =
        (zx ≫ (eqToHom (congrArg SSet.FundamentalGroupoid.mk hx).symm ≫
          ge ≫ eqToHom (congrArg SSet.FundamentalGroupoid.mk hy))) ≫
            inv zy := by rw [hHom']
    _ = ((zx ≫ eqToHom
          (congrArg SSet.FundamentalGroupoid.mk hx).symm) ≫ ge) ≫
        (eqToHom (congrArg SSet.FundamentalGroupoid.mk hy) ≫ inv zy) := by
      simp only [Category.assoc]
    _ = (kS ≫ ge) ≫
        (eqToHom (congrArg SSet.FundamentalGroupoid.mk hy) ≫ inv zy) := by
      rw [hsourceTransport]
    _ = (kS ≫ ge) ≫ inv kT := by rw [htargetCancel]
    _ = oA := hstage

end CategoryTheory.Waldhausen.SConstruction

end
