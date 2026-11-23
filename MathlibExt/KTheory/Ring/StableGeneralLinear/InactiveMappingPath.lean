/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteUnitCompatibility

/-!
# The ORIGINAL whole inactive natural loop in its mapping space

The same general inactive-family filler is used for every computed
conjugation difference. Its original normalized loop and entire original
finite-BGL parameter give ONE joint square. That square contracts the
original RAW mapping-space loop; it is not a collection of pointwise
fundamental-group nullity statements.
-/

noncomputable section

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped TopCat.modelCategory Simplicial

universe u

namespace AlgebraicKTheory.StableGL

private local instance independentCellPointCofibrant (R : Type u) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{u + 1} ⟶ independentBGLCellTarget R) :=
  independentBGLCellPoint_cofibration R

attribute [local instance] independentBGLCellPoint_cofibration

/-- The original whole inactive natural loop, in the ORIGINAL compact-open
mapping space and SAME independent plus model. -/
public abbrev independentBGLInactiveNaturalLoopMappingPath
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    Path (independentBGLFiniteMapToNativeModel R n)
      (independentBGLFiniteMapToNativeModel R n) :=
  NatTrans.nativeNerveMappingPathPostcomp (finiteInactiveClassifyingLoop R h g)
    (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R))

/-- Every value is the SAME original inactive family applied to its
original normalized group loop, retaining EVERY active parameter. -/
private theorem independentBGLInactiveNaturalLoopMappingPath_eq_recipe
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    independentBGLInactiveNaturalLoopMappingPath R h g =
      NatTrans.nativeNerveMappingPathPostcomp (finiteInactiveClassifyingLoop R h g)
        (originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
          (independentBGLCellPoint R)) := rfl

private theorem inactiveMappingSource_eq_realization
    (R : Type u) [Ring R] (n : ℕ) :
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
        CGWH.nativeInterval.{u, u} =
      SSet.toCGWH.{u, u}.obj (nerve ((finiteClassifyingCategoryDiagram R).obj n)) ⊗
        SSet.toCGWH.{u, u}.obj (Δ[1] : SSet.{u}) := rfl

private theorem inactiveMappingBGL_eq_realization (R : Type u) [Ring R] :
    BGL.{u} R = SSet.toCGWH.{u, u}.obj (classifyingNerve R) := rfl

private theorem inactiveMappingFamily_eq_original
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N) :
    independentBGLInactiveFamilyToNativeModel R h =
      originalInactiveFamilyToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h := rfl

private theorem inactiveMappingPrism_model_eq_computed
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h g =
      eqToHom (inactiveMappingSource_eq_realization R n) ≫
        ((SSet.realizationTensorIsoCGWH.{u, u}
            (nerve ((finiteClassifyingCategoryDiagram R).obj n)) (Δ[1] : SSet.{u})).inv ≫
          SSet.toCGWH.{u, u}.map
            (NatTrans.nerveHomotopyMap (initialInactiveClassifyingLoop R h g)) ≫
          (eqToHom (inactiveMappingBGL_eq_realization R).symm ≫
            originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
              (independentBGLCellPoint R))) := by
  let K : SSet.{u} := nerve ((finiteClassifyingCategoryDiagram R).obj n)
  let J : SSet.{u} := Δ[1]
  let L : SSet.{u} := classifyingNerve R
  let F := SSet.toCGWH.{u, u}
  let Y := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  let β : K ⊗ J ⟶ L := NatTrans.nerveHomotopyMap (initialInactiveClassifyingLoop R h g)
  let q : BGL.{u} R ⟶ Y := originalBGLToPlusNativeModel R
    (independentBGLCellInclusion R) (independentBGLCellPoint R)
  let q₀ : F.obj L ⟶ Y := eqToHom (inactiveMappingBGL_eq_realization R).symm ≫ q
  have hq₀ : q₀ = eqToHom (inactiveMappingBGL_eq_realization R).symm ≫ q := rfl
  let e : F.obj K ⊗ F.obj J ⟶ F.obj (K ⊗ J) :=
    (SSet.realizationTensorIsoCGWH.{u, u} K J).inv
  let s₀ : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CGWH.nativeInterval.{u, u} ⟶ F.obj K ⊗ F.obj J :=
    eqToHom (inactiveMappingSource_eq_realization R n)
  change originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R) h g = s₀ ≫ (e ≫ F.map β ≫ q₀)
  let C₀ := SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
  let D₀ := SingleObj (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ
  let θ := initialInactiveClassifyingFamilyFunctor R (h)
  let k : SingleObj.star (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ ⟶
      SingleObj.star (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ :=
    MulOpposite.op (g)⁻¹
  let ND : SSet.{u} := CategoryTheory.nerve D₀
  let NP : SSet.{u} := CategoryTheory.nerve (C₀ × D₀)
  let edge : J ⟶ ND := SSet.yonedaEquiv.symm (CategoryTheory.nerve.edgeMk k).edge
  let Q : K ⊗ ND ⟶ K ⨯ ND :=
    CategoryTheory.Limits.prod.lift
      (CartesianMonoidalCategory.fst K ND) (CartesianMonoidalCategory.snd K ND)
  let nInv : K ⨯ ND ⟶ NP := (CategoryTheory.nerveProdIso C₀ D₀).inv
  let nF : NP ⟶ L := CategoryTheory.nerveMap θ
  have hPair : CategoryTheory.Limits.prod.lift
      (CartesianMonoidalCategory.fst K J)
      (CartesianMonoidalCategory.snd K J ≫ edge) = (K ◁ edge) ≫ Q := by
    apply CategoryTheory.Limits.prod.hom_ext
    · rw [Category.assoc, CategoryTheory.Limits.prod.lift_fst,
        CategoryTheory.Limits.prod.lift_fst, CartesianMonoidalCategory.whiskerLeft_fst]
    · rw [Category.assoc, CategoryTheory.Limits.prod.lift_snd,
        CategoryTheory.Limits.prod.lift_snd, CartesianMonoidalCategory.whiskerLeft_snd]
  have hBeta : β = ((K ◁ edge) ≫ (Q ≫ nInv)) ≫ nF := by
    have h := initialInactiveClassifyingLoop_nerveHomotopyMap R
      (h) (g)
    change β = CategoryTheory.Limits.prod.lift
      (CartesianMonoidalCategory.fst K J)
      (CartesianMonoidalCategory.snd K J ≫ edge) ≫ nInv ≫ nF at h
    rw [hPair] at h
    simpa only [Category.assoc] using h
  let T₁ := SSet.realizationTensorIsoCGWH.{u, u} K ND
  let P₁ := CategoryTheory.classifyingSpaceCGWHProductIso.{u} C₀ D₀
  let W : F.obj K ⊗ F.obj J ⟶ F.obj K ⊗ F.obj ND := F.obj K ◁ F.map edge
  let c : F.obj K ⊗ F.obj J ⟶ F.obj L := W ≫ P₁.inv ≫ F.map nF
  have hInv : T₁.inv ≫ F.map (Q ≫ nInv) = P₁.inv :=
    (CategoryTheory.classifyingSpaceCGWHProductIso_inv_tensor.{u} C₀ D₀).symm
  have hTensor : e ≫ F.map (K ◁ edge) = W ≫ T₁.inv :=
    SSet.realizationTensorIsoCGWH_inv_whiskerLeft.{u, u} K edge
  have hCanonical : e ≫ F.map β = c := by
    calc
      _ = e ≫ F.map (((K ◁ edge) ≫ (Q ≫ nInv)) ≫ nF) :=
        congrArg (fun f : K ⊗ J ⟶ L => e ≫ F.map f) hBeta
      _ = (e ≫ F.map (K ◁ edge)) ≫ F.map (Q ≫ nInv) ≫ F.map nF := by
        simp only [Functor.map_comp, Category.assoc]
      _ = W ≫ (T₁.inv ≫ F.map (Q ≫ nInv)) ≫ F.map nF := by
        simpa only [Category.assoc] using
          congrArg (fun m : F.obj K ⊗ F.obj J ⟶ F.obj (K ⊗ ND) =>
            m ≫ F.map (Q ≫ nInv) ≫ F.map nF) hTensor
      _ = c :=
        congrArg (fun m : F.obj K ⊗ F.obj ND ⟶ F.obj NP => W ≫ m ≫ F.map nF) hInv
  have hPublic := CategoryTheory.productLoopNativeMap_eq.{u} C₀ D₀
    (SingleObj.star (InactivePerfectMatrixGroup R N (initialActiveIndices n N))ᵐᵒᵖ) k θ
  have hNative : originalInactiveLoopNativePrism R (h)
      (g) ≍ c :=
    (heq_of_eq hPublic).trans HEq.rfl
  have hNativeEq : originalInactiveLoopNativePrism R (h)
      (g) =
    s₀ ≫ c ≫ eqToHom (inactiveMappingBGL_eq_realization R).symm :=
    (CategoryTheory.conj_eqToHom_iff_heq _ _
      (inactiveMappingSource_eq_realization R n)
      (inactiveMappingBGL_eq_realization R)).2 hNative
  calc
    _ = originalInactiveLoopNativePrism R (h)
        (g) ≫ q := rfl
    _ = (s₀ ≫ c ≫ eqToHom (inactiveMappingBGL_eq_realization R).symm) ≫ q :=
      congrArg (fun m : CategoryTheory.groupClassifyingNative.{u, u}
          (Matrix.GeneralLinearGroup (Fin n) R) ⊗ CGWH.nativeInterval.{u, u} ⟶ BGL.{u} R =>
        m ≫ q) hNativeEq
    _ = s₀ ≫ (c ≫ q₀) := by
      rw [hq₀]
      simp only [Category.assoc]
    _ = s₀ ≫ (e ≫ F.map β ≫ q₀) := by
      simpa only [Category.assoc] using
        congrArg (fun m : F.obj K ⊗ F.obj J ⟶ F.obj L => s₀ ≫ m ≫ q₀) hCanonical.symm


private theorem inactiveMappingValue_of_casted_mapEq
    {A A' B B' Y : CGWH.{u, u}}
    (hA : A = A') (hB : B = B')
    (r : A ⟶ B) (r' : A' ⟶ B') (hr : r ≍ r')
    (q : B ⟶ Y) (ψ : A ⟶ Y)
    (hψ : eqToHom hA ≫ (r' ≫ eqToHom hB.symm ≫ q) = ψ)
    (x : A) : q (r x) = ψ x := by
  have hR : r = eqToHom hA ≫ r' ≫ eqToHom hB.symm :=
    (CategoryTheory.conj_eqToHom_iff_heq r r' hA hB).2 hr
  have hComp : r ≫ q = ψ := by
    calc
      _ = (eqToHom hA ≫ r' ≫ eqToHom hB.symm) ≫ q :=
        congrArg (fun f : A ⟶ B => f ≫ q) hR
      _ = ψ := by simpa only [Category.assoc] using hψ
  exact (ConcreteCategory.comp_apply (C := CGWH.{u, u}) r q x).symm.trans
    (ConcreteCategory.congr_hom hComp x)

private theorem independentBGLInactiveNaturalLoopMappingPath_apply_computed
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N))
    (t : unitInterval)
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)) :
    independentBGLInactiveNaturalLoopMappingPath R h g t a =
      independentBGLInactiveFamilyToNativeModel R h
        (CGWH.tensorMk a (CategoryTheory.groupClassifyingNativeLoop.{u, u}
          (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) g t)) := by
  rw [independentBGLInactiveNaturalLoopMappingPath_eq_recipe]
  let K : SSet.{u} := nerve ((finiteClassifyingCategoryDiagram R).obj n)
  let J : SSet.{u} := Δ[1]
  let L : SSet.{u} := classifyingNerve R
  let F := SSet.toCGWH.{u, u}
  let Y := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  let α := finiteInactiveClassifyingLoop R h g
  let β : K ⊗ J ⟶ L := NatTrans.nerveHomotopyMap (initialInactiveClassifyingLoop R h g)
  let q : BGL.{u} R ⟶ Y := originalBGLToPlusNativeModel R
    (independentBGLCellInclusion R) (independentBGLCellPoint R)
  let q₀ : F.obj L ⟶ Y := eqToHom (inactiveMappingBGL_eq_realization R).symm ≫ q
  let e : F.obj K ⊗ F.obj J ⟶ F.obj (K ⊗ J) :=
    (SSet.realizationTensorIsoCGWH.{u, u} K J).inv
  let p : F.obj (K ⊗ J) ⟶ F.obj L := F.map (NatTrans.nerveHomotopyMap α)
  let rNative : CategoryTheory.groupClassifyingNative.{u, u}
      (Matrix.GeneralLinearGroup (Fin n) R) ⊗ CGWH.nativeInterval.{u, u} ⟶ BGL.{u} R :=
    e ≫ p
  have hNativeMap : rNative ≍ e ≫ p := HEq.rfl
  let z : (CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CGWH.nativeInterval.{u, u} : CGWH.{u, u}) :=
    CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm t)
  let s₀ : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CGWH.nativeInterval.{u, u} ⟶ F.obj K ⊗ F.obj J :=
    eqToHom (inactiveMappingSource_eq_realization R n)
  have hMap : e ≫ p ≫ q₀ = e ≫ F.map β ≫ q₀ :=
    congrArg (fun f : K ⊗ J ⟶ L => e ≫ F.map f ≫ q₀)
      (finiteInactiveClassifyingLoop_nerveHomotopyMap R h g)
  have hPrism : originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h g =
      s₀ ≫ (e ≫ F.map β ≫ q₀) :=
    inactiveMappingPrism_model_eq_computed R h g
  have he : s₀ ≫ (e ≫ p ≫ q₀) =
      originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h g :=
    (congrArg (fun f : F.obj K ⊗ F.obj J ⟶ Y => s₀ ≫ f) hMap).trans hPrism.symm
  have hCastMap : eqToHom (inactiveMappingSource_eq_realization R n) ≫
        ((e ≫ p) ≫ eqToHom (inactiveMappingBGL_eq_realization R).symm ≫ q) =
      originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h g := by
    simpa only [s₀, q₀, Category.assoc] using he
  have hApply : NatTrans.nativeNerveMappingPathPostcomp α q t a = q (rNative z) :=
    NatTrans.nativeNerveMappingPathPostcomp_apply α q t a
  have hValue : q (rNative z) =
      originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h g z :=
    inactiveMappingValue_of_casted_mapEq
      (inactiveMappingSource_eq_realization R n) (inactiveMappingBGL_eq_realization R)
      rNative (e ≫ p) hNativeMap q
      (originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h g) hCastMap z
  calc
    _ = q (rNative z) := hApply
    _ = originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h g z := hValue
    _ = independentBGLInactiveFamilyToNativeModel R h
        (CGWH.tensorMk a (CategoryTheory.groupClassifyingNativeLoop.{u, u}
          (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) g t)) := by
      rw [inactiveMappingFamily_eq_original]
      exact originalInactiveLoopPrismToModel_apply R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h g a t

public theorem independentBGLInactiveNaturalLoopMappingPath_apply
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N))
    (t : unitInterval)
    (a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)) :
    independentBGLInactiveNaturalLoopMappingPath R h g t a =
      independentBGLInactiveFamilyToNativeModel R h
        (CGWH.tensorMk a (CategoryTheory.groupClassifyingNativeLoop.{u, u}
          (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) g t)) :=
  independentBGLInactiveNaturalLoopMappingPath_apply_computed R h g t a

/-- The actual inactive element gives ONE nullhomotopy of its ORIGINAL
WHOLE mapping-space loop. Its perfect group, plus map, product comparison
and joint filler are all derived internally, over every unchanged Ring. -/
public theorem independentBGLInactiveNaturalLoopMappingPath_null
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N)
    (g : InactivePerfectMatrixGroup R N (initialActiveIndices n N)) :
    (independentBGLInactiveNaturalLoopMappingPath R h g).Homotopic
      (Path.refl (independentBGLFiniteMapToNativeModel R n)) := by
  let G := InactivePerfectMatrixGroup R N (initialActiveIndices n N)
  let x := CategoryTheory.groupClassifyingNativePoint.{u, u} G
  let γ := CategoryTheory.groupClassifyingNativeLoop.{u, u} G g
  let p := independentBGLInactiveNaturalLoopMappingPath R h g
  obtain ⟨K⟩ := exists_independentBGLInactiveFamilyFiller R h γ
  have hfixed (a : CategoryTheory.groupClassifyingNative.{u, u}
      (Matrix.GeneralLinearGroup (Fin n) R)) :
      independentBGLInactiveFamilyToNativeModel R h (CGWH.tensorMk a x) =
        independentBGLFiniteMapToNativeModel R n a := by
    exact (K.source 0 a).symm.trans ((K.zero 0 a).trans
      ((independentBGLInactiveNaturalLoopMappingPath_apply R h g 0 a).symm.trans
        (congrArg (fun f : C(CategoryTheory.groupClassifyingNative.{u, u}
          (Matrix.GeneralLinearGroup (Fin n) R),
            TopCat.nativeSingularSpace (independentBGLCellTarget R)) => f a) p.source)))
  apply CGWH.mappingSpaceLoop_homotopic_refl_of_square p K.map
  · intro s a
    exact (K.zero s a).trans
      (independentBGLInactiveNaturalLoopMappingPath_apply R h g s a).symm
  · intro s a
    exact (K.one s a).trans (hfixed a)
  · intro t a
    exact (K.source t a).trans (hfixed a)
  · intro t a
    exact (K.target t a).trans (hfixed a)

end AlgebraicKTheory.StableGL

end
