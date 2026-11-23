/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.NativeInactiveFamily
public import MathlibExt.KTheory.Ring.StableGeneralLinear.IndependentPlusPoint
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteUnitStabilizationDifferences
public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteUnitDifferenceNaturalLoop

/-!
# Original finite inactive families in the actual independent BGL plus

This specialization supplies the actual independently constructed target,
its original cell inclusion, its original point and the DERIVED point
cofibration. Every ring and every original finite BG_n parameter are kept.
The native target is only the derived pointed singular model of that SAME
cell target, with both original inverse homotopies, not a Q-model target.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory Simplicial

universe u

namespace AlgebraicKTheory.StableGL

private local instance independentBGLCellPointCofibrant (R : Type u) [Ring R] :
    Cofibration (TopCat.const (independentBGLCellPoint R) :
      TopCat.of PUnit.{u + 1} ⟶ independentBGLCellTarget R) :=
  independentBGLCellPoint_cofibration R

attribute [local instance] independentBGLCellPoint_cofibration

/-- The whole original finite active/inactive family in the actual
pointed native model of the SAME independent BGL cell plus. -/
public abbrev independentBGLInactiveFamilyToNativeModel
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N) :
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CategoryTheory.groupClassifyingNative.{u, u}
        (InactivePerfectMatrixGroup R N (initialActiveIndices n N)) ⟶
      TopCat.nativeSingularSpace (independentBGLCellTarget R) :=
  originalInactiveFamilyToModel R (independentBGLCellInclusion R)
    (independentBGLCellPoint R) h

private theorem independentBGLInactiveFamilyToNativeModel_eq_original
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N) :
    independentBGLInactiveFamilyToNativeModel R h =
      originalInactiveFamilyToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) h := rfl

/-- Its marked image is the original singular vertex of the original
independent target point. -/
public theorem independentBGLInactiveFamilyToNativeModel_point
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N) :
    independentBGLInactiveFamilyToNativeModel R h
        (CGWH.tensorMk
          (CategoryTheory.groupClassifyingNativePoint.{u, u} (Matrix.GeneralLinearGroup (Fin n) R))
          (CategoryTheory.groupClassifyingNativePoint.{u, u}
            (InactivePerfectMatrixGroup R N (initialActiveIndices n N)))) =
      TopCat.nativeSingularPoint (independentBGLCellTarget R) (independentBGLCellPoint R) := by
  rw [independentBGLInactiveFamilyToNativeModel_eq_original]
  exact originalInactiveFamilyToModel_point R (independentBGLCellInclusion R)
    (independentBGLCellPoint R) (independentBGLCellInclusion_point R) h

/-- The complete jointly continuous original inactive square exists over
EVERY unchanged ring and all original BG_n parameters. Its plus map,
point cofibrancy, target commutativity, auxiliary perfect-group plus,
CW-product inverse and raw mapping-space contraction are all derived. -/
public theorem exists_independentBGLInactiveFamilyFiller
    (R : Type u) [Ring R] {n N : ℕ} (h : n ≤ N)
    (γ : Path
      (CategoryTheory.groupClassifyingNativePoint.{u, u}
        (InactivePerfectMatrixGroup R N (initialActiveIndices n N)))
      (CategoryTheory.groupClassifyingNativePoint.{u, u}
        (InactivePerfectMatrixGroup R N (initialActiveIndices n N)))) :
    Nonempty (CGWH.NativeParameterLoopFiller (independentBGLInactiveFamilyToNativeModel R h) γ) := by
  rw [independentBGLInactiveFamilyToNativeModel_eq_original]
  exact exists_originalInactiveFamilyFiller R (independentBGLCellInclusion R)
    (independentBGLCellPoint R) (independentBGLCellInclusion_point R)
      (independentBGLCellInclusion_isPlus R) h γ

/-- The actual normalized loop of the COMPUTED consecutive unit
permutation difference, in its DERIVED perfect inactive image group. -/
public abbrev independentBGLLeftUnitDifferenceLoop
    (R : Type u) [Ring R] (n : ℕ) :
    Path
      (CategoryTheory.groupClassifyingNativePoint.{u, u} (LeftUnitDifferencePerfectGroup R n))
      (CategoryTheory.groupClassifyingNativePoint.{u, u} (LeftUnitDifferencePerfectGroup R n)) :=
  CategoryTheory.groupClassifyingNativeLoop.{u, u} (LeftUnitDifferencePerfectGroup R n)
    (leftUnitDifferencePerfectFactor R n)

/-- The consecutive unit difference has one actual jointly continuous
filler over ALL original BG_n parameters and over EVERY unchanged ring.
The rank, fixed-set proof, parity, perfect image and original difference
matrix are computed; no factor or homotopy witness is assumed. -/
public theorem exists_independentBGLLeftUnitDifferenceFiller
    (R : Type u) [Ring R] (n : ℕ) :
    Nonempty (CGWH.NativeParameterLoopFiller
      (independentBGLInactiveFamilyToNativeModel R (leftUnitCommonRank_bound.{u} n))
        (independentBGLLeftUnitDifferenceLoop R n)) :=
  exists_independentBGLInactiveFamilyFiller R (leftUnitCommonRank_bound.{u} n)
    (independentBGLLeftUnitDifferenceLoop R n)

/-- The literal native cylinder of the WHOLE original consecutive unit
natural-transformation difference, in the SAME independent target model. -/
public abbrev independentBGLLeftUnitDifferenceNativeCylinder
    (R : Type u) [Ring R] (n : ℕ) :
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CGWH.nativeInterval.{u, u} ⟶ TopCat.nativeSingularSpace (independentBGLCellTarget R) :=
  (SSet.realizationTensorIsoCGWH.{u, u}
    (CategoryTheory.nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ))
    (Δ[1] : SSet.{u})).inv ≫
      SSet.toCGWH.{u, u}.map
        (CategoryTheory.NatTrans.nerveHomotopyMap (finiteLeftUnitDifferenceLoop R n)) ≫
          originalBGLToPlusNativeModel R (independentBGLCellInclusion R) (independentBGLCellPoint R)

private theorem independentInactiveNativeMapComposite_congr
    {K L : SSet.{u}} {A B : CGWH.{u, u}}
    (e : A ⟶ SSet.toCGWH.{u, u}.obj K)
    (g : SSet.toCGWH.{u, u}.obj L ⟶ B)
    (α β : K ⟶ L) (h : α = β) :
    e ≫ SSet.toCGWH.{u, u}.map α ≫ g =
      e ≫ SSet.toCGWH.{u, u}.map β ≫ g :=
  congrArg (fun f : K ⟶ L => e ≫ SSet.toCGWH.{u, u}.map f ≫ g) h

private theorem independentInactiveCylinderSource_eq_realization
    (R : Type u) [Ring R] (n : ℕ) :
    CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
        CGWH.nativeInterval.{u, u} =
      SSet.toCGWH.{u, u}.obj
          (CategoryTheory.nerve (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)) ⊗
        SSet.toCGWH.{u, u}.obj (Δ[1] : SSet.{u}) := rfl

private theorem independentInactiveBGL_eq_realization (R : Type u) [Ring R] :
    BGL.{u} R = SSet.toCGWH.{u, u}.obj (classifyingNerve R) := rfl

private theorem independentBGLLeftUnitDifferenceNativeCylinder_eq_original
    (R : Type u) [Ring R] (n : ℕ) :
    independentBGLLeftUnitDifferenceNativeCylinder R n =
      originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) (leftUnitCommonRank_bound.{u} n)
          (leftUnitDifferencePerfectFactor R n) := by
  let K : SSet.{u} := CategoryTheory.nerve
    (SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ)
  let J : SSet.{u} := Δ[1]
  let L : SSet.{u} := classifyingNerve R
  let F := SSet.toCGWH.{u, u}
  let Y := TopCat.nativeSingularSpace (independentBGLCellTarget R)
  let e : F.obj K ⊗ F.obj J ⟶ F.obj (K ⊗ J) :=
    (SSet.realizationTensorIsoCGWH.{u, u} K J).inv
  let g : F.obj L ⟶ Y :=
    eqToHom (independentInactiveBGL_eq_realization R).symm ≫
      originalBGLToPlusNativeModel R (independentBGLCellInclusion R) (independentBGLCellPoint R)
  let α : K ⊗ J ⟶ L :=
    CategoryTheory.NatTrans.nerveHomotopyMap (finiteLeftUnitDifferenceLoop R n)
  let β : K ⊗ J ⟶ L :=
    CategoryTheory.NatTrans.nerveHomotopyMap
      (initialInactiveClassifyingLoop R (leftUnitCommonRank_bound.{u} n)
        (leftUnitDifferencePerfectFactor R n))
  have hMap : e ≫ F.map α ≫ g = e ≫ F.map β ≫ g :=
    independentInactiveNativeMapComposite_congr e g α β
      (finiteLeftUnitDifferenceLoop_nerveHomotopyMap R n)
  let a : CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R) ⊗
      CGWH.nativeInterval.{u, u} ⟶ F.obj K ⊗ F.obj J :=
    eqToHom (independentInactiveCylinderSource_eq_realization R n)
  have hCylinder : independentBGLLeftUnitDifferenceNativeCylinder R n =
      a ≫ (e ≫ F.map α ≫ g) := by
    rfl
  have hPrism : originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) (leftUnitCommonRank_bound.{u} n)
          (leftUnitDifferencePerfectFactor R n) =
      a ≫ (e ≫ F.map β ≫ g) := by
    let C₀ := SingleObj (Matrix.GeneralLinearGroup (Fin n) R)ᵐᵒᵖ
    let D₀ := SingleObj (LeftUnitDifferencePerfectGroup R n)ᵐᵒᵖ
    let θ := initialInactiveClassifyingFamilyFunctor R (leftUnitCommonRank_bound.{u} n)
    let k : SingleObj.star (LeftUnitDifferencePerfectGroup R n)ᵐᵒᵖ ⟶
        SingleObj.star (LeftUnitDifferencePerfectGroup R n)ᵐᵒᵖ :=
      MulOpposite.op (leftUnitDifferencePerfectFactor R n)⁻¹
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
        (leftUnitCommonRank_bound.{u} n) (leftUnitDifferencePerfectFactor R n)
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
      (SingleObj.star (LeftUnitDifferencePerfectGroup R n)ᵐᵒᵖ) k θ
    have hNative : originalInactiveLoopNativePrism R (leftUnitCommonRank_bound.{u} n)
        (leftUnitDifferencePerfectFactor R n) ≍ c :=
      (heq_of_eq hPublic).trans HEq.rfl
    have hNativeEq : originalInactiveLoopNativePrism R (leftUnitCommonRank_bound.{u} n)
        (leftUnitDifferencePerfectFactor R n) =
      a ≫ c ≫ eqToHom (independentInactiveBGL_eq_realization R).symm :=
      (CategoryTheory.conj_eqToHom_iff_heq _ _
        (independentInactiveCylinderSource_eq_realization R n)
        (independentInactiveBGL_eq_realization R)).2 hNative
    let q := originalBGLToPlusNativeModel R (independentBGLCellInclusion R)
      (independentBGLCellPoint R)
    calc
      _ = originalInactiveLoopNativePrism R (leftUnitCommonRank_bound.{u} n)
          (leftUnitDifferencePerfectFactor R n) ≫ q := rfl
      _ = (a ≫ c ≫ eqToHom (independentInactiveBGL_eq_realization R).symm) ≫ q :=
        congrArg (fun m : CategoryTheory.groupClassifyingNative.{u, u}
            (Matrix.GeneralLinearGroup (Fin n) R) ⊗ CGWH.nativeInterval.{u, u} ⟶ BGL.{u} R =>
          m ≫ q) hNativeEq
      _ = a ≫ (c ≫ g) := by simp only [g, q, Category.assoc]
      _ = a ≫ (e ≫ F.map β ≫ g) := by
        simpa only [Category.assoc] using
          congrArg (fun m : F.obj K ⊗ F.obj J ⟶ F.obj L => a ≫ m ≫ g) hCanonical.symm
  exact hCylinder.trans
    ((congrArg (fun f : F.obj K ⊗ F.obj J ⟶ Y => a ≫ f) hMap).trans hPrism.symm)

/-- The whole original unit-difference cylinder is the SAME original
inactive perfect-family prism, by the computed natural-loop equality. -/
public theorem independentBGLLeftUnitDifferenceNativeCylinder_eq
    (R : Type u) [Ring R] (n : ℕ) :
    independentBGLLeftUnitDifferenceNativeCylinder R n =
      originalInactiveLoopPrismToModel R (independentBGLCellInclusion R)
        (independentBGLCellPoint R) (leftUnitCommonRank_bound.{u} n)
          (leftUnitDifferencePerfectFactor R n) :=
  independentBGLLeftUnitDifferenceNativeCylinder_eq_original R n

/-- One jointly continuous square fills the WHOLE ORIGINAL native unit
difference on every original BG_n parameter. ALL four original faces are
retained, over every unchanged ring and without a supplied filler/model. -/
public theorem exists_independentBGLLeftUnitDifferenceNativeCylinder_filler
    (R : Type u) [Ring R] (n : ℕ) :
    let A := CategoryTheory.groupClassifyingNative.{u, u} (Matrix.GeneralLinearGroup (Fin n) R)
    let Y := TopCat.nativeSingularSpace (independentBGLCellTarget R)
    let φ := independentBGLInactiveFamilyToNativeModel R (leftUnitCommonRank_bound.{u} n)
    let x := CategoryTheory.groupClassifyingNativePoint.{u, u} (LeftUnitDifferencePerfectGroup R n)
    ∃ K : C((unitInterval × unitInterval) × A, Y),
      (∀ s a, K ((0, s), a) = independentBGLLeftUnitDifferenceNativeCylinder R n
        (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm s))) ∧
      (∀ s a, K ((1, s), a) = φ (CGWH.tensorMk a x)) ∧
      (∀ t a, K ((t, 0), a) = φ (CGWH.tensorMk a x)) ∧
      (∀ t a, K ((t, 1), a) = φ (CGWH.tensorMk a x)) := by
  obtain ⟨K⟩ := exists_independentBGLLeftUnitDifferenceFiller R n
  refine ⟨K.map, ?_, K.one, K.source, K.target⟩
  intro s a
  have hface : independentBGLLeftUnitDifferenceNativeCylinder R n
      (CGWH.tensorMk a (CGWH.nativeIntervalHomeomorph.{u, u}.symm s)) =
    independentBGLInactiveFamilyToNativeModel R (leftUnitCommonRank_bound.{u} n)
      (CGWH.tensorMk a (independentBGLLeftUnitDifferenceLoop R n s)) := by
    rw [independentBGLLeftUnitDifferenceNativeCylinder_eq,
      independentBGLInactiveFamilyToNativeModel_eq_original]
    exact originalInactiveLoopPrismToModel_apply R (independentBGLCellInclusion R)
      (independentBGLCellPoint R) (leftUnitCommonRank_bound.{u} n)
        (leftUnitDifferencePerfectFactor R n) a s
  exact (K.zero s a).trans hface.symm

end AlgebraicKTheory.StableGL

end
