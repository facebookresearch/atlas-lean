/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Standard
public import MathlibExt.Analysis.CStarAlgebra.Module.Unitary
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.Logic.Equiv.Nat

/-!
# Unitary equivalences of standard right C-star modules

This file constructs the canonical unitary equivalences induced by a
reindexing of coordinates and by splitting a sum of coordinate types.  In
particular, the countable standard module is unitarily equivalent to the
direct sum of two copies of itself.
-/

@[expose] public section

noncomputable section

open Set
open scoped RightActions

namespace CStarModule.Right.Standard

universe uB uι uκ

variable {B : Type uB} [NonUnitalCStarAlgebra B]
variable {ι : Type uι} {κ : Type uκ}

local instance coefficientSpectralOrder : PartialOrder Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrder Bᵐᵒᵖ

local instance coefficientSpectralOrderedRing : StarOrderedRing Bᵐᵒᵖ :=
  CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ

/-! ## Reindexing -/

/-- Reindex finite-support standard vectors along an equivalence of
coordinate types. -/
def preReindexLinearEquiv (e : ι ≃ κ) :
    StandardPre B ι ≃ₗ[ℂ] StandardPre B κ :=
  (StandardPre.toFinsuppLinearEquiv (B := B) (ι := ι)).trans
    ((Finsupp.domLCongr (R := ℂ) (M := B) e).trans
      (StandardPre.toFinsuppLinearEquiv (B := B) (ι := κ)).symm)

/-- Reindexing has the expected coordinate formula. -/
@[simp]
theorem preReindexLinearEquiv_apply
    (e : ι ≃ κ) (x : StandardPre B ι) (j : κ) :
    preReindexLinearEquiv (B := B) e x j = x (e.symm j) := by
  change (Finsupp.domLCongr (R := ℂ) (M := B) e
    (StandardPre.toFinsupp x)) j = x (e.symm j)
  simp

/-- The inverse reindexing formula. -/
@[simp]
theorem preReindexLinearEquiv_symm_apply
    (e : ι ≃ κ) (x : StandardPre B κ) (i : ι) :
    (preReindexLinearEquiv (B := B) e).symm x i = x (e i) := by
  have h := preReindexLinearEquiv_apply
    (B := B) e ((preReindexLinearEquiv (B := B) e).symm x) (e i)
  simpa using h.symm

/-- Reindexing preserves the coefficient-valued inner product. -/
theorem preReindexLinearEquiv_rightInner
    (e : ι ≃ κ) (x y : StandardPre B ι) :
    CStarModule.rightInner (B := B)
        (preReindexLinearEquiv (B := B) e x)
        (preReindexLinearEquiv (B := B) e y) =
      CStarModule.rightInner (B := B) x y := by
  classical
  rw [StandardPre.rightInner_apply, StandardPre.rightInner_apply]
  rw [Finsupp.sum]
  change (∑ j ∈ (Finsupp.equivMapDomain e
      (StandardPre.toFinsupp x)).support,
        star (x (e.symm j)) * y (e.symm j)) = _
  rw [Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.mapDomain_support_of_injective e.injective,
    Finset.sum_image]
  · simp only [e.symm_apply_apply]
    rw [Finsupp.sum]
  · exact fun _ _ _ _ h ↦ e.injective h

/-- Reindexing preserves the standard-module norm. -/
@[simp]
theorem norm_preReindexLinearEquiv
    (e : ι ≃ κ) (x : StandardPre B ι) :
    ‖preReindexLinearEquiv (B := B) e x‖ = ‖x‖ := by
  calc
    ‖preReindexLinearEquiv (B := B) e x‖ =
        √‖CStarModule.rightInner (B := B)
          (preReindexLinearEquiv (B := B) e x)
          (preReindexLinearEquiv (B := B) e x)‖ :=
      CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner _
    _ = √‖CStarModule.rightInner (B := B) x x‖ := by
      rw [preReindexLinearEquiv_rightInner]
    _ = ‖x‖ :=
      (CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner x).symm

theorem reindexComparison_norm
    (e : ι ≃ κ) (x : StandardPre B ι) :
    ‖(ofPre (B := B) (ι := κ)).toLinearMap
        (preReindexLinearEquiv (B := B) e x)‖ =
      ‖(ofPre (B := B) (ι := ι)).toLinearMap x‖ := by
  change ‖ofPre (preReindexLinearEquiv (B := B) e x)‖ = ‖ofPre x‖
  rw [(ofPre (B := B) (ι := κ)).norm_map,
    (ofPre (B := B) (ι := ι)).norm_map,
    norm_preReindexLinearEquiv]

/-- The linear isometric equivalence of completed standard modules induced
by a coordinate equivalence. -/
noncomputable def reindexLinearIsometryEquiv (e : ι ≃ κ) :
    Standard B ι ≃ₗᵢ[ℂ] Standard B κ :=
  (preReindexLinearEquiv (B := B) e).extendOfIsometry
    (ofPre (B := B) (ι := ι)).toLinearMap
    (ofPre (B := B) (ι := κ)).toLinearMap
    (denseRange_ofPre (B := B) (ι := ι))
    (denseRange_ofPre (B := B) (ι := κ))
    (reindexComparison_norm (B := B) e)

/-- Completed reindexing extends finite-support reindexing. -/
@[simp]
theorem reindexLinearIsometryEquiv_ofPre
    (e : ι ≃ κ) (x : StandardPre B ι) :
    reindexLinearIsometryEquiv (B := B) e (ofPre x) =
      ofPre (preReindexLinearEquiv (B := B) e x) := by
  unfold reindexLinearIsometryEquiv
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _
    (reindexComparison_norm (B := B) e) x

/-- Completed reindexing has the expected coordinate formula. -/
@[simp]
theorem coord_reindexLinearIsometryEquiv
    (e : ι ≃ κ) (x : Standard B ι) (j : κ) :
    coord j (reindexLinearIsometryEquiv (B := B) e x) =
      coord (e.symm j) x := by
  have hleft : Continuous fun x : Standard B ι ↦
      coord j (reindexLinearIsometryEquiv (B := B) e x) :=
    (coord j).continuous.comp
      (reindexLinearIsometryEquiv (B := B) e).continuous
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq hleft (coord (e.symm j)).continuous) ?_
  intro x
  change coord j
      (reindexLinearIsometryEquiv (B := B) e
        (ofPre x : Standard B ι)) =
    coord (e.symm j) (ofPre x : Standard B ι)
  rw [reindexLinearIsometryEquiv_ofPre, coord_ofPre, coord_ofPre,
    preReindexLinearEquiv_apply]

/-- Completed reindexing preserves the coefficient-valued inner product. -/
theorem reindexLinearIsometryEquiv_rightInner
    (e : ι ≃ κ) (x y : Standard B ι) :
    CStarModule.rightInner (B := B)
        (reindexLinearIsometryEquiv (B := B) e x)
        (reindexLinearIsometryEquiv (B := B) e y) =
      CStarModule.rightInner (B := B) x y := by
  have hdense : DenseRange
      (fun p : StandardPre B ι × StandardPre B ι ↦
        (ofPre p.1, ofPre p.2)) :=
    (denseRange_ofPre (B := B) (ι := ι)).prodMap
      (denseRange_ofPre (B := B) (ι := ι))
  have hfun :
      (fun p : Standard B ι × Standard B ι ↦
        CStarModule.rightInner (B := B)
          (reindexLinearIsometryEquiv (B := B) e p.1)
          (reindexLinearIsometryEquiv (B := B) e p.2)) =
      (fun p : Standard B ι × Standard B ι ↦
        CStarModule.rightInner (B := B) p.1 p.2) := by
    apply Continuous.ext_on hdense
    · exact CStarModule.continuous_rightInner.comp
        (((reindexLinearIsometryEquiv (B := B) e).continuous.comp
            continuous_fst).prodMk
          ((reindexLinearIsometryEquiv (B := B) e).continuous.comp
            continuous_snd))
    · exact CStarModule.continuous_rightInner
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      change CStarModule.rightInner (B := B)
          (reindexLinearIsometryEquiv (B := B) e
            (ofPre x : Standard B ι))
          (reindexLinearIsometryEquiv (B := B) e
            (ofPre y : Standard B ι)) =
        CStarModule.rightInner (B := B)
          (ofPre x : Standard B ι) (ofPre y : Standard B ι)
      rw [reindexLinearIsometryEquiv_ofPre,
        reindexLinearIsometryEquiv_ofPre,
        rightInner_ofPre_ofPre, rightInner_ofPre_ofPre,
        preReindexLinearEquiv_rightInner]
  exact congrFun hfun (x, y)

/-- The unitary equivalence of standard modules induced by a coordinate
equivalence. -/
noncomputable def reindexUnitary (e : ι ≃ κ) :
    CStarModule.UnitaryEquiv B (Standard B ι) (Standard B κ) :=
  CStarModule.UnitaryEquiv.ofLinearIsometryEquiv
    (reindexLinearIsometryEquiv (B := B) e)
    (reindexLinearIsometryEquiv_rightInner (B := B) e)

@[simp]
theorem coord_reindexUnitary
    (e : ι ≃ κ) (x : Standard B ι) (j : κ) :
    coord j (reindexUnitary (B := B) e x) = coord (e.symm j) x :=
  coord_reindexLinearIsometryEquiv e x j

/-! ## Splitting a sum of coordinate types -/

/-- Split a finite-support standard vector on a sum of coordinate types into
its two components. -/
def preSumLinearEquiv :
    StandardPre B (ι ⊕ κ) ≃ₗ[ℂ]
      WithCStarModule Bᵐᵒᵖ
        (StandardPre B ι × StandardPre B κ) :=
  (StandardPre.toFinsuppLinearEquiv
      (B := B) (ι := ι ⊕ κ)).trans
    ((Finsupp.sumFinsuppLEquivProdFinsupp ℂ).trans
      (((StandardPre.toFinsuppLinearEquiv
          (B := B) (ι := ι)).symm.prodCongr
        (StandardPre.toFinsuppLinearEquiv
          (B := B) (ι := κ)).symm).trans
        (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ
          (StandardPre B ι × StandardPre B κ)).symm))

@[simp]
theorem preSumLinearEquiv_fst
    (x : StandardPre B (ι ⊕ κ)) (i : ι) :
    (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x).1 i =
      x (Sum.inl i) :=
  rfl

@[simp]
theorem preSumLinearEquiv_snd
    (x : StandardPre B (ι ⊕ κ)) (j : κ) :
    (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x).2 j =
      x (Sum.inr j) :=
  rfl

@[simp]
theorem preSumLinearEquiv_symm_inl
    (x : WithCStarModule Bᵐᵒᵖ
      (StandardPre B ι × StandardPre B κ)) (i : ι) :
    (preSumLinearEquiv (B := B) (ι := ι) (κ := κ)).symm x
        (Sum.inl i) = x.1 i :=
  rfl

@[simp]
theorem preSumLinearEquiv_symm_inr
    (x : WithCStarModule Bᵐᵒᵖ
      (StandardPre B ι × StandardPre B κ)) (j : κ) :
    (preSumLinearEquiv (B := B) (ι := ι) (κ := κ)).symm x
        (Sum.inr j) = x.2 j :=
  rfl

/-- Splitting finite-support vectors preserves the coefficient-valued inner
product. -/
theorem preSumLinearEquiv_rightInner
    (x y : StandardPre B (ι ⊕ κ)) :
    CStarModule.rightInner (B := B)
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x)
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) y) =
      CStarModule.rightInner (B := B) x y := by
  classical
  change CStarModule.rightInner (B := B)
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x).1
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) y).1 +
      CStarModule.rightInner (B := B)
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x).2
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) y).2 =
    CStarModule.rightInner (B := B) x y
  rw [StandardPre.rightInner_apply, StandardPre.rightInner_apply,
    StandardPre.rightInner_apply]
  have hx :
      (StandardPre.toFinsupp
          (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x).1).sumElim
        (StandardPre.toFinsupp
          (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x).2) =
      StandardPre.toFinsupp x := by
    ext s
    cases s with
    | inl i => exact preSumLinearEquiv_fst x i
    | inr j => exact preSumLinearEquiv_snd x j
  rw [← hx, Finsupp.sum_sumElim]
  rfl

/-- Splitting finite-support vectors preserves the standard-module norm. -/
@[simp]
theorem norm_preSumLinearEquiv
    (x : StandardPre B (ι ⊕ κ)) :
    ‖preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x‖ = ‖x‖ := by
  calc
    ‖preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x‖ =
        √‖CStarModule.rightInner (B := B)
          (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x)
          (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x)‖ :=
      CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner _
    _ = √‖CStarModule.rightInner (B := B) x x‖ := by
      rw [preSumLinearEquiv_rightInner]
    _ = ‖x‖ :=
      (CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner x).symm

/-- Include a pair of finite-support vectors into the completed direct sum. -/
def productOfPre :
    WithCStarModule Bᵐᵒᵖ
        (StandardPre B ι × StandardPre B κ) →ₗ[ℂ]
      WithCStarModule Bᵐᵒᵖ
        (Standard B ι × Standard B κ) :=
  (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ
      (Standard B ι × Standard B κ)).symm.toLinearMap.comp
    (((ofPre (B := B) (ι := ι)).toLinearMap.prodMap
      (ofPre (B := B) (ι := κ)).toLinearMap).comp
      (WithCStarModule.linearEquiv ℂ Bᵐᵒᵖ
        (StandardPre B ι × StandardPre B κ)).toLinearMap)

/-- The product inclusion acts componentwise. -/
@[simp]
theorem productOfPre_apply
    (x : WithCStarModule Bᵐᵒᵖ
      (StandardPre B ι × StandardPre B κ)) :
    WithCStarModule.equiv Bᵐᵒᵖ
        (Standard B ι × Standard B κ)
        (productOfPre (B := B) (ι := ι) (κ := κ) x) =
      (ofPre x.1, ofPre x.2) :=
  rfl

/-- The componentwise finite-support inclusion has dense range in the
completed direct sum. -/
theorem denseRange_productOfPre :
    DenseRange (productOfPre (B := B) (ι := ι) (κ := κ)) := by
  let raw : StandardPre B ι × StandardPre B κ →L[ℂ]
      Standard B ι × Standard B κ :=
    (ofPre (B := B) (ι := ι)).toContinuousLinearMap.prodMap
      (ofPre (B := B) (ι := κ)).toContinuousLinearMap
  have hraw : DenseRange raw :=
    (denseRange_ofPre (B := B) (ι := ι)).prodMap
      (denseRange_ofPre (B := B) (ι := κ))
  have hin : DenseRange
      (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
        (E := StandardPre B ι × StandardPre B κ)) :=
    (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
      (E := StandardPre B ι × StandardPre B κ)).surjective.denseRange
  have hout : DenseRange
      (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
        (E := Standard B ι × Standard B κ)).symm :=
    (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
      (E := Standard B ι × Standard B κ)).symm.surjective.denseRange
  have hcomp : DenseRange
      ((WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
          (E := Standard B ι × Standard B κ)).symm ∘
        raw ∘
        (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
          (E := StandardPre B ι × StandardPre B κ))) :=
    hout.comp (hraw.comp hin raw.continuous)
      (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
        (E := Standard B ι × Standard B κ)).symm.continuous
  have hmap :
      (fun x ↦ productOfPre (B := B) (ι := ι) (κ := κ) x) =
      ((WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
          (E := Standard B ι × Standard B κ)).symm ∘
        raw ∘
        (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
          (E := StandardPre B ι × StandardPre B κ))) := by
    funext x
    rfl
  change DenseRange
    (fun x ↦ productOfPre (B := B) (ι := ι) (κ := κ) x)
  rw [hmap]
  exact hcomp

/-- The componentwise finite-support inclusion preserves the
coefficient-valued inner product. -/
theorem productOfPre_rightInner
    (x y : WithCStarModule Bᵐᵒᵖ
      (StandardPre B ι × StandardPre B κ)) :
    CStarModule.rightInner (B := B)
        (productOfPre (B := B) (ι := ι) (κ := κ) x)
        (productOfPre (B := B) (ι := ι) (κ := κ) y) =
      CStarModule.rightInner (B := B) x y := by
  change CStarModule.rightInner (B := B) (ofPre x.1) (ofPre y.1) +
      CStarModule.rightInner (B := B) (ofPre x.2) (ofPre y.2) =
    CStarModule.rightInner (B := B) x.1 y.1 +
      CStarModule.rightInner (B := B) x.2 y.2
  rw [rightInner_ofPre_ofPre, rightInner_ofPre_ofPre]

/-- The componentwise finite-support inclusion is isometric for the genuine
C-star-module direct-sum norm. -/
@[simp]
theorem norm_productOfPre
    (x : WithCStarModule Bᵐᵒᵖ
      (StandardPre B ι × StandardPre B κ)) :
    ‖productOfPre (B := B) (ι := ι) (κ := κ) x‖ = ‖x‖ := by
  calc
    ‖productOfPre (B := B) (ι := ι) (κ := κ) x‖ =
        √‖CStarModule.rightInner (B := B)
          (productOfPre (B := B) (ι := ι) (κ := κ) x)
          (productOfPre (B := B) (ι := ι) (κ := κ) x)‖ :=
      CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner _
    _ = √‖CStarModule.rightInner (B := B) x x‖ := by
      rw [productOfPre_rightInner]
    _ = ‖x‖ :=
      (CStarModule.AdjointableOperator.norm_eq_sqrt_norm_rightInner x).symm

theorem sumComparison_norm
    (x : StandardPre B (ι ⊕ κ)) :
    ‖productOfPre (B := B) (ι := ι) (κ := κ)
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x)‖ =
      ‖(ofPre (B := B) (ι := ι ⊕ κ)).toLinearMap x‖ := by
  rw [norm_productOfPre, norm_preSumLinearEquiv]
  exact ((ofPre (B := B) (ι := ι ⊕ κ)).norm_map x).symm

/-- Splitting the coordinate type gives a linear isometric equivalence from
the completed standard module to the genuine direct sum. -/
noncomputable def sumLinearIsometryEquiv :
    Standard B (ι ⊕ κ) ≃ₗᵢ[ℂ]
      WithCStarModule Bᵐᵒᵖ
        (Standard B ι × Standard B κ) :=
  (preSumLinearEquiv (B := B) (ι := ι) (κ := κ)).extendOfIsometry
    (ofPre (B := B) (ι := ι ⊕ κ)).toLinearMap
    (productOfPre (B := B) (ι := ι) (κ := κ))
    (denseRange_ofPre (B := B) (ι := ι ⊕ κ))
    (denseRange_productOfPre (B := B) (ι := ι) (κ := κ))
    (sumComparison_norm (B := B) (ι := ι) (κ := κ))

/-- The completed sum equivalence extends finite-support splitting. -/
@[simp]
theorem sumLinearIsometryEquiv_ofPre
    (x : StandardPre B (ι ⊕ κ)) :
    sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) (ofPre x) =
      productOfPre (B := B) (ι := ι) (κ := κ)
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x) := by
  unfold sumLinearIsometryEquiv
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _
    (sumComparison_norm (B := B) (ι := ι) (κ := κ)) x

/-- The first coordinates of the completed sum equivalence are the left
summand coordinates. -/
@[simp]
theorem coord_sumLinearIsometryEquiv_inl
    (x : Standard B (ι ⊕ κ)) (i : ι) :
    coord i
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) x).1 =
      coord (Sum.inl i) x := by
  have hprod : Continuous fun x : Standard B (ι ⊕ κ) ↦
      WithCStarModule.equiv Bᵐᵒᵖ
        (Standard B ι × Standard B κ)
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) x) :=
    (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
      (E := Standard B ι × Standard B κ)).continuous.comp
        (sumLinearIsometryEquiv
          (B := B) (ι := ι) (κ := κ)).continuous
  have hleft : Continuous fun x : Standard B (ι ⊕ κ) ↦
      coord i
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) x).1 :=
    (coord i).continuous.comp (continuous_fst.comp hprod)
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq hleft (coord (Sum.inl i)).continuous) ?_
  intro x
  change coord i
      (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ)
        (ofPre x : Standard B (ι ⊕ κ))).1 =
    coord (Sum.inl i) (ofPre x : Standard B (ι ⊕ κ))
  rw [sumLinearIsometryEquiv_ofPre]
  change coord i
      (ofPre
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x).1) =
    coord (Sum.inl i) (ofPre x : Standard B (ι ⊕ κ))
  rw [coord_ofPre, coord_ofPre, preSumLinearEquiv_fst]

/-- The second coordinates of the completed sum equivalence are the right
summand coordinates. -/
@[simp]
theorem coord_sumLinearIsometryEquiv_inr
    (x : Standard B (ι ⊕ κ)) (j : κ) :
    coord j
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) x).2 =
      coord (Sum.inr j) x := by
  have hprod : Continuous fun x : Standard B (ι ⊕ κ) ↦
      WithCStarModule.equiv Bᵐᵒᵖ
        (Standard B ι × Standard B κ)
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) x) :=
    (WithCStarModule.equivL (R := ℂ) (A := Bᵐᵒᵖ)
      (E := Standard B ι × Standard B κ)).continuous.comp
        (sumLinearIsometryEquiv
          (B := B) (ι := ι) (κ := κ)).continuous
  have hright : Continuous fun x : Standard B (ι ⊕ κ) ↦
      coord j
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) x).2 :=
    (coord j).continuous.comp (continuous_snd.comp hprod)
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq hright (coord (Sum.inr j)).continuous) ?_
  intro x
  change coord j
      (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ)
        (ofPre x : Standard B (ι ⊕ κ))).2 =
    coord (Sum.inr j) (ofPre x : Standard B (ι ⊕ κ))
  rw [sumLinearIsometryEquiv_ofPre]
  change coord j
      (ofPre
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x).2) =
    coord (Sum.inr j) (ofPre x : Standard B (ι ⊕ κ))
  rw [coord_ofPre, coord_ofPre, preSumLinearEquiv_snd]

/-- The inverse sum equivalence reconstructs the left coordinates. -/
@[simp]
theorem coord_sumLinearIsometryEquiv_symm_inl
    (x : WithCStarModule Bᵐᵒᵖ
      (Standard B ι × Standard B κ)) (i : ι) :
    coord (Sum.inl i)
        ((sumLinearIsometryEquiv
          (B := B) (ι := ι) (κ := κ)).symm x) =
      coord i x.1 := by
  have h := coord_sumLinearIsometryEquiv_inl
    (B := B) (ι := ι) (κ := κ)
    ((sumLinearIsometryEquiv
      (B := B) (ι := ι) (κ := κ)).symm x) i
  calc
    coord (Sum.inl i)
        ((sumLinearIsometryEquiv
          (B := B) (ι := ι) (κ := κ)).symm x) =
      coord i
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ)
          ((sumLinearIsometryEquiv
            (B := B) (ι := ι) (κ := κ)).symm x)).1 := h.symm
    _ = coord i x.1 := by
      rw [(sumLinearIsometryEquiv
        (B := B) (ι := ι) (κ := κ)).apply_symm_apply]

/-- The inverse sum equivalence reconstructs the right coordinates. -/
@[simp]
theorem coord_sumLinearIsometryEquiv_symm_inr
    (x : WithCStarModule Bᵐᵒᵖ
      (Standard B ι × Standard B κ)) (j : κ) :
    coord (Sum.inr j)
        ((sumLinearIsometryEquiv
          (B := B) (ι := ι) (κ := κ)).symm x) =
      coord j x.2 := by
  have h := coord_sumLinearIsometryEquiv_inr
    (B := B) (ι := ι) (κ := κ)
    ((sumLinearIsometryEquiv
      (B := B) (ι := ι) (κ := κ)).symm x) j
  calc
    coord (Sum.inr j)
        ((sumLinearIsometryEquiv
          (B := B) (ι := ι) (κ := κ)).symm x) =
      coord j
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ)
          ((sumLinearIsometryEquiv
            (B := B) (ι := ι) (κ := κ)).symm x)).2 := h.symm
    _ = coord j x.2 := by
      rw [(sumLinearIsometryEquiv
        (B := B) (ι := ι) (κ := κ)).apply_symm_apply]

/-- The completed sum equivalence preserves the coefficient-valued inner
product. -/
theorem sumLinearIsometryEquiv_rightInner
    (x y : Standard B (ι ⊕ κ)) :
    CStarModule.rightInner (B := B)
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) x)
        (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) y) =
      CStarModule.rightInner (B := B) x y := by
  have hdense : DenseRange
      (fun p : StandardPre B (ι ⊕ κ) × StandardPre B (ι ⊕ κ) ↦
        (ofPre p.1, ofPre p.2)) :=
    (denseRange_ofPre (B := B) (ι := ι ⊕ κ)).prodMap
      (denseRange_ofPre (B := B) (ι := ι ⊕ κ))
  have hfun :
      (fun p : Standard B (ι ⊕ κ) × Standard B (ι ⊕ κ) ↦
        CStarModule.rightInner (B := B)
          (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) p.1)
          (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) p.2)) =
      (fun p : Standard B (ι ⊕ κ) × Standard B (ι ⊕ κ) ↦
        CStarModule.rightInner (B := B) p.1 p.2) := by
    apply Continuous.ext_on hdense
    · exact CStarModule.continuous_rightInner.comp
        (((sumLinearIsometryEquiv
            (B := B) (ι := ι) (κ := κ)).continuous.comp
              continuous_fst).prodMk
          ((sumLinearIsometryEquiv
            (B := B) (ι := ι) (κ := κ)).continuous.comp
              continuous_snd))
    · exact CStarModule.continuous_rightInner
    · rintro _ ⟨⟨x, y⟩, rfl⟩
      change CStarModule.rightInner (B := B)
          (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ)
            (ofPre x : Standard B (ι ⊕ κ)))
          (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ)
            (ofPre y : Standard B (ι ⊕ κ))) =
        CStarModule.rightInner (B := B)
          (ofPre x : Standard B (ι ⊕ κ))
          (ofPre y : Standard B (ι ⊕ κ))
      rw [sumLinearIsometryEquiv_ofPre,
        sumLinearIsometryEquiv_ofPre,
        productOfPre_rightInner,
        preSumLinearEquiv_rightInner,
        rightInner_ofPre_ofPre]
  exact congrFun hfun (x, y)

/-- The standard module on a sum of coordinate types is unitarily equivalent
to the genuine direct sum of the two standard modules. -/
noncomputable def sumUnitary :
    CStarModule.UnitaryEquiv B
      (Standard B (ι ⊕ κ))
      (WithCStarModule Bᵐᵒᵖ
        (Standard B ι × Standard B κ)) :=
  CStarModule.UnitaryEquiv.ofLinearIsometryEquiv
    (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ))
    (sumLinearIsometryEquiv_rightInner
      (B := B) (ι := ι) (κ := κ))

/-- The direct sum of two countable standard modules is unitarily equivalent
to the countable standard module. -/
noncomputable def doubleHUnitary :
    CStarModule.UnitaryEquiv B
      (WithCStarModule Bᵐᵒᵖ (H B × H B)) (H B) :=
  (sumUnitary (B := B) (ι := ℕ) (κ := ℕ)).symm.trans
    (reindexUnitary (B := B) Equiv.natSumNatEquivNat)

end CStarModule.Right.Standard
