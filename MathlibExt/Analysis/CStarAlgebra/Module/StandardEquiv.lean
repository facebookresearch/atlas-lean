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
# Coordinate equivalences of standard Hilbert modules

For a nonunital C-star algebra `B` and any index type `I`, `Standard B I` is the completion of
finitely supported `B`-valued families with norm `‖x‖ = sqrt ‖∑ i, star (x i) * x i‖`. A
bijection `e : I ≃ J` induces the unitary reindexing `(U x)_j = x_(e.symm j)`.

Splitting the index type `I ⊕ J` gives a unitary `Standard B (I ⊕ J) ≃ Standard B I ⊕ Standard B
J`; the direct-sum inner product is the sum of the component inner products. The countable index
bijection then gives `H_B ⊕ H_B ≃ H_B`, where `H_B = Standard B ℕ`. All index types, including
empty ones, are allowed.
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

/-- **Reindexing finitely supported standard vectors.** For nonunital `B` and a bijection `e : I ≃
J`, this complex-linear equivalence sends a finitely supported family `x` to `j ↦ x (e.symm
j)`. -/
def preReindexLinearEquiv (e : ι ≃ κ) :
    StandardPre B ι ≃ₗ[ℂ] StandardPre B κ :=
  (StandardPre.toFinsuppLinearEquiv (B := B) (ι := ι)).trans
    ((Finsupp.domLCongr (R := ℂ) (M := B) e).trans
      (StandardPre.toFinsuppLinearEquiv (B := B) (ι := κ)).symm)

/-- **Coordinate formula for finite reindexing.** `preReindexLinearEquiv e x j = x (e.symm j)` for
each finitely supported standard vector `x`. -/
@[simp]
theorem preReindexLinearEquiv_apply
    (e : ι ≃ κ) (x : StandardPre B ι) (j : κ) :
    preReindexLinearEquiv (B := B) e x j = x (e.symm j) := by
  change (Finsupp.domLCongr (R := ℂ) (M := B) e
    (StandardPre.toFinsupp x)) j = x (e.symm j)
  simp

/-- **Inverse finite reindexing.** `(preReindexLinearEquiv e).symm x i = x (e i)`. -/
@[simp]
theorem preReindexLinearEquiv_symm_apply
    (e : ι ≃ κ) (x : StandardPre B κ) (i : ι) :
    (preReindexLinearEquiv (B := B) e).symm x i = x (e i) := by
  have h := preReindexLinearEquiv_apply
    (B := B) e ((preReindexLinearEquiv (B := B) e).symm x) (e i)
  simpa using h.symm

/-- **Inner product under finite reindexing.** Reindexing by a bijection preserves the `B`-valued
inner product: `⟨U x, U y⟩_B = ⟨x,y⟩_B`. -/
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

/-- **Norm under finite reindexing.** For the standard-module norm, `‖preReindexLinearEquiv e x‖ =
‖x‖`. -/
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

/-- **Isometric reindexing of completed standard modules.** A bijection `e : I ≃ J` gives a
complex-linear isometric equivalence `Standard B I ≃ Standard B J` extending finite-support
reindexing. -/
noncomputable def reindexLinearIsometryEquiv (e : ι ≃ κ) :
    Standard B ι ≃ₗᵢ[ℂ] Standard B κ :=
  (preReindexLinearEquiv (B := B) e).extendOfIsometry
    (ofPre (B := B) (ι := ι)).toLinearMap
    (ofPre (B := B) (ι := κ)).toLinearMap
    (denseRange_ofPre (B := B) (ι := ι))
    (denseRange_ofPre (B := B) (ι := κ))
    (reindexComparison_norm (B := B) e)

/-- **Completed reindexing on finite-support vectors.** `reindexLinearIsometryEquiv e (ofPre x) =
ofPre (preReindexLinearEquiv e x)`. -/
@[simp]
theorem reindexLinearIsometryEquiv_ofPre
    (e : ι ≃ κ) (x : StandardPre B ι) :
    reindexLinearIsometryEquiv (B := B) e (ofPre x) =
      ofPre (preReindexLinearEquiv (B := B) e x) := by
  unfold reindexLinearIsometryEquiv
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _
    (reindexComparison_norm (B := B) e) x

/-- **Coordinates of completed reindexing.** For `x : Standard B I`, `coord j
(reindexLinearIsometryEquiv e x) = coord (e.symm j) x`. -/
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

/-- **Inner product under completed reindexing.** The reindexing isometry preserves `⟨x,y⟩_B` for
every pair of completed standard vectors. -/
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

/-- **Unitary reindexing of a standard module.** For nonunital `B` and a bijection `e : I ≃ J`,
this unitary is the reindexing map with coordinate formula `(U x)_j = x_(e.symm j)`. -/
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

/-- **Splitting finite-support sum coordinates.** The equivalence sends a vector on `I ⊕ J` to the
pair of restrictions `i ↦ x (Sum.inl i)` and `j ↦ x (Sum.inr j)`. -/
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

/-- **Inner product of split finite-support vectors.** Splitting sum coordinates preserves the
`B`-valued inner product, using the sum of the two component inner products on the target. -/
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

/-- **Norm of split finite-support vectors.** `‖preSumLinearEquiv x‖ = ‖x‖` for the Hilbert-module
direct-sum norm. -/
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

/-- **Finite-support inclusion into a completed direct sum.** Map `(x,y)` to `(ofPre x, ofPre y)`
from the two finite-support standard modules into the direct sum of their completions. -/
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

/-- **Components of the finite-support product inclusion.** Under the direct-sum carrier
identification, `productOfPre (x,y) = (ofPre x, ofPre y)`. -/
@[simp]
theorem productOfPre_apply
    (x : WithCStarModule Bᵐᵒᵖ
      (StandardPre B ι × StandardPre B κ)) :
    WithCStarModule.equiv Bᵐᵒᵖ
        (Standard B ι × Standard B κ)
        (productOfPre (B := B) (ι := ι) (κ := κ) x) =
      (ofPre x.1, ofPre x.2) :=
  rfl

/-- **Density of finite-support pairs.** The map `(x,y) ↦ (ofPre x, ofPre y)` has dense range in
the completed Hilbert-module direct sum. -/
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

/-- **Inner product of finite-support pairs after completion.** `productOfPre` preserves the
coefficient-valued inner product of the two-component Hilbert-module direct sum. -/
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

/-- **Norm of the finite-support product inclusion.** `‖productOfPre x‖ = ‖x‖`, with the
direct-sum norm given by the sum of component inner products. -/
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

/-- **Isometric splitting of a completed standard module.** `Standard B (I ⊕ J)` is
complex-linearly isometrically equivalent to the Hilbert-module direct sum of `Standard B I`
and `Standard B J`. -/
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

/-- **Completed splitting on a finite-support vector.** The completed sum equivalence sends `ofPre
x` to `productOfPre (preSumLinearEquiv x)`. -/
@[simp]
theorem sumLinearIsometryEquiv_ofPre
    (x : StandardPre B (ι ⊕ κ)) :
    sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ) (ofPre x) =
      productOfPre (B := B) (ι := ι) (κ := κ)
        (preSumLinearEquiv (B := B) (ι := ι) (κ := κ) x) := by
  unfold sumLinearIsometryEquiv
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _
    (sumComparison_norm (B := B) (ι := ι) (κ := κ)) x

/-- **Left coordinates of completed splitting.** The first component satisfies `coord i
(sumLinearIsometryEquiv x).1 = coord (Sum.inl i) x`. -/
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

/-- **Right coordinates of completed splitting.** The second component satisfies `coord j
(sumLinearIsometryEquiv x).2 = coord (Sum.inr j) x`. -/
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

/-- **Left coordinates of inverse splitting.** For a pair `x`, `coord (Sum.inl i)
((sumLinearIsometryEquiv).symm x) = coord i x.1`. -/
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

/-- **Right coordinates of inverse splitting.** For a pair `x`, `coord (Sum.inr j)
((sumLinearIsometryEquiv).symm x) = coord j x.2`. -/
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

/-- **Inner product under completed splitting.** `⟨sumLinearIsometryEquiv x,
sumLinearIsometryEquiv y⟩_B = ⟨x,y⟩_B`, with the target direct-sum inner product. -/
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

/-- **Unitary splitting of standard sum coordinates.** The coordinate restrictions give a unitary
`Standard B (I ⊕ J) ≃ Standard B I ⊕ Standard B J` for arbitrary index types. -/
noncomputable def sumUnitary :
    CStarModule.UnitaryEquiv B
      (Standard B (ι ⊕ κ))
      (WithCStarModule Bᵐᵒᵖ
        (Standard B ι × Standard B κ)) :=
  CStarModule.UnitaryEquiv.ofLinearIsometryEquiv
    (sumLinearIsometryEquiv (B := B) (ι := ι) (κ := κ))
    (sumLinearIsometryEquiv_rightInner
      (B := B) (ι := ι) (κ := κ))

/-- **Two copies of the countable standard module.** For `H_B = Standard B ℕ`, this unitary
identifies `H_B ⊕ H_B` with `H_B` by splitting and reindexing through
`Equiv.natSumNatEquivNat`. -/
noncomputable def doubleHUnitary :
    CStarModule.UnitaryEquiv B
      (WithCStarModule Bᵐᵒᵖ (H B × H B)) (H B) :=
  (sumUnitary (B := B) (ι := ℕ) (κ := ℕ)).symm.trans
    (reindexUnitary (B := B) Equiv.natSumNatEquivNat)

end CStarModule.Right.Standard
