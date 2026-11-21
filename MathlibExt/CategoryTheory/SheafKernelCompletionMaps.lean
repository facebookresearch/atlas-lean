/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.SheafKernelCompletion

/-!
# Maps of native kernel completions and ideal sheaf powers

A commuting original ring square induces every finite quotient map,
then its sheafification, then the native inverse limit map. Ideal powers
below are kernels of the SHEAFIFIED quotient units, so local generators
and locally varying ideal expressions are retained.

Reference: Scholze, arXiv:1205.3463v2, Definitions 6.1 and 6.8.
Native Mathlib limits, quotients and sheafification: Apache 2.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.SheafKernelCompletionMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Functor
open SheafKernelCompletion

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Maps

variable
  (R S R' S' : Sheaf J CommRingCat.{1}) (θ : R ⟶ S) (θ' : R' ⟶ S')
  (a : R ⟶ R') (b : S ⟶ S') (square : a ≫ θ' = θ ≫ b)

include b square

theorem map_kernel_le (U : Cᵒᵖ) :
    (kernelIdeal R S θ U).map (a.hom.app U).hom ≤ kernelIdeal R' S' θ' U := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change (θ'.hom.app U).hom ((a.hom.app U).hom x) = 0
  have h := congrArg (fun f => (f.hom.app U).hom x) square
  change (θ'.hom.app U).hom ((a.hom.app U).hom x) =
    (b.hom.app U).hom ((θ.hom.app U).hom x) at h
  rw [h]
  change (θ.hom.app U).hom x = 0 at hx
  simpa using congrArg (b.hom.app U).hom hx

theorem map_power_le (n : ℕ) (U : Cᵒᵖ) :
    ((kernelIdeal R S θ U) ^ (n + 1)).map (a.hom.app U).hom ≤
      (kernelIdeal R' S' θ' U) ^ (n + 1) := by
  rw [Ideal.map_pow]
  exact pow_le_pow_left' (map_kernel_le R S R' S' θ θ' a b square U) (n + 1)

def rawMap (n : ℕ) : rawQuotient R S θ n ⟶ rawQuotient R' S' θ' n where
  app U := CommRingCat.ofHom
    (Ideal.Quotient.lift _
      ((Ideal.Quotient.mk ((kernelIdeal R' S' θ' U) ^ (n + 1))).comp (a.hom.app U).hom)
      (by
        intro x hx
        exact Ideal.Quotient.eq_zero_iff_mem.mpr
          (map_power_le R S R' S' θ θ' a b square n U (Ideal.mem_map_of_mem _ hx))))
  naturality {U V} f := by
    ext x
    refine Quotient.inductionOn x (fun y => ?_)
    exact congrArg (Ideal.Quotient.mk _) (congrArg (fun g => g.hom y) (a.hom.naturality f))

def rawTowerMap : rawTower R S θ ⟶ rawTower R' S' θ' where
  app n := rawMap R S R' S' θ θ' a b square n.unop
  naturality {n m} f := by
    apply NatTrans.ext
    funext U
    ext x
    refine Quotient.inductionOn x (fun y => ?_)
    rfl

variable [HasSheafify J CommRingCat.{1}]

def quotientMap (n : ℕ) : quotientSheaf R S θ n ⟶ quotientSheaf R' S' θ' n :=
  (presheafToSheaf J CommRingCat.{1}).map (rawMap R S R' S' θ θ' a b square n)

def towerMap : tower R S θ ⟶ tower R' S' θ' :=
  whiskerRight (rawTowerMap R S R' S' θ θ' a b square) (presheafToSheaf J CommRingCat.{1})

/-- Every finite projection of this map is induced by the original ring square. -/
def completionMap : completion R S θ ⟶ completion R' S' θ' :=
  limMap (towerMap R S R' S' θ θ' a b square)

@[reassoc (attr := simp)] theorem completionMap_projection (n : ℕ) :
    completionMap R S R' S' θ θ' a b square ≫ projection R' S' θ' n =
      projection R S θ n ≫ quotientMap R S R' S' θ θ' a b square n := by
  exact limMap_π (towerMap R S R' S' θ θ' a b square) (op n)

end Maps

variable (R S : Sheaf J CommRingCat.{1}) (θ : R ⟶ S)
  [HasSheafify J CommRingCat.{1}]

/-- Sections of the actual ideal SHEAF power, not powers of its section ideal. -/
def idealSheafPower (n : ℕ) (U : Cᵒᵖ) : Ideal (R.obj.obj U) :=
  match n with
  | 0 => ⊤
  | n + 1 => kernelIdeal R (quotientSheaf R S θ n) (quotientUnit R S θ n) U

theorem idealSheafPower_restrict {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    (idealSheafPower R S θ n U).map (R.obj.map f).hom ≤ idealSheafPower R S θ n V := by
  cases n with
  | zero => exact le_top
  | succ n =>
      exact SheafKernelCompletion.map_kernel_le R (quotientSheaf R S θ n)
        (quotientUnit R S θ n) f

end MathlibExt.CategoryTheory.SheafKernelCompletionMaps
