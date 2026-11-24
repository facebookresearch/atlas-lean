/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHocolim

/-!
# Bousfield--Kan carrier tests

These tests pin the all-universe carrier, diagonal degree computation,
diagram-map functoriality, and the exact coproduct-summand formula. They make
no homotopy-invariance, weak-equivalence, realization, or Theorem A claim.
-/

open CategoryTheory Limits Opposite Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanHocolimTests

variable {J : Type u} [Category.{0} J]
variable {D E F : J ⥤ SSet.{u}}

/-- The carrier and induced map have the intended symbolic-universe types. -/
noncomputable example : SSet.{u} := SSet.bkHocolim D

noncomputable example (α : D ⟶ E) :
    SSet.bkHocolim D ⟶ SSet.bkHocolim E :=
  SSet.bkHocolimMap α

/-- A diagonal degree is the matching inner degree of the matching bar
degree. -/
example (n : ℕ) :
    (SSet.bkHocolim D).obj (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit J) D n).obj (op ⦋n⦌) :=
  SSet.bkHocolim_obj_mk D n

/-- Degrees zero and one specialize without changing the diagonal/bar
orientation. -/
example :
    (SSet.bkHocolim D).obj (op ⦋0⦌) =
        (StrictOrdinaryWeightedBar.wbarObj
          (CategoryBar.replUnit J) D 0).obj (op ⦋0⦌) ∧
      (SSet.bkHocolim D).obj (op ⦋1⦌) =
        (StrictOrdinaryWeightedBar.wbarObj
          (CategoryBar.replUnit J) D 1).obj (op ⦋1⦌) :=
  ⟨SSet.bkHocolim_obj_mk D 0, SSet.bkHocolim_obj_mk D 1⟩

/-- Identity and composition are strict at the packaged map level. -/
example (α : D ⟶ E) (β : E ⟶ F) :
    SSet.bkHocolimMap (𝟙 D) = 𝟙 (SSet.bkHocolim D) ∧
      SSet.bkHocolimMap (α ≫ β) =
        SSet.bkHocolimMap α ≫ SSet.bkHocolimMap β :=
  ⟨SSet.bkHocolimMap_id D, SSet.bkHocolimMap_comp α β⟩

/-- The map acts on a weighted summand through the component at the chain's
left endpoint, without changing the chain. -/
example (α : D ⟶ E) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) ≫
      (SSet.bkHocolimMap α).app (op ⦋n⦌) =
    (α.app p.1.left).app (op ⦋n⦌) ≫
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p).app (op ⦋n⦌) :=
  SSet.bkHocolimMap_app_mk_ι α n p

/-- Elementwise weighted-summand computation. -/
example (α : D ⟶ E) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) :
    (SSet.bkHocolimMap α).app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl
          (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) =
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) E n p).app (op ⦋n⦌)
          ((α.app p.1.left).app (op ⦋n⦌) x) :=
  SSet.bkHocolimMap_app_mk_ι_apply α n p x

section UniverseOne

variable {J₁ : Type 1} [Category.{0} J₁]
variable {D₁ E₁ : J₁ ⥤ SSet.{1}}

/-- Concrete universe-one carrier and map clients. -/
noncomputable example : SSet.{1} := SSet.bkHocolim D₁

noncomputable example (α : D₁ ⟶ E₁) :
    SSet.bkHocolim D₁ ⟶ SSet.bkHocolim E₁ :=
  SSet.bkHocolimMap α

example : SSet.bkHocolimMap (𝟙 D₁) = 𝟙 (SSet.bkHocolim D₁) :=
  SSet.bkHocolimMap_id D₁

end UniverseOne

section UniverseZero

variable {J₀ : Type} [Category J₀]
variable {D₀ E₀ : J₀ ⥤ SSet.{0}}

/-- Retained universe-zero source compatibility. -/
noncomputable example : SSet.{0} := SSet.bkHocolim D₀

noncomputable example (α : D₀ ⟶ E₀) :
    SSet.bkHocolim D₀ ⟶ SSet.bkHocolim E₀ :=
  SSet.bkHocolimMap α

end UniverseZero

section UniverseZeroIndexBoundaries

variable (Dempty : Discrete PEmpty ⥤ SSet.{0})
variable (Dtwo : Discrete (Fin 2) ⥤ SSet.{0})

/-- Empty and disconnected discrete indexing categories remain accepted. -/
noncomputable example : SSet.{0} := SSet.bkHocolim Dempty

noncomputable example : SSet.{0} := SSet.bkHocolim Dtwo

example : SSet.bkHocolimMap (𝟙 Dempty) = 𝟙 (SSet.bkHocolim Dempty) :=
  SSet.bkHocolimMap_id Dempty

example : SSet.bkHocolimMap (𝟙 Dtwo) = 𝟙 (SSet.bkHocolim Dtwo) :=
  SSet.bkHocolimMap_id Dtwo

end UniverseZeroIndexBoundaries

section GeneralizedTargetMixed

variable {Jm : Type} [Category.{0} Jm]
variable {Dm Em Fm : Jm ⥤ SSet.{1}}

/-- Mixed-universe carrier and map elaborate with an explicit larger target
level. -/
noncomputable example : SSet.{1} := SSet.bkHocolimOf.{0, 0, 1} Dm

noncomputable example (α : Dm ⟶ Em) :
    SSet.bkHocolimOf.{0, 0, 1} Dm ⟶ SSet.bkHocolimOf.{0, 0, 1} Em :=
  SSet.bkHocolimMapOf.{0, 0, 1} α

/-- Diagonal degree computation at the generalized target. -/
example (n : ℕ) :
    (SSet.bkHocolimOf.{0, 0, 1} Dm).obj (op ⦋n⦌) =
      (StrictOrdinaryWeightedBar.wbarObj
        (CategoryBar.replUnit Jm) Dm n).obj (op ⦋n⦌) :=
  SSet.bkHocolimOf_obj_mk.{0, 0, 1} Dm n

/-- Identity and composition are strict at the generalized target. -/
example (α : Dm ⟶ Em) (β : Em ⟶ Fm) :
    SSet.bkHocolimMapOf.{0, 0, 1} (𝟙 Dm) =
        𝟙 (SSet.bkHocolimOf.{0, 0, 1} Dm) ∧
      SSet.bkHocolimMapOf.{0, 0, 1} (α ≫ β) =
        SSet.bkHocolimMapOf.{0, 0, 1} α ≫
          SSet.bkHocolimMapOf.{0, 0, 1} β :=
  ⟨SSet.bkHocolimMapOf_id.{0, 0, 1} Dm,
    SSet.bkHocolimMapOf_comp.{0, 0, 1} α β⟩

/-- Summand behavior at the generalized target. -/
example (α : Dm ⟶ Em) (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx Jm (CategoryBar.replUnit Jm) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit Jm) Dm n p).app (op ⦋n⦌) ≫
      (SSet.bkHocolimMapOf.{0, 0, 1} α).app (op ⦋n⦌) =
    (α.app p.1.left).app (op ⦋n⦌) ≫
      (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit Jm) Em n p).app (op ⦋n⦌) :=
  SSet.bkHocolimMapOf_app_mk_ι.{0, 0, 1} α n p

end GeneralizedTargetMixed

#print axioms SSet.bkHocolimMap_id
#print axioms SSet.bkHocolimMap_comp
#print axioms SSet.bkHocolimMap_app_mk_ι
#print axioms SSet.bkHocolimMapOf_id
#print axioms SSet.bkHocolimMapOf_comp
#print axioms SSet.bkHocolimMapOf_app_mk_ι

end MathlibExtTest.AlgebraicTopology.SimplicialSet.BousfieldKanHocolimTests
