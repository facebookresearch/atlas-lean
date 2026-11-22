/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.BlockCoinvariants
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijDecomposition

/-!
# Balanced-smash components of free symmetric modules

Constructs the balanced-smash component functor of a Day coefficient and compares it
with the induced component functor at two finite cardinalities. When the coefficient is
a monoid, free-module evaluation at the larger cardinality is naturally isomorphic to
this same balanced-smash functor.
-/

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid

namespace PointedCGWH

/-- Equal equivariant coefficient arrows select the same actual native quotient map. -/
private theorem nativeBalancedMap_congr_coefficient
    (H G : Type) [Monoid H] [Group G]
    (Z Z' : PointedCGWH.{u, v}) (rho : H →* End Z) (rho' : H →* End Z')
    (iota : H →* G) (f g : Z ⟶ Z')
    (hf : ∀ a, (rho a).asHom ≫ f = f ≫ (rho' a).asHom)
    (hg : ∀ a, (rho a).asHom ≫ g = g ≫ (rho' a).asHom)
    [HasCoequalizer (smashBalancingGroup.{u, v, 0, 0} H G Z iota)
      (smashBalancingCoefficient.{u, v, 0, 0} H G Z rho)]
    [HasCoequalizer (smashBalancingGroup.{u, v, 0, 0} H G Z' iota)
      (smashBalancingCoefficient.{u, v, 0, 0} H G Z' rho')]
    (h : f = g) :
    nativeBalancedMap.{u, v, 0, 0} H G Z rho iota Z' rho' f hf =
      nativeBalancedMap.{u, v, 0, 0} H G Z rho iota Z' rho' g hg := by
  cases h
  rfl

/-- The actual native balanced component functor for a general Day coefficient. -/
def nativeCardInducedFunctor
    (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v})
    {n m : ℕ} (h : n ≤ m) :
    PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} where
  obj X := nativeBalancedSmash.{u, v, 0, 0}
    (Aut (card (m - n))) (Aut (card m)) (A.functor.obj (card (m - n)) ⊗ X)
    (blockCoefficientAction A (card (m - n)) X)
    (blockAutHom (card (m - n)) (card n) (card m)
      (cardBlockSumIso (Nat.sub_add_cancel h)))
  map {X Y} f := nativeBalancedMap.{u, v, 0, 0}
    (Aut (card (m - n))) (Aut (card m)) (A.functor.obj (card (m - n)) ⊗ X)
    (blockCoefficientAction A (card (m - n)) X)
    (blockAutHom (card (m - n)) (card n) (card m)
      (cardBlockSumIso (Nat.sub_add_cancel h)))
    (A.functor.obj (card (m - n)) ⊗ Y) (blockCoefficientAction A (card (m - n)) Y)
    (𝟙 (A.functor.obj (card (m - n))) ⊗ₘ f)
    (blockCoefficientAction_naturality A (card (m - n)) f)
  map_id X := by
    let R := card (m - n)
    let N := card n
    let M := card m
    let Z := A.functor.obj R ⊗ X
    let rho := blockCoefficientAction A R X
    let iota := blockAutHom R N M (cardBlockSumIso (Nat.sub_add_cancel h))
    have hid : 𝟙 (A.functor.obj R) ⊗ₘ 𝟙 X = 𝟙 Z :=
      id_tensorHom_id _ _
    change nativeBalancedMap.{u, v, 0, 0} (Aut R) (Aut M) Z rho iota Z rho
      (𝟙 (A.functor.obj R) ⊗ₘ 𝟙 X) _ = _
    exact (nativeBalancedMap_congr_coefficient (Aut R) (Aut M) Z Z rho rho iota
      (𝟙 (A.functor.obj R) ⊗ₘ 𝟙 X) (𝟙 Z)
      (blockCoefficientAction_naturality A R (𝟙 X))
      (fun _ => (Category.comp_id _).trans (Category.id_comp _).symm) hid).trans
      (nativeBalancedMap_id.{u, v, 0, 0} (Aut R) (Aut M) Z rho iota)
  map_comp {X Y Z} f g := by
    let R := card (m - n)
    let N := card n
    let M := card m
    let iota := blockAutHom R N M (cardBlockSumIso (Nat.sub_add_cancel h))
    have hfg : 𝟙 (A.functor.obj R) ⊗ₘ (f ≫ g) =
        (𝟙 (A.functor.obj R) ⊗ₘ f) ≫ (𝟙 (A.functor.obj R) ⊗ₘ g) := by
      exact (congrArg (fun k => k ⊗ₘ (f ≫ g)) (Category.id_comp _)).symm.trans
        (tensorHom_comp_tensorHom (𝟙 (A.functor.obj R)) f
          (𝟙 (A.functor.obj R)) g).symm
    change nativeBalancedMap.{u, v, 0, 0} (Aut R) (Aut M)
      (A.functor.obj R ⊗ X) (blockCoefficientAction A R X) iota
      (A.functor.obj R ⊗ Z) (blockCoefficientAction A R Z)
      (𝟙 (A.functor.obj R) ⊗ₘ (f ≫ g)) _ = _
    let hf := blockCoefficientAction_naturality A R f
    let hg := blockCoefficientAction_naturality A R g
    let hcomp : ∀ a : Aut R,
        (blockCoefficientAction A R X a).asHom ≫
            ((𝟙 (A.functor.obj R) ⊗ₘ f) ≫ (𝟙 (A.functor.obj R) ⊗ₘ g)) =
          ((𝟙 (A.functor.obj R) ⊗ₘ f) ≫ (𝟙 (A.functor.obj R) ⊗ₘ g)) ≫
            (blockCoefficientAction A R Z a).asHom :=
      fun a => (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k => k ≫ (𝟙 (A.functor.obj R) ⊗ₘ g)) (hf a)).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (fun k => (𝟙 (A.functor.obj R) ⊗ₘ f) ≫ k) (hg a)).trans
              (Category.assoc _ _ _).symm)))
    have hmap := nativeBalancedMap_congr_coefficient (Aut R) (Aut M)
      (A.functor.obj R ⊗ X) (A.functor.obj R ⊗ Z)
      (blockCoefficientAction A R X) (blockCoefficientAction A R Z) iota
      (𝟙 (A.functor.obj R) ⊗ₘ (f ≫ g))
      ((𝟙 (A.functor.obj R) ⊗ₘ f) ≫ (𝟙 (A.functor.obj R) ⊗ₘ g))
      (blockCoefficientAction_naturality A R (f ≫ g)) hcomp hfg
    exact hmap.trans (nativeBalancedMap_comp.{u, v, 0, 0} (Aut R) (Aut M)
      (A.functor.obj R ⊗ X) (blockCoefficientAction A R X) iota
      (A.functor.obj R ⊗ Y) (A.functor.obj R ⊗ Z)
      (blockCoefficientAction A R Y) (blockCoefficientAction A R Z)
      (𝟙 (A.functor.obj R) ⊗ₘ f) hf
      (𝟙 (A.functor.obj R) ⊗ₘ g) hg)

/-- The original induced coefficient functor is the actual native balanced smash functor. -/
def cardInducedNativeIso
    (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v})
    {n m : ℕ} (h : n ≤ m) :
    cardInducedFunctor A n m h ≅ nativeCardInducedFunctor A h :=
  NatIso.ofComponents
    (fun X => blockCoefficientNativeIso (card (m - n)) (card n) (card m)
      (cardBlockSumIso (Nat.sub_add_cancel h))
      (A.functor.obj (card (m - n)) ⊗ X) (blockCoefficientAction A (card (m - n)) X))
    (by
      intro X Y f
      exact blockCoefficientNativeIso_naturality (card (m - n)) (card n) (card m)
        (cardBlockSumIso (Nat.sub_add_cancel h))
        (A.functor.obj (card (m - n)) ⊗ X) (blockCoefficientAction A (card (m - n)) X)
        (A.functor.obj (card (m - n)) ⊗ Y) (blockCoefficientAction A (card (m - n)) Y)
        (𝟙 (A.functor.obj (card (m - n))) ⊗ₘ f)
        (blockCoefficientAction_naturality A (card (m - n)) f))

/-- The actual free-at-card/evaluation component compares to the native balanced functor. -/
def dayFreeAtCardNativeIso
    (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v}) [MonObj A]
    {n m : ℕ} (h : n ≤ m) :
    Mod.dayFreeAt A (card n) ⋙ Mod.dayEvaluation A (card m) ≅
      nativeCardInducedFunctor A h :=
  Mod.dayFreeAtCardInducedIso A h ≪≫ cardInducedNativeIso A h

end PointedCGWH
