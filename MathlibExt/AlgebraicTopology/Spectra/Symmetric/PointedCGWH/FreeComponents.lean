/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.PointedCGWH.FreeComponentsFunctor
import MathlibExt.CategoryTheory.Monoidal.DayConvolution.FinBijDecomposition

/-!
# Generators of native free Day-module components

For a monoid object in the Day category of finite-set groupoids and
`PointedCGWH`, `dayFreeAtCardNativeIso_generator` computes the free generator
at degree `n` in degree `m ≥ n` as a native balanced quotient generator.
Its coefficient is transported to the complementary block of size `m - n`
with the monoid’s block action. The target-generator formula identifies
target automorphisms with the native left quotient action.
-/

set_option autoImplicit false
noncomputable section


namespace PointedCGWH

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid

universe u v

variable (A : DayFunctor CategoryTheory.Operad.SmallFinBijGroupoid PointedCGWH.{u, v})
variable [MonObj A]

/-- The original free Day generator becomes its actual normalized native coefficient leg. -/
theorem dayFreeAtCardNativeIso_generator {n m : ℕ} (h : n ≤ m)
    (X : PointedCGWH.{u, v}) (d : BlockDecomposition (card n) (card m)) :
    let G := (DayFunctor.equiv CategoryTheory.Operad.SmallFinBijGroupoid
      PointedCGWH.{u, v}).symm.functor.obj
      ((evaluationLeftAdjoint PointedCGWH.{u, v} (card n)).obj X)
    (((𝟙 (A.functor.obj d.left) ⊗ₘ
            Sigma.ι (fun _ : card n ⟶ card n => X) (𝟙 (card n))) ≫
          (DayFunctor.η A G).app (d.left, card n) ≫
          (A ⊗ G).functor.map d.hom ≫
          (eqToHom (Mod.free_obj A G).symm).natTrans.app (card m)) ≫
        (dayFreeAtCardNativeIso A h).hom.app X) =
      (A.functor.map (cardComplementIso h d).inv ⊗ₘ 𝟙 X) ≫
        nativeBalancedGenerator.{u, v, 0, 0}
          (Aut (card (m - n))) (Aut (card m)) (A.functor.obj (card (m - n)) ⊗ X)
          (blockCoefficientAction A (card (m - n)) X)
          (blockAutHom (card (m - n)) (card n) (card m)
            (cardBlockSumIso (Nat.sub_add_cancel h)))
          (blockIsoEquivAut (card (m - n)) (card n) (card m)
            (cardBlockSumIso (Nat.sub_add_cancel h)) (cardNormalizedBlock h d)) := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let b : R ⊗ N ≅ M := cardBlockSumIso (Nat.sub_add_cancel h)
  let _ := blockMulAction R N M
  let G := (DayFunctor.equiv CategoryTheory.Operad.SmallFinBijGroupoid
    PointedCGWH.{u, v}).symm.functor.obj
    ((evaluationLeftAdjoint PointedCGWH.{u, v} N).obj X)
  let gen : A.functor.obj d.left ⊗ X ⟶ ((Mod.dayFreeAt A N).obj X).X.functor.obj M :=
    (𝟙 (A.functor.obj d.left) ⊗ₘ
      Sigma.ι (fun _ : N ⟶ N => X) (𝟙 N)) ≫
    (DayFunctor.η A G).app (d.left, N) ≫ (A ⊗ G).functor.map d.hom ≫
    (eqToHom (Mod.free_obj A G).symm).natTrans.app M
  let J : ActionCategory (Aut R) (R ⊗ N ≅ M) ⥤ PointedCGWH.{u, v} :=
    blockCoefficientDiagram R N M (A.functor.obj R ⊗ X)
    (blockCoefficientAction A R X)
  let e := cardNormalizedBlock h d
  let leg : A.functor.obj R ⊗ X ⟶ colimit J :=
    colimit.ι J (e : ActionCategory (Aut R) (R ⊗ N ≅ M))
  let coeff : A.functor.obj d.left ⊗ X ⟶ A.functor.obj R ⊗ X :=
    A.functor.map (cardComplementIso h d).inv ⊗ₘ 𝟙 X
  let c : ((Mod.dayFreeAt A N).obj X).X.functor.obj M ⟶ colimit J :=
    (Mod.dayFreeAtCardInducedIso A h).hom.app X
  let q : colimit J ⟶ (nativeCardInducedFunctor A h).obj X :=
    (blockCoefficientNativeIso R N M b (A.functor.obj R ⊗ X)
    (blockCoefficientAction A R X)).hom
  have hcard : gen ≫ c = coeff ≫ leg := Mod.dayFreeAtCardInducedIso_generator A h X d
  have hblock : leg ≫ q = nativeBalancedGenerator.{u, v, 0, 0}
      (Aut R) (Aut M) (A.functor.obj R ⊗ X) (blockCoefficientAction A R X)
      (blockAutHom R N M b) (blockIsoEquivAut R N M b e) :=
    blockCoefficientNativeIso_generator R N M b (A.functor.obj R ⊗ X)
      (blockCoefficientAction A R X) e
  change gen ≫ (c ≫ q) = coeff ≫ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ q) hcard).trans
      ((Category.assoc _ _ _).trans (congrArg (fun f => coeff ≫ f) hblock)))

/-- Full target automorphisms act through the actual native left quotient action. -/
theorem dayFreeAtCardNativeIso_target_generator {n m : ℕ} (h : n ≤ m)
    (X : PointedCGWH.{u, v}) (d : BlockDecomposition (card n) (card m))
    (k : Aut (card m)) :
    colimit.ι (CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
        A.functor ⋙ tensorRight X) d ≫
      (Mod.dayFreeAtComponentIso A (card n) (card m)).inv.app X ≫
        ((Mod.dayFreeAt A (card n)).obj X).X.functor.map k.asIso.hom ≫
          (dayFreeAtCardNativeIso A h).hom.app X =
    colimit.ι (CostructuredArrow.proj (tensorRight (card n)) (card m) ⋙
        A.functor ⋙ tensorRight X) d ≫
      (Mod.dayFreeAtComponentIso A (card n) (card m)).inv.app X ≫
        (dayFreeAtCardNativeIso A h).hom.app X ≫
          (nativeBalancedLeftAut.{u, v, 0, 0}
            (Aut (card (m - n))) (Aut (card m)) (A.functor.obj (card (m - n)) ⊗ X)
            (blockCoefficientAction A (card (m - n)) X)
            (blockAutHom (card (m - n)) (card n) (card m)
              (cardBlockSumIso (Nat.sub_add_cancel h))) k).asIso.hom := by
  let R := card (m - n)
  let N := card n
  let M := card m
  let b : R ⊗ N ≅ M := cardBlockSumIso (Nat.sub_add_cancel h)
  let _ := blockMulAction R N M
  let D : BlockDecomposition N M ⥤ PointedCGWH.{u, v} :=
    CostructuredArrow.proj (tensorRight N) M ⋙ A.functor ⋙ tensorRight X
  let J : ActionCategory (Aut R) (R ⊗ N ≅ M) ⥤ PointedCGWH.{u, v} :=
    blockCoefficientDiagram R N M (A.functor.obj R ⊗ X)
    (blockCoefficientAction A R X)
  let ld : A.functor.obj d.left ⊗ X ⟶ colimit D := colimit.ι D d
  let ci : colimit D ⟶ ((Mod.dayFreeAt A N).obj X).X.functor.obj M :=
    (Mod.dayFreeAtComponentIso A N M).inv.app X
  let c : ((Mod.dayFreeAt A N).obj X).X.functor.obj M ⟶ colimit J :=
    (Mod.dayFreeAtCardInducedIso A h).hom.app X
  let q : colimit J ⟶ (nativeCardInducedFunctor A h).obj X :=
    (blockCoefficientNativeIso R N M b (A.functor.obj R ⊗ X)
    (blockCoefficientAction A R X)).hom
  let e := cardNormalizedBlock h d
  let le : A.functor.obj R ⊗ X ⟶ colimit J :=
    colimit.ι J (e : ActionCategory (Aut R) (R ⊗ N ≅ M))
  let lek : A.functor.obj R ⊗ X ⟶ colimit J :=
    colimit.ι J (e ≪≫ k.asIso : ActionCategory (Aut R) (R ⊗ N ≅ M))
  let coeff : A.functor.obj d.left ⊗ X ⟶ A.functor.obj R ⊗ X :=
    A.functor.map (cardComplementIso h d).inv ⊗ₘ 𝟙 X
  let km : ((Mod.dayFreeAt A N).obj X).X.functor.obj M ⟶
      ((Mod.dayFreeAt A N).obj X).X.functor.obj M :=
    ((Mod.dayFreeAt A N).obj X).X.functor.map k.asIso.hom
  let left : colimit J ⟶ colimit J :=
    blockCoefficientLeftMap R N M (A.functor.obj R ⊗ X)
    (blockCoefficientAction A R X) k
  let nativeLeft : (nativeCardInducedFunctor A h).obj X ⟶
      (nativeCardInducedFunctor A h).obj X :=
    (nativeBalancedLeftAut.{u, v, 0, 0} (Aut R) (Aut M)
    (A.functor.obj R ⊗ X) (blockCoefficientAction A R X) (blockAutHom R N M b) k).asIso.hom
  have hcard : ld ≫ ci ≫ c = coeff ≫ le :=
    Mod.dayFreeAtCardInducedIso_decomposition_generator A h X d
  have htarget : ld ≫ ci ≫ km ≫ c = coeff ≫ lek :=
    Mod.dayFreeAtCardInducedIso_target_generator A h X d k
  have hleft : le ≫ left = lek :=
    ActionCategory.coefficientColimitReindex_generator (Aut R) (R ⊗ N ≅ M)
      (A.functor.obj R ⊗ X) (blockCoefficientAction A R X)
      (fun e => e ≪≫ k.asIso) (fun a e => (blockMulAction_postcompose R N M a e k).symm) e
  have hnative : left ≫ q = q ≫ nativeLeft :=
    blockCoefficientNativeIso_left R N M b (A.functor.obj R ⊗ X)
      (blockCoefficientAction A R X) k
  have hmiddle : coeff ≫ lek ≫ q = coeff ≫ le ≫ q ≫ nativeLeft := by
    have he := congrArg (fun f => coeff ≫ f ≫ q) hleft.symm
    have hn := congrArg (fun f => coeff ≫ le ≫ f) hnative
    exact he.trans (by simpa only [Category.assoc] using hn)
  change ld ≫ ci ≫ km ≫ (c ≫ q) = ld ≫ ci ≫ (c ≫ q) ≫ nativeLeft
  have ht := congrArg (fun f => f ≫ q) htarget
  have hc := congrArg (fun f => f ≫ q ≫ nativeLeft) hcard.symm
  have hFirst : ld ≫ ci ≫ km ≫ (c ≫ q) = coeff ≫ lek ≫ q := by
    simpa only [Category.assoc] using ht
  have hLast : coeff ≫ le ≫ q ≫ nativeLeft = ld ≫ ci ≫ (c ≫ q) ≫ nativeLeft := by
    simpa only [Category.assoc] using hc
  exact hFirst.trans (hmiddle.trans hLast)

end PointedCGWH
