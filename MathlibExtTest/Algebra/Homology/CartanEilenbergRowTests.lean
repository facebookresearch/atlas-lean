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

public import MathlibExt.Algebra.Homology.CartanEilenberg.Existence
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyPositive
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyZeroAugmentation
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Tactic.NormNum

/-!
# Nonzero row coordinates in a Cartan–Eilenberg resolution

Start with the zero-differential complex having an integer module in every nonnegative degree.
Its Cartan–Eilenberg resolution is obtained from actual projective resolutions. Their proven
augmentation epimorphisms supply lifts of the homology class represented by three.

The positive row comparison and its resolution augmentation detect three. In degree zero,
the inclusion of the homology-resolution summand has zero boundary coordinate and its actual
row-homology augmentation also detects three. Both resulting row classes are nonzero.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace MathlibExtTest.CartanEilenbergRows

private abbrev E := ModuleCat.{0} ℤ
private abbrev N : E := ModuleCat.of ℤ ℤ

private def L : ChainComplex E ℕ :=
  ChainComplex.of (fun _ => N) (fun _ => 0) (by intro n; simp)

private theorem differential_zero (i j : ℕ) : L.d i j = 0 := by
  simp [L, ChainComplex.of.d]

private def coordinate (n : ℕ) : L.homology n ≅ N :=
  (ShortComplex.HomologyData.ofZeros (L.sc n)
    (differential_zero _ _) (differential_zero _ _)).left.homologyIso

private def threeClass (n : ℕ) : L.homology n := (coordinate n).inv.hom 3

private def P : CartanEilenbergResolution L := CartanEilenbergResolution.of L

private def liftThree (n : ℕ) : (P.homologyResolution n).complex.X 0 :=
  ((ModuleCat.epi_iff_surjective ((P.homologyResolution n).π.f 0)).mp
    (by infer_instance) (threeClass n)).choose

private theorem liftThree_spec (n : ℕ) :
    ((P.homologyResolution n).π.f 0).hom (liftThree n) = threeClass n :=
  ((ModuleCat.epi_iff_surjective ((P.homologyResolution n).π.f 0)).mp
    (by infer_instance) (threeClass n)).choose_spec

private def positiveClass : (P.bicomplex.verticalHomologyComplex 1).X 0 :=
  (P.cartanEilenbergRowHomologySuccIso 0 0).inv.hom (liftThree 1)

private theorem positive_value :
    (coordinate 1).hom.hom
      (((P.cartanEilenbergVerticalHomologySuccResolution 0).π.f 0).hom positiveClass) = 3 := by
  change (coordinate 1).hom.hom
    (((P.homologyResolution 1).π.f 0).hom
      ((P.cartanEilenbergRowHomologySuccIso 0 0).hom.hom positiveClass)) = 3
  rw [positiveClass, ModuleCat.hom_inv_apply, liftThree_spec, threeClass,
    ModuleCat.hom_inv_apply]

private def zeroClass : (P.bicomplex.verticalHomologyComplex 0).X 0 :=
  (P.cartanEilenbergVerticalHomologyZeroι.f 0).hom (liftThree 0)

private theorem zero_aug_value :
    (coordinate 0).hom.hom (((P.rowHomologyAugmentation 0).f 0).hom zeroClass) = 3 := by
  have h := congrArg
    (fun f : (P.homologyResolution 0).complex ⟶ (ChainComplex.single₀ E).obj (L.homology 0) =>
      f.f 0)
    P.cartanEilenbergVerticalHomologyZeroι_comp_rowHomologyAugmentation
  have hv := ConcreteCategory.congr_hom h (liftThree 0)
  change ((P.rowHomologyAugmentation 0).f 0).hom zeroClass =
    ((P.homologyResolution 0).π.f 0).hom (liftThree 0) at hv
  rw [hv, liftThree_spec, threeClass, ModuleCat.hom_inv_apply]

example : ((P.homologyResolution 0).π.f 0).hom (liftThree 0) = threeClass 0 :=
  liftThree_spec 0

example :
    (coordinate 1).hom.hom
      (((P.cartanEilenbergVerticalHomologySuccResolution 0).π.f 0).hom positiveClass) = 3 :=
  positive_value

example : positiveClass ≠ 0 := by
  intro hzero
  have h := congrArg (fun x => (coordinate 1).hom.hom
    (((P.cartanEilenbergVerticalHomologySuccResolution 0).π.f 0).hom x)) hzero
  rw [positive_value, map_zero, map_zero] at h
  norm_num at h

example :
    ((P.cartanEilenbergVerticalHomologySuccComplexIso 0).hom.f 0).hom positiveClass =
      liftThree 1 := by
  change (P.cartanEilenbergRowHomologySuccIso 0 0).hom.hom positiveClass = liftThree 1
  exact ModuleCat.hom_inv_apply _ _

example :
    (coordinate 0).hom.hom (((P.rowHomologyAugmentation 0).f 0).hom zeroClass) = 3 :=
  zero_aug_value

example : zeroClass ≠ 0 := by
  intro hzero
  have h := congrArg (fun x => (coordinate 0).hom.hom
    (((P.rowHomologyAugmentation 0).f 0).hom x)) hzero
  rw [zero_aug_value, map_zero, map_zero] at h
  norm_num at h

example :
    (biprod.fst : (P.homologyResolution 0).complex.X 0 ⊞
      (P.boundaryResolution 0).complex.X 0 ⟶ (P.homologyResolution 0).complex.X 0).hom
        ((P.rowHomologyZeroIso 0).hom.hom zeroClass) = liftThree 0 := by
  have h := P.cartanEilenbergVerticalHomologyZeroι_f_comp_rowHomologyZeroIso_hom 0
  have hv := ConcreteCategory.congr_hom (congrArg (fun f => f ≫ biprod.fst) h) (liftThree 0)
  simpa only [Category.assoc, biprod.inl_fst, Category.id_comp] using hv

example :
    (P.cartanEilenbergVerticalHomologyZeroπ.f 0).hom zeroClass = 0 := by
  have h := congrArg
    (fun f : (P.homologyResolution 0).complex ⟶ (P.boundaryResolution 0).complex => f.f 0)
    P.cartanEilenbergVerticalHomologyZeroι_comp_π
  exact ConcreteCategory.congr_hom h (liftThree 0)

example : QuasiIso (P.rowHomologyAugmentation 0) := P.rowHomologyZeroAugmentation_quasiIso

example : (P.cartanEilenbergVerticalHomologyZeroShortComplex).ShortExact :=
  P.cartanEilenbergVerticalHomologyZeroShortExact

end MathlibExtTest.CartanEilenbergRows
