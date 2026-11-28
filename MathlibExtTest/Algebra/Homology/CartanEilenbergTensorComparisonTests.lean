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
public import MathlibExt.Algebra.Homology.CartanEilenberg.TotalAugmentation
public import MathlibExt.Algebra.Homology.CartanEilenberg.TensorAbutment
public import MathlibExt.Algebra.Homology.CartanEilenberg.RowHomologyResolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Tactic.NormNum

/-!
# Integer total-augmentation and tensor-comparison clients

The term-resolution augmentation of a zero-differential integer complex is epi, so it supplies
an actual lift of three. Its corner summand in the Cartan–Eilenberg total augments to three.
A chosen resolution comparison over multiplication by two carries that summand to one whose
augmentation is six.

The tensor comparison is tested on the pure tensor of two with that earned lift. Flatness of
each integer component is supplied by the native instance, so the actual tensor augmentation
is a quasi-isomorphism and gives its stated homology map. Uniform row resolutions include the
zero-degree augmentation. No outcome isomorphism or comparison certificate is assumed.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HomologicalComplex.CartanEilenbergResolution
open scoped TensorProduct

namespace MathlibExtTest.CartanEilenbergTensorComparison

private abbrev E := ModuleCat.{0} ℤ
private abbrev N : E := ModuleCat.of ℤ ℤ
private abbrev L : ChainComplex E ℕ :=
  ChainComplex.of (fun _ => N) (fun _ => 0) (by intro n; simp)

private theorem differential_zero (i j : ℕ) : L.d i j = 0 := by
  simp [L, ChainComplex.of.d]

private def P : CartanEilenbergResolution L := CartanEilenbergResolution.of L

private def liftThree : (P.termResolution 0).complex.X 0 :=
  ((ModuleCat.epi_iff_surjective ((P.termResolution 0).π.f 0)).mp
    (by infer_instance) (3 : ℤ)).choose

private theorem liftThree_spec : ((P.termResolution 0).π.f 0).hom liftThree = (3 : ℤ) :=
  ((ModuleCat.epi_iff_surjective ((P.termResolution 0).π.f 0)).mp
    (by infer_instance) (3 : ℤ)).choose_spec

private def totalGenerator : (P.bicomplex.total (ComplexShape.down ℕ)).X 0 :=
  (P.bicomplex.ιTotal (ComplexShape.down ℕ) 0 0 0 (Nat.zero_add 0)).hom liftThree

private theorem totalGenerator_value : (P.totalAugmentation.f 0).hom totalGenerator = 3 := by
  have h := ConcreteCategory.congr_hom (P.ιTotal_comp_totalAugmentation_zero 0) liftThree
  change (P.totalAugmentation.f 0).hom totalGenerator =
    (P.termColumnZeroAugmentation.f 0).hom liftThree at h
  rw [P.termColumnZeroAugmentation_f] at h
  exact h.trans liftThree_spec

private def twice : L ⟶ L :=
  ChainComplex.ofHom (fun _ => ModuleCat.ofHom ((2 : ℤ) • LinearMap.id)) (by
    intro n
    simp only [differential_zero, comp_zero, zero_comp])

private def comparison : CartanEilenbergResolution.Hom P P twice :=
  Classical.choice (CartanEilenbergResolution.nonempty_hom P P twice)

private def comparisonTotal : P.bicomplex.total (ComplexShape.down ℕ) ⟶
    P.bicomplex.total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.map comparison.bicomplexHom (ComplexShape.down ℕ)

private theorem compared_value :
    (P.totalAugmentation.f 0).hom ((comparisonTotal.f 0).hom totalGenerator) = 6 := by
  have h := congrArg
    (fun f : P.bicomplex.total (ComplexShape.down ℕ) ⟶ L => f.f 0)
    (CartanEilenbergResolution.Hom.totalAugmentation_naturality (P := P) comparison)
  have hv := ConcreteCategory.congr_hom h totalGenerator
  change (P.totalAugmentation.f 0).hom ((comparisonTotal.f 0).hom totalGenerator) =
    (twice.f 0).hom ((P.totalAugmentation.f 0).hom totalGenerator) at hv
  rw [totalGenerator_value] at hv
  have htwo : (twice.f 0).hom (3 : ℤ) = 6 := by norm_num [twice, smul_eq_mul]
  exact hv.trans htwo

private def tensorCell : ((kunnethCEBicomplex L P).X 0).X 0 :=
  (HomologicalComplex.ιTensorObj L (P.bicomplex.X 0) 0 0 0 (by simp)).hom
    (TensorProduct.tmul ℤ (2 : ℤ) liftThree)

private def tensorTotalGenerator : ((kunnethCEBicomplex L P).total (ComplexShape.down ℕ)).X 0 :=
  ((kunnethCEBicomplex L P).ιTotal (ComplexShape.down ℕ) 0 0 0 (Nat.zero_add 0)).hom tensorCell

private theorem degreewise_flat (n : ℕ) : Module.Flat ℤ (L.X n) :=
  inferInstanceAs (Module.Flat ℤ ℤ)

example : (P.totalAugmentation.f 0).hom totalGenerator = 3 := totalGenerator_value

example : totalGenerator ≠ 0 := by
  intro hzero
  have h := congrArg (P.totalAugmentation.f 0).hom hzero
  rw [totalGenerator_value, map_zero] at h
  norm_num at h

example :
    (P.totalAugmentation.f 0).hom ((comparisonTotal.f 0).hom totalGenerator) = 6 :=
  compared_value

example : (comparisonTotal.f 0).hom totalGenerator ≠ 0 := by
  intro hzero
  have h := congrArg (P.totalAugmentation.f 0).hom hzero
  rw [compared_value, map_zero] at h
  norm_num at h

example : QuasiIso P.totalAugmentation := P.totalAugmentation_quasiIso

example :
    ((tensorCartanEilenbergToTensor L P).f 0).hom tensorTotalGenerator =
      ((tensorHom (𝟙 L) P.termColumnZeroAugmentation).f 0).hom tensorCell :=
  ConcreteCategory.congr_hom (tensorCartanEilenbergToTensor_ιTotal L P 0) tensorCell

example : QuasiIso (tensorCartanEilenbergToTensor L P) :=
  quasiIso_tensorCartanEilenbergToTensor_of_degreewise_flat L P degreewise_flat

example :
    (tensorCartanEilenbergAbutmentIso L P degreewise_flat 0).hom =
      homologyMap (tensorCartanEilenbergToTensor L P) 0 :=
  tensorCartanEilenbergAbutmentIso_hom L P degreewise_flat 0

example : (P.cartanEilenbergVerticalHomologyResolution 0).π = P.rowHomologyAugmentation 0 :=
  P.cartanEilenbergVerticalHomologyResolution_π_zero

example :
    (P.cartanEilenbergVerticalHomologyResolution 1).complex =
      P.bicomplex.verticalHomologyComplex 1 :=
  P.cartanEilenbergVerticalHomologyResolution_complex 1

end MathlibExtTest.CartanEilenbergTensorComparison
