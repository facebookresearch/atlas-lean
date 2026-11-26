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

public import MathlibExt.Algebra.Homology.KoszulTensorBraiding
public import MathlibExt.Algebra.Homology.Kunneth.HomologicalUCT
import MathlibExt.Algebra.Homology.ChainGradedPairingHomologyBraiding
import MathlibExt.Algebra.Homology.ChainGradedPairingKoszul

/-!
# Homological universal coefficients with a flat coefficient

Over any commutative ring, if A is flat, the canonical map H_n(K) ⊗ A → H_n(K ⊗ A[0]) is an
isomorphism for every nonnegative chain complex K. The Koszul tensor braiding exchanges the
factors and reduces this to the one-sided tensor homology comparison.

The swapped source comparison and coefficient map are natural in K and A. Mathematical source:
May, A Concise Course in Algebraic Topology, Chapter 17 §1, for the canonical coefficient map
and universal-coefficient context.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject

namespace HomologicalComplex

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ModuleCat.{u} R) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

local instance {R : Type u} [CommRing R] :
    HasFiniteBiproducts (ChainComplex (ModuleCat.{u} R) ℕ) :=
  CategoryTheory.Abelian.hasFiniteBiproducts

/-- Compression of the swapped coefficient tensor source.

The Künneth tensor-source sum for A[0] and K identifies with A ⊗ H_n(K). -/
noncomputable def homologyUCTSwappedTensorSourceIso
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R) (n : ℕ) :
    (⨁ fun ij : KunnethTensorIndex n =>
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj A).homology ij.val.1 ⊗
        K.homology ij.val.2) ≅
      A ⊗ K.homology n := by
  let L := (ChainComplex.single₀ (ModuleCat.{u} R)).obj A
  let F : KunnethTensorIndex n → ModuleCat.{u} R := fun ij =>
    L.homology ij.val.1 ⊗ K.homology ij.val.2
  let j : KunnethTensorIndex n :=
    ⟨(0, n), Finset.mem_antidiagonal.mpr (by omega)⟩
  have hzero : ∀ k, k ≠ j → IsZero (F k) := by
    intro k hk
    have hfst : k.val.1 ≠ 0 := by
      intro hfst
      apply hk
      apply Subtype.ext
      change k.val = (0, n)
      apply Prod.ext
      · change k.val.1 = 0
        exact hfst
      · change k.val.2 = n
        have hsum := Finset.mem_antidiagonal.mp k.property
        omega
    apply (tensorRight (K.homology k.val.2)).map_isZero
    exact isZero_single_obj_homology
      (ComplexShape.down ℕ) 0 A k.val.1 hfst
  let e : (⨁ F) ≅ F j :=
    { hom := biproduct.π F j
      inv := biproduct.ι F j
      hom_inv_id := by
        apply biproduct.hom_ext
        intro k
        by_cases hk : k = j
        · subst k
          simp
        · exact (hzero k hk).eq_of_tgt _ _
      inv_hom_id := by simp }
  exact e ≪≫
    tensorIso (singleObjHomologySelfIso
      (ComplexShape.down ℕ) 0 A) (Iso.refl _)

/-- The swapped coefficient comparison as a degree-(0,n) pairing.

The inverse source comparison followed by the Künneth map is the homology pairing of A[0] with
K, with degree 0+n transported to n. -/
@[reassoc]
theorem homologyUCTSwappedTensorSourceIso_inv_comp_kunnethHomologyTensorMap
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R) (n : ℕ) :
    let L := (ChainComplex.single₀ (ModuleCat.{u} R)).obj A
    (homologyUCTSwappedTensorSourceIso K A n).inv ≫
        kunnethHomologyTensorMap L K n =
      ((singleObjHomologySelfIso
          (ComplexShape.down ℕ) 0 A).inv ⊗ₘ 𝟙 (K.homology n)) ≫
        ChainGradedPairing.pairHomology
          (𝟙 (tensorObj L K))
          (ChainGradedPairing.homologyDescentData
            (𝟙 (tensorObj L K))) 0 n ≫
        (homologyIsoOfEq (tensorObj L K) (Nat.zero_add n)).hom := by
  dsimp only
  unfold homologyUCTSwappedTensorSourceIso
  simp only [Iso.trans_inv, tensorIso_inv, Iso.refl_inv,
    tensorHom_id, Category.assoc]
  rw [kunnethHomologyTensorMap_ι]

/-- Naturality of the inverse swapped tensor-source comparison.

Coefficient and chain maps commute with the inverse swapped comparison and its Künneth
tensor-source map. -/
@[reassoc]
theorem homologyUCTSwappedTensorSourceIso_inv_naturality
    {R : Type u} [CommRing R]
    {K K' : ChainComplex (ModuleCat.{u} R) ℕ}
    {A A' : ModuleCat.{u} R} (f : K ⟶ K') (a : A ⟶ A') (n : ℕ) :
    (a ⊗ₘ HomologicalComplex.homologyMap f n) ≫
        (homologyUCTSwappedTensorSourceIso K' A' n).inv =
      (homologyUCTSwappedTensorSourceIso K A n).inv ≫
        kunnethTensorSourceMap
          ((ChainComplex.single₀ (ModuleCat.{u} R)).map a) f n := by
  let j : KunnethTensorIndex n :=
    ⟨(0, n), Finset.mem_antidiagonal.mpr (by omega)⟩
  apply biproduct.hom_ext
  intro ij
  by_cases hij : ij = j
  · subst ij
    simp only [homologyUCTSwappedTensorSourceIso, Iso.trans_inv,
      tensorIso_inv, Iso.refl_inv, tensorHom_id, Category.assoc,
      bicone_ι_π_self, Category.comp_id, kunnethTensorSourceMap,
      biproduct.ι_map, j]
    rw [← MonoidalCategory.tensorHom_id,
      ← MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_comp_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp,
      singleObjHomologySelfIso_inv_naturality]
  · have hfst : ij.val.1 ≠ 0 := by
      intro hfst
      apply hij
      apply Subtype.ext
      change ij.val = (0, n)
      apply Prod.ext
      · change ij.val.1 = 0
        exact hfst
      · change ij.val.2 = n
        have hsum := Finset.mem_antidiagonal.mp ij.property
        omega
    have hzero := isZero_single_obj_homology
      (ComplexShape.down ℕ) 0 A' ij.val.1 hfst
    have htensor : IsZero
        (((ChainComplex.single₀ (ModuleCat.{u} R)).obj A').homology
            ij.val.1 ⊗
          K'.homology ij.val.2) :=
      (tensorRight (K'.homology ij.val.2)).map_isZero hzero
    exact htensor.eq_of_tgt _ _

/-- The coefficient map commutes with Koszul tensor braiding.

The canonical coefficient map followed by the chain tensor braiding on homology equals the
module tensor braid followed by the swapped Künneth coefficient map. -/
@[reassoc]
theorem homologyUniversalCoefficientMap_koszul_braiding
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (A : ModuleCat.{u} R) (n : ℕ) :
    let L := (ChainComplex.single₀ (ModuleCat.{u} R)).obj A
    homologyUniversalCoefficientMap K A n ≫
        HomologicalComplex.homologyMap
          (koszulTensorBraidingIso K L).hom n =
      (β_ (K.homology n) A).hom ≫
        (homologyUCTSwappedTensorSourceIso K A n).inv ≫
        kunnethHomologyTensorMap L K n := by
  dsimp only
  let L := (ChainComplex.single₀ (ModuleCat.{u} R)).obj A
  let P : ChainGradedPairing K L (tensorObj K L) := 𝟙 _
  let Q : ChainGradedPairing L K (tensorObj L K) := 𝟙 _
  let b := (koszulTensorBraidingIso K L).hom
  have hpair := ChainGradedPairing.pair_braiding_of_koszul
    P Q b (by simp [P, Q, b]) n 0
  have hpairHomology := ChainGradedPairing.pairHomology_braiding
    P (ChainGradedPairing.homologyDescentData P)
    Q (ChainGradedPairing.homologyDescentData Q)
    b ((-1 : ℤ) ^ (n * 0)) n 0 hpair
  have hpairHomology' :
      ChainGradedPairing.pairHomology
          (𝟙 (tensorObj K L))
          (ChainGradedPairing.homologyDescentData
            (𝟙 (tensorObj K L))) n 0 ≫
          HomologicalComplex.homologyMap b (n + 0) =
        (β_ (K.homology n) (L.homology 0)).hom ≫
          ChainGradedPairing.pairHomology
            (𝟙 (tensorObj L K))
            (ChainGradedPairing.homologyDescentData
              (𝟙 (tensorObj L K))) 0 n ≫
          (homologyIsoOfEq (tensorObj L K) (Nat.add_comm 0 n)).hom := by
    simpa only [P, Q, Nat.mul_zero, pow_zero, one_smul] using
      hpairHomology
  have htransport :
      (homologyIsoOfEq (tensorObj L K) (Nat.add_comm 0 n)).hom ≫
          (homologyIsoOfEq (tensorObj L K) (Nat.add_zero n)).hom =
        (homologyIsoOfEq (tensorObj L K) (Nat.zero_add n)).hom := by
    rw [HomologicalComplex.homologyIsoOfEq_hom_trans (tensorObj L K)]
  rw [homologyUniversalCoefficientMap_eq_pairing]
  simp only [Category.assoc]
  rw [← homologyIsoOfEq_hom_naturality b (Nat.add_zero n)]
  slice_lhs 2 3 => rw [hpairHomology']
  simp only [Category.assoc]
  rw [BraidedCategory.braiding_naturality_assoc]
  rw [htransport]
  rw [← homologyUCTSwappedTensorSourceIso_inv_comp_kunnethHomologyTensorMap]

/-- A flat coefficient makes the canonical homological coefficient map an isomorphism.

For any commutative R and chain complex K, flatness of A implies H_n(K) ⊗ A ≅ H_n(K ⊗ A[0]). -/
theorem isIso_homologyUniversalCoefficientMap_of_flat
    {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (A : ModuleCat.{u} R) [Module.Flat R A] (n : ℕ) :
    IsIso (homologyUniversalCoefficientMap K A n) := by
  let L := (ChainComplex.single₀ (ModuleCat.{u} R)).obj A
  have hL (i : ℕ) : Module.Flat R (L.X i) := by
    by_cases hi : i = 0
    · subst i
      exact Module.Flat.of_linearEquiv
        (singleObjXSelf (ComplexShape.down ℕ) 0 A).toLinearEquiv
    · let _ : Projective (L.X i) :=
        (isZero_single_obj_X (ComplexShape.down ℕ) 0 A i hi).projective
      let _ : Module.Projective R (L.X i) := by infer_instance
      exact Module.Flat.of_projective
  have hHL (i : ℕ) : Module.Flat R (L.homology i) := by
    by_cases hi : i = 0
    · subst i
      exact Module.Flat.of_linearEquiv
        (singleObjHomologySelfIso
          (ComplexShape.down ℕ) 0 A).toLinearEquiv
    · let _ : Projective (L.homology i) :=
        (isZero_single_obj_homology
          (ComplexShape.down ℕ) 0 A i hi).projective
      let _ : Module.Projective R (L.homology i) := by infer_instance
      exact Module.Flat.of_projective
  let _ : IsIso (kunnethHomologyTensorMap L K n) :=
    isIso_kunnethHomologyTensorMap_of_flat_homology L K hL hHL n
  let _ : IsIso
      (HomologicalComplex.homologyMap
        (koszulTensorBraidingIso K L).hom n) := by
    change IsIso (homologyMapIso (koszulTensorBraidingIso K L) n).hom
    infer_instance
  let _ : IsIso
      (homologyUniversalCoefficientMap K A n ≫
        HomologicalComplex.homologyMap
          (koszulTensorBraidingIso K L).hom n) := by
    rw [homologyUniversalCoefficientMap_koszul_braiding]
    infer_instance
  exact CategoryTheory.IsIso.of_isIso_comp_right
    (homologyUniversalCoefficientMap K A n)
    (HomologicalComplex.homologyMap
      (koszulTensorBraidingIso K L).hom n)

end HomologicalComplex

end
