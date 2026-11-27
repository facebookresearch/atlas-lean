/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.KoszulComplexCoefficientFiniteEuler
public import MathlibExt.Algebra.Homology.KoszulComplexFamilyReindex
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Reindexing and scalar cofibers for Koszul tensor complexes

Equivalences of coefficient modules and finite families induce isomorphisms
of Koszul tensor complexes. If every family member annihilates the module,
the tensor differential is zero. An exterior basis then computes each
homology length, and the binomial alternating sum vanishes for a nonempty
family.

Adjoining one family member gives the homotopy cofiber of its scalar map
on the smaller-family complex. The component formulas retain the order of
the two summands and the sign of the shifted differential.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R] {n : ℕ}

/-- Reindexing the original family gives an isomorphism of the same
coefficient tensor complexes. -/
def familyTensorCoefficientReindexIso
    (a : Fin n → R) (M : ModuleCat.{v} R) (e : Fin n ≃ Fin n) :
    familyTensorCoefficientComplex R a M ≅
      familyTensorCoefficientComplex R (fun j => a (e.symm j)) M :=
  ((coefficientTensorFunctor R M).mapHomologicalComplex
    (ComplexShape.down ℕ)).mapIso (familyComplexReindexIso R a e)

/-- Actual full-family coefficient Euler is invariant under original family
reindexing, with every native homology term retained. -/
theorem familyTensorCoefficientEuler_reindex [IsNoetherianRing R]
    (a : Fin n → R) (M : ModuleCat.{v} R) [Module.Finite R M] (e : Fin n ≃ Fin n)
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤)
    (hquot' : Module.length R
      (R ⧸ (Ideal.span (Set.range (fun j => a (e.symm j))) ⊔ Module.annihilator R M)) ≠ ⊤) :
    familyTensorCoefficientEuler R a M hquot =
      familyTensorCoefficientEuler R (fun j => a (e.symm j)) M hquot' := by
  rw [familyTensorCoefficientEuler_eq, familyTensorCoefficientEuler_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [(HomologicalComplex.homologyMapIso
    (familyTensorCoefficientReindexIso R a M e) j).toLinearEquiv.length_eq]

/-- The actual exterior tensor term is the finite direct product of copies
of the original coefficient module indexed by its exterior basis. -/
def familyTensorCoefficientTermEquiv (a : Fin n → R) (M : ModuleCat.{v} R) (j : ℕ) :
    (familyTensorCoefficientComplex R a M).X j ≃ₗ[R]
      (Set.powersetCard (Fin n) j → M) :=
  TensorProduct.congr (LinearEquiv.refl R M)
    (((Pi.basisFun R (Fin n)).exteriorPower j).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite R R (Set.powersetCard (Fin n) j)) ≪≫ₗ
    TensorProduct.piScalarRight R R M (Set.powersetCard (Fin n) j)

/-- The original family term length has its actual binomial multiplicity. -/
theorem familyTensorCoefficientTerm_length
    (a : Fin n → R) (M : ModuleCat.{v} R) (j : ℕ) :
    Module.length R ((familyTensorCoefficientComplex R a M).X j) =
      (n.choose j : ENat) * Module.length R M := by
  rw [(familyTensorCoefficientTermEquiv R a M j).length_eq]
  simp only [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Fintype.card_eq_nat_card, Set.powersetCard.card]
  simp only [Nat.card_fin]

/-- When each original coefficient annihilates the original module, every
actual coefficient tensor differential vanishes. -/
theorem familyTensorCoefficient_d_eq_zero_of_coefficients_annihilate
    (a : Fin n → R) (M : ModuleCat.{v} R)
    (ha : ∀ i, a i ∈ Module.annihilator R M) (i j : ℕ) :
    (familyTensorCoefficientComplex R a M).d i j = 0 := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · have hi : i = j + 1 := hij.symm
    subst i
    change (coefficientTensorFunctor R M).map
      ((complex R (Fin n → R) (familyFunctional R a)).d (j + 1) j) = 0
    rw [complex_d_succ]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro m
    apply ((Pi.basisFun R (Fin n)).exteriorPower (j + 1)).ext
    intro s
    change m ⊗ₜ[R] differential R (Fin n → R) (familyFunctional R a) j
      (((Pi.basisFun R (Fin n)).exteriorPower (j + 1)) s) = 0
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    simp only [Function.comp_def, Pi.basisFun_apply]
    change m ⊗ₜ[R] differential R (Fin n → R) (familyFunctional R a) j
      (exteriorPower.ιMulti R (j + 1)
        (fun k => Pi.single ((Set.powersetCard.ofFinEmbEquiv.symm s) k) 1)) = 0
    rw [familyDifferential_apply_basis, TensorProduct.tmul_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    have hk : (((-1 : R) ^ k.val) * a ((Set.powersetCard.ofFinEmbEquiv.symm s) k)) • m = 0 := by
      rw [mul_smul, Module.mem_annihilator.mp (ha _) m, smul_zero]
    rw [hk, TensorProduct.zero_tmul]
  · exact (familyTensorCoefficientComplex R a M).shape i j hij

/-- With annihilated coefficients the original native homology is its
actual tensor term, including every positive exterior degree. -/
def familyTensorCoefficientHomologyIsoTermOfCoefficientsAnnihilate
    (a : Fin n → R) (M : ModuleCat.{v} R)
    (ha : ∀ i, a i ∈ Module.annihilator R M) (j : ℕ) :
    (familyTensorCoefficientComplex R a M).homology j ≅
      (familyTensorCoefficientComplex R a M).X j :=
  (ShortComplex.LeftHomologyData.ofZeros
    ((familyTensorCoefficientComplex R a M).sc j)
    (familyTensorCoefficient_d_eq_zero_of_coefficients_annihilate R a M ha _ _)
    (familyTensorCoefficient_d_eq_zero_of_coefficients_annihilate R a M ha _ _)).homologyIso

/-- Every positive-size family annihilating the original finite coefficient
module has zero actual full-family Euler characteristic. -/
theorem familyTensorCoefficientEuler_eq_zero_of_coefficients_annihilate
    [IsNoetherianRing R] (a : Fin n → R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (hquot : Module.length R
      (R ⧸ (Ideal.span (Set.range a) ⊔ Module.annihilator R M)) ≠ ⊤)
    (ha : ∀ i, a i ∈ Module.annihilator R M) (hn : n ≠ 0) :
    familyTensorCoefficientEuler R a M hquot = 0 := by
  have hlength (j : ℕ) :
      Module.length R ((familyTensorCoefficientComplex R a M).homology j) =
        (n.choose j : ENat) * Module.length R M :=
    (familyTensorCoefficientHomologyIsoTermOfCoefficientsAnnihilate R a M ha j).toLinearEquiv.length_eq.trans
      (familyTensorCoefficientTerm_length R a M j)
  rw [familyTensorCoefficientEuler_eq]
  calc
    (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j *
        (Module.length R ((familyTensorCoefficientComplex R a M).homology j)).toNat) =
        ∑ j ∈ Finset.range (n + 1),
          ((-1 : ℤ) ^ j * n.choose j) * (Module.length R M).toNat := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hlength, ENat.toNat_mul, ENat.toNat_natCast, Nat.cast_mul, mul_assoc]
    _ = (∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * n.choose j) *
        (Module.length R M).toNat := (Finset.sum_mul _ _ _).symm
    _ = 0 := by rw [Int.alternating_sum_range_choose_of_ne hn, zero_mul]

section ProductCone

variable (E : Type u) [AddCommGroup E] [Module R E]

/-- The original product-one differential in actual decomposed coordinates. -/
theorem productOneDecompose_differential
    (y : E →ₗ[R] R) (r : R) (j : ℕ) (z : ⋀[R]^(j + 2) (E × R)) :
    exteriorPower.productOneDecompose R E j
        (differential R (E × R) (productOneFunctional R E y r) (j + 1) z) =
      (differential R E y (j + 1) (exteriorPower.productOneDecompose R E (j + 1) z).1 +
        r • (exteriorPower.productOneDecompose R E (j + 1) z).2,
        -differential R E y j (exteriorPower.productOneDecompose R E (j + 1) z).2) := by
  have h := productOneDifferential_assemble R E y r j
    (exteriorPower.productOneDecompose R E (j + 1) z).1
    (exteriorPower.productOneDecompose R E (j + 1) z).2
  rw [exteriorPower.productOneAssemble_decompose] at h
  simpa only [exteriorPower.productOneDecompose_assemble] using
    congrArg (exteriorPower.productOneDecompose R E j) h

/-- The actual degree-one endpoint after product-one decomposition. -/
theorem productOneZeroEquiv_differential
    (y : E →ₗ[R] R) (r : R) (z : ⋀[R]^1 (E × R)) :
    exteriorPower.zeroEquiv R (E × R)
        (differential R (E × R) (productOneFunctional R E y r) 0 z) =
      exteriorPower.zeroEquiv R E
          (differential R E y 0 (exteriorPower.productOneDecompose R E 0 z).1) +
        r * exteriorPower.zeroEquiv R E (exteriorPower.productOneDecompose R E 0 z).2 := by
  have h := productOneDifferential_assemble_zero R E y r
    (exteriorPower.productOneDecompose R E 0 z).1
    (exteriorPower.productOneDecompose R E 0 z).2
  rwa [exteriorPower.productOneAssemble_decompose] at h

/-- The original product-one exterior term is the original scalar-map
homotopy cofiber term, with the shifted component first. -/
def productOneConeComponentIso (y : E →ₗ[R] R) (r : R) (j : ℕ) :
    (complex R (E × R) (productOneFunctional R E y r)).X j ≅
      (HomologicalComplex.homotopyCofiber (r • 𝟙 (complex R E y))).X j :=
  match j with
  | 0 =>
      ((exteriorPower.zeroEquiv R (E × R)) ≪≫ₗ
        (exteriorPower.zeroEquiv R E).symm).toModuleIso ≪≫
          (HomologicalComplex.homotopyCofiber.XIso (r • 𝟙 (complex R E y)) 0 (by simp)).symm
  | j + 1 =>
      ((exteriorPower.productOneEquiv R E j) ≪≫ₗ
        LinearEquiv.prodComm R _ _).toModuleIso ≪≫
          (ModuleCat.biprodIsoProd ((complex R E y).X j) ((complex R E y).X (j + 1))).symm ≪≫
            (HomologicalComplex.homotopyCofiber.XIsoBiprod
              (r • 𝟙 (complex R E y)) (j + 1) j rfl).symm

/-- The canonical degree-term equivalence of the original exterior complex. -/
def complexTermEquiv (y : E →ₗ[R] R) (j : ℕ) :
    (complex R E y).X j ≃ₗ[R] ⋀[R]^j E :=
  (eqToIso (complex_X R E y j)).toLinearEquiv

/-- The lower exterior component as a map between the original degree objects. -/
def productOneConeFstMap (y : E →ₗ[R] R) (r : R) (j : ℕ) :
    (complex R (E × R) (productOneFunctional R E y r)).X (j + 1) ⟶ (complex R E y).X j :=
  ModuleCat.ofHom ((LinearMap.snd R (⋀[R]^(j + 1) E) (⋀[R]^j E)).comp
    (exteriorPower.productOneDecompose R E j))

/-- The upper exterior component as a map between the original degree objects. -/
def productOneConeSndMap (y : E →ₗ[R] R) (r : R) (j : ℕ) :
    (complex R (E × R) (productOneFunctional R E y r)).X (j + 1) ⟶ (complex R E y).X (j + 1) :=
  ModuleCat.ofHom ((LinearMap.fst R (⋀[R]^(j + 1) E) (⋀[R]^j E)).comp
    (exteriorPower.productOneDecompose R E j))

/-- The actual degree-zero scalar comparison as a map of original degree objects. -/
def productOneConeZeroMap (y : E →ₗ[R] R) (r : R) :
    (complex R (E × R) (productOneFunctional R E y r)).X 0 ⟶ (complex R E y).X 0 :=
  ((exteriorPower.zeroEquiv R (E × R)) ≪≫ₗ (exteriorPower.zeroEquiv R E).symm).toModuleIso.hom

@[simp]
theorem productOneConeFstMap_apply (y : E →ₗ[R] R) (r : R) (j : ℕ)
    (z : (complex R (E × R) (productOneFunctional R E y r)).X (j + 1)) :
    complexTermEquiv R E y j (productOneConeFstMap R E y r j z) =
      (exteriorPower.productOneDecompose R E j
        (complexTermEquiv R (E × R) (productOneFunctional R E y r) (j + 1) z)).2 := rfl

@[simp]
theorem productOneConeSndMap_apply (y : E →ₗ[R] R) (r : R) (j : ℕ)
    (z : (complex R (E × R) (productOneFunctional R E y r)).X (j + 1)) :
    complexTermEquiv R E y (j + 1) (productOneConeSndMap R E y r j z) =
      (exteriorPower.productOneDecompose R E j
        (complexTermEquiv R (E × R) (productOneFunctional R E y r) (j + 1) z)).1 := rfl

@[simp]
theorem productOneConeZeroMap_apply (y : E →ₗ[R] R) (r : R)
    (z : (complex R (E × R) (productOneFunctional R E y r)).X 0) :
    complexTermEquiv R E y 0 (productOneConeZeroMap R E y r z) =
      (exteriorPower.zeroEquiv R E).symm ((exteriorPower.zeroEquiv R (E × R))
        (complexTermEquiv R (E × R) (productOneFunctional R E y r) 0 z)) := rfl

/-- The original successor differential under its canonical degree-term equivalences. -/
theorem complex_d_succ_apply (y : E →ₗ[R] R) (j : ℕ)
    (z : (complex R E y).X (j + 1)) :
    complexTermEquiv R E y j ((complex R E y).d (j + 1) j z) =
      differential R E y j (complexTermEquiv R E y (j + 1) z) := by
  rw [complex_d_succ]
  rfl

private theorem cofiber_sndX_eq
    {K L : ChainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L) (i j : ℕ)
    (h : (ComplexShape.down ℕ).Rel i j) :
    HomologicalComplex.homotopyCofiber.sndX f i =
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i j h).hom ≫ biprod.snd := by
  obtain rfl := (ComplexShape.down ℕ).next_eq' h
  exact dite_eq_left h

/-- The first cofiber component is the original lower exterior component. -/
theorem productOneConeComponentIso_succ_hom_fst
    (y : E →ₗ[R] R) (r : R) (j : ℕ) :
    (productOneConeComponentIso R E y r (j + 1)).hom ≫
        HomologicalComplex.homotopyCofiber.fstX (r • 𝟙 (complex R E y)) (j + 1) j rfl =
      productOneConeFstMap R E y r j := by
  let A : (complex R (E × R) (productOneFunctional R E y r)).X (j + 1) ≅
      ModuleCat.of R (((complex R E y).X j) × ((complex R E y).X (j + 1))) :=
    ((exteriorPower.productOneEquiv R E j) ≪≫ₗ LinearEquiv.prodComm R _ _).toModuleIso
  let B := ModuleCat.biprodIsoProd ((complex R E y).X j) ((complex R E y).X (j + 1))
  let C := HomologicalComplex.homotopyCofiber.XIsoBiprod (r • 𝟙 (complex R E y)) (j + 1) j rfl
  change A.hom ≫ B.inv ≫ (C.inv ≫ C.hom) ≫ biprod.fst = _
  rw [C.inv_hom_id, Category.id_comp]
  have hB := ModuleCat.biprodIsoProd_inv_comp_fst ((complex R E y).X j) ((complex R E y).X (j + 1))
  rw [hB]
  rfl

/-- The second cofiber component is the original upper exterior component. -/
theorem productOneConeComponentIso_succ_hom_snd
    (y : E →ₗ[R] R) (r : R) (j : ℕ) :
    (productOneConeComponentIso R E y r (j + 1)).hom ≫
        HomologicalComplex.homotopyCofiber.sndX (r • 𝟙 (complex R E y)) (j + 1) =
      productOneConeSndMap R E y r j := by
  rw [cofiber_sndX_eq R _ (j + 1) j (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl)]
  let A : (complex R (E × R) (productOneFunctional R E y r)).X (j + 1) ≅
      ModuleCat.of R (((complex R E y).X j) × ((complex R E y).X (j + 1))) :=
    ((exteriorPower.productOneEquiv R E j) ≪≫ₗ LinearEquiv.prodComm R _ _).toModuleIso
  let B := ModuleCat.biprodIsoProd ((complex R E y).X j) ((complex R E y).X (j + 1))
  let C := HomologicalComplex.homotopyCofiber.XIsoBiprod (r • 𝟙 (complex R E y)) (j + 1) j rfl
  change A.hom ≫ B.inv ≫ (C.inv ≫ C.hom) ≫ biprod.snd = _
  rw [C.inv_hom_id, Category.id_comp]
  have hB := ModuleCat.biprodIsoProd_inv_comp_snd ((complex R E y).X j) ((complex R E y).X (j + 1))
  rw [hB]
  rfl

/-- The true zero endpoint preserves the original degree-zero scalar. -/
theorem productOneConeComponentIso_zero_hom_snd
    (y : E →ₗ[R] R) (r : R) :
    (productOneConeComponentIso R E y r 0).hom ≫
        HomologicalComplex.homotopyCofiber.sndX (r • 𝟙 (complex R E y)) 0 =
      productOneConeZeroMap R E y r := by
  have hn : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by simp
  let A : (complex R (E × R) (productOneFunctional R E y r)).X 0 ≅
      (complex R E y).X 0 :=
    ((exteriorPower.zeroEquiv R (E × R)) ≪≫ₗ (exteriorPower.zeroEquiv R E).symm).toModuleIso
  let C := HomologicalComplex.homotopyCofiber.XIso (r • 𝟙 (complex R E y)) 0 hn
  rw [HomologicalComplex.homotopyCofiber.sndX, dite_eq_right hn]
  change A.hom ≫ (C.inv ≫ C.hom) = A.hom
  rw [C.inv_hom_id, Category.comp_id]

/-- The actual product-one Koszul complex is the native homotopy cofiber
of scalar multiplication on the original smaller Koszul complex. -/
def productOneComplexIsoCone (y : E →ₗ[R] R) (r : R) :
    complex R (E × R) (productOneFunctional R E y r) ≅
      HomologicalComplex.homotopyCofiber (r • 𝟙 (complex R E y)) :=
  HomologicalComplex.Hom.isoOfComponents (productOneConeComponentIso R E y r)
    (by
      intro i j hij
      have hi : i = j + 1 := hij.symm
      subst i
      cases j with
      | zero =>
          have hrel : (ComplexShape.down ℕ).Rel 1 0 := by rfl
          have hn : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by simp
          change (productOneConeComponentIso R E y r 1).hom ≫
              HomologicalComplex.homotopyCofiber.d (r • 𝟙 (complex R E y)) 1 0 =
            (complex R (E × R) (productOneFunctional R E y r)).d 1 0 ≫
              (productOneConeComponentIso R E y r 0).hom
          apply HomologicalComplex.homotopyCofiber.ext_to_X' (r • 𝟙 (complex R E y)) 0 hn
          rw [Category.assoc, HomologicalComplex.homotopyCofiber.d_sndX
            (r • 𝟙 (complex R E y)) 1 0 hrel, Preadditive.comp_add]
          simp only [← Category.assoc, productOneConeComponentIso_succ_hom_fst,
            productOneConeComponentIso_succ_hom_snd]
          rw [Category.assoc, productOneConeComponentIso_zero_hom_snd]
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro z
          simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply]
          change r • productOneConeFstMap R E y r 0 z +
              (complex R E y).d 1 0 (productOneConeSndMap R E y r 0 z) =
            productOneConeZeroMap R E y r
              ((complex R (E × R) (productOneFunctional R E y r)).d 1 0 z)
          apply (complexTermEquiv R E y 0).injective
          apply (exteriorPower.zeroEquiv R E).injective
          rw [productOneConeZeroMap_apply, LinearEquiv.apply_symm_apply,
            complex_d_succ_apply, map_add, map_smul, productOneConeFstMap_apply,
            complex_d_succ_apply, productOneConeSndMap_apply, map_add, map_smul,
            smul_eq_mul, productOneZeroEquiv_differential]
          exact add_comm _ _
      | succ j =>
          have hrel : (ComplexShape.down ℕ).Rel (j + 1) j := by rfl
          have hfar : (ComplexShape.down ℕ).Rel (j + 1 + 1) (j + 1) := by rfl
          rw [HomologicalComplex.homotopyCofiber_d]
          apply HomologicalComplex.homotopyCofiber.ext_to_X (r • 𝟙 (complex R E y)) (j + 1) j hrel
          · rw [Category.assoc, HomologicalComplex.homotopyCofiber.d_fstX
              (r • 𝟙 (complex R E y)) (j + 1 + 1) (j + 1) j hfar hrel]
            simp only [← Category.assoc, productOneConeComponentIso_succ_hom_fst,
              Preadditive.comp_neg]
            rw [Category.assoc, productOneConeComponentIso_succ_hom_fst]
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro z
            simp only [ModuleCat.hom_comp, ModuleCat.hom_neg, LinearMap.comp_apply, LinearMap.neg_apply]
            change -((complex R E y).d (j + 1) j (productOneConeFstMap R E y r (j + 1) z)) =
              productOneConeFstMap R E y r j
                ((complex R (E × R) (productOneFunctional R E y r)).d (j + 1 + 1) (j + 1) z)
            apply (complexTermEquiv R E y j).injective
            rw [map_neg, complex_d_succ_apply, productOneConeFstMap_apply,
              productOneConeFstMap_apply, complex_d_succ_apply,
              productOneDecompose_differential]
          · rw [Category.assoc, HomologicalComplex.homotopyCofiber.d_sndX
              (r • 𝟙 (complex R E y)) (j + 1 + 1) (j + 1) hfar, Preadditive.comp_add]
            simp only [← Category.assoc, productOneConeComponentIso_succ_hom_fst,
              productOneConeComponentIso_succ_hom_snd]
            rw [Category.assoc, productOneConeComponentIso_succ_hom_snd]
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro z
            simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply]
            change r • productOneConeFstMap R E y r (j + 1) z +
                (complex R E y).d (j + 1 + 1) (j + 1) (productOneConeSndMap R E y r (j + 1) z) =
              productOneConeSndMap R E y r j
                ((complex R (E × R) (productOneFunctional R E y r)).d (j + 1 + 1) (j + 1) z)
            apply (complexTermEquiv R E y (j + 1)).injective
            rw [map_add, map_smul, productOneConeFstMap_apply,
              complex_d_succ_apply, productOneConeSndMap_apply,
              productOneConeSndMap_apply, complex_d_succ_apply,
              productOneDecompose_differential]
            exact add_comm _ _)

end ProductCone

/-- Original coefficient tensoring sends scalar multiplication of a term
to scalar multiplication of the original tensor term. -/
theorem coefficientTensorFunctor_map_smul_id
    (M : ModuleCat.{v} R) (K : ModuleCat.{u} R) (r : R) :
    (coefficientTensorFunctor R M).map (r • 𝟙 K) =
      r • 𝟙 ((coefficientTensorFunctor R M).obj K) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  change m ⊗ₜ[R] (r • x) = r • (m ⊗ₜ[R] x)
  exact TensorProduct.tmul_smul _ _ _

/-- Scalar multiplication of the original finite-family complex maps to
literal scalar multiplication of the original coefficient tensor complex. -/
theorem familyTensorCoefficientScalarMap_eq
    (a : Fin n → R) (M : ModuleCat.{v} R) (r : R) :
    ((coefficientTensorFunctor R M).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (r • 𝟙 (familyComplex R a)) = r • 𝟙 (familyTensorCoefficientComplex R a M) := by
  apply HomologicalComplex.hom_ext
  intro j
  exact coefficientTensorFunctor_map_smul_id R M ((familyComplex R a).X j) r

/-- Original coefficient scalar multiplication induces scalar multiplication
of the actual whole coefficient tensor complex. -/
theorem familyTensorCoefficientMap_smul_id
    (a : Fin n → R) (M : ModuleCat.{v} R) (r : R) :
    familyTensorCoefficientMap R a (r • 𝟙 M) = r • 𝟙 (familyTensorCoefficientComplex R a M) := by
  apply HomologicalComplex.hom_ext
  intro j
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro x
  change (r • m) ⊗ₜ[R] x = r • (m ⊗ₜ[R] x)
  exact (TensorProduct.smul_tmul' _ _ _).symm

/-- The original last-coordinate family equivalence identifies the same
finite-family complex with the actual product-one complex. -/
def familySnocProductIso (a : Fin (n + 1) → R) :
    complex R ((Fin n → R) × R)
        (productOneFunctional R (Fin n → R)
          (familyFunctional R (fun i : Fin n => a i.castSucc)) (a (Fin.last n))) ≅ familyComplex R a :=
  mapIso R ((Fin n → R) × R)
    (productOneFunctional R (Fin n → R)
      (familyFunctional R (fun i : Fin n => a i.castSucc)) (a (Fin.last n)))
    (familyFunctional R a) (finiteFamilySnocModuleEquiv R n)
    (familyFunctional_comp_snocModuleEquiv R a)

/-- The full original family is the native scalar cofiber of its actual
last-coordinate deletion. -/
def familySnocConeIso (a : Fin (n + 1) → R) :
    familyComplex R a ≅
      HomologicalComplex.homotopyCofiber
        (a (Fin.last n) • 𝟙 (familyComplex R (fun i : Fin n => a i.castSucc))) :=
  (familySnocProductIso R a).symm ≪≫
    productOneComplexIsoCone R (Fin n → R)
      (familyFunctional R (fun i : Fin n => a i.castSucc)) (a (Fin.last n))

/-- The actual full-family coefficient tensor is the native cofiber of the
original scalar coefficient map on its actual smaller-family tensor. -/
def familyTensorCoefficientSnocConeIso
    (a : Fin (n + 1) → R) (M : ModuleCat.{v} R) :
    familyTensorCoefficientComplex R a M ≅
      HomologicalComplex.homotopyCofiber
        (familyTensorCoefficientMap R (fun i : Fin n => a i.castSucc) (a (Fin.last n) • 𝟙 M)) := by
  let F : ModuleCat.{u} R ⥤ ModuleCat.{max u v} R := coefficientTensorFunctor R M
  let K : ChainComplex (ModuleCat.{u} R) ℕ := familyComplex R (fun i : Fin n => a i.castSucc)
  let f : K ⟶ K := a (Fin.last n) • 𝟙 K
  let g := familyTensorCoefficientMap R (fun i : Fin n => a i.castSucc) (a (Fin.last n) • 𝟙 M)
  have hmap : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map f = g :=
    (familyTensorCoefficientScalarMap_eq R (fun i : Fin n => a i.castSucc) M (a (Fin.last n))).trans
      (familyTensorCoefficientMap_smul_id R (fun i : Fin n => a i.castSucc) M (a (Fin.last n))).symm
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso (familySnocConeIso R a) ≪≫
    HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f F ≪≫
      HomologicalComplex.homotopyCofiber.mapArrowIso _ g
        (fun j => ⟨j + 1, rfl⟩) (eqToIso (congrArg Arrow.mk hmap))

end KoszulComplex
