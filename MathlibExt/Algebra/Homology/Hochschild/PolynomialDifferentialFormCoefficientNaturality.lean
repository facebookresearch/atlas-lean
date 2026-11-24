/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDifferentialFormComplexComparison

/-!
# Integral polynomial HKR naturality in the coefficient

The signed inverse comparison commutes with algebra-linear
coefficient maps already at the level of chains. The forward comparison
commutes up to the homotopies of the chain homotopy equivalences.
The resulting homology square uses the coefficient-head form map.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)
  {M N : Type w} [AddCommGroup M] [AddCommGroup N]
  [Module k M] [Module k N]
  [Module (MvPolynomial σ k) M] [Module (MvPolynomial σ k) N]
  [SMulCommClass k (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) N]
  [IsScalarTower k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) N]

local notation "A" => MvPolynomial σ k
local notation "V" => σ →₀ k
local notation "Ω" => KaehlerDifferential k A

/-- The ground free exterior coordinates of the canonical lifted
form object. -/
def polynomialFormFreeDegreeEquiv (M : Type w) [AddCommGroup M] [Module k M]
    [Module A M] [SMulCommClass k A M] [IsScalarTower k A M] (n : ℕ) :
    M ⊗[k] (⋀[k]^n V) ≃ₗ[k] (Symmetric.coefficientDifferentialFormComplex k A M).X n :=
  ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).restrictScalars k).trans
    (ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
      M ⊗[A] (⋀[A]^n Ω)).symm

/-- Free variable coordinates give the original lifted differential word. -/
theorem polynomialFormFreeDegreeEquiv_basis
    (n : ℕ) (m : M) (a : Fin n → σ) :
    polynomialFormFreeDegreeEquiv k σ M n
      (m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (a j) (1 : k))) =
      ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (MvPolynomial.X (a j)))) := by
  change ULift.up (KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n _) = _
  rw [KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_tmul_basis]

/-- The form-complex map acts only on the original coefficient head. -/
theorem polynomialFormCoefficientMap_basis (f : M →ₗ[A] N)
    (n : ℕ) (m : M) (a : Fin n → σ) :
    ((Symmetric.coefficientDifferentialFormComplexMap k A f).f n).hom
      (ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (MvPolynomial.X (a j))))) =
      ULift.up (f m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (MvPolynomial.X (a j)))) := by
  let raw : M ⊗[A] (⋀[A]^n Ω) →ₗ[k] N ⊗[A] (⋀[A]^n Ω) :=
    (TensorProduct.map f
      (LinearMap.id : (⋀[A]^n Ω) →ₗ[A] (⋀[A]^n Ω))).restrictScalars k
  have hUp (ω : M ⊗[A] (⋀[A]^n Ω)) :
      ((Symmetric.coefficientDifferentialFormComplexMap k A f).f n).hom (ULift.up ω) =
        ULift.up (raw ω) := rfl
  have hRaw : raw (m ⊗ₜ[A] exteriorPower.ιMulti A n
      (fun j => KaehlerDifferential.D k A (MvPolynomial.X (a j)))) =
        f m ⊗ₜ[A] exteriorPower.ιMulti A n
          (fun j => KaehlerDifferential.D k A (MvPolynomial.X (a j))) := by
    simp only [raw, LinearMap.restrictScalars_apply, TensorProduct.map_tmul,
      LinearMap.id_apply]
  exact (hUp _).trans (congrArg ULift.up hRaw)

/-- The integral signed inverse comparison is strictly natural in the
symmetric coefficient. No factorial cancellation enters this square. -/
@[reassoc]
theorem polynomialDifferentialFormComparison_inv_coefficient (f : M →ₗ[A] N) :
    Symmetric.coefficientDifferentialFormComplexMap k A f ≫
        (polynomialDifferentialFormComparison k σ N).inv =
      (polynomialDifferentialFormComparison k σ M).inv ≫
        Symmetric.symmetricOriginalCoefficientChainMap k A M f := by
  apply HomologicalComplex.hom_ext
  intro n
  let e := polynomialFormFreeDegreeEquiv k σ M n
  let L : M ⊗[k] (⋀[k]^n V) →ₗ[k] (Symmetric.chainComplex k A N).X n :=
    (((polynomialDifferentialFormComparison k σ N).inv.f n).hom.comp
      ((Symmetric.coefficientDifferentialFormComplexMap k A f).f n).hom).comp e.toLinearMap
  let R : M ⊗[k] (⋀[k]^n V) →ₗ[k] (Symmetric.chainComplex k A N).X n :=
    (((Symmetric.symmetricOriginalCoefficientChainMap k A M f).f n).hom.comp
      ((polynomialDifferentialFormComparison k σ M).inv.f n).hom).comp e.toLinearMap
  let head : M ⊗[k] TensorPower k n A →ₗ[k] N ⊗[k] TensorPower k n A :=
    TensorProduct.map (f.restrictScalars k)
      (LinearMap.id : TensorPower k n A →ₗ[k] TensorPower k n A)
  have hHead : ((Symmetric.symmetricOriginalCoefficientChainMap k A M f).f n).hom = head :=
    Symmetric.symmetricOriginalCoefficientChainMap_tensor k A f n
  have hLR : L = R := by
    apply TensorProduct.curry_injective
    apply LinearMap.ext
    intro m
    apply exteriorPower.linearMap_ext
    apply (Finsupp.basisSingleOne (R := k) (ι := σ)).ext_alternating
    intro a _
    simp only [Finsupp.coe_basisSingleOne, LinearMap.compAlternatingMap_apply,
      TensorProduct.curry_apply]
    change ((polynomialDifferentialFormComparison k σ N).inv.f n).hom
      (((Symmetric.coefficientDifferentialFormComplexMap k A f).f n).hom
        (e (m ⊗ₜ[k] exteriorPower.ιMulti k n
          (fun j => Finsupp.single (a j) (1 : k))))) =
      ((Symmetric.symmetricOriginalCoefficientChainMap k A M f).f n).hom
        (((polynomialDifferentialFormComparison k σ M).inv.f n).hom
          (e (m ⊗ₜ[k] exteriorPower.ιMulti k n
            (fun j => Finsupp.single (a j) (1 : k)))))
    let ωM : (Symmetric.coefficientDifferentialFormComplex k A M).X n :=
      ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (MvPolynomial.X (a j))))
    let ωN : (Symmetric.coefficientDifferentialFormComplex k A N).X n :=
      ULift.up (f m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (MvPolynomial.X (a j))))
    let sM : M ⊗[k] TensorPower k n A :=
      ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
        (m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (a (π j))))
    let sN : N ⊗[k] TensorPower k n A :=
      ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
        (f m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (a (π j))))
    have hFree : e (m ⊗ₜ[k] exteriorPower.ιMulti k n
        (fun j => Finsupp.single (a j) (1 : k))) = ωM :=
      polynomialFormFreeDegreeEquiv_basis k σ n m a
    have hForm : ((Symmetric.coefficientDifferentialFormComplexMap k A f).f n).hom ωM = ωN :=
      polynomialFormCoefficientMap_basis k σ f n m a
    have hInvM : ((polynomialDifferentialFormComparison k σ M).inv.f n).hom ωM = sM :=
      polynomialDifferentialFormComparison_inv_f_basis k σ M n m a
    have hInvN : ((polynomialDifferentialFormComparison k σ N).inv.f n).hom ωN = sN :=
      polynomialDifferentialFormComparison_inv_f_basis k σ N n (f m) a
    have hSigned : head sM = sN := by
      simp only [sM, sN, map_sum, map_zsmul, head, TensorProduct.map_tmul,
        LinearMap.restrictScalars_apply, LinearMap.id_apply]
    have hSignedActual :
        ((Symmetric.symmetricOriginalCoefficientChainMap k A M f).f n).hom sM = sN :=
      (LinearMap.congr_fun hHead sM).trans hSigned
    have hLeft : ((polynomialDifferentialFormComparison k σ N).inv.f n).hom
        (((Symmetric.coefficientDifferentialFormComplexMap k A f).f n).hom
          (e (m ⊗ₜ[k] exteriorPower.ιMulti k n
            (fun j => Finsupp.single (a j) (1 : k))))) = sN :=
      (congrArg (fun ω : (Symmetric.coefficientDifferentialFormComplex k A M).X n =>
        ((polynomialDifferentialFormComparison k σ N).inv.f n).hom
          (((Symmetric.coefficientDifferentialFormComplexMap k A f).f n).hom ω)) hFree).trans
            ((congrArg ((polynomialDifferentialFormComparison k σ N).inv.f n).hom hForm).trans
              hInvN)
    have hRight : ((Symmetric.symmetricOriginalCoefficientChainMap k A M f).f n).hom
        (((polynomialDifferentialFormComparison k σ M).inv.f n).hom
          (e (m ⊗ₜ[k] exteriorPower.ιMulti k n
            (fun j => Finsupp.single (a j) (1 : k))))) = sN :=
      (congrArg (fun ω : (Symmetric.coefficientDifferentialFormComplex k A M).X n =>
        ((Symmetric.symmetricOriginalCoefficientChainMap k A M f).f n).hom
          (((polynomialDifferentialFormComparison k σ M).inv.f n).hom ω)) hFree).trans
            ((congrArg ((Symmetric.symmetricOriginalCoefficientChainMap k A M f).f n).hom
              hInvM).trans hSignedActual)
    exact hLeft.trans hRight.symm
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  obtain ⟨x, rfl⟩ := e.surjective ω
  exact DFunLike.congr_fun hLR x

/-- The forward chain comparison is coefficient-natural up to the chain homotopies supplied by the integral signed equivalences. -/
def polynomialDifferentialFormComparison_coefficientHomotopy (f : M →ₗ[A] N) :
    Homotopy
      (Symmetric.symmetricOriginalCoefficientChainMap k A M f ≫
        (polynomialDifferentialFormComparison k σ N).hom)
      ((polynomialDifferentialFormComparison k σ M).hom ≫
        Symmetric.coefficientDifferentialFormComplexMap k A f) := by
  let eM := polynomialDifferentialFormComparison k σ M
  let eN := polynomialDifferentialFormComparison k σ N
  let h := Symmetric.symmetricOriginalCoefficientChainMap k A M f
  let F := Symmetric.coefficientDifferentialFormComplexMap k A f
  have hinv : F ≫ eN.inv = eM.inv ≫ h :=
    polynomialDifferentialFormComparison_inv_coefficient k σ f
  have hfirst := (eM.homotopyHomInvId.compRight (h ≫ eN.hom)).symm
  have hmiddle : (eM.hom ≫ eM.inv) ≫ (h ≫ eN.hom) =
      (eM.hom ≫ F) ≫ (eN.inv ≫ eN.hom) := by
    calc
      _ = eM.hom ≫ ((eM.inv ≫ h) ≫ eN.hom) := by simp only [Category.assoc]
      _ = eM.hom ≫ ((F ≫ eN.inv) ≫ eN.hom) := by rw [← hinv]
      _ = _ := by simp only [Category.assoc]
  have hlast := eN.homotopyInvHomId.compLeft (eM.hom ≫ F)
  exact (((Homotopy.ofEq (Category.id_comp (h ≫ eN.hom))).symm.trans hfirst).trans
    (Homotopy.ofEq hmiddle)).trans (hlast.trans (Homotopy.ofEq (Category.comp_id _)))

/-- The all-degree HKR homology comparison preserves the coefficient-head map on differential forms. -/
@[reassoc]
theorem polynomialDifferentialFormHomologyIso_coefficient (f : M →ₗ[A] N) (n : ℕ) :
    HomologicalComplex.homologyMap
        (Symmetric.symmetricOriginalCoefficientChainMap k A M f) n ≫
      (polynomialDifferentialFormHomologyIso k σ N n).hom =
        (polynomialDifferentialFormHomologyIso k σ M n).hom ≫
          (Symmetric.coefficientDifferentialFormComplexMap k A f).f n := by
  have h := (polynomialDifferentialFormComparison_coefficientHomotopy k σ f).homologyMap_eq n
  have hF := HomologicalComplex.zeroDifferentialHomologyIso_naturality
    (Symmetric.coefficientDifferentialFormComplexMap k A f) n
    (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A M)
    (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A N)
  unfold polynomialDifferentialFormHomologyIso
  change _ ≫ (HomologicalComplex.homologyMap
    (polynomialDifferentialFormComparison k σ N).hom n ≫ _) =
      (HomologicalComplex.homologyMap (polynomialDifferentialFormComparison k σ M).hom n ≫ _) ≫ _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, h,
    HomologicalComplex.homologyMap_comp, Category.assoc, hF, ← Category.assoc]

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
