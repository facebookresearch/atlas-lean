/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialNormalizedExterior
public import MathlibExt.Algebra.Homology.Hochschild.DifferentialFormNaturality
public import MathlibExt.Algebra.Homology.HomologicalComplex.ZeroDifferentialClassNaturality

/-!
# Polynomial Hochschild complexes and coefficient forms

For a polynomial algebra over a commutative ground ring and an
arbitrary symmetric coefficient module, the diagonal Koszul and
enveloping bar resolutions give a chain homotopy equivalence with
the zero-differential coefficient form complex. Its inverse is
signed Koszul-to-bar antisymmetrization. Coefficient flatness and
factorial inverses are not required.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)
  (M : Type w) [AddCommGroup M] [Module k M]
  [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]

local notation "A" => MvPolynomial σ k
local notation "V" => σ →₀ k
local notation "Ω" => KaehlerDifferential k A
local notation "Forms" => Symmetric.coefficientDifferentialFormComplex k A M
local notation "Diagonal" => symmetricCoefficientComplex k σ M
local notation "HH" => Symmetric.chainComplex k A M

/-- The coefficient diagonal degree in polynomial differential-form
coordinates, before its canonical carrier lift. -/
def symmetricCoefficientFormDegreeEquiv (n : ℕ) :
    (Diagonal).X n ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  (symmetricFreeExteriorEquiv k σ M n).trans
    ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).restrictScalars k)

/-- Canonical polynomial coordinates identify the entire diagonal coefficient
complex with the zero-differential coefficient form complex. -/
def symmetricCoefficientFormChainIso : Diagonal ≅ Forms :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((symmetricCoefficientFormDegreeEquiv k σ M n).trans
      (ULift.moduleEquiv : ULift.{u} (M ⊗[A] (⋀[A]^n Ω)) ≃ₗ[k]
        M ⊗[A] (⋀[A]^n Ω)).symm).toModuleIso)
    (by
      intro i j _h
      rw [symmetricCoefficientComplex_d_eq_zero,
        Symmetric.coefficientDifferentialFormComplex_d_eq_zero]
      simp only [CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp])

/-- The component is the form coordinate map and the canonical lift. -/
theorem symmetricCoefficientFormChainIso_hom_f (n : ℕ) (x : (Diagonal).X n) :
    ((symmetricCoefficientFormChainIso k σ M).hom.f n).hom x =
      ULift.up (symmetricCoefficientFormDegreeEquiv k σ M n x) := rfl

/-- The inverse component removes only the canonical lift and recovers the
original diagonal coordinates. -/
theorem symmetricCoefficientFormChainIso_inv_f (n : ℕ) (ω : M ⊗[A] (⋀[A]^n Ω)) :
    ((symmetricCoefficientFormChainIso k σ M).inv.f n).hom (ULift.up ω) =
      (symmetricCoefficientFormDegreeEquiv k σ M n).symm ω := rfl

/-- The symmetric diagonal-to-Hochschild homotopy equivalence whose forward
map is the concrete signed polynomial Koszul-to-Bar map. -/
def symmetricAntisymmetricCoefficientComparison : HomotopyEquiv Diagonal HH := by
  let := Symmetric.opModule A M
  let := Symmetric.actionsComm A M
  let := Symmetric.kOpComm k A M
  let := Symmetric.kOpTower k A M
  exact polynomialAntisymmetricCoefficientComparison k σ M

/-- The polynomial Hochschild-to-forms chain homotopy equivalence.
The inverse is signed antisymmetrization; the forward comparison is the
augmentation-preserving projective Bar lift followed by cotangent coordinates. -/
def polynomialDifferentialFormComparison : HomotopyEquiv HH Forms :=
  (symmetricAntisymmetricCoefficientComparison k σ M).symm.trans
    (HomotopyEquiv.ofIso (symmetricCoefficientFormChainIso k σ M))

/-- The forward map retains the projective-resolution comparison. -/
theorem polynomialDifferentialFormComparison_hom :
    (polynomialDifferentialFormComparison k σ M).hom =
      (symmetricCoefficientComparison k σ M).hom ≫
        (symmetricCoefficientFormChainIso k σ M).hom := by
  let := Symmetric.opModule A M
  let := Symmetric.actionsComm A M
  let := Symmetric.kOpComm k A M
  let := Symmetric.kOpTower k A M
  rfl

/-- The inverse takes the original form coordinates into the signed
Koszul-to-Bar map, rather than choosing an abstract homology inverse. -/
theorem polynomialDifferentialFormComparison_inv :
    letI := Symmetric.opModule A M
    letI := Symmetric.actionsComm A M
    letI := Symmetric.kOpComm k A M
    letI := Symmetric.kOpTower k A M
    (polynomialDifferentialFormComparison k σ M).inv =
      (symmetricCoefficientFormChainIso k σ M).inv ≫
        polynomialAntisymmetricCoefficientMap k σ M := by
  let := Symmetric.opModule A M
  let := Symmetric.actionsComm A M
  let := Symmetric.kOpComm k A M
  let := Symmetric.kOpTower k A M
  rfl

/-- Inverse form comparison in the original free generator coordinates. -/
theorem polynomialDifferentialFormComparison_inv_f_up
    (n : ℕ) (ω : M ⊗[A] (⋀[A]^n Ω)) :
    ((polynomialDifferentialFormComparison k σ M).inv.f n).hom (ULift.up ω) =
      polynomialSignedRepresentative k σ M n
        ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).symm ω) := by
  let := Symmetric.opModule A M
  let := Symmetric.actionsComm A M
  let := Symmetric.kOpComm k A M
  let := Symmetric.kOpTower k A M
  let z : (Forms).X n := ULift.up ω
  have hi : ((polynomialDifferentialFormComparison k σ M).inv.f n) =
      (symmetricCoefficientFormChainIso k σ M).inv.f n ≫
        (polynomialAntisymmetricCoefficientMap k σ M).f n :=
    (congrArg (fun f : Forms ⟶ HH => f.f n)
      (polynomialDifferentialFormComparison_inv k σ M)).trans
        (HomologicalComplex.comp_f (symmetricCoefficientFormChainIso k σ M).inv
          (polynomialAntisymmetricCoefficientMap k σ M) n)
  have hp := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hi) z
  have hc := ModuleCat.comp_apply ((symmetricCoefficientFormChainIso k σ M).inv.f n)
    ((polynomialAntisymmetricCoefficientMap k σ M).f n) z
  have hCoordinates : (symmetricCoefficientFormDegreeEquiv k σ M n).symm ω =
      (symmetricFreeExteriorEquiv k σ M n).symm
        ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).symm ω) := rfl
  exact hp.trans (hc.trans
    ((congrArg ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom
      (symmetricCoefficientFormChainIso_inv_f k σ M n ω)).trans
        (congrArg ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom hCoordinates)))

/-- A coefficient differential-variable word is sent to the complete signed
Hochschild tensor, with its coefficient first and without normalization. -/
theorem polynomialDifferentialFormComparison_inv_f_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    ((polynomialDifferentialFormComparison k σ M).inv.f n).hom
      (ULift.up (m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (MvPolynomial.X (f j))))) =
      ∑ π : Equiv.Perm (Fin n), (π.sign : ℤ) •
        (m ⊗ₜ[k] PiTensorProduct.tprod k (fun j => MvPolynomial.X (f (π j)))) := by
  rw [polynomialDifferentialFormComparison_inv_f_up,
    KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_symm_tmul_basis]
  let := Symmetric.opModule A M
  let := Symmetric.actionsComm A M
  let := Symmetric.kOpComm k A M
  let := Symmetric.kOpTower k A M
  exact polynomialAntisymmetricCoefficientMap_free_basis k σ M n m f

/-- The chain comparison computes every polynomial Hochschild degree
as the original coefficient differential-form object. -/
def polynomialDifferentialFormHomologyIso (n : ℕ) :
    (HH).homology n ≅ (Forms).X n :=
  (polynomialDifferentialFormComparison k σ M).toHomologyIso n ≪≫
    HomologicalComplex.zeroDifferentialHomologyIso Forms n
      (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A M)

/-- Homology of the chain comparison is the integral
polynomial HKR coordinate map, with only its canonical carrier lift. -/
theorem polynomialDifferentialFormHomologyIso_hom (n : ℕ) :
    (polynomialDifferentialFormHomologyIso k σ M n).hom =
      (symmetricCoefficientHomologyIsoDegree k σ M n).hom ≫
        (symmetricCoefficientFormChainIso k σ M).hom.f n := by
  unfold polynomialDifferentialFormHomologyIso
  change HomologicalComplex.homologyMap
    (polynomialDifferentialFormComparison k σ M).hom n ≫ _ = _
  have hcoordinates := HomologicalComplex.zeroDifferentialHomologyIso_naturality
    (symmetricCoefficientFormChainIso k σ M).hom n
    (symmetricCoefficientComplex_d_eq_zero k σ M)
    (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A M)
  rw [polynomialDifferentialFormComparison_hom,
    HomologicalComplex.homologyMap_comp, Category.assoc, hcoordinates]
  rfl

/-- Removing the canonical lift gives the original integral all-degree HKR
equivalence from the two resolutions. -/
theorem polynomialDifferentialFormHomologyIso_hom_down
    (n : ℕ) (z : (HH).homology n) :
    ((polynomialDifferentialFormHomologyIso k σ M n).hom.hom z).down =
      symmetricHochschildDifferentialFormEquiv k σ M n z := by
  rw [polynomialDifferentialFormHomologyIso_hom]
  rfl

/-- Every polynomial form is represented by the inverse of the homology comparison, hence by the constructed signed map. -/
theorem polynomialDifferentialFormHomologyIso_inv_up
    (n : ℕ) (ω : M ⊗[A] (⋀[A]^n Ω)) :
    (polynomialDifferentialFormHomologyIso k σ M n).inv.hom (ULift.up ω) =
      polynomialAntisymmetrizationHomology k σ M n ω := by
  let e := polynomialDifferentialFormHomologyIso k σ M n
  let z : (Forms).X n := ULift.up ω
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  have hInv : e.hom.hom (e.inv.hom z) = z := ModuleCat.hom_inv_apply e z
  have hTarget : e.hom.hom (polynomialAntisymmetrizationHomology k σ M n ω) = z := by
    apply ULift.ext
    exact (polynomialDifferentialFormHomologyIso_hom_down k σ M n _).trans
      (polynomialAntisymmetrizationHomology_coordinates k σ M n ω)
  exact hInv.trans hTarget.symm

/-- The inverse homology comparison is the diagonal form coordinate,
the native zero-differential class, and homology of signed antisymmetrization. -/
theorem polynomialDifferentialFormHomologyIso_inv_factor (n : ℕ) :
    letI := Symmetric.opModule A M
    letI := Symmetric.actionsComm A M
    letI := Symmetric.kOpComm k A M
    letI := Symmetric.kOpTower k A M
    (polynomialDifferentialFormHomologyIso k σ M n).inv =
      (symmetricCoefficientFormChainIso k σ M).inv.f n ≫
        HomologicalComplex.zeroDifferentialClassMap Diagonal n
          (symmetricCoefficientComplex_d_eq_zero k σ M) ≫
        HomologicalComplex.homologyMap (polynomialAntisymmetricCoefficientMap k σ M) n := by
  let := Symmetric.opModule A M
  let := Symmetric.actionsComm A M
  let := Symmetric.kOpComm k A M
  let := Symmetric.kOpTower k A M
  let qF := HomologicalComplex.zeroDifferentialHomologyIso Forms n
    (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A M)
  let qD := HomologicalComplex.zeroDifferentialHomologyIso Diagonal n
    (symmetricCoefficientComplex_d_eq_zero k σ M)
  let e := symmetricCoefficientFormChainIso k σ M
  have he := HomologicalComplex.zeroDifferentialHomologyIso_naturality e.inv n
    (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A M)
    (symmetricCoefficientComplex_d_eq_zero k σ M)
  have hi : qF.inv ≫ HomologicalComplex.homologyMap e.inv n = e.inv.f n ≫ qD.inv := by
    apply (cancel_mono qD.hom).1
    calc
      _ = qF.inv ≫ (HomologicalComplex.homologyMap e.inv n ≫ qD.hom) := Category.assoc _ _ _
      _ = qF.inv ≫ (qF.hom ≫ e.inv.f n) := by rw [he]
      _ = e.inv.f n := by simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = _ := by simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let a : Diagonal ⟶ HH := polynomialAntisymmetricCoefficientMap k σ M
  have hInv : (polynomialDifferentialFormComparison k σ M).inv = e.inv ≫ a :=
    polynomialDifferentialFormComparison_inv k σ M
  have hComp : HomologicalComplex.homologyMap (polynomialDifferentialFormComparison k σ M).inv n =
      HomologicalComplex.homologyMap e.inv n ≫ HomologicalComplex.homologyMap a n :=
    (congrArg (fun f : Forms ⟶ HH => HomologicalComplex.homologyMap f n) hInv).trans
      (HomologicalComplex.homologyMap_comp e.inv a n)
  have hClass : qD.inv = HomologicalComplex.zeroDifferentialClassMap Diagonal n
      (symmetricCoefficientComplex_d_eq_zero k σ M) :=
    (HomologicalComplex.zeroDifferentialClassMap_eq_inv Diagonal n
      (symmetricCoefficientComplex_d_eq_zero k σ M)).symm
  change qF.inv ≫ HomologicalComplex.homologyMap
    (polynomialDifferentialFormComparison k σ M).inv n = _
  exact (congrArg (fun f => qF.inv ≫ f) hComp).trans
    ((Category.assoc qF.inv (HomologicalComplex.homologyMap e.inv n)
      (HomologicalComplex.homologyMap a n)).symm.trans
        ((congrArg (fun f => f ≫ HomologicalComplex.homologyMap a n) hi).trans
          ((Category.assoc (e.inv.f n) qD.inv (HomologicalComplex.homologyMap a n)).trans
            (congrArg (fun f => e.inv.f n ≫ f ≫ HomologicalComplex.homologyMap a n) hClass))))

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
