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
# Polynomial Hochschild complexes and coefficient exterior forms

Let k be a commutative ring, A = k[σ] and M an A-module with compatible k-action, regarded as a
symmetric bimodule. Its coefficient diagonal Koszul complex has zero differential and terms
canonically equivalent to M ⊗_A ∧ⁿ_AΩ¹_{A/k}. These coordinate maps give an isomorphism with the
zero-differential coefficient-form complex, using the canonical form-object universe lifts.

Combining this isomorphism with the diagonal-to-bar homotopy equivalence gives a polynomial
Hochschild-to-form homotopy equivalence. The inverse chain map on a differential-variable word
is the signed permutation sum of its Hochschild tensor words. The resulting homology isomorphism
and all forward, inverse and cycle-class factorization formulas hold for every n : ℕ, without a
coefficient-flatness hypothesis or division by n!.

This is the polynomial diagonal-resolution description underlying the
Hochschild–Kostant–Rosenberg differential-form comparison; see Hochschild, Kostant and
Rosenberg, “Differential forms on regular affine algebras,” Transactions of the American
Mathematical Society 102 (1962), 383–408.
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

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe. In
each degree n : ℕ, the free exterior coordinates followed by eᵢ ↦ dXᵢ give a k-linear
equivalence Dₙ ≅ M ⊗_A ∧ⁿ_AΩ¹_{A/k}, before the form term is lifted. -/
def symmetricCoefficientFormDegreeEquiv (n : ℕ) :
    (Diagonal).X n ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  (symmetricFreeExteriorEquiv k σ M n).trans
    ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).restrictScalars k)

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
Both D and the coefficient-form complex have zero differentials. The degreewise polynomial
cotangent coordinate equivalences, followed by the canonical form-object lifts, give an
isomorphism D ≅ Forms of ℕ-indexed k-module chain complexes. -/
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

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
For n : ℕ and x ∈ Dₙ, the nth component of symmetricCoefficientFormChainIso sends x to the
canonical lift of symmetricCoefficientFormDegreeEquiv k σ M n x. -/
theorem symmetricCoefficientFormChainIso_hom_f (n : ℕ) (x : (Diagonal).X n) :
    ((symmetricCoefficientFormChainIso k σ M).hom.f n).hom x =
      ULift.up (symmetricCoefficientFormDegreeEquiv k σ M n x) := rfl

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
For an n-form ω ∈ M ⊗_A ∧ⁿ_AΩ¹_{A/k}, the inverse component of symmetricCoefficientFormChainIso
sends the canonical lift of ω to (symmetricCoefficientFormDegreeEquiv k σ M n)⁻¹(ω). -/
theorem symmetricCoefficientFormChainIso_inv_f (n : ℕ) (ω : M ⊗[A] (⋀[A]^n Ω)) :
    ((symmetricCoefficientFormChainIso k σ M).inv.f n).hom (ULift.up ω) =
      (symmetricCoefficientFormDegreeEquiv k σ M n).symm ω := rfl

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
The signed polynomial coefficient antisymmetrization gives a homotopy equivalence from D to the
Hochschild chain complex Cₙ(A,M) = M ⊗[k] A^{⊗n}. Its forward map is
polynomialAntisymmetricCoefficientMap. -/
def symmetricAntisymmetricCoefficientComparison : HomotopyEquiv Diagonal HH := by
  let := Symmetric.opModule A M
  let := Symmetric.actionsComm A M
  let := Symmetric.kOpComm k A M
  let := Symmetric.kOpTower k A M
  exact polynomialAntisymmetricCoefficientComparison k σ M

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
The Hochschild chain complex is homotopy equivalent to the zero-differential coefficient-form
complex. The forward map is the bar-to-diagonal projective-resolution comparison followed by
cotangent coordinates; the inverse is diagonal form coordinates followed by signed
antisymmetrization. -/
def polynomialDifferentialFormComparison : HomotopyEquiv HH Forms :=
  (symmetricAntisymmetricCoefficientComparison k σ M).symm.trans
    (HomotopyEquiv.ofIso (symmetricCoefficientFormChainIso k σ M))

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
The forward map of polynomialDifferentialFormComparison equals (symmetricCoefficientComparison k
σ M).hom followed by (symmetricCoefficientFormChainIso k σ M).hom. -/
theorem polynomialDifferentialFormComparison_hom :
    (polynomialDifferentialFormComparison k σ M).hom =
      (symmetricCoefficientComparison k σ M).hom ≫
        (symmetricCoefficientFormChainIso k σ M).hom := by
  let := Symmetric.opModule A M
  let := Symmetric.actionsComm A M
  let := Symmetric.kOpComm k A M
  let := Symmetric.kOpTower k A M
  rfl

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
The inverse map of polynomialDifferentialFormComparison equals (symmetricCoefficientFormChainIso
k σ M).inv followed by polynomialAntisymmetricCoefficientMap k σ M. -/
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

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
For n : ℕ and ω ∈ M ⊗_A ∧ⁿ_AΩ¹_{A/k}, the inverse comparison sends its canonical lift to
polynomialSignedRepresentative evaluated at the inverse free cotangent coordinates of ω. -/
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

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
For m ∈ M and f : Fin n → σ, the inverse comparison sends the lift of m
⊗_A(dX_{f(0)}∧…∧dX_{f(n−1)}) to ∑π sign(π)·(m ⊗ X_{f(π(0))} ⊗ … ⊗ X_{f(π(n−1))}), where π ranges
over permutations of Fin n. -/
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

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
The polynomial chain comparison and the zero form differential give an isomorphism HHₙ(A,M) ≅
Formsₙ for every n : ℕ. -/
def polynomialDifferentialFormHomologyIso (n : ℕ) :
    (HH).homology n ≅ (Forms).X n :=
  (polynomialDifferentialFormComparison k σ M).toHomologyIso n ≪≫
    HomologicalComplex.zeroDifferentialHomologyIso Forms n
      (Symmetric.coefficientDifferentialFormComplex_d_eq_zero k A M)

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe. In
degree n : ℕ, the forward map of polynomialDifferentialFormHomologyIso equals the
homology-to-diagonal degree map symmetricCoefficientHomologyIsoDegree.hom followed by the nth
component of symmetricCoefficientFormChainIso.hom. -/
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

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
For z ∈ HHₙ(A,M), project the forward categorical form coordinate of z from its canonical
universe lift. The result is symmetricHochschildDifferentialFormEquiv k σ M n z. -/
theorem polynomialDifferentialFormHomologyIso_hom_down
    (n : ℕ) (z : (HH).homology n) :
    ((polynomialDifferentialFormHomologyIso k σ M n).hom.hom z).down =
      symmetricHochschildDifferentialFormEquiv k σ M n z := by
  rw [polynomialDifferentialFormHomologyIso_hom]
  rfl

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe.
For ω ∈ M ⊗_A ∧ⁿ_AΩ¹_{A/k}, the inverse of polynomialDifferentialFormHomologyIso sends its
canonical lift to polynomialAntisymmetrizationHomology k σ M n ω. -/
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

/-- Let k be a commutative ring, σ an arbitrary variable set and A = k[σ]. Let M be an A-module with
compatible k-action, regarded as a symmetric A-bimodule. Put E = A ⊗[k] Aᵐᵒᵖ, D = M ⊗_E Kdiag
and Formsₙ = M ⊗_A ∧ⁿ_AΩ¹_{A/k}, with the canonical lift to the coefficient-complex universe. In
degree n : ℕ, the inverse form homology map is the composite Formsₙ → Dₙ → Hₙ(D) → HHₙ(A,M).
These arrows are respectively the inverse diagonal form component, the zero-differential
cycle-class map, and homology of signed polynomial antisymmetrization. -/
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
