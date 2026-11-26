/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialAntisymmetrization
public import MathlibExt.Algebra.Homology.Hochschild.Normalized
public import MathlibExt.Algebra.Homology.HomologicalComplex.ConcreteCycleClass

/-!
# Polynomial exterior classes under Hochschild normalization

Let k be a commutative ring, A = k[σ] and M a compatible A-module with its symmetric right
action. A free exterior element x ∈ M ⊗_k ∧ⁿₖ(⊕ᵢk·eᵢ) gives a signed Hochschild tensor
representative through the diagonal-to-bar chain map. The diagonal coefficient differential is
zero, so this representative is a cycle.

Normalization applies A → A/(k·1) to each tail factor. It sends signed representatives to
normalized cycles and induces homology isomorphisms in every natural-number degree. The
normalized exterior class is the homology class of that normalized signed tensor, and the
normalized polynomial form coordinates recover the coefficient exterior differential form of x.
These formulas hold for arbitrary variable sets and symmetric coefficient modules over any
commutative k.

For normalized Hochschild chains and their homology, see J.-L. Loday, Cyclic Homology, second
edition, §1.1.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)
  (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

local notation "A" => MvPolynomial σ k
local notation "V" => σ →₀ k
local notation "Ω" => KaehlerDifferential k A

local instance : Module Aᵐᵒᵖ M := Symmetric.opModule A M
local instance : SMulCommClass A Aᵐᵒᵖ M := Symmetric.actionsComm A M
local instance : SMulCommClass k Aᵐᵒᵖ M := Symmetric.kOpComm k A M
local instance : IsScalarTower k Aᵐᵒᵖ M := Symmetric.kOpTower k A M

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. For n : ℕ and x ∈ M ⊗[k]
∧ⁿₖV, take the inverse free coordinates of x in the diagonal coefficient term and apply the
degree-n antisymmetric coefficient map. This defines polynomialSignedRepresentative in M ⊗[k]
A^{⊗n}; on a variable wedge it is the full signed permutation sum. -/
def polynomialSignedRepresentative (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    M ⊗[k] TensorPower k n A :=
  ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom
    ((coefficientFreeExteriorEquiv k σ M n).symm x)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. For every n : ℕ and x ∈ M
⊗[k] ∧ⁿₖV, the Hochschild differential vanishes on polynomialSignedRepresentative k σ M n x. The
diagonal coefficient differential is zero and the antisymmetrization map is a chain map. -/
theorem polynomialSignedRepresentative_cycle (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    ((Symmetric.chainComplex k A M).sc n).g (polynomialSignedRepresentative k σ M n x) = 0 := by
  let C := coefficientComplex k σ M
  let H := Symmetric.chainComplex k A M
  let ε : C ⟶ H := polynomialAntisymmetricCoefficientMap k σ M
  let y : C.X n := (coefficientFreeExteriorEquiv k σ M n).symm x
  let j := (ComplexShape.down ℕ).next n
  have hD : C.d n j = 0 := symmetricCoefficientComplex_d_eq_zero k σ M n j
  have hz : (C.d n j).hom y = 0 :=
    (congrArg (fun f : C.X n ⟶ C.X j => f.hom y) hD).trans (LinearMap.zero_apply y)
  have h := congrArg (fun f : C.X n ⟶ H.X j => f.hom y) (ε.comm n j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change (H.d n j).hom ((ε.f n).hom y) = 0
  exact h.trans ((congrArg (ε.f j).hom hz).trans (ε.f j).hom.map_zero)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. For n : ℕ and x ∈ M ⊗[k]
∧ⁿₖV, polynomialAntisymmetricExteriorClass k σ M n x equals the Hochschild homology class of
polynomialSignedRepresentative k σ M n x, using its cycle equation. -/
theorem polynomialAntisymmetricExteriorClass_eq_cycle
    (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    polynomialAntisymmetricExteriorClass k σ M n x =
      HomologicalComplex.moduleCatCycleClass (Symmetric.chainComplex k A M) n
        (polynomialSignedRepresentative k σ M n x) (polynomialSignedRepresentative_cycle k σ M n x) := by
  let C := symmetricCoefficientComplex k σ M
  let H := Symmetric.chainComplex k A M
  let ε : C ⟶ H := polynomialAntisymmetricCoefficientMap k σ M
  let y : C.X n := (symmetricFreeExteriorEquiv k σ M n).symm x
  have hz : (C.sc n).g.hom y = 0 := by
    change (C.d n ((ComplexShape.down ℕ).next n)).hom y = 0
    have hd : C.d n ((ComplexShape.down ℕ).next n) = 0 :=
      symmetricCoefficientComplex_d_eq_zero k σ M n ((ComplexShape.down ℕ).next n)
    exact (congrArg (fun f : C.X n ⟶ C.X ((ComplexShape.down ℕ).next n) => f.hom y) hd).trans
      (LinearMap.zero_apply y)
  have hClass := HomologicalComplex.zeroDifferentialClassMap_eq_moduleCatCycleClass
    C n (symmetricCoefficientComplex_d_eq_zero k σ M) y
  have hMap := HomologicalComplex.moduleCatCycleClass_naturality ε n y hz
  change (HomologicalComplex.homologyMap ε n).hom
      ((HomologicalComplex.zeroDifferentialClassMap C n
        (symmetricCoefficientComplex_d_eq_zero k σ M)).hom y) =
    HomologicalComplex.moduleCatCycleClass H n ((ε.f n).hom y) _
  exact (congrArg (HomologicalComplex.homologyMap ε n).hom hClass).trans hMap

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. The normalized
representative of x ∈ M ⊗[k] ∧ⁿₖV is the image of polynomialSignedRepresentative under the
degree-n Hochschild normalization projection. The projection applies q : A → A/(k·1) to every
tail factor and leaves the coefficient unchanged. -/
def normalizedPolynomialSignedRepresentative (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    (Symmetric.normalizedChainComplex k A M).X n :=
  ((Symmetric.normalizationProjection k A M).f n).hom (polynomialSignedRepresentative k σ M n x)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. For each n : ℕ and x ∈ M
⊗[k] ∧ⁿₖV, the normalized Hochschild differential vanishes on
normalizedPolynomialSignedRepresentative k σ M n x. -/
theorem normalizedPolynomialSignedRepresentative_cycle (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    ((Symmetric.normalizedChainComplex k A M).sc n).g
      (normalizedPolynomialSignedRepresentative k σ M n x) = 0 := by
  let K := Symmetric.chainComplex k A M
  let L := Symmetric.normalizedChainComplex k A M
  let ε : K ⟶ L := Symmetric.normalizationProjection k A M
  let y : K.X n := polynomialSignedRepresentative k σ M n x
  let j := (ComplexShape.down ℕ).next n
  have hz : (K.d n j).hom y = 0 := polynomialSignedRepresentative_cycle k σ M n x
  have h := congrArg (fun f : K.X n ⟶ L.X j => f.hom y) (ε.comm n j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  change (L.d n j).hom ((ε.f n).hom y) = 0
  exact h.trans ((congrArg (ε.f j).hom hz).trans (ε.f j).hom.map_zero)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. Compose the signed
exterior class map M ⊗[k] ∧ⁿₖV → HHₙ(A,M) with the homology map of normalization. This defines
normalizedPolynomialExteriorClass in the nth normalized Hochschild homology. -/
def normalizedPolynomialExteriorClass (n : ℕ) :
    M ⊗[k] (⋀[k]^n V) →ₗ[k] (Symmetric.normalizedChainComplex k A M).homology n :=
  (HomologicalComplex.homologyMap (Symmetric.normalizationProjection k A M) n).hom.comp
    (polynomialAntisymmetricExteriorClass k σ M n)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. For n : ℕ and x ∈ M ⊗[k]
∧ⁿₖV, normalizedPolynomialExteriorClass k σ M n x equals the normalized Hochschild class of
normalizedPolynomialSignedRepresentative k σ M n x. -/
theorem normalizedPolynomialExteriorClass_eq_cycle
    (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    normalizedPolynomialExteriorClass k σ M n x =
      HomologicalComplex.moduleCatCycleClass (Symmetric.normalizedChainComplex k A M) n
        (normalizedPolynomialSignedRepresentative k σ M n x)
          (normalizedPolynomialSignedRepresentative_cycle k σ M n x) := by
  let ε := Symmetric.normalizationProjection k A M
  have hClass := polynomialAntisymmetricExteriorClass_eq_cycle k σ M n x
  have hMap := HomologicalComplex.moduleCatCycleClass_naturality ε n
    (polynomialSignedRepresentative k σ M n x) (polynomialSignedRepresentative_cycle k σ M n x)
  change (HomologicalComplex.homologyMap ε n).hom
      (polynomialAntisymmetricExteriorClass k σ M n x) = _
  exact (congrArg (HomologicalComplex.homologyMap ε n).hom hClass).trans hMap

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. The normalization
projection gives an isomorphism between raw and normalized Hochschild homology in every degree n
: ℕ, because the projection is a quasi-isomorphism. -/
def polynomialNormalizationHomologyIso (n : ℕ) :
    (Symmetric.chainComplex k A M).homology n ≅
      (Symmetric.normalizedChainComplex k A M).homology n := by
  letI : QuasiIso (Symmetric.normalizationProjection k A M) := by
    change QuasiIso (ModuleCat.Algebra.Hochschild.normalizationProjection k A M)
    infer_instance
  exact _root_.isoOfQuasiIsoAt (Symmetric.normalizationProjection k A M) n

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. In degree n : ℕ, the
forward map of polynomialNormalizationHomologyIso equals the homology map induced by
Symmetric.normalizationProjection k A M. -/
theorem polynomialNormalizationHomologyIso_hom (n : ℕ) :
    (polynomialNormalizationHomologyIso k σ M n).hom =
      HomologicalComplex.homologyMap (Symmetric.normalizationProjection k A M) n := rfl

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. In degree n : ℕ, first
apply the inverse normalization homology comparison, then the polynomial diagonal
differential-form comparison. This gives a k-linear equivalence Hₙ(C̄(A,M)) ≅ M ⊗_A
∧ⁿ_AΩ¹_{A/k}. -/
def normalizedPolynomialDifferentialFormEquiv (n : ℕ) :
    (Symmetric.normalizedChainComplex k A M).homology n ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  (polynomialNormalizationHomologyIso k σ M n).toLinearEquiv.symm.trans
    (symmetricHochschildDifferentialFormEquiv k σ M n)

/-- Let k be a commutative ring, σ any variable set and A = k[σ]. Let M be an A-module with
compatible k-action and symmetric right action, and put V = ⊕ᵢ∈σ k·eᵢ. For x ∈ M ⊗[k] ∧ⁿₖV,
normalizedPolynomialDifferentialFormEquiv sends normalizedPolynomialExteriorClass k σ M n x to
the polynomial cotangent exterior coordinate of x. In particular eᵢ is replaced by dXᵢ and the
coefficient is retained. -/
theorem normalizedPolynomialExteriorClass_coordinates
    (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    normalizedPolynomialDifferentialFormEquiv k σ M n
      (normalizedPolynomialExteriorClass k σ M n x) =
        KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n x := by
  change symmetricHochschildDifferentialFormEquiv k σ M n
    ((polynomialNormalizationHomologyIso k σ M n).inv
      ((polynomialNormalizationHomologyIso k σ M n).hom
        (polynomialAntisymmetricExteriorClass k σ M n x))) = _
  rw [ModuleCat.inv_hom_apply]
  change KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n
    (symmetricHochschildFreeExteriorEquiv k σ M n
      (polynomialAntisymmetricExteriorClass k σ M n x)) = _
  rw [polynomialAntisymmetricExteriorClass_coordinates]

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
