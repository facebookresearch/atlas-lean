/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Source proposal; Native elaboration is unexecuted. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialAntisymmetrization
public import MathlibExt.Algebra.Homology.Hochschild.Normalized
public import MathlibExt.Algebra.Homology.HomologicalComplex.ConcreteCycleClass

/-!
# Polynomial exterior classes under normalization

The signed polynomial resolution comparison and simplicial
normalization identify coefficient exterior classes with normalized
Hochschild homology. The representative formulas retain the signed
antisymmetrization over arbitrary commutative ground rings and
arbitrary symmetric coefficient modules.
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

/-- The original signed comparison representative of an original free exterior coefficient. -/
def polynomialSignedRepresentative (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    M ⊗[k] TensorPower k n A :=
  ((polynomialAntisymmetricCoefficientMap k σ M).f n).hom
    ((coefficientFreeExteriorEquiv k σ M n).symm x)

/-- The representative is an cycle of the original raw Hochschild complex in every degree. -/
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

/-- The signed exterior class is the native class of its literal original representative. -/
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

/-- Native normalization of the original signed polynomial representative. -/
def normalizedPolynomialSignedRepresentative (n : ℕ) (x : M ⊗[k] (⋀[k]^n V)) :
    (Symmetric.normalizedChainComplex k A M).X n :=
  ((Symmetric.normalizationProjection k A M).f n).hom (polynomialSignedRepresentative k σ M n x)

/-- The normalized representative retains the complete original cycle equation. -/
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

/-- The signed exterior class in original normalized Hochschild homology. -/
def normalizedPolynomialExteriorClass (n : ℕ) :
    M ⊗[k] (⋀[k]^n V) →ₗ[k] (Symmetric.normalizedChainComplex k A M).homology n :=
  (HomologicalComplex.homologyMap (Symmetric.normalizationProjection k A M) n).hom.comp
    (polynomialAntisymmetricExteriorClass k σ M n)

/-- The normalized class is the native class of the literal normalized signed tensor. -/
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

/-- The canonical native normalization homology comparison on the original endpoints. -/
def polynomialNormalizationHomologyIso (n : ℕ) :
    (Symmetric.chainComplex k A M).homology n ≅
      (Symmetric.normalizedChainComplex k A M).homology n := by
  letI : QuasiIso (Symmetric.normalizationProjection k A M) := by
    change QuasiIso (ModuleCat.Algebra.Hochschild.normalizationProjection k A M)
    infer_instance
  exact _root_.isoOfQuasiIsoAt (Symmetric.normalizationProjection k A M) n

/-- Its forward map is precisely homology of the original factorwise quotient projection. -/
theorem polynomialNormalizationHomologyIso_hom (n : ℕ) :
    (polynomialNormalizationHomologyIso k σ M n).hom =
      HomologicalComplex.homologyMap (Symmetric.normalizationProjection k A M) n := rfl

/-- Actual normalized polynomial Hochschild homology has the original cotangent exterior coordinates. -/
def normalizedPolynomialDifferentialFormEquiv (n : ℕ) :
    (Symmetric.normalizedChainComplex k A M).homology n ≃ₗ[k] M ⊗[A] (⋀[A]^n Ω) :=
  (polynomialNormalizationHomologyIso k σ M n).toLinearEquiv.symm.trans
    (symmetricHochschildDifferentialFormEquiv k σ M n)

/-- The normalized signed class has its original exterior differential form coordinates. -/
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
