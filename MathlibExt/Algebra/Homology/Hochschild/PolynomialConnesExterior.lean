/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- Source proposal; Native elaboration is unexecuted. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialNormalizedExterior
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricRegularConnesHomology
public import MathlibExt.LinearAlgebra.TensorPower.AntisymmetrizationTwo

/-!
# Polynomial Connes classes in degrees one and two

On the normalized regular coefficient complex, Connes B sends
X s ⊗ q(X t) to the signed two-term tensor. Its polynomial
exterior homology coordinate is d(X s) ∧ d(X t). This degree-one
to degree-two formula holds over every commutative ground ring.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)

local notation "A" => MvPolynomial σ k
local notation "V" => σ →₀ k
local notation "Q" => (ModuleCat.Algebra.Hochschild.quotientCarrier k A)
local notation "q" => Submodule.mkQ (ModuleCat.Algebra.Hochschild.unitSubmodule k A)

local instance : Module Aᵐᵒᵖ A := Symmetric.opModule A A
local instance : SMulCommClass A Aᵐᵒᵖ A := Symmetric.actionsComm A A
local instance : SMulCommClass k Aᵐᵒᵖ A := Symmetric.kOpComm k A A
local instance : IsScalarTower k Aᵐᵒᵖ A := Symmetric.kOpTower k A A

/-- The free exterior input for the original polynomial one-form X s d(X t). -/
def polynomialConnesInputExterior (s t : σ) : A ⊗[k] (⋀[k]^1 V) := by
  classical
  exact MvPolynomial.X s ⊗ₜ[k] exteriorPower.ιMulti k 1
    (fun _ : Fin 1 => Finsupp.single t (1 : k))

/-- The independently specified original polynomial two-form generator. -/
def polynomialConnesOutputExterior (s t : σ) : A ⊗[k] (⋀[k]^2 V) := by
  classical
  exact (1 : A) ⊗ₜ[k] exteriorPower.ιMulti k 2
    (Fin.cons (Finsupp.single s (1 : k)) (fun _ : Fin 1 => Finsupp.single t (1 : k)))

/-- The original normalized polynomial input tensor. -/
def polynomialConnesPairInput (s t : σ) : (Symmetric.normalizedChainComplex k A A).X 1 :=
  MvPolynomial.X s ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => q (MvPolynomial.X t))

/-- The original descended regular Connes value of that original tensor. -/
def polynomialConnesPairOutput (s t : σ) : (Symmetric.normalizedChainComplex k A A).X 2 :=
  Symmetric.regularNormalizedConnes k A 1 (polynomialConnesPairInput k σ s t)

private theorem signed_input (s t : σ) :
    polynomialSignedRepresentative k σ A 1 (polynomialConnesInputExterior k σ s t) =
      MvPolynomial.X s ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => MvPolynomial.X t) := by
  classical
  let : Unique (Equiv.Perm (Fin 1)) :=
    { default := 1, uniq := fun π => Subsingleton.elim _ _ }
  have h := polynomialAntisymmetricCoefficientMap_free_basis k σ A 1
    (MvPolynomial.X s) (fun _ : Fin 1 => t)
  simp only [Fintype.sum_unique] at h
  have hd : (default : Equiv.Perm (Fin 1)) = 1 := Subsingleton.elim _ _
  rw [hd, Equiv.Perm.sign_one, Units.val_one, one_zsmul] at h
  exact h

private theorem signed_output (s t : σ) :
    polynomialSignedRepresentative k σ A 2 (polynomialConnesOutputExterior k σ s t) =
      (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons (MvPolynomial.X s) (fun _ : Fin 1 => MvPolynomial.X t)) -
        (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons (MvPolynomial.X t) (fun _ : Fin 1 => MvPolynomial.X s)) := by
  classical
  have hg (a b : σ) :
      (fun j : Fin 2 => polynomialGeneratorLinear k σ
        (Fin.cons (α := fun _ : Fin 2 => V)
          (Finsupp.single a (1 : k)) (fun _ : Fin 1 => Finsupp.single b (1 : k)) j)) =
      Fin.cons (MvPolynomial.X a) (fun _ : Fin 1 => MvPolynomial.X b) := by
    funext j
    cases j using Fin.cases <;> simp only [Fin.cons_zero, Fin.cons_succ, polynomialGeneratorLinear_single]
  have hValue :
      TensorProduct.map (LinearMap.id : A →ₗ[k] A)
        (AdjacentBar.exteriorAntisymmetrizationAlong k A V (polynomialGeneratorLinear k σ) 2)
        ((1 : A) ⊗ₜ[k] exteriorPower.ιMulti k 2
          (Fin.cons (Finsupp.single s (1 : k)) (fun _ : Fin 1 => Finsupp.single t (1 : k)))) =
      (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k
        (Fin.cons (MvPolynomial.X s) (fun _ : Fin 1 => MvPolynomial.X t)) -
        (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k
          (Fin.cons (MvPolynomial.X t) (fun _ : Fin 1 => MvPolynomial.X s)) := by
    rw [TensorProduct.map_tmul, LinearMap.id_apply,
      AdjacentBar.exteriorAntisymmetrizationAlong, LinearMap.comp_apply,
      TensorPower.exteriorAntisymmetrization_two, map_sub,
      PiTensorProduct.map_tprod, PiTensorProduct.map_tprod, hg, hg, TensorProduct.tmul_sub]
  have h := DFunLike.congr_fun (polynomialAntisymmetricCoefficientMap_free_coordinates k σ A 2)
    (polynomialConnesOutputExterior k σ s t)
  simp only [LinearMap.comp_apply] at h
  exact h.trans hValue

private theorem projection_f (n : ℕ) :
    ((Symmetric.normalizationProjection k A A).f n).hom =
      (ModuleCat.Algebra.Hochschild.normalizationLevelMap k A A n).hom := by
  change ((ModuleCat.Algebra.Hochschild.normalizationProjection k A A).f n).hom = _
  exact congrArg ModuleCat.Hom.hom
    (ModuleCat.Algebra.Hochschild.normalizationProjection_f k A A n)

/-- The literal original input is the independently computed normalized degree-one signed representative. -/
theorem polynomialConnesPairInput_eq_signed (s t : σ) :
    polynomialConnesPairInput k σ s t =
      normalizedPolynomialSignedRepresentative k σ A 1 (polynomialConnesInputExterior k σ s t) := by
  let P := ((Symmetric.normalizationProjection k A A).f 1).hom
  have hSigned := congrArg P (signed_input k σ s t)
  have hProjection := LinearMap.congr_fun (projection_f k σ 1)
    (MvPolynomial.X s ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => MvPolynomial.X t))
  have hValue := ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod k A A 1
    (MvPolynomial.X s) (fun _ : Fin 1 => MvPolynomial.X t)
  exact (hSigned.trans (hProjection.trans hValue)).symm

/-- The original B value is exactly the independently specified normalized degree-two signed representative. -/
theorem polynomialConnesPairOutput_eq_signed (s t : σ) :
    polynomialConnesPairOutput k σ s t =
      normalizedPolynomialSignedRepresentative k σ A 2 (polynomialConnesOutputExterior k σ s t) := by
  let P := ((Symmetric.normalizationProjection k A A).f 2).hom
  let u : A ⊗[k] TensorPower k 2 A :=
    1 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons (MvPolynomial.X s) (fun _ : Fin 1 => MvPolynomial.X t))
  let v : A ⊗[k] TensorPower k 2 A :=
    1 ⊗ₜ[k] PiTensorProduct.tprod k (Fin.cons (MvPolynomial.X t) (fun _ : Fin 1 => MvPolynomial.X s))
  have hq (a b : A) :
      (fun j : Fin 2 => q (Fin.cons (α := fun _ : Fin 2 => A) a (fun _ : Fin 1 => b) j)) =
        Fin.cons (q a) (fun _ : Fin 1 => q b) := by
    funext j
    cases j using Fin.cases <;> rfl
  have hu : P u = (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k
      (Fin.cons (q (MvPolynomial.X s)) (fun _ : Fin 1 => q (MvPolynomial.X t))) := by
    have hf := LinearMap.congr_fun (projection_f k σ 2) u
    have hv := ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod k A A 2
      (1 : A) (Fin.cons (MvPolynomial.X s) (fun _ : Fin 1 => MvPolynomial.X t))
    rw [hq] at hv
    exact hf.trans hv
  have hv : P v = (1 : A) ⊗ₜ[k] PiTensorProduct.tprod k
      (Fin.cons (q (MvPolynomial.X t)) (fun _ : Fin 1 => q (MvPolynomial.X s))) := by
    have hf := LinearMap.congr_fun (projection_f k σ 2) v
    have hw := ModuleCat.Algebra.Hochschild.normalizationLevelMap_tmul_tprod k A A 2
      (1 : A) (Fin.cons (MvPolynomial.X t) (fun _ : Fin 1 => MvPolynomial.X s))
    rw [hq] at hw
    exact hf.trans hw
  have hProjection := (congrArg P (signed_output k σ s t)).trans
    ((P.map_sub u v).trans (congrArg₂ (fun a b => a - b) hu hv))
  have hB := LinearMap.congr_fun (Symmetric.regularNormalizedConnes_hom k A 1)
    (polynomialConnesPairInput k σ s t)
  exact (hB.trans (NonUnital.normalizedBoundary_one_tprod k A (MvPolynomial.X s) (MvPolynomial.X t))).trans
    hProjection.symm

/-- The original input is a cycle, proved through the signed polynomial chain comparison. -/
theorem polynomialConnesPairInput_cycle (s t : σ) :
    ((Symmetric.normalizedChainComplex k A A).sc 1).g (polynomialConnesPairInput k σ s t) = 0 := by
  rw [polynomialConnesPairInput_eq_signed]
  exact normalizedPolynomialSignedRepresentative_cycle k σ A 1 (polynomialConnesInputExterior k σ s t)

/-- The original B value is a cycle in the original normalized complex. -/
theorem polynomialConnesPairOutput_cycle (s t : σ) :
    ((Symmetric.normalizedChainComplex k A A).sc 2).g (polynomialConnesPairOutput k σ s t) = 0 := by
  rw [polynomialConnesPairOutput_eq_signed]
  exact normalizedPolynomialSignedRepresentative_cycle k σ A 2 (polynomialConnesOutputExterior k σ s t)

/-- The original normalized Hochschild class of X s tensor q(X t). -/
def polynomialConnesPairInputClass (s t : σ) : (Symmetric.normalizedChainComplex k A A).homology 1 :=
  HomologicalComplex.moduleCatCycleClass (Symmetric.normalizedChainComplex k A A) 1
    (polynomialConnesPairInput k σ s t) (polynomialConnesPairInput_cycle k σ s t)

/-- The homology class of the literal original Connes output. -/
def polynomialConnesPairOutputClass (s t : σ) : (Symmetric.normalizedChainComplex k A A).homology 2 :=
  HomologicalComplex.moduleCatCycleClass (Symmetric.normalizedChainComplex k A A) 2
    (polynomialConnesPairOutput k σ s t) (polynomialConnesPairOutput_cycle k σ s t)

/-- The native Connes homology map sends the original input class to this literal output class. -/
theorem regularNormalizedConnesHomology_polynomialPair (s t : σ) :
    Symmetric.regularNormalizedConnesHomology k A 1 (polynomialConnesPairInputClass k σ s t) =
      polynomialConnesPairOutputClass k σ s t := by
  rw [polynomialConnesPairInputClass, Symmetric.regularNormalizedConnesHomology_cycle]
  rfl

/-- The original output class is the class of the independently specified exterior word. -/
theorem polynomialConnesPairOutputClass_eq_exterior (s t : σ) :
    polynomialConnesPairOutputClass k σ s t =
      normalizedPolynomialExteriorClass k σ A 2 (polynomialConnesOutputExterior k σ s t) := by
  simpa only [polynomialConnesPairOutputClass, polynomialConnesPairOutput_eq_signed] using
    (normalizedPolynomialExteriorClass_eq_cycle k σ A 2 (polynomialConnesOutputExterior k σ s t)).symm

/-- The original input class has the independently specified degree-one exterior word. -/
theorem polynomialConnesPairInputClass_eq_exterior (s t : σ) :
    polynomialConnesPairInputClass k σ s t =
      normalizedPolynomialExteriorClass k σ A 1 (polynomialConnesInputExterior k σ s t) := by
  simpa only [polynomialConnesPairInputClass, polynomialConnesPairInput_eq_signed] using
    (normalizedPolynomialExteriorClass_eq_cycle k σ A 1 (polynomialConnesInputExterior k σ s t)).symm

/-- The canonical polynomial coordinates of B(X s tensor X t) are d(X s) wedge d(X t). -/
theorem polynomialConnesPairOutputClass_coordinates (s t : σ) :
    normalizedPolynomialDifferentialFormEquiv k σ A 2 (polynomialConnesPairOutputClass k σ s t) =
      (1 : A) ⊗ₜ[A] exteriorPower.ιMulti A 2
        (Fin.cons (KaehlerDifferential.D k A (MvPolynomial.X s))
          (fun _ : Fin 1 => KaehlerDifferential.D k A (MvPolynomial.X t))) := by
  classical
  rw [polynomialConnesPairOutputClass_eq_exterior, normalizedPolynomialExteriorClass_coordinates,
    polynomialConnesOutputExterior, KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_tmul_ιMulti]
  congr 1
  congr 1
  funext j
  cases j using Fin.cases <;>
    simp only [Fin.cons_zero, Fin.cons_succ, KaehlerDifferential.mvPolynomialCotangentGenerator_single]

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
