/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialNormalizedExterior
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricRegularConnesHomology
public import MathlibExt.LinearAlgebra.TensorPower.AntisymmetrizationTwo

/-!
# Polynomial Connes classes in degrees one and two

Let k be a commutative ring, A = k[σ] and q : A → A/(k·1). In the normalized Hochschild complex
with regular coefficients A, the Connes operator satisfies B₁(Xₛ ⊗ q(Xₜ)) = 1 ⊗ q(Xₛ) ⊗ q(Xₜ) −
1 ⊗ q(Xₜ) ⊗ q(Xₛ). Both tensors are Hochschild cycles. The induced homology map sends [Xₛ ⊗
q(Xₜ)] to this signed degree-two class, whose polynomial differential-form coordinate is 1
⊗_A(dXₛ∧dXₜ).

This calculation uses polynomial exterior coordinates and holds over every commutative ground
ring. For the relation between Connes' operator and differential forms, see J.-L. Loday, Cyclic
Homology, second edition, §2.1, and the Hochschild–Kostant–Rosenberg differential-form
comparison.
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

-- Use the canonical symmetric opposite-action dictionaries locally.
attribute [local instance] Symmetric.opModule Symmetric.actionsComm
  Symmetric.kOpComm Symmetric.kOpTower

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, polynomialConnesInputExterior is Xₛ ⊗ eₜ ∈ A ⊗[k] ∧¹ₖV, the free exterior
coordinate of the one-form Xₛ dXₜ. -/
def polynomialConnesInputExterior (s t : σ) : A ⊗[k] (⋀[k]^1 V) := by
  classical
  exact MvPolynomial.X s ⊗ₜ[k] exteriorPower.ιMulti k 1
    (fun _ : Fin 1 => Finsupp.single t (1 : k))

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, polynomialConnesOutputExterior is 1 ⊗ (eₛ∧eₜ) ∈ A ⊗[k] ∧²ₖV, corresponding
to dXₛ∧dXₜ. -/
def polynomialConnesOutputExterior (s t : σ) : A ⊗[k] (⋀[k]^2 V) := by
  classical
  exact (1 : A) ⊗ₜ[k] exteriorPower.ιMulti k 2
    (Fin.cons (Finsupp.single s (1 : k)) (fun _ : Fin 1 => Finsupp.single t (1 : k)))

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, polynomialConnesPairInput is Xₛ ⊗ q(Xₜ) in degree one of the normalized
Hochschild complex with regular coefficients A. -/
def polynomialConnesPairInput (s t : σ) : (Symmetric.normalizedChainComplex k A A).X 1 :=
  MvPolynomial.X s ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => q (MvPolynomial.X t))

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, polynomialConnesPairOutput is B₁(Xₛ ⊗ q(Xₜ)) in degree two of the
normalized regular Hochschild complex, where B is the descended Connes operator. -/
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

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). The normalized tensor Xₛ ⊗ q(Xₜ) equals the normalized signed representative of
polynomialConnesInputExterior k σ s t in degree one. -/
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

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). The Connes image of Xₛ ⊗ q(Xₜ) equals the normalized signed representative of 1 ⊗
(eₛ∧eₜ). This representative is 1 ⊗ q(Xₛ) ⊗ q(Xₜ) − 1 ⊗ q(Xₜ) ⊗ q(Xₛ). -/
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

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, the degree-one Hochschild differential vanishes on
polynomialConnesPairInput k σ s t = Xₛ ⊗ q(Xₜ). -/
theorem polynomialConnesPairInput_cycle (s t : σ) :
    ((Symmetric.normalizedChainComplex k A A).sc 1).g (polynomialConnesPairInput k σ s t) = 0 := by
  rw [polynomialConnesPairInput_eq_signed]
  exact normalizedPolynomialSignedRepresentative_cycle k σ A 1 (polynomialConnesInputExterior k σ s t)

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, the degree-two Hochschild differential vanishes on
polynomialConnesPairOutput k σ s t = B₁(Xₛ ⊗ q(Xₜ)). -/
theorem polynomialConnesPairOutput_cycle (s t : σ) :
    ((Symmetric.normalizedChainComplex k A A).sc 2).g (polynomialConnesPairOutput k σ s t) = 0 := by
  rw [polynomialConnesPairOutput_eq_signed]
  exact normalizedPolynomialSignedRepresentative_cycle k σ A 2 (polynomialConnesOutputExterior k σ s t)

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, polynomialConnesPairInputClass is the degree-one normalized Hochschild
homology class [Xₛ ⊗ q(Xₜ)]. -/
def polynomialConnesPairInputClass (s t : σ) : (Symmetric.normalizedChainComplex k A A).homology 1 :=
  HomologicalComplex.moduleCatCycleClass (Symmetric.normalizedChainComplex k A A) 1
    (polynomialConnesPairInput k σ s t) (polynomialConnesPairInput_cycle k σ s t)

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, polynomialConnesPairOutputClass is the degree-two normalized Hochschild
class [B₁(Xₛ ⊗ q(Xₜ))] = [1 ⊗ q(Xₛ) ⊗ q(Xₜ) − 1 ⊗ q(Xₜ) ⊗ q(Xₛ)]. -/
def polynomialConnesPairOutputClass (s t : σ) : (Symmetric.normalizedChainComplex k A A).homology 2 :=
  HomologicalComplex.moduleCatCycleClass (Symmetric.normalizedChainComplex k A A) 2
    (polynomialConnesPairOutput k σ s t) (polynomialConnesPairOutput_cycle k σ s t)

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). In normalized regular Hochschild homology, B : HH₁(A,A) → HH₂(A,A) sends
polynomialConnesPairInputClass k σ s t to polynomialConnesPairOutputClass k σ s t. -/
theorem regularNormalizedConnesHomology_polynomialPair (s t : σ) :
    Symmetric.regularNormalizedConnesHomology k A 1 (polynomialConnesPairInputClass k σ s t) =
      polynomialConnesPairOutputClass k σ s t := by
  rw [polynomialConnesPairInputClass, Symmetric.regularNormalizedConnesHomology_cycle]
  rfl

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, polynomialConnesPairOutputClass equals normalizedPolynomialExteriorClass
applied in degree two to 1 ⊗ (eₛ∧eₜ). -/
theorem polynomialConnesPairOutputClass_eq_exterior (s t : σ) :
    polynomialConnesPairOutputClass k σ s t =
      normalizedPolynomialExteriorClass k σ A 2 (polynomialConnesOutputExterior k σ s t) := by
  simpa only [polynomialConnesPairOutputClass, polynomialConnesPairOutput_eq_signed] using
    (normalizedPolynomialExteriorClass_eq_cycle k σ A 2 (polynomialConnesOutputExterior k σ s t)).symm

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). For s,t ∈ σ, polynomialConnesPairInputClass equals normalizedPolynomialExteriorClass
applied in degree one to Xₛ ⊗ eₜ. -/
theorem polynomialConnesPairInputClass_eq_exterior (s t : σ) :
    polynomialConnesPairInputClass k σ s t =
      normalizedPolynomialExteriorClass k σ A 1 (polynomialConnesInputExterior k σ s t) := by
  simpa only [polynomialConnesPairInputClass, polynomialConnesPairInput_eq_signed] using
    (normalizedPolynomialExteriorClass_eq_cycle k σ A 1 (polynomialConnesInputExterior k σ s t)).symm

/-- Let k be a commutative ring, σ a variable set and A = k[σ]. Put V = ⊕ᵢ∈σ k·eᵢ and q : A →
A/(k·1). The normalized polynomial differential-form isomorphism sends the degree-two class of
B₁(Xₛ ⊗ q(Xₜ)) to 1 ⊗_A (dXₛ∧dXₜ) in A ⊗_A ∧²_AΩ¹_{A/k}. -/
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
