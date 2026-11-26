/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDifferentialFormComplexComparison
public import MathlibExt.RingTheory.MvPolynomial.EnvelopingDiagonalCotangentLifts
public import MathlibExt.LinearAlgebra.ExteriorPower.Semilinear

/-!
# Cotangent coordinates of polynomial diagonal Koszul wedges

For a commutative ring k and A = k[σ], multiplication μ : A ⊗[k] Aᵐᵒᵖ → A gives a semilinear map
from the diagonal free module to Ω¹_{A/k}, sending eᵢ to dXᵢ and a finitely supported family x
to ∑ᵢ μ(xᵢ)·dXᵢ. Its exterior powers give the form coordinates of arbitrary diagonal exterior
elements.

For a compatible symmetric coefficient module M, the degree-n coefficient-form equivalence sends
m ⊗_E x to m ⊗_A ∧ⁿC(x). In particular, a scalar e on a variable wedge becomes the coefficient
μ(e)·m, and a wedge of arbitrary diagonal vectors becomes the wedge of their cotangent images.
These formulas hold for arbitrary variable sets and do not require coefficient flatness.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. For i ∈ σ, the map E → Ω¹_{A/k} given by e ↦ μ(e)·dXᵢ is semilinear along μ. -/
def diagonalCotangentSemilinearSingle (i : σ) :
    MvPolynomial.PolynomialEnveloping k σ →ₛₗ[(MvPolynomial.diagonalMultiplication k σ).toRingHom]
      KaehlerDifferential k (MvPolynomial σ k) where
  toFun e := MvPolynomial.diagonalMultiplication k σ e •
    KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i)
  map_add' e e' := by rw [map_add, add_smul]
  map_smul' e e' := by
    simp only [smul_eq_mul, map_mul, mul_smul,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. The semilinear map C : ⊕ᵢ∈σ E·eᵢ → Ω¹_{A/k} sends a finitely supported
family x to ∑ᵢ μ(xᵢ)·dXᵢ. Its scalar map is μ : E → A. -/
def diagonalCotangentSemilinearMap :
    (σ →₀ MvPolynomial.PolynomialEnveloping k σ) →ₛₗ[(MvPolynomial.diagonalMultiplication k σ).toRingHom]
      KaehlerDifferential k (MvPolynomial σ k) :=
  Finsupp.lsum ℕ (diagonalCotangentSemilinearSingle k σ)

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. For every x ∈ ⊕ᵢ∈σ E·eᵢ, diagonalCotangentSemilinearMap k σ x equals
MvPolynomial.diagonalCotangentCoordinates k σ x. Both expressions give ∑ᵢ μ(xᵢ)·dXᵢ. -/
theorem diagonalCotangentSemilinearMap_coordinates
    (x : σ →₀ MvPolynomial.PolynomialEnveloping k σ) :
    diagonalCotangentSemilinearMap k σ x = MvPolynomial.diagonalCotangentCoordinates k σ x := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | single i e =>
      rw [diagonalCotangentSemilinearMap, Finsupp.lsum_single,
        MvPolynomial.diagonalCotangentCoordinates_single]
      change MvPolynomial.diagonalMultiplication k σ e •
        KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i) = _
      rfl

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. For i ∈ σ, the diagonal cotangent map sends the standard vector
Finsupp.single i 1 to dXᵢ. -/
theorem diagonalCotangentSemilinearMap_single (i : σ) :
    diagonalCotangentSemilinearMap k σ
        (Finsupp.single i (1 : MvPolynomial.PolynomialEnveloping k σ)) =
      KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i) := by
  rw [diagonalCotangentSemilinearMap, Finsupp.lsum_single]
  change MvPolynomial.diagonalMultiplication k σ (1 : MvPolynomial.PolynomialEnveloping k σ) •
    KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X i) = _
  rw [map_one, one_smul]

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. For n : ℕ, the nth exterior power of the μ-semilinear cotangent map gives a
k-linear map ∧ⁿ_E(⊕ᵢE·eᵢ) → ∧ⁿ_AΩ¹_{A/k} after restriction of the source scalars to k. -/
def diagonalCotangentExteriorGround (n : ℕ) :
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) →ₗ[k]
      (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) := by
  letI : Module k
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
    Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
  exact
    { toFun := exteriorPower.mapSemilinear (MvPolynomial.diagonalMultiplication k σ).toRingHom
        (diagonalCotangentSemilinearMap k σ) n
      map_add' := map_add _
      map_smul' := by
        intro c x
        change exteriorPower.mapSemilinear (MvPolynomial.diagonalMultiplication k σ).toRingHom
          (diagonalCotangentSemilinearMap k σ) n
          (algebraMap k (MvPolynomial.PolynomialEnveloping k σ) c • x) = _
        rw [map_smulₛₗ]
        simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, RingHom.id_apply]
        rw [(MvPolynomial.diagonalMultiplication k σ).commutes,
          IsScalarTower.algebraMap_smul (MvPolynomial σ k)] }

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. For e ∈ E and a : Fin n → σ, the ground-linear exterior cotangent map sends
e·(e_{a(0)}∧…∧e_{a(n−1)}) to μ(e)·(dX_{a(0)}∧…∧dX_{a(n−1)}). -/
private theorem diagonalCotangentExteriorGround_smul_basis
    (n : ℕ) (e : MvPolynomial.PolynomialEnveloping k σ) (a : Fin n → σ) :
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    diagonalCotangentExteriorGround k σ n
        (e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n
          (fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ))) =
      MvPolynomial.diagonalMultiplication k σ e •
        exteriorPower.ιMulti (MvPolynomial σ k) n
          (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j))) := by
  letI : Module k
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
    Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
  let φ : MvPolynomial.PolynomialEnveloping k σ →+* MvPolynomial σ k :=
    (MvPolynomial.diagonalMultiplication k σ).toRingHom
  let f₀ : (σ →₀ MvPolynomial.PolynomialEnveloping k σ) →ₛₗ[φ]
      KaehlerDifferential k (MvPolynomial σ k) := diagonalCotangentSemilinearMap k σ
  let F :
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) →ₛₗ[φ]
          (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) :=
    exteriorPower.mapSemilinear φ f₀ n
  let v : Fin n → (σ →₀ MvPolynomial.PolynomialEnveloping k σ) :=
    fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ)
  let ω : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) :=
    exteriorPower.ιMulti (MvPolynomial σ k) n
      (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j)))
  have hvec : (fun j : Fin n => f₀ (v j)) =
      (fun j : Fin n =>
        KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j))) := by
    funext j
    exact diagonalCotangentSemilinearMap_single k σ (a j)
  have hmap := exteriorPower.mapSemilinear_ιMulti
    (R := MvPolynomial.PolynomialEnveloping k σ) (S := MvPolynomial σ k)
    (M := σ →₀ MvPolynomial.PolynomialEnveloping k σ)
    (N := KaehlerDifferential k (MvPolynomial σ k)) φ f₀ n v
  have htail := congrArg
    (fun l : Fin n → KaehlerDifferential k (MvPolynomial σ k) =>
      exteriorPower.ιMulti (MvPolynomial σ k) n l) hvec
  have hw := hmap.trans htail
  have hφ : φ e = MvPolynomial.diagonalMultiplication k σ e :=
    congrFun (AlgHom.coe_toRingHom (MvPolynomial.diagonalMultiplication k σ)) e
  have hsmul := F.map_smulₛₗ e
    (exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n v)
  have hscaled := hsmul.trans
    ((congrArg
      (fun z : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) =>
        φ e • z) hw).trans
      (congrArg (fun r : MvPolynomial σ k => r • ω) hφ))
  have hground :
      diagonalCotangentExteriorGround k σ n
          (e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n v) =
        F (e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n v) := rfl
  exact hground.trans hscaled

section Coefficients

variable (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. Let M be an A-module with compatible k-action, regarded as a symmetric
A-bimodule. The degree-n coefficient-form equivalence sends m ⊗_E(e·(e_{a(0)}∧…∧e_{a(n−1)})) to
(μ(e)·m) ⊗_A(dX_{a(0)}∧…∧dX_{a(n−1)}), for m ∈ M, e ∈ E and a : Fin n → σ. -/
theorem symmetricCoefficientFormDegreeEquiv_mk_smul_basis
    (n : ℕ) (m : M) (e : MvPolynomial.PolynomialEnveloping k σ) (a : Fin n → σ) :
    letI := Symmetric.opModule (MvPolynomial σ k) M
    letI := Symmetric.actionsComm (MvPolynomial σ k) M
    letI := Symmetric.kOpComm k (MvPolynomial σ k) M
    letI := Symmetric.kOpTower k (MvPolynomial σ k) M
    letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    symmetricCoefficientFormDegreeEquiv k σ M n
      (TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m
        (e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n
          (fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ)))) =
      (MvPolynomial.diagonalMultiplication k σ e • m) ⊗ₜ[MvPolynomial σ k]
        exteriorPower.ιMulti (MvPolynomial σ k) n
          (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j))) := by
  letI := Symmetric.opModule (MvPolynomial σ k) M
  letI := Symmetric.actionsComm (MvPolynomial σ k) M
  letI := Symmetric.kOpComm k (MvPolynomial σ k) M
  letI := Symmetric.kOpTower k (MvPolynomial σ k) M
  letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
  letI : Module k
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
    Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
  change KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n
    (coefficientFreeExteriorEquiv k σ M n _) = _
  rw [coefficientFreeExteriorEquiv_mk_smul_basis,
    KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_tmul_basis]
  have he : MulOpposite.op e • m = MvPolynomial.diagonalMultiplication k σ e • m :=
    symmetricRightEnvelopingAction_multiplication k σ M e m
  rw [he]

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. Let M be an A-module with compatible k-action, regarded as a symmetric
A-bimodule. For m ∈ M and a : Fin n → σ, the degree-n coefficient-form equivalence sends m
⊗_E(e_{a(0)}∧…∧e_{a(n−1)}) to m ⊗_A(dX_{a(0)}∧…∧dX_{a(n−1)}). -/
theorem symmetricCoefficientFormDegreeEquiv_mk_basis
    (n : ℕ) (m : M) (a : Fin n → σ) :
    letI := Symmetric.opModule (MvPolynomial σ k) M
    letI := Symmetric.actionsComm (MvPolynomial σ k) M
    letI := Symmetric.kOpComm k (MvPolynomial σ k) M
    letI := Symmetric.kOpTower k (MvPolynomial σ k) M
    letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    symmetricCoefficientFormDegreeEquiv k σ M n
      (TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m
        (exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n
          (fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ)))) =
      m ⊗ₜ[MvPolynomial σ k] exteriorPower.ιMulti (MvPolynomial σ k) n
        (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j))) := by
  simpa only [map_one, one_smul] using
    symmetricCoefficientFormDegreeEquiv_mk_smul_basis k σ M n m
      (1 : MvPolynomial.PolynomialEnveloping k σ) a

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. Let M be an A-module with compatible k-action, regarded as a symmetric
A-bimodule. For x ∈ ∧ⁿ_E(⊕ᵢE·eᵢ) and m ∈ M, symmetricCoefficientFormDegreeEquiv sends m ⊗_E x to
m ⊗_A ∧ⁿC(x), where C is the μ-semilinear cotangent coordinate map. -/
theorem symmetricCoefficientFormDegreeEquiv_mk
    (n : ℕ) (m : M)
    (x : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
    letI := Symmetric.opModule (MvPolynomial σ k) M
    letI := Symmetric.actionsComm (MvPolynomial σ k) M
    letI := Symmetric.kOpComm k (MvPolynomial σ k) M
    letI := Symmetric.kOpTower k (MvPolynomial σ k) M
    letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    symmetricCoefficientFormDegreeEquiv k σ M n
      (TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m x) =
      m ⊗ₜ[MvPolynomial σ k]
        exteriorPower.mapSemilinear (MvPolynomial.diagonalMultiplication k σ).toRingHom
          (diagonalCotangentSemilinearMap k σ) n x := by
  classical
  letI : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  letI := Symmetric.opModule (MvPolynomial σ k) M
  letI := Symmetric.actionsComm (MvPolynomial σ k) M
  letI := Symmetric.kOpComm k (MvPolynomial σ k) M
  letI := Symmetric.kOpTower k (MvPolynomial σ k) M
  letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
  letI : Module k
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
    Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
  let S := symmetricCoefficientFormDegreeEquiv k σ M n
  let q := TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
    (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m
  let G := diagonalCotangentExteriorGround k σ n
  let t₀ := TensorProduct.mk (MvPolynomial σ k) M
    (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) m
  let t := t₀.restrictScalars k
  let L :
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) →ₗ[k]
          M ⊗[MvPolynomial σ k] (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) :=
    S.toLinearMap.comp q
  let T :
      (⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) →ₗ[k]
          M ⊗[MvPolynomial σ k] (⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k))) :=
    t.comp G
  have hSourceValue
      (y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
      L y = S (q y) := by
    have hcomp := LinearMap.comp_apply S.toLinearMap q y
    have hequiv := congrFun (LinearEquiv.coe_toLinearMap S) (q y)
    exact hcomp.trans hequiv
  have hTargetValue
      (y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
      T y = m ⊗ₜ[MvPolynomial σ k] G y := by
    have hcomp := LinearMap.comp_apply t G y
    have hrestrict := LinearMap.restrictScalars_apply k t₀ (G y)
    exact hcomp.trans hrestrict
  have hGroundValue
      (y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
      G y = exteriorPower.mapSemilinear (MvPolynomial.diagonalMultiplication k σ).toRingHom
        (diagonalCotangentSemilinearMap k σ) n y := rfl
  have hDesired : L x = T x := by
    generalize hL : L = L'
    generalize hT : T = T'
    let b := Module.Basis.exteriorPower
      (R := MvPolynomial.PolynomialEnveloping k σ)
      (M := σ →₀ MvPolynomial.PolynomialEnveloping k σ) (I := σ) n
      (Finsupp.basisSingleOne (R := MvPolynomial.PolynomialEnveloping k σ) (ι := σ))
    have h : ∀ a : Set.powersetCard σ n →₀ MvPolynomial.PolynomialEnveloping k σ,
        L' (Finsupp.linearCombination (MvPolynomial.PolynomialEnveloping k σ) b a) =
          T' (Finsupp.linearCombination (MvPolynomial.PolynomialEnveloping k σ) b a) := by
      intro a
      induction a using Finsupp.induction_linear with
      | zero => simp only [map_zero]
      | add a a' ha ha' => simp only [map_add, ha, ha']
      | single s e =>
          rw [Finsupp.linearCombination_single]
          simp only [b, exteriorPower.coe_basis, exteriorPower.ιMulti_family, Finsupp.coe_basisSingleOne]
          let a : Fin n → σ := fun j => Set.powersetCard.ofFinEmbEquiv.symm s j
          let w : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
              (σ →₀ MvPolynomial.PolynomialEnveloping k σ) :=
            e • exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n
              (fun j => Finsupp.single (a j) (1 : MvPolynomial.PolynomialEnveloping k σ))
          let ω : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) :=
            exteriorPower.ιMulti (MvPolynomial σ k) n
              (fun j => KaehlerDifferential.D k (MvPolynomial σ k) (MvPolynomial.X (a j)))
          change L' w = T' w
          have hNativeLeft := symmetricCoefficientFormDegreeEquiv_mk_smul_basis k σ M n m e a
          have hNativeRight := diagonalCotangentExteriorGround_smul_basis k σ n e a
          have hleft := (LinearMap.congr_fun hL w).symm.trans
            ((hSourceValue w).trans hNativeLeft)
          have hright := congrArg
            (fun z : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) =>
              m ⊗ₜ[MvPolynomial σ k] z) hNativeRight
          have htensor :
              (MvPolynomial.diagonalMultiplication k σ e • m) ⊗ₜ[MvPolynomial σ k] ω =
                m ⊗ₜ[MvPolynomial σ k] (MvPolynomial.diagonalMultiplication k σ e • ω) :=
            TensorProduct.smul_tmul (R := MvPolynomial σ k) (R' := MvPolynomial σ k)
              (M := M) (N := ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)))
              (MvPolynomial.diagonalMultiplication k σ e) m ω
          exact hleft.trans
            (htensor.trans
              (hright.symm.trans ((hTargetValue w).symm.trans (LinearMap.congr_fun hT w))))
    have hx := h (b.repr x)
    have hrepr := Module.Basis.linearCombination_repr
      (R := MvPolynomial.PolynomialEnveloping k σ)
      (M := ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) b x
    have hLrepr := congrArg
      (fun y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ) => L' y) hrepr
    have hTrepr := congrArg
      (fun y : ⋀[MvPolynomial.PolynomialEnveloping k σ]^n
        (σ →₀ MvPolynomial.PolynomialEnveloping k σ) => T' y) hrepr
    exact hLrepr.symm.trans (hx.trans hTrepr)
  exact (hSourceValue x).symm.trans
    (hDesired.trans
      ((hTargetValue x).trans
        (congrArg
          (fun z : ⋀[MvPolynomial σ k]^n (KaehlerDifferential k (MvPolynomial σ k)) =>
            m ⊗ₜ[MvPolynomial σ k] z) (hGroundValue x))))

/-- Let k be a commutative ring, σ any variable set, A = k[σ], E = A ⊗[k] Aᵐᵒᵖ and μ : E → A the
multiplication map. Let M be an A-module with compatible k-action, regarded as a symmetric
A-bimodule. For a : Fin n → (⊕ᵢE·eᵢ) and m ∈ M, the coefficient-form equivalence sends m
⊗_E(a₀∧…∧aₙ₋₁) to m ⊗_A(C(a₀)∧…∧C(aₙ₋₁)), where C(x) = ∑ᵢ μ(xᵢ)·dXᵢ. -/
theorem symmetricCoefficientFormDegreeEquiv_mk_ιMulti
    (n : ℕ) (m : M) (a : Fin n → (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :
    letI := Symmetric.opModule (MvPolynomial σ k) M
    letI := Symmetric.actionsComm (MvPolynomial σ k) M
    letI := Symmetric.kOpComm k (MvPolynomial σ k) M
    letI := Symmetric.kOpTower k (MvPolynomial σ k) M
    letI := EnvelopingCoefficient.rightEnvelopingModule k (MvPolynomial σ k) M
    letI : Module k
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) :=
      Module.compHom _ (algebraMap k (MvPolynomial.PolynomialEnveloping k σ))
    symmetricCoefficientFormDegreeEquiv k σ M n
      (TensorProduct.Balanced.mk k (MvPolynomial.PolynomialEnveloping k σ) M
        (⋀[MvPolynomial.PolynomialEnveloping k σ]^n (σ →₀ MvPolynomial.PolynomialEnveloping k σ)) m
        (exteriorPower.ιMulti (MvPolynomial.PolynomialEnveloping k σ) n a)) =
      m ⊗ₜ[MvPolynomial σ k] exteriorPower.ιMulti (MvPolynomial σ k) n
        (fun j => diagonalCotangentSemilinearMap k σ (a j)) := by
  rw [symmetricCoefficientFormDegreeEquiv_mk, exteriorPower.mapSemilinear_ιMulti]

end Coefficients

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
