/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import MathlibExt.LinearAlgebra.Finsupp.ScalarExtensionCoordinates
public import MathlibExt.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Polynomial cotangent and exterior coordinates

For a commutative ring `k` and a type `σ`, put `A = MvPolynomial σ k` and `V = σ →₀ k`. The
free generators of `V` give the variable differentials in `Ω = Ω¹(A/k)`: `A ⊗[k] V ≃ₗ[A] Ω`,
with `a ⊗ e_i ↦ a dX_i`. Exterior powers give `A ⊗[k] Λ^n_k V ≃ₗ[A] Λ^n_A Ω` in every degree.

For a coefficient module `M` with compatible commuting `k`- and `A`-actions, the comparison is
`M ⊗[k] Λ^n_k V ≃ₗ[A] M ⊗[A] Λ^n_A Ω`, keeping `M` as the first tensor factor.

When `σ` is linearly ordered, a finite subset `s` of cardinality `n` specifies an ordered
exterior coordinate. Its value on `df_0 ∧ ⋯ ∧ df_(n-1)` is the determinant of the matrix with
entry `∂f_i/∂X_(e_s j)`, where `e_s : Fin n ↪o σ` enumerates `s` in order.

References: Loday, *Cyclic Homology*, Section 1.1; Hochschild, Kostant and Rosenberg,
*Differential forms on regular affine algebras*, Transactions of the AMS 102 (1962), 383–408.
-/

@[expose] public section
noncomputable section

open scoped TensorProduct

universe u v w w'

namespace KaehlerDifferential

variable (k : Type u) [CommRing k] (σ : Type v)

local notation "A" => MvPolynomial σ k
local notation "V" => (σ →₀ k)
local notation "Ω" => KaehlerDifferential k A

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. This is the `A`-linear equivalence `A ⊗[k] V ≃ₗ[A] Ω` sending `a ⊗
single i 1` to `a • D k A (X_i)` for `a : A` and `i : σ`. -/
def mvPolynomialBaseChangeEquiv : A ⊗[k] V ≃ₗ[A] Ω :=
  (Finsupp.scalarExtensionCoordinates k A σ).trans (mvPolynomialEquiv k σ).symm

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. For `a : A` and `i : σ`, `mvPolynomialBaseChangeEquiv k σ (a ⊗
single i 1) = a • D k A (X_i)`. -/
theorem mvPolynomialBaseChangeEquiv_tmul_single (i : σ) (a : A) :
    mvPolynomialBaseChangeEquiv k σ (a ⊗ₜ[k] Finsupp.single i (1 : k)) =
      a • D k A (MvPolynomial.X i) := by
  rw [mvPolynomialBaseChangeEquiv, LinearEquiv.trans_apply,
    Finsupp.scalarExtensionCoordinates_tmul_single, map_one, one_mul]
  exact mvPolynomialBasis_repr_symm_single k σ i a

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. This is the `k`-linear map `G : V → Ω` sending `single i 1` to `D
k A (X_i)`. It is the composite `v ↦ 1 ⊗ v` followed by `mvPolynomialBaseChangeEquiv k σ`. -/
def mvPolynomialCotangentGenerator : V →ₗ[k] Ω :=
  ((mvPolynomialBaseChangeEquiv k σ).toLinearMap.restrictScalars k).comp
    (TensorProduct.mk k A V 1)

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. For every `i : σ`, `mvPolynomialCotangentGenerator k σ (single i
1) = D k A (X_i)`. -/
theorem mvPolynomialCotangentGenerator_single (i : σ) :
    mvPolynomialCotangentGenerator k σ (Finsupp.single i (1 : k)) =
      D k A (MvPolynomial.X i) := by
  change mvPolynomialBaseChangeEquiv k σ ((1 : A) ⊗ₜ[k] Finsupp.single i (1 : k)) = _
  rw [mvPolynomialBaseChangeEquiv_tmul_single, one_smul]

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. For every `n : ℕ`, this is the `A`-linear equivalence `A ⊗[k]
Λ^n_k V ≃ₗ[A] Λ^n_A Ω` induced by the variable-differential map `G(e_i) = dX_i`. -/
def mvPolynomialExteriorEquiv (n : ℕ) : A ⊗[k] (⋀[k]^n V) ≃ₗ[A] (⋀[A]^n Ω) :=
  (exteriorPower.baseChangeEquiv k A V n).trans
    (exteriorPower.mapEquiv A (A ⊗[k] V) n (mvPolynomialBaseChangeEquiv k σ))

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `n : ℕ`, `a : A`, and `v : Fin n → V`. Writing `G =
mvPolynomialCotangentGenerator k σ`, the equivalence satisfies `E_n(a ⊗ ιMulti_k(v)) = a •
ιMulti_A(fun j ↦ G(v j))`. -/
theorem mvPolynomialExteriorEquiv_tmul_ιMulti (n : ℕ) (a : A) (v : Fin n → V) :
    mvPolynomialExteriorEquiv k σ n (a ⊗ₜ[k] exteriorPower.ιMulti k n v) =
      a • exteriorPower.ιMulti A n (fun j => mvPolynomialCotangentGenerator k σ (v j)) := by
  rw [mvPolynomialExteriorEquiv, LinearEquiv.trans_apply,
    exteriorPower.baseChangeEquiv_apply_tmul_ιMulti, map_smul,
    exteriorPower.mapEquiv_apply_ιMulti]
  rfl

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. For `n : ℕ`, `a : A`, and any `f : Fin n → σ`, the exterior
equivalence sends `a ⊗ (e_(f 0) ∧ ⋯ ∧ e_(f (n-1)))` to `a • (dX_(f 0) ∧ ⋯ ∧ dX_(f (n-1)))`,
where `e_i = single i 1`. The empty wedge is `1` when `n = 0`. -/
theorem mvPolynomialExteriorEquiv_tmul_basis (n : ℕ) (a : A) (f : Fin n → σ) :
    mvPolynomialExteriorEquiv k σ n
      (a ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))) =
      a • exteriorPower.ιMulti A n (fun j => D k A (MvPolynomial.X (f j))) := by
  rw [mvPolynomialExteriorEquiv_tmul_ιMulti]
  simp only [mvPolynomialCotangentGenerator_single]

section Coefficients

variable (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `M` have `k`- and `A`-module structures with commuting actions
and scalar tower `k → A → M` (`SMulCommClass k A M` and `IsScalarTower k A M`). For each `n :
ℕ`, this is the `A`-linear equivalence `M ⊗[k] Λ^n_k V ≃ₗ[A] M ⊗[A] Λ^n_A Ω`. Its pure-word
formula is `m ⊗ ιMulti_k(v) ↦ m ⊗ ιMulti_A(G ∘ v)`, with `G(e_i) = dX_i`. -/
def mvPolynomialCoefficientExteriorEquiv (n : ℕ) :
    M ⊗[k] (⋀[k]^n V) ≃ₗ[A] M ⊗[A] (⋀[A]^n Ω) :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange k A A M (⋀[k]^n V)).symm.trans
    (TensorProduct.congr (LinearEquiv.refl A M) (mvPolynomialExteriorEquiv k σ n))

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `M` have `k`- and `A`-module structures with commuting actions
and scalar tower `k → A → M` (`SMulCommClass k A M` and `IsScalarTower k A M`). For `n : ℕ`,
`m : M`, and `v : Fin n → V`, the coefficient comparison satisfies `E^M_n(m ⊗ ιMulti_k(v)) = m
⊗ ιMulti_A(fun j ↦ G(v j))`, where `G = mvPolynomialCotangentGenerator k σ`. -/
theorem mvPolynomialCoefficientExteriorEquiv_tmul_ιMulti
    (n : ℕ) (m : M) (v : Fin n → V) :
    mvPolynomialCoefficientExteriorEquiv k σ M n (m ⊗ₜ[k] exteriorPower.ιMulti k n v) =
      m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => mvPolynomialCotangentGenerator k σ (v j)) := by
  rw [mvPolynomialCoefficientExteriorEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply,
    mvPolynomialExteriorEquiv_tmul_ιMulti, one_smul]

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `M` have `k`- and `A`-module structures with commuting actions
and scalar tower `k → A → M` (`SMulCommClass k A M` and `IsScalarTower k A M`). For `n : ℕ`,
`m : M`, and any `f : Fin n → σ`, the coefficient comparison sends `m ⊗ (e_(f 0) ∧ ⋯ ∧ e_(f
(n-1)))` to `m ⊗ (dX_(f 0) ∧ ⋯ ∧ dX_(f (n-1)))`. The empty wedge is `1` when `n = 0`. -/
theorem mvPolynomialCoefficientExteriorEquiv_tmul_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    mvPolynomialCoefficientExteriorEquiv k σ M n
      (m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))) =
      m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => D k A (MvPolynomial.X (f j))) := by
  rw [mvPolynomialCoefficientExteriorEquiv_tmul_ιMulti]
  simp only [mvPolynomialCotangentGenerator_single]

/-- Let `k` be a commutative ring and `σ` a type. Set `A = MvPolynomial σ k`, `V = σ →₀ k`, and `Ω
= KaehlerDifferential k A`. Let `M` have `k`- and `A`-module structures with commuting actions
and scalar tower `k → A → M` (`SMulCommClass k A M` and `IsScalarTower k A M`). For `n : ℕ`,
`m : M`, and `f : Fin n → σ`, the inverse comparison sends `m ⊗ (dX_(f 0) ∧ ⋯ ∧ dX_(f (n-1)))`
to `m ⊗ (e_(f 0) ∧ ⋯ ∧ e_(f (n-1)))`, where `e_i = single i 1`. The empty wedge is `1` when `n
= 0`. -/
theorem mvPolynomialCoefficientExteriorEquiv_symm_tmul_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    (mvPolynomialCoefficientExteriorEquiv k σ M n).symm
      (m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => D k A (MvPolynomial.X (f j)))) =
      m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k)) := by
  apply (mvPolynomialCoefficientExteriorEquiv k σ M n).injective
  rw [LinearEquiv.apply_symm_apply, mvPolynomialCoefficientExteriorEquiv_tmul_basis]

section Coordinates

variable [LinearOrder σ]

/-- Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. For `n : ℕ`, the `A`-linear map `π_s : Λ^n_A Ω →
A` is the exterior-basis coordinate at the ordered variable word `dX_(e_s 0) ∧ ⋯ ∧ dX_(e_s
(n-1))`. The empty wedge is `1` when `n = 0`. -/
def mvPolynomialFormCoordinate (n : ℕ) (s : Set.powersetCard σ n) :
    (⋀[A]^n Ω) →ₗ[A] A :=
  ((mvPolynomialBasis k σ).exteriorPower n).coord s

/-- Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. For `n : ℕ` and `f : Fin n → A`, the coordinate
satisfies `π_s(df_0 ∧ ⋯ ∧ df_(n-1)) = det(∂f_i/∂X_(e_s j))`. Rows are indexed by the
differentials `f_i` and columns by the ordered variables `e_s j`. The empty wedge is `1` when
`n = 0`. -/
theorem mvPolynomialFormCoordinate_differentials
    (n : ℕ) (s : Set.powersetCard σ n) (f : Fin n → A) :
    mvPolynomialFormCoordinate k σ n s
      (exteriorPower.ιMulti A n (fun j => D k A (f j))) =
      (Matrix.of fun i j =>
        MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s j) (f i)).det := by
  rw [mvPolynomialFormCoordinate, exteriorPower.basis_coord,
    exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  apply Matrix.ext
  intro i j
  change (mvPolynomialBasis k σ).coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (D k A (f i)) =
    MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s j) (f i)
  rw [Module.Basis.coord_apply]
  exact mvPolynomialBasis_repr_apply k σ _ _

/-- Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. Let `M` be an `A`-module. The `A`-linear
coefficient coordinate `κ_s : M ⊗[A] Λ^n_A Ω → M` sends `m ⊗ ω` to `π_s(ω) • m`, where `π_s`
is the ordered exterior form coordinate. -/
def mvPolynomialCoefficientFormCoordinate (n : ℕ) (s : Set.powersetCard σ n) :
    M ⊗[A] (⋀[A]^n Ω) →ₗ[A] M :=
  (TensorProduct.rid A M).toLinearMap.comp
    (TensorProduct.map LinearMap.id (mvPolynomialFormCoordinate k σ n s))

omit [Module k M] [SMulCommClass k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M] in
/-- Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. Let `M` be an `A`-module. For `m : M` and `ω :
Λ^n_A Ω`, `κ_s(m ⊗ ω) = π_s(ω) • m`. The scalar `π_s(ω) : A` acts on the coefficient module. -/
theorem mvPolynomialCoefficientFormCoordinate_tmul
    (n : ℕ) (s : Set.powersetCard σ n) (m : M) (ω : ⋀[A]^n Ω) :
    mvPolynomialCoefficientFormCoordinate k σ M n s (m ⊗ₜ[A] ω) =
      mvPolynomialFormCoordinate k σ n s ω • m := by
  rw [mvPolynomialCoefficientFormCoordinate, LinearMap.comp_apply,
    TensorProduct.map_tmul, LinearMap.id_apply]
  change (TensorProduct.rid A M) (m ⊗ₜ[A] mvPolynomialFormCoordinate k σ n s ω) =
    mvPolynomialFormCoordinate k σ n s ω • m
  exact TensorProduct.rid_tmul m _

omit [Module k M] [SMulCommClass k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M] in
/-- Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. Let `M` be an `A`-module. For `m : M` and `f :
Fin n → A`, the coefficient coordinate satisfies `κ_s(m ⊗ (df_0 ∧ ⋯ ∧ df_(n-1))) =
det(∂f_i/∂X_(e_s j)) • m`, with rows indexed by `i` and ordered variable columns by `j`. The
empty wedge is `1` when `n = 0`. -/
theorem mvPolynomialCoefficientFormCoordinate_differentials
    (n : ℕ) (s : Set.powersetCard σ n) (m : M) (f : Fin n → A) :
    mvPolynomialCoefficientFormCoordinate k σ M n s
      (m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j => D k A (f j))) =
      (Matrix.of fun i j =>
        MvPolynomial.pderiv (Set.powersetCard.ofFinEmbEquiv.symm s j) (f i)).det • m := by
  rw [mvPolynomialCoefficientFormCoordinate_tmul, mvPolynomialFormCoordinate_differentials]

/-- Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. The ordered variable wedge has unit coordinate:
`π_s(dX_(e_s 0) ∧ ⋯ ∧ dX_(e_s (n-1))) = 1` in `A`. The empty wedge is `1` when `n = 0`. -/
theorem mvPolynomialFormCoordinate_basis (n : ℕ) (s : Set.powersetCard σ n) :
    mvPolynomialFormCoordinate k σ n s
      (exteriorPower.ιMulti A n (fun j =>
        D k A (MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s j)))) = 1 := by
  simp only [mvPolynomialFormCoordinate, ← mvPolynomialBasis_apply]
  change ((mvPolynomialBasis k σ).exteriorPower n).coord s
    (exteriorPower.ιMulti_family A n (mvPolynomialBasis k σ) s) = 1
  rw [Module.Basis.coord_apply, ← exteriorPower.basis_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

omit [Module k M] [SMulCommClass k (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M] in
/-- Let `k` be a commutative ring, `σ` a linearly ordered type, `A = MvPolynomial σ k`, and `Ω =
KaehlerDifferential k A`. For `n : ℕ` and `s : Set.powersetCard σ n`, write `e_s : Fin n ↪o σ`
for `Set.powersetCard.ofFinEmbEquiv.symm s`. Let `M` be an `A`-module. For every `m : M`,
`κ_s(m ⊗ (dX_(e_s 0) ∧ ⋯ ∧ dX_(e_s (n-1)))) = m`. The empty wedge is `1` when `n = 0`. -/
theorem mvPolynomialCoefficientFormCoordinate_basis
    (n : ℕ) (s : Set.powersetCard σ n) (m : M) :
    mvPolynomialCoefficientFormCoordinate k σ M n s
      (m ⊗ₜ[A] exteriorPower.ιMulti A n (fun j =>
        D k A (MvPolynomial.X (Set.powersetCard.ofFinEmbEquiv.symm s j)))) = m := by
  rw [mvPolynomialCoefficientFormCoordinate_tmul, mvPolynomialFormCoordinate_basis, one_smul]

end Coordinates

end Coefficients

end KaehlerDifferential
