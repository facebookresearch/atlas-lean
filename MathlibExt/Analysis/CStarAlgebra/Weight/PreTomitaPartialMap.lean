/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Weight.PreTomita
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Complex and real partial maps for the pre-Tomita operator

For a faithful extended positive weight on a nonunital complex C-star algebra, let `C_φ=Λ({x :
φ(x* x)<∞ ∧ φ(x x*)<∞})` in the GNS Hilbert space. The pre-Tomita operator `S₀Λ(x)=Λ(x*)`
defines a complex conjugate-linear partial map with domain `C_φ`.

Restricting scalars gives a real-linear partial map on the same Hilbert space and the same
domain, since complex conjugation fixes real scalars. Both maps retain the Hilbert norm topology
and the values of `S₀`. Density, closability, closure and polar decomposition are separate
properties, not part of these partial-map definitions.

Source: Connes, Noncommutative Geometry (1994), V.3 Definition 6 and the NSF-weight core
paragraph, OCR 14358--14386.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Conjugate-linear partial pre-Tomita map.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. `preTomitaPMap φ : H_φ →ₛₗ.[conj] H_φ` has domain `C_φ` and value
`S₀Λ(x)=Λ(x*)` for `x ∈ D_φ`; no domain density or closability is required. -/
def Weight.preTomitaPMap (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.GNS →ₛₗ.[starRingEnd ℂ] φ.GNS where
  domain := φ.tomitaCore
  toFun := φ.preTomitaOperator hφ

/-- **Domain of the complex pre-Tomita partial map.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. the domain of `preTomitaPMap φ` is exactly the complex submodule
`C_φ=Λ(D_φ)`. -/
@[simp]
theorem Weight.preTomitaPMap_domain (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    (φ.preTomitaPMap hφ).domain = φ.tomitaCore :=
  rfl

/-- **Value of the complex partial pre-Tomita map.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. for `x ∈ D_φ`, `preTomitaPMap φ (e(x))=Λ(x*)`. -/
theorem Weight.preTomitaPMap_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    φ.preTomitaPMap hφ (φ.tomitaCoreEquiv hφ x) = φ.finiteStarSquareGNSMap (star x) :=
  φ.preTomitaOperator_apply hφ x

/-- **Real-linear partial pre-Tomita map.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let
`H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear map `Λ :
n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put `D_φ={x ∈ n_φ
: x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`.
`preTomitaRealPMap φ : H_φ →ₗ.[ℝ] H_φ` has domain `C_φ` with scalars restricted to `ℝ`, and
value `S₀Λ(x)=Λ(x*)`. The Hilbert norm and topology are unchanged. -/
def Weight.preTomitaRealPMap (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.GNS →ₗ.[ℝ] φ.GNS where
  domain := φ.tomitaCore.restrictScalars ℝ
  toFun := {
    toFun ξ := φ.preTomitaOperator hφ ⟨ξ.val, ξ.property⟩
    map_add' := by
      intro ξ η
      change φ.preTomitaOperator hφ
        ((⟨ξ.val, ξ.property⟩ : φ.tomitaCore) + ⟨η.val, η.property⟩) = _
      exact (φ.preTomitaOperator hφ).map_add _ _
    map_smul' := by
      intro c ξ
      let ζ : φ.tomitaCore := ⟨ξ.val, ξ.property⟩
      change φ.preTomitaOperator hφ (c • ζ) = c • φ.preTomitaOperator hφ ζ
      rw [← algebraMap_smul ℂ c ζ]
      have hs : φ.preTomitaOperator hφ (algebraMap ℝ ℂ c • ζ) =
          star (algebraMap ℝ ℂ c) • φ.preTomitaOperator hφ ζ :=
        (φ.preTomitaOperator hφ).map_smul' (algebraMap ℝ ℂ c) ζ
      have hc : star (algebraMap ℝ ℂ c) = algebraMap ℝ ℂ c := by simp
      calc
        φ.preTomitaOperator hφ (algebraMap ℝ ℂ c • ζ) =
            star (algebraMap ℝ ℂ c) • φ.preTomitaOperator hφ ζ := hs
        _ = c • φ.preTomitaOperator hφ ζ := by
          rw [hc]
          exact algebraMap_smul ℂ c (φ.preTomitaOperator hφ ζ)
  }

/-- **Real domain of the pre-Tomita partial map.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. the domain of `preTomitaRealPMap φ` is `C_φ.restrictScalars ℝ`, containing
the same Hilbert vectors as the complex domain. -/
@[simp]
theorem Weight.preTomitaRealPMap_domain (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    (φ.preTomitaRealPMap hφ).domain = φ.tomitaCore.restrictScalars ℝ :=
  rfl

/-- **Real partial map agrees with the semilinear operator.** Let `A` be a nonunital complex
C-star algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real
homogeneous weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x*
x)).toReal` for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with
dense complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every
positive `a : A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear
equivalence `e : D_φ ≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `ξ ∈ C_φ.restrictScalars ℝ`,
`preTomitaRealPMap φ ξ=preTomitaOperator φ ξ`, regarding the domain vector as a member of
`C_φ`. -/
theorem Weight.preTomitaRealPMap_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ : φ.tomitaCore.restrictScalars ℝ) :
    φ.preTomitaRealPMap hφ ξ = φ.preTomitaOperator hφ ⟨ξ.val, ξ.property⟩ :=
  rfl

/-- **Pre-Tomita formula after restricting scalars.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `x ∈ D_φ`, `preTomitaRealPMap φ (e(x))=Λ(x*)`, exactly as for the
complex partial map. -/
theorem Weight.preTomitaRealPMap_originalValue (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    φ.preTomitaRealPMap hφ (φ.tomitaCoreEquiv hφ x) = φ.finiteStarSquareGNSMap (star x) :=
  φ.preTomitaOperator_apply hφ x

end

end CStarAlgebra.ScalarWeight
