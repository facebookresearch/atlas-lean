/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.ClassSetHecke

@[expose] public section

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace QuaternionAlgebra

variable {a b : ℚ}

theorem exactSource_classSet_mk
    (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Function.Surjective (ClassSet.mk U) :=
  ClassSet.mk_surjective

example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ClassSet.mk U x ∈ Set.univ := trivial

example (Λ : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ)
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    h ∈ primeHeckeSet Λ ℓ ↔
      (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
      (ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ∧
      ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)
        ∉ Submodule.finiteAdeleBox Λ ∧
      (ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∉
        Submodule.finiteAdeleBox Λ :=
  mem_primeHeckeSet_iff Λ ℓ h

/-- Nontrivial instance: the top submodule is an order, so the norm ideal
API applies to it. -/
example {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ) :
    normIdeal Λ q ≤ Λ :=
  hΛ.normIdeal_le q

example {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (q : ℕ)
    {x : ℍ[ℚ, a, b]} (hx : x ∈ Λ) : (q : ℍ[ℚ, a, b]) * x ∈ normIdeal Λ q :=
  hΛ.natCast_mul_mem_normIdeal q hx

example {x y z : ℍ[ℚ, a, b]} (hx : x ∈ (⊤ : Submodule ℤ ℍ[ℚ, a, b]))
    (hy : y ∈ (⊤ : Submodule ℤ ℍ[ℚ, a, b])) (hz : z ∈ (⊤ : Submodule ℤ ℍ[ℚ, a, b]))
    (m : ℤ) (hm : nrd y = ((5 : ℕ) : ℚ) * m) :
    x * y * z ∈ normIdeal (⊤ : Submodule ℤ ℍ[ℚ, a, b]) 5 :=
  mul_mul_mem_normIdeal hx hy hz m hm

example (α : ℍ[ℚ, a, b]) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈
      finiteIdeleQuadUnits α := by
  show (1 : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ finiteIdeleQuadUnits α
  exact one_mem _

end QuaternionAlgebra

end
