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

private theorem exactSource_classSet_mk
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

/-- Zero is never an embedding conductor. -/
example (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) :
    ¬ HasEmbeddingConductor Λ α 0 :=
  fun h => lt_irrefl 0 h.1

/-- So no embedding class is counted with conductor zero. -/
example (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : condEmbeddingCount Λ t n 0 = 0 :=
  Nat.card_eq_zero.mpr (Or.inl ⟨fun ⟨_, _, _, h⟩ => lt_irrefl 0 h.1⟩)

/-- The Lipschitz order in `ℍ[ℚ, -1, -1]`, spanned over `ℤ` by `1, i, j, k`. -/
private def lipschitzOrder : Submodule ℤ ℍ[ℚ, -1, -1] :=
  Submodule.span ℤ {(1 : ℍ[ℚ, -1, -1]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩,
    ⟨0, 0, 0, 1⟩}

private theorem exists_eq_mk_of_mem_lipschitzOrder {x : ℍ[ℚ, -1, -1]}
    (hx : x ∈ lipschitzOrder) :
    ∃ m n p r : ℤ, x = ⟨(m : ℚ), (n : ℚ), (p : ℚ), (r : ℚ)⟩ := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    obtain rfl | rfl | rfl | rfl := hu
    · exact ⟨1, 0, 0, 0, by ext <;> simp⟩
    · exact ⟨0, 1, 0, 0, by ext <;> simp⟩
    · exact ⟨0, 0, 1, 0, by ext <;> simp⟩
    · exact ⟨0, 0, 0, 1, by ext <;> simp⟩
  | zero => exact ⟨0, 0, 0, 0, by ext <;> simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨m, n, p, r, rfl⟩ := hu
    obtain ⟨m', n', p', r', rfl⟩ := hv
    exact ⟨m + m', n + n', p + p', r + r', by ext <;> simp⟩
  | smul c u _ hu =>
    obtain ⟨m, n, p, r, rfl⟩ := hu
    exact ⟨c * m, c * n, c * p, c * r, by ext <;> simp⟩

/-- The embedding `i ↦ i` of `ℤ[i]` into the Lipschitz order has conductor `1`,
the least value the conductor can take. -/
example :
    EmbeddingDatum.HasConductor (Λ := lipschitzOrder) (t := 0) (n := 1)
      ⟨⟨0, 1, 0, 0⟩, Submodule.subset_span (by simp), by
        rw [isQuadraticDatum_iff]; ext <;> simp⟩ 1 := by
  refine ⟨one_pos, fun x hx ⟨c, e, hce⟩ => ?_, fun g hg hg1 => absurd hg1 (by omega)⟩
  obtain ⟨m, n, p, r, rfl⟩ := exists_eq_mk_of_mem_lipschitzOrder hx
  have hp : p = 0 := by simpa using congrArg QuaternionAlgebra.imJ hce
  have hr : r = 0 := by simpa using congrArg QuaternionAlgebra.imK hce
  subst hp hr
  exact ⟨m, n, by ext <;> simp⟩

/-- An infinite incidence set gives the Hecke kernel `⊤`, not `0`. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x y : ClassSet U)
    [Infinite (HeckeIncidence U S x.out y)] : heckeKernel U S x y = ⊤ :=
  ENat.card_eq_top_of_infinite

/-- The kernel is `⊤` exactly when the incidence set is infinite. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x y : ClassSet U) :
    heckeKernel U S x y = ⊤ ↔ Infinite (HeckeIncidence U S x.out y) :=
  ENat.card_eq_top

/-- A finite incidence set gives its number of cosets. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x y : ClassSet U)
    [Finite (HeckeIncidence U S x.out y)] :
    heckeKernel U S x y = Nat.card (HeckeIncidence U S x.out y) :=
  ENat.card_eq_coe_natCard _

/-- The empty set has Hecke kernel `0`. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x y : ClassSet U) :
    heckeKernel U ∅ x y = 0 :=
  (ENat.card_eq_zero_iff_empty _).mpr ⟨fun ⟨_, _, h, _⟩ => Set.notMem_empty _ h⟩

end QuaternionAlgebra

end
