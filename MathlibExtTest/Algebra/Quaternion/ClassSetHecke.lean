/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
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

example {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ} (d : EmbeddingDatum Λ t n) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈
      finiteIdeleQuadUnits d := by
  show (1 : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) ∈ finiteIdeleQuadUnits d
  exact one_mem _

/-! ### The norm ideal of the Lipschitz order -/

/-- The Lipschitz order in `ℍ[ℚ, -1, -1]`, spanned over `ℤ` by `1, i, j, k`. -/
private def lipschitzOrder : Submodule ℤ ℍ[ℚ, -1, -1] :=
  Submodule.span ℤ {(1 : ℍ[ℚ, -1, -1]), ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩,
    ⟨0, 0, 0, 1⟩}

private theorem mem_lipschitzOrder_mk (m n p r : ℤ) :
    (⟨(m : ℚ), (n : ℚ), (p : ℚ), (r : ℚ)⟩ : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder := by
  have h1 : (1 : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder :=
    Submodule.subset_span (by simp)
  have hi : (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder :=
    Submodule.subset_span (by simp)
  have hj : (⟨0, 0, 1, 0⟩ : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder :=
    Submodule.subset_span (by simp)
  have hk : (⟨0, 0, 0, 1⟩ : ℍ[ℚ, -1, -1]) ∈ lipschitzOrder :=
    Submodule.subset_span (by simp)
  have heq : (⟨(m : ℚ), (n : ℚ), (p : ℚ), (r : ℚ)⟩ : ℍ[ℚ, -1, -1]) =
      m • (1 : ℍ[ℚ, -1, -1]) + n • (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -1, -1]) +
        p • (⟨0, 0, 1, 0⟩ : ℍ[ℚ, -1, -1]) +
        r • (⟨0, 0, 0, 1⟩ : ℍ[ℚ, -1, -1]) := by
    ext <;> simp
  rw [heq]
  exact add_mem (add_mem (add_mem (Submodule.smul_mem _ _ h1)
    (Submodule.smul_mem _ _ hi)) (Submodule.smul_mem _ _ hj))
    (Submodule.smul_mem _ _ hk)

/-- The Lipschitz order is an order: it contains `1`, is closed under multiplication, spans
`ℍ[ℚ, -1, -1]` over `ℚ` and is finitely generated over `ℤ`. -/
private theorem lipschitzOrder_isOrder : IsOrder lipschitzOrder := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Submodule.subset_span
    simp
  · intro x y hx hy
    induction hx using Submodule.span_induction with
    | mem u hu =>
      induction hy using Submodule.span_induction with
      | mem v hv =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        obtain rfl | rfl | rfl | rfl := hu <;>
          obtain rfl | rfl | rfl | rfl := hv <;>
          (norm_num [QuaternionAlgebra.mk_mul_mk]; first
            | exact mem_lipschitzOrder_mk 1 0 0 0
            | exact mem_lipschitzOrder_mk 0 1 0 0
            | exact mem_lipschitzOrder_mk 0 0 1 0
            | exact mem_lipschitzOrder_mk 0 0 0 1
            | exact mem_lipschitzOrder_mk (-1) 0 0 0
            | exact mem_lipschitzOrder_mk 0 (-1) 0 0
            | exact mem_lipschitzOrder_mk 0 0 (-1) 0
            | exact mem_lipschitzOrder_mk 0 0 0 (-1))
      | zero => simp
      | add v w _ _ hv hw => rw [mul_add]; exact add_mem hv hw
      | smul c v _ hv => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hv
    | zero => simp
    | add u v _ _ hu hv => rw [add_mul]; exact add_mem hu hv
    | smul c u _ hu => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hu
  · refine top_unique fun q _ => ?_
    have hg : ∀ g : ℍ[ℚ, -1, -1], g ∈ ({(1 : ℍ[ℚ, -1, -1]), ⟨0, 1, 0, 0⟩,
        ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩} : Set ℍ[ℚ, -1, -1]) →
        g ∈ Submodule.span ℚ (lipschitzOrder : Set ℍ[ℚ, -1, -1]) :=
      fun g hg => Submodule.subset_span (Submodule.subset_span hg)
    have hq : q = q.re • (1 : ℍ[ℚ, -1, -1]) + q.imI • ⟨0, 1, 0, 0⟩ +
        q.imJ • ⟨0, 0, 1, 0⟩ + q.imK • ⟨0, 0, 0, 1⟩ := by
      ext <;> simp
    rw [hq]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_ <;>
      exact Submodule.smul_mem _ _ (hg _ (by simp))
  · apply Submodule.fg_span
    exact Set.finite_insert.2 (Set.finite_insert.2
      (Set.finite_insert.2 (Set.finite_singleton _)))

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

/-- The norm ideal of the Lipschitz order at `2` lies in the order. -/
example : normIdeal lipschitzOrder 2 ≤ lipschitzOrder :=
  lipschitzOrder_isOrder.normIdeal_le 2

/-- It contains `2 x` for every `x` in the order. -/
example {x : ℍ[ℚ, -1, -1]} (hx : x ∈ lipschitzOrder) :
    (2 : ℍ[ℚ, -1, -1]) * x ∈ normIdeal lipschitzOrder 2 := by
  exact_mod_cast lipschitzOrder_isOrder.natCast_mul_mem_normIdeal 2 hx

/-- It contains `1 + i`, whose reduced norm is `2`. -/
example : (⟨1, 1, 0, 0⟩ : ℍ[ℚ, -1, -1]) ∈ normIdeal lipschitzOrder 2 := by
  have h := mul_mul_mem_normIdeal (q := 2) lipschitzOrder_isOrder.one_mem
    (mem_lipschitzOrder_mk 1 1 0 0) lipschitzOrder_isOrder.one_mem 1 (by norm_num [nrd])
  simpa using h

/-- The sum of the four coordinates of a quaternion in `ℍ[ℚ, -1, -1]`. -/
private def coordSum (x : ℍ[ℚ, -1, -1]) : ℚ := x.re + x.imI + x.imJ + x.imK

private theorem exists_coordSum_eq {x : ℍ[ℚ, -1, -1]} (hx : x ∈ lipschitzOrder) :
    ∃ k : ℤ, coordSum x = k := by
  obtain ⟨m, n, p, r, rfl⟩ := exists_eq_mk_of_mem_lipschitzOrder hx
  exact ⟨m + n + p + r, by simp [coordSum]⟩

/-- On the Lipschitz order the coordinate sum is multiplicative modulo `2`. -/
private theorem exists_coordSum_mul_eq {x y : ℍ[ℚ, -1, -1]} (hx : x ∈ lipschitzOrder)
    (hy : y ∈ lipschitzOrder) :
    ∃ k : ℤ, coordSum (x * y) = coordSum x * coordSum y + 2 * k := by
  obtain ⟨m, n, p, r, rfl⟩ := exists_eq_mk_of_mem_lipschitzOrder hx
  obtain ⟨m', n', p', r', rfl⟩ := exists_eq_mk_of_mem_lipschitzOrder hy
  refine ⟨-(n * n' + p * p' + r * r' + r * p' + n * r' + p * n'), ?_⟩
  simp only [coordSum, QuaternionAlgebra.mk_mul_mk]
  push_cast
  ring

/-- An element of the Lipschitz order of even reduced norm has even coordinate sum. -/
private theorem exists_coordSum_eq_two_mul {y : ℍ[ℚ, -1, -1]} (hy : y ∈ lipschitzOrder)
    {m : ℤ} (hm : nrd y = ((2 : ℕ) : ℚ) * m) : ∃ k : ℤ, coordSum y = 2 * k := by
  obtain ⟨y₀, y₁, y₂, y₃, rfl⟩ := exists_eq_mk_of_mem_lipschitzOrder hy
  obtain ⟨e₀, he₀⟩ := Int.even_mul_pred_self y₀
  obtain ⟨e₁, he₁⟩ := Int.even_mul_pred_self y₁
  obtain ⟨e₂, he₂⟩ := Int.even_mul_pred_self y₂
  obtain ⟨e₃, he₃⟩ := Int.even_mul_pred_self y₃
  refine ⟨m - e₀ - e₁ - e₂ - e₃, ?_⟩
  have h₀ : ((y₀ : ℚ) * (y₀ - 1)) = e₀ + e₀ := by exact_mod_cast he₀
  have h₁ : ((y₁ : ℚ) * (y₁ - 1)) = e₁ + e₁ := by exact_mod_cast he₁
  have h₂ : ((y₂ : ℚ) * (y₂ - 1)) = e₂ + e₂ := by exact_mod_cast he₂
  have h₃ : ((y₃ : ℚ) * (y₃ - 1)) = e₃ + e₃ := by exact_mod_cast he₃
  simp only [nrd_mk] at hm
  simp only [coordSum]
  push_cast at hm ⊢
  linear_combination hm - h₀ - h₁ - h₂ - h₃

/-- The norm ideal of the Lipschitz order at `2` is proper: each of its elements has even
coordinate sum, while `1` has coordinate sum `1`. -/
example : (1 : ℍ[ℚ, -1, -1]) ∉ normIdeal lipschitzOrder 2 := by
  have key : ∀ w ∈ normIdeal lipschitzOrder 2, ∃ k : ℤ, coordSum w = 2 * k := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, y, hy, z, hz, ⟨m, hm⟩, rfl⟩ := hw
      obtain ⟨k₁, hk₁⟩ := exists_coordSum_mul_eq (lipschitzOrder_isOrder.mul_mem hx hy) hz
      obtain ⟨k₂, hk₂⟩ := exists_coordSum_mul_eq hx hy
      obtain ⟨k₃, hk₃⟩ := exists_coordSum_eq_two_mul hy hm
      obtain ⟨cx, hcx⟩ := exists_coordSum_eq hx
      obtain ⟨cz, hcz⟩ := exists_coordSum_eq hz
      refine ⟨cx * k₃ * cz + k₂ * cz + k₁, ?_⟩
      rw [hk₁, hk₂, hk₃, hcx, hcz]
      push_cast
      ring
    | zero => exact ⟨0, by simp [coordSum]⟩
    | add u v _ _ hu hv =>
      obtain ⟨k, hk⟩ := hu
      obtain ⟨k', hk'⟩ := hv
      refine ⟨k + k', ?_⟩
      simp only [coordSum, QuaternionAlgebra.re_add, QuaternionAlgebra.imI_add,
        QuaternionAlgebra.imJ_add, QuaternionAlgebra.imK_add] at hk hk' ⊢
      push_cast
      linear_combination hk + hk'
    | smul c u _ hu =>
      obtain ⟨k, hk⟩ := hu
      refine ⟨c * k, ?_⟩
      simp only [coordSum] at hk ⊢
      simp only [zsmul_eq_mul, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, QuaternionAlgebra.re_intCast, QuaternionAlgebra.imI_intCast,
        QuaternionAlgebra.imJ_intCast, QuaternionAlgebra.imK_intCast]
      push_cast
      linear_combination (c : ℚ) * hk
  intro h1
  obtain ⟨k, hk⟩ := key 1 h1
  have hk' : (1 : ℚ) = 2 * k := by simpa [coordSum] using hk
  have hk'' : (1 : ℤ) = 2 * k := by exact_mod_cast hk'
  omega

/-! ### The Hecke kernel -/

/-- For a set stable under left multiplication by `U`, the incidence count does not see a
change of representative within a class. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (δ : (ℍ[ℚ, a, b])ˣ) (x u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : u ∈ U)
    (y : ClassSet U) :
    heckeKernel U S hS (ClassSet.mk U (Submodule.finiteIdeleDiagonal _ δ * x * u)) y =
      ENat.card (HeckeIncidence U S x y) := by
  rw [ClassSet.mk_mul_of_mem _ u hu, ClassSet.mk_diagonal_mul, heckeKernel_mk]

/-- For `S = U`, the Hecke kernel is `1` at a pair of equal classes. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    heckeKernel U U (fun _ hu _ hs => mul_mem hu hs) (ClassSet.mk U x) (ClassSet.mk U x) = 1 := by
  rw [heckeKernel_mk, ENat.card_eq_one_iff_unique]
  refine ⟨{ default := ⟨((1 : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _ ⧸ U),
      1, one_mem U, rfl, by rw [mul_one]⟩, uniq := ?_ }⟩
  rintro ⟨c, h, hh, rfl, -⟩
  exact Subtype.ext (QuotientGroup.eq.mpr (by simpa using inv_mem hh))

/-- For `S = U`, the Hecke kernel is `0` at a pair of distinct classes. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U)
    (hy : y ≠ ClassSet.mk U x) :
    heckeKernel U U (fun _ hu _ hs => mul_mem hu hs) (ClassSet.mk U x) y = 0 := by
  rw [heckeKernel_mk, ENat.card_eq_zero_iff_empty]
  exact ⟨fun ⟨_, h, hh, _, hxy⟩ => hy (hxy.symm.trans (ClassSet.mk_mul_of_mem x h hh))⟩

/-- An infinite incidence set gives the Hecke kernel `⊤`, not `0`. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U)
    [Infinite (HeckeIncidence U S x y)] : heckeKernel U S hS (ClassSet.mk U x) y = ⊤ := by
  rw [heckeKernel_mk]
  exact ENat.card_eq_top_of_infinite

/-- The kernel is `⊤` exactly when the incidence set is infinite. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U) :
    heckeKernel U S hS (ClassSet.mk U x) y = ⊤ ↔ Infinite (HeckeIncidence U S x y) := by
  rw [heckeKernel_mk]
  exact ENat.card_eq_top

/-- A finite incidence set gives its number of cosets. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (S : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hS : ∀ u ∈ U, ∀ s ∈ S, u * s ∈ S)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (y : ClassSet U)
    [Finite (HeckeIncidence U S x y)] :
    heckeKernel U S hS (ClassSet.mk U x) y = Nat.card (HeckeIncidence U S x y) := by
  rw [heckeKernel_mk]
  exact ENat.card_eq_coe_natCard _

/-- The empty set has Hecke kernel `0`. -/
example (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x y : ClassSet U) :
    heckeKernel U ∅ (fun _ _ s hs => absurd hs (Set.notMem_empty s)) x y = 0 := by
  obtain ⟨x, rfl⟩ := ClassSet.mk_surjective x
  rw [heckeKernel_mk]
  exact (ENat.card_eq_zero_iff_empty _).mpr ⟨fun ⟨_, _, h, _⟩ => Set.notMem_empty _ h⟩

/-! ### The idelic embedding constructions take a non-scalar element

They take an embedding datum, whose element `α` is never a scalar. So the adelic quadratic subring
contains `α ⊗ 1`, which is not a central scalar `1 ⊗ r`; for a scalar such as `α = 1` the subring
would be `1 ⊗ 𝔸_f`, and every finite idele would lie in the embedding set. -/

/-- The element of an embedding datum lies outside the `ℚ`-span of `1`. -/
private theorem val_notMem_span_one {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ}
    (d : EmbeddingDatum Λ t n) : d.1 ∉ Submodule.span ℚ {(1 : ℍ[ℚ, a, b])} := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  have h1 := (LinearIndependent.pair_iff.mp d.2.2.2 c (-1)
    (by rw [← hc, neg_one_smul, add_neg_cancel])).2
  norm_num at h1

/-- No embedding datum has the element `1`. -/
example {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ} (d : EmbeddingDatum Λ t n) : d.1 ≠ 1 :=
  fun h => val_notMem_span_one d (by rw [h]; exact Submodule.mem_span_singleton_self 1)

private theorem one_ne_zero_finiteAdeleRing : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ≠ 0 := fun h =>
  one_ne_zero (congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ =>
    x (Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩)) h)

/-- The adelic quadratic subring of an embedding datum contains `α ⊗ 1`, which is not a central
scalar `1 ⊗ r`. -/
example {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ} (d : EmbeddingDatum Λ t n) :
    d.1 ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ finiteAdeleQuadSubring d ∧
      d.1 ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∉
        Set.range (fun r : FiniteAdeleRing (𝓞 ℚ) ℚ => (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) := by
  refine ⟨Subring.subset_closure (Or.inl rfl), ?_⟩
  rintro ⟨r, hr⟩
  obtain ⟨f, hfα, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem (val_notMem_span_one d)
    inferInstance
  have hf1 : f 1 = 0 := by
    have h := Submodule.mem_map_of_mem (f := f) (Submodule.mem_span_singleton_self (1 : ℍ[ℚ, a, b]))
    rwa [hf, Submodule.mem_bot] at h
  have h := congrArg (fun x => TensorProduct.lid ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
    (f.rTensor (FiniteAdeleRing (𝓞 ℚ) ℚ) x)) hr
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, hf1, zero_smul] at h
  have h2 : (f d.1)⁻¹ • (f d.1 • (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) = 0 := by rw [← h, smul_zero]
  rw [smul_smul, inv_mul_cancel₀ hfα, one_smul] at h2
  exact one_ne_zero_finiteAdeleRing h2

/-- `i` is an embedding datum of the Lipschitz order, with `i² - 0 i + 1 = 0`. -/
private def lipschitzI : EmbeddingDatum lipschitzOrder 0 1 :=
  ⟨⟨0, 1, 0, 0⟩, by simpa using mem_lipschitzOrder_mk 0 1 0 0,
    by ext <;> simp [QuaternionAlgebra.mk_mul_mk],
    by
      refine LinearIndependent.pair_iff.mpr fun s u h => ?_
      have h0 := congrArg QuaternionAlgebra.re h
      have h1 := congrArg QuaternionAlgebra.imI h
      simp at h0 h1
      exact ⟨h0, h1⟩⟩

/-- For the Lipschitz order and `i`, the identity idele lies in the idelic embedding set, so the
idelic embedding class set is nonempty. -/
example : Nonempty (IdelicEmbeddingClassSet lipschitzOrder lipschitzI) :=
  ⟨⟨DoubleCoset.mk _ _ 1, 1, fun y _ => by simp, rfl⟩⟩

end QuaternionAlgebra

end
