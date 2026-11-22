/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RingTheory.Adjoin.LinearRelations
import Mathlib.Data.Matrix.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
/-! Consumers and source-shape regressions for algebra maps from generators. -/

open Algebra

-- The two source signatures, with independent universe-polymorphic types.
example {K : Type*} [Field K] {F : Type*} [CommRing F] [Algebra K F]
    (L : Type*) [CommRing L] [Algebra K L]
    {ι : Type*} (t : ι → F) (a : ι → L)
    (hone : ∃ i₀, t i₀ = 1 ∧ a i₀ = 1)
    (hmul : ∀ i j, ∃ k, t k = t i * t j ∧ a k = a i * a j)
    (hcons : ∀ (n : ℕ) (idx : Fin n → ι) (c : Fin n → K),
      ∑ l, c l • t (idx l) = 0 → ∑ l, c l • a (idx l) = 0) :
    ∃ χ : adjoin K (Set.range t) →ₐ[K] L,
      ∀ i, χ ⟨t i, subset_adjoin (Set.mem_range_self i)⟩ = a i :=
  exists_algHom_adjoin_of_linearRelations L t a hone hmul hcons

example {κ : Type*} [Field κ] {B : Type*} [Ring B] [Algebra κ B]
    {ι : Type*} (c : ι → (B →ₗ[κ] κ)) (hc : ∀ b : B, (∀ i, c i b = 0) → b = 0)
    {T : Type*} [CommRing T] (red : T →+* B) (ρ : T →+* κ)
    (hbot : ∀ (t : T) (i : ι), c i (red t) ∈ (⊥ : Subfield κ))
    (hker : ∀ t : T, red t = 0 → ρ t = 0) :
    ∃ χ : adjoin κ (Set.range red) →ₐ[κ] κ,
      ∀ t : T, χ ⟨red t, subset_adjoin (Set.mem_range_self t)⟩ = ρ t :=
  exists_algHom_adjoin_of_primeSubfield c hc red ρ hbot hker

namespace LinearRelationsTest

-- Idempotent splitting: construct a hom out of a product algebra from a
-- linear assignment, rather than assuming a preexisting algebra hom.
private def splitLinear {L : Type*} [CommRing L] [Algebra ℚ L] (e : L) :
    (ℚ × ℚ) →ₗ[ℚ] L where
  toFun x := x.1 • e + x.2 • (1 - e)
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' r x := by simp [smul_add, smul_smul]

private theorem splitMap (L : Type*) [CommRing L] [Algebra ℚ L]
    (e : L) (he : e * e = e) :
    ∃ χ : adjoin ℚ (Set.range (id : ℚ × ℚ → ℚ × ℚ)) →ₐ[ℚ] L,
      ∀ x, χ ⟨x, subset_adjoin (Set.mem_range_self x)⟩ =
        x.1 • e + x.2 • (1 - e) := by
  apply exists_algHom_adjoin_of_linearRelations L id (splitLinear e)
  · exact ⟨1, rfl, by simp [splitLinear]⟩
  · intro x y
    refine ⟨x * y, rfl, ?_⟩
    change (x.1 * y.1) • e + (x.2 * y.2) • (1 - e) =
      (x.1 • e + x.2 • (1 - e)) * (y.1 • e + y.2 • (1 - e))
    simp only [Algebra.smul_def, map_mul]
    linear_combination
      (-algebraMap ℚ L x.1 * algebraMap ℚ L y.1 +
        algebraMap ℚ L x.1 * algebraMap ℚ L y.2 +
        algebraMap ℚ L x.2 * algebraMap ℚ L y.1 -
        algebraMap ℚ L x.2 * algebraMap ℚ L y.2) * he
  · intro n idx c h
    change ∑ i, c i • idx i = 0 at h
    simpa only [map_sum, map_smul, map_zero] using congrArg (splitLinear e) h

-- A target with zero divisors is admitted. The resulting map fixes the two
-- complementary idempotents, and sends (3,5) to (3,5).
example : ∃ χ : adjoin ℚ (Set.range (id : ℚ × ℚ → ℚ × ℚ)) →ₐ[ℚ] (ℚ × ℚ),
    χ ⟨(3, 5), subset_adjoin (Set.mem_range_self (3, 5))⟩ = (3, 5) := by
  obtain ⟨χ, hχ⟩ := splitMap (ℚ × ℚ) (1, 0) (by ext <;> norm_num)
  refine ⟨χ, (hχ (3, 5)).trans ?_⟩
  ext <;> norm_num

-- Character on an integral diagonal ring inside a NONCOMMUTATIVE ambient
-- complex matrix algebra. Complex coefficients are not all in the prime field.
private def diagonalIntegers : (Fin 2 → ℤ) →+* Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix.diagonalRingHom (Fin 2) ℂ).comp
    (RingHom.pi fun i : Fin 2 => (Int.castRingHom ℂ).comp (Pi.evalRingHom _ i))

private def firstCoordinate : (Fin 2 → ℤ) →+* ℂ :=
  (Int.castRingHom ℂ).comp (Pi.evalRingHom _ 0)

private theorem diagonalCharacter :
    ∃ χ : adjoin ℂ (Set.range diagonalIntegers) →ₐ[ℂ] ℂ,
      ∀ t, χ ⟨diagonalIntegers t, subset_adjoin (Set.mem_range_self t)⟩ = (t 0 : ℂ) := by
  apply exists_algHom_adjoin_of_primeSubfield
    (fun ij : Fin 2 × Fin 2 => Matrix.entryLinearMap ℂ ℂ ij.1 ij.2)
    (fun b hb => by ext i j; exact hb (i, j)) diagonalIntegers firstCoordinate
  · intro t ij
    change Matrix.diagonal (fun i => (t i : ℂ)) ij.1 ij.2 ∈ (⊥ : Subfield ℂ)
    by_cases h : ij.1 = ij.2
    · rw [h, Matrix.diagonal_apply_eq]
      exact intCast_mem _ _
    · simp [Matrix.diagonal_apply_ne _ h]
  · intro t ht
    have h := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ => m 0 0) ht
    change Matrix.diagonal (fun i => (t i : ℂ)) 0 0 = 0 at h
    exact h

example : ∃ χ : adjoin ℂ (Set.range diagonalIntegers) →ₐ[ℂ] ℂ,
    χ ⟨diagonalIntegers ![3, 5], subset_adjoin (Set.mem_range_self ![3, 5])⟩ = 3 := by
  obtain ⟨χ, hχ⟩ := diagonalCharacter
  exact ⟨χ, by simpa using hχ ![3, 5]⟩

-- Empty sums and repeated generators are genuine instances of the relation
-- premise, not a hidden linear-independence hypothesis on the indexing map.
example (n : ℕ) (idx : Fin n → ℚ × ℚ) (c : Fin n → ℚ)
    (h : ∑ i, c i • idx i = 0) : ∑ i, c i • splitLinear (1 : ℚ) (idx i) = 0 := by
  simpa only [map_sum, map_smul, map_zero] using congrArg (splitLinear (1 : ℚ)) h

example : (∑ _i : Fin 0, (1 : ℚ) • (id : ℚ × ℚ → ℚ × ℚ) (0, 0)) = 0 := by simp
example (x : ℚ × ℚ) : (1 : ℚ) • x + (-1 : ℚ) • x = 0 := by simp

-- A multiplicative, unital assignment need not preserve linear relations:
-- squaring rational scalars violates 1 + 1 - 2 = 0.
example : (1 : ℚ) + 1 - 2 = 0 ∧ (1 : ℚ)^2 + 1^2 - 2^2 ≠ 0 := by norm_num

-- Without the unit premise, the zero assignment preserves products and all
-- linear relations, but cannot be the values of a unital algebra map.
example : ¬ ∃ χ : adjoin ℚ (Set.range (id : ℚ → ℚ)) →ₐ[ℚ] ℚ,
    χ ⟨1, subset_adjoin (Set.mem_range_self 1)⟩ = 0 := by
  rintro ⟨χ, h⟩
  change χ 1 = 0 at h
  simp at h

-- If the indexing type is empty, the common unit witness is impossible.
example (t a : Empty → ℚ) : ¬ ∃ i, t i = 1 ∧ a i = 1 := by simp

-- Positive characteristic and a noninjective source map: 5 maps to zero.
example : ∃ χ : adjoin (ZMod 5) (Set.range (Int.castRingHom (ZMod 5))) →ₐ[ZMod 5] ZMod 5,
    χ ⟨(2 : ZMod 5), subset_adjoin (Set.mem_range_self (2 : ℤ))⟩ = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := exists_algHom_adjoin_of_primeSubfield
    (fun _ : Unit => LinearMap.id (R := ZMod 5) (M := ZMod 5))
    (fun b hb => hb ()) (Int.castRingHom (ZMod 5)) (Int.castRingHom (ZMod 5))
    (fun t _ => show (t : ZMod 5) ∈ (⊥ : Subfield (ZMod 5)) from intCast_mem _ t)
    (fun t h => show Int.castRingHom (ZMod 5) t = 0 from h)
  obtain ⟨χ, hχ⟩ := h
  exact ⟨χ, hχ 2⟩

example : Int.castRingHom (ZMod 5) 5 = 0 := by
  exact_mod_cast ZMod.natCast_self 5

-- The prime-subfield condition cannot be discarded: conjugation is a ring
-- automorphism of C, but cannot be the restriction of a C-algebra hom.
example : ¬ ∃ χ : adjoin ℂ (Set.range (RingHom.id ℂ)) →ₐ[ℂ] ℂ,
    χ ⟨Complex.I, subset_adjoin (Set.mem_range_self Complex.I)⟩ = -Complex.I := by
  rintro ⟨χ, h⟩
  change χ (algebraMap ℂ _ Complex.I) = -Complex.I at h
  rw [AlgHom.commutes] at h
  have hi := congrArg Complex.im h
  norm_num at hi

end LinearRelationsTest
