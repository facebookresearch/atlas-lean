/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.IntermediateField.AdjoinAlgHomTranscendental
import Mathlib.FieldTheory.RatFunc.IntermediateField

@[expose] public section

-- `exactSource` consumer, with the original binders.
example
    (K : Type*) {L L' : Type*} [Field K] [Field L] [Algebra K L] [Field L'] [Algebra K L']
    (G : Set L) (h1 : (1 : L) ∈ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (θ : L → L') (hθ : ∀ x ∈ G, ∀ y ∈ G, θ (x * y) = θ x * θ y)
    (hlin : ∀ c : L →₀ K, (↑c.support : Set L) ⊆ G →
      (c.sum fun x r => r • x) = 0 → (c.sum fun x r => r • θ x) = 0)
    (F : IntermediateField K L) (hF : F = IntermediateField.adjoin K G)
    (x₀ : F) (hx₀G : (x₀ : L) ∈ G) (hx₀ : Transcendental K (θ x₀))
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F) :
    ∃ Θ : F →ₐ[K] L', ∀ x : F, (x : L) ∈ G → Θ x = θ x :=
  IntermediateField.exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental
    K G h1 hmul θ hθ hlin F hF x₀ hx₀G hx₀ halg

-- Higher-universe consumer.
example
    (K : Type 1) {L L' : Type 1} [Field K] [Field L] [Algebra K L] [Field L']
    [Algebra K L']
    (G : Set L) (h1 : (1 : L) ∈ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (θ : L → L') (hθ : ∀ x ∈ G, ∀ y ∈ G, θ (x * y) = θ x * θ y)
    (hlin : ∀ c : L →₀ K, (↑c.support : Set L) ⊆ G →
      (c.sum fun x r => r • x) = 0 → (c.sum fun x r => r • θ x) = 0)
    (F : IntermediateField K L) (hF : F = IntermediateField.adjoin K G)
    (x₀ : F) (hx₀G : (x₀ : L) ∈ G) (hx₀ : Transcendental K (θ x₀))
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀} : Set F)) F) :
    ∃ Θ : F →ₐ[K] L', ∀ x : F, (x : L) ∈ G → Θ x = θ x :=
  IntermediateField.exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental
    K G h1 hmul θ hθ hlin F hF x₀ hx₀G hx₀ halg

namespace AdjoinAlgHomTranscendentalTest

open RatFunc

variable (K : Type*) [Field K]

-- A concrete instance in `K⟮X⟯`: `G` is the powers of `X`, whose span `K[X]` is not a field,
-- `θ` is squaring, which is multiplicative but need not be additive, and `x₀ = X`.
private noncomputable abbrev G : Set (RatFunc K) := Set.range ((X : RatFunc K) ^ ·)

private noncomputable abbrev F : IntermediateField K (RatFunc K) := IntermediateField.adjoin K (G K)

private theorem one_mem_G : (1 : RatFunc K) ∈ G K := ⟨0, pow_zero _⟩

private theorem mul_mem_G : ∀ x ∈ G K, ∀ y ∈ G K, x * y ∈ G K := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩
  exact ⟨m + n, pow_add _ m n⟩

private theorem X_mem_G : (X : RatFunc K) ∈ G K := ⟨1, pow_one _⟩

private noncomputable abbrev x₀ : F K := ⟨X, IntermediateField.subset_adjoin K _ (X_mem_G K)⟩

-- On the powers of `X`, squaring agrees with the substitution `X ↦ X ^ 2`, an algebra map, so
-- it preserves their linear relations.
private theorem sq_linearRelations (c : RatFunc K →₀ K)
    (hc : (↑c.support : Set (RatFunc K)) ⊆ G K) (h : (c.sum fun x r => r • x) = 0) :
    (c.sum fun x r => r • x ^ 2) = 0 := by
  let φ : RatFunc K →ₐ[K] RatFunc K := (IntermediateField.val _).comp
    (algEquivOfTranscendental _ ((transcendental_X (K := K)).pow two_pos)).toAlgHom
  have hφ : ∀ x ∈ G K, φ x = x ^ 2 := by
    rintro _ ⟨n, rfl⟩
    simp [φ, ← pow_mul, mul_comm]
  calc (c.sum fun x r => r • x ^ 2) = c.sum fun x r => r • φ x :=
        Finsupp.sum_congr fun x hx => by rw [hφ x (hc (Finset.mem_coe.mpr hx))]
    _ = φ (c.sum fun x r => r • x) := by rw [map_finsuppSum]; simp only [map_smul]
    _ = 0 := by rw [h, map_zero]

-- `X` generates `F K`, so `F K` is algebraic over `K(x₀)`.
private theorem isAlgebraic_adjoin_x₀ :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({x₀ K} : Set (F K))) (F K) := by
  refine ⟨fun y => ?_⟩
  have hy : y ∈ IntermediateField.adjoin K ({x₀ K} : Set (F K)) := by
    rw [← IntermediateField.mem_lift, IntermediateField.lift_adjoin_simple]
    change y.1 ∈ IntermediateField.adjoin K {(X : RatFunc K)}
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  exact isAlgebraic_algebraMap (⟨y, hy⟩ : IntermediateField.adjoin K ({x₀ K} : Set (F K)))

-- The theorem, with every hypothesis proved.
private theorem exists_sq_extension :
    ∃ Θ : F K →ₐ[K] RatFunc K, ∀ x : F K, (x : RatFunc K) ∈ G K → Θ x = (x : RatFunc K) ^ 2 :=
  IntermediateField.exists_algHom_adjoin_apply_eq_of_isAlgebraic_of_transcendental K (G K)
    (one_mem_G K) (mul_mem_G K) (· ^ 2) (fun x _ y _ => mul_pow x y 2)
    (sq_linearRelations K) (F K) rfl (x₀ K) (X_mem_G K)
    ((transcendental_X (K := K)).pow two_pos) (isAlgebraic_adjoin_x₀ K)

-- Boundary: the algebra map agrees with `θ` at `1`, which lies in every admissible `G`, and
-- sends the generator `X` to `X ^ 2`.
example : ∃ Θ : F K →ₐ[K] RatFunc K, Θ 1 = 1 ^ 2 ∧ Θ (x₀ K) = X ^ 2 := by
  obtain ⟨Θ, hΘ⟩ := exists_sq_extension K
  exact ⟨Θ, hΘ 1 (one_mem_G K), hΘ (x₀ K) (X_mem_G K)⟩

-- Off `G` the map need not agree with `θ`: when `2 ≠ 0` in `K`, it sends `1 + X ∉ G` to
-- `1 + X ^ 2`, while `θ (1 + X) = (1 + X) ^ 2`.
example (h2 : (2 : K) ≠ 0) :
    ∃ Θ : F K →ₐ[K] RatFunc K, Θ (1 + x₀ K) = 1 + X ^ 2 ∧
      Θ (1 + x₀ K) ≠ ((1 + x₀ K : F K) : RatFunc K) ^ 2 := by
  obtain ⟨Θ, hΘ⟩ := exists_sq_extension K
  have hΘ1X : Θ (1 + x₀ K) = 1 + X ^ 2 := by rw [map_add, map_one, hΘ (x₀ K) (X_mem_G K)]
  refine ⟨Θ, hΘ1X, fun h => ?_⟩
  have h' : (1 : RatFunc K) + X ^ 2 = (1 + X) ^ 2 := hΘ1X.symm.trans h
  have h2X : (2 : RatFunc K) * X = 0 := by linear_combination -h'
  rcases mul_eq_zero.mp h2X with h0 | h0
  · exact h2 ((algebraMap K (RatFunc K)).injective (by rw [map_ofNat, h0, map_zero]))
  · exact X_ne_zero h0

end AdjoinAlgHomTranscendentalTest
