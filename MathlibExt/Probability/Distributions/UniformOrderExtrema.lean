/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators

/-!
# Extrema of uniform random orders

Precomposing a rank bijection with a transposition exchanges the elements that
attain the minimum. The minimum fibers have equal size and partition the
bijections. Reversing the rank order gives the corresponding maximum law.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

namespace MetaMathlibExt

variable {α β : Type*} [DecidableEq α] [LinearOrder β]

private lemma orderMin_swap {s : Finset α} {x y : α} (hy : y ∈ s) {σ : α ≃ β}
    (h : ∀ z ∈ s, z ≠ x → σ x < σ z) :
    ∀ z ∈ s, z ≠ y → (Equiv.swap x y |>.trans σ) y < (Equiv.swap x y |>.trans σ) z := by
  intro z hz hzy
  change σ (Equiv.swap x y y) < σ (Equiv.swap x y z)
  rw [Equiv.swap_apply_right]
  apply h
  · by_cases hzx : z = x
    · simpa only [hzx, Equiv.swap_apply_left] using hy
    · rwa [Equiv.swap_apply_of_ne_of_ne hzx hzy]
  · intro he
    exact hzy ((Equiv.swap x y).injective (he.trans (Equiv.swap_apply_right x y).symm))

/-- For two elements of a finite set, precomposition with their transposition
is a bijection between the fibers of rank bijections making each element the
strict minimum. The inverse precomposes with the same transposition. -/
@[expose] public def orderMinFibersEquiv {s : Finset α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    {σ : α ≃ β // ∀ z ∈ s, z ≠ x → σ x < σ z} ≃
      {σ : α ≃ β // ∀ z ∈ s, z ≠ y → σ y < σ z} where
  toFun σ := ⟨(Equiv.swap x y).trans σ.1, by exact orderMin_swap hy σ.2⟩
  invFun σ := ⟨(Equiv.swap y x).trans σ.1, by exact orderMin_swap hx σ.2⟩
  left_inv σ := Subtype.ext (Equiv.ext fun z ↦ by
    change σ.1 (Equiv.swap x y (Equiv.swap y x z)) = σ.1 z
    simp only [← Equiv.swap_comm x y, Equiv.swap_apply_self])
  right_inv σ := Subtype.ext (Equiv.ext fun z ↦ by
    change σ.1 (Equiv.swap y x (Equiv.swap x y z)) = σ.1 z
    simp only [← Equiv.swap_comm x y, Equiv.swap_apply_self])

variable [Fintype α] [Fintype β]

private lemma card_equiv_eq_card_mul {s : Finset α} {x : α} (hx : x ∈ s) :
    Fintype.card (α ≃ β) = s.card * Fintype.card {σ : α ≃ β // ∀ z ∈ s, z ≠ x → σ x < σ z} := by
  classical
  let fiber (y : s) := {σ : α ≃ β // ∀ z ∈ s, z ≠ y.1 → σ y.1 < σ z}
  let forget (p : Σ y : s, fiber y) : α ≃ β := p.2.1
  have hforget : Function.Bijective forget := by
    constructor
    · rintro ⟨⟨y, hy⟩, ⟨σ, hσ⟩⟩ ⟨⟨z, hz⟩, ⟨τ, hτ⟩⟩ h
      change σ = τ at h
      subst τ
      have hyz : y = z := by
        by_contra hne
        exact (lt_asymm (hσ z hz (Ne.symm hne))) (hτ y hy hne)
      subst z
      rfl
    · intro σ
      have hs : (s.image σ).Nonempty := ⟨σ x, Finset.mem_image_of_mem σ hx⟩
      obtain ⟨y, hy, hmin⟩ := Finset.mem_image.mp (Finset.min'_mem _ hs)
      refine ⟨⟨⟨y, hy⟩, ⟨σ, ?_⟩⟩, rfl⟩
      intro z hz hzy
      apply lt_of_le_of_ne
      · rw [hmin]
        exact Finset.min'_le _ _ (Finset.mem_image_of_mem σ hz)
      · exact fun h ↦ hzy (σ.injective h.symm)
  calc
    Fintype.card (α ≃ β) = Fintype.card (Σ y : s, fiber y) :=
      (Fintype.card_congr (Equiv.ofBijective forget hforget)).symm
    _ = ∑ y : s, Fintype.card (fiber y) := Fintype.card_sigma
    _ = _ := by
      have hcard (y : s) : Fintype.card (fiber y) = Fintype.card (fiber ⟨x, hx⟩) :=
        Fintype.card_congr (orderMinFibersEquiv (β := β) y.2 hx)
      simp only [hcard, Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul]
      rfl

variable [m : MeasurableSpace (α ≃ β)] [ms : MeasurableSingletonClass (α ≃ β)]

/-- Under the uniform measure on all bijections to an equally large finite
linear order, an element of `s` has probability `1 / s.card` of attaining the
minimum in `s`. Bijections rule out ties between distinct elements.

Source: Broder, Charikar, Frieze and Mitzenmacher, *Min-Wise Independent
Permutations*, J. Comput. System Sci. 60 (2000), §1, (4) (the full symmetric group).
-/
public theorem uniformOfFinset_orderMin_eq (hcard : Fintype.card α = Fintype.card β)
    {s : Finset α} {x : α} (hx : x ∈ s) :
    uniformOfFinset (Finset.univ : Finset (α ≃ β)) {σ | ∀ y ∈ s, y ≠ x → σ x < σ y} =
      (s.card : ℝ≥0∞)⁻¹ := by
  classical
  let n := Fintype.card {σ : α ≃ β // ∀ y ∈ s, y ≠ x → σ x < σ y}
  have htotal : Fintype.card (α ≃ β) = s.card * n := card_equiv_eq_card_mul (β := β) hx
  have : Nonempty (α ≃ β) := ⟨Fintype.equivOfCardEq hcard⟩
  have hn : n ≠ 0 := fun h ↦ Fintype.card_ne_zero (α := α ≃ β) (by simp [htotal, h])
  rw [uniformOfFinset_apply, Finset.card_univ]
  simp only [Set.mem_ofPred_eq]
  rw [← Fintype.card_subtype (fun σ : α ≃ β ↦ ∀ y ∈ s, y ≠ x → σ x < σ y)]
  change (n : ℝ≥0∞) / (Fintype.card (α ≃ β) : ℝ≥0∞) = _
  rw [htotal, Nat.cast_mul]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [ENNReal.mul_comm_div, ← mul_div_assoc, mul_comm (n : ℝ≥0∞) (s.card : ℝ≥0∞)]
  exact ENNReal.div_self (by exact_mod_cast Nat.mul_ne_zero (Finset.card_ne_zero_of_mem hx) hn)
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))

/-- Under the uniform measure on all bijections to an equally large finite
linear order, an element of `s` has probability `1 / s.card` of attaining the
maximum in `s`. This is the minimum law for the reverse rank order. -/
public theorem uniformOfFinset_orderMax_eq (hcard : Fintype.card α = Fintype.card β)
    {s : Finset α} {x : α} (hx : x ∈ s) :
    uniformOfFinset (Finset.univ : Finset (α ≃ β)) {σ | ∀ y ∈ s, y ≠ x → σ y < σ x} =
      (s.card : ℝ≥0∞)⁻¹ := by
  let reversed : LinearOrder β := (inferInstance : LinearOrder βᵒᵈ)
  exact @uniformOfFinset_orderMin_eq α β _ reversed _ _ m ms hcard s x hx

end MetaMathlibExt
