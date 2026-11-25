/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.CompleteLattice.Finset

/-!
# Weisner's theorem and the crosscut theorem

Two recurrences for the Möbius function `μ` of a finite lattice `L`, from Stanley,
*Enumerative Combinatorics*, vol. 1, 2nd ed. (author's draft of 15 July 2011,
https://math.mit.edu/~rstan/ec/ec1.pdf), Section 3.9:

* `sum_mu_top_of_inf_eq_bot` (**Weisner's theorem**, Corollary 3.9.3): for `a ≠ 1̂`,
  `∑_{t : t ∧ a = 0̂} μ(t, 1̂) = 0`.
* `mu_bot_top_eq_sum_crosscut` (**crosscut theorem**, Corollary 3.9.4): if `X ⊆ L` omits `1̂`
  and every `s ≠ 1̂` lies below some element of `X`, then `μ(0̂, 1̂) = ∑_k (-1)^k N_k` where `N_k`
  is the number of `k`-subsets of `X` whose meet is `0̂`.

Stanley derives both from the Möbius algebra (Theorem 3.9.2). The proofs here instead expand the
indicator of `u = 0̂` as `∑_{0̂ ≤ s ≤ u} μ(0̂, s)` (Mathlib's `IncidenceAlgebra.sum_Icc_mu_right`)
and exchange the order of summation, which is the same computation written out.

A finite nonempty lattice has a least and a greatest element; the statements assume them as a
`BoundedOrder` instance. The crosscut theorem only needs `L` locally finite, which together with
the bounds makes it finite.
-/

@[expose] public section

open Finset IncidenceAlgebra

namespace MathlibExt.Order.IncidenceAlgebra.Lattice

variable {L : Type*} [Lattice L] [BoundedOrder L] [Fintype L] [LocallyFiniteOrder L]
  [DecidableEq L]

/-- **Weisner's theorem.** Let `L` be a finite lattice with least element `0̂` and greatest element
`1̂`, and let `a ∈ L` with `a ≠ 1̂`. Then `∑_{t : t ∧ a = 0̂} μ(t, 1̂) = 0` (Stanley, *Enumerative
Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Corollary 3.9.3). -/
theorem sum_mu_top_of_inf_eq_bot (𝕜 : Type*) [Ring 𝕜] {a : L} (ha : a ≠ ⊤) :
    ∑ t ∈ univ.filter (fun t => t ⊓ a = ⊥), mu 𝕜 t ⊤ = 0 := by
  rw [sum_filter]
  have key : ∀ t : L, (if t ⊓ a = ⊥ then mu 𝕜 t ⊤ else 0) =
      ∑ s ∈ Icc ⊥ (t ⊓ a), mu 𝕜 ⊥ s * mu 𝕜 t ⊤ := by
    intro t
    rw [← sum_mul, sum_Icc_mu_right]
    by_cases h : t ⊓ a = ⊥
    · simp [h]
    · simp [h, Ne.symm h]
  simp_rw [key]
  rw [sum_comm' (t' := Icc ⊥ a) (s' := fun s => Icc s ⊤) (fun t s => by
    simp only [mem_univ, true_and, mem_Icc, bot_le, le_top, and_true, le_inf_iff])]
  refine sum_eq_zero fun s hs => ?_
  rw [← mul_sum, sum_Icc_mu_left]
  have hs' : s ≠ ⊤ := by
    rintro rfl
    exact ha (top_le_iff.mp (mem_Icc.mp hs).2)
  simp [hs']

omit [Fintype L] in
/-- **Crosscut theorem, summed over subsets.** Under the hypotheses of the crosscut theorem,
`μ(0̂, 1̂)` is the sum of `(-1)^{|Y|}` over the subsets `Y ⊆ X` whose meet is `0̂`, the meet of
the empty subset being `1̂`. -/
theorem mu_bot_top_eq_sum_powerset (𝕜 : Type*) [Ring 𝕜] (X : Finset L) (hX : ⊤ ∉ X)
    (hcover : ∀ s : L, s ≠ ⊤ → ∃ t ∈ X, s ≤ t) :
    mu 𝕜 (⊥ : L) ⊤ =
      ∑ Y ∈ X.powerset, if Y.inf id = ⊥ then (-1 : 𝕜) ^ Y.card else 0 := by
  classical
  have key : ∀ Y : Finset L, (if Y.inf id = ⊥ then (-1 : 𝕜) ^ Y.card else 0) =
      ∑ s ∈ Icc ⊥ (Y.inf id), mu 𝕜 ⊥ s * (-1) ^ Y.card := by
    intro Y
    rw [← sum_mul, sum_Icc_mu_right]
    by_cases h : Y.inf id = ⊥
    · simp [h]
    · simp [h, Ne.symm h]
  simp_rw [key]
  rw [sum_comm' (t' := Icc ⊥ ⊤) (s' := fun s => X.powerset.filter fun Y => ∀ t ∈ Y, s ≤ t)
    (fun Y s => by
      simp only [mem_powerset, mem_Icc, bot_le, true_and, le_top, and_true, mem_filter,
        Finset.le_inf_iff, id])]
  rw [sum_eq_single (⊤ : L)]
  · -- Only the empty subset of `X` lies above `1̂`.
    have hempty : (X.powerset.filter fun Y => ∀ t ∈ Y, (⊤ : L) ≤ t) = {∅} := by
      ext Y
      simp only [mem_filter, mem_powerset, mem_singleton, top_le_iff]
      constructor
      · rintro ⟨hYX, hY⟩
        rw [eq_empty_iff_forall_notMem]
        intro t ht
        exact hX (hY t ht ▸ hYX ht)
      · rintro rfl
        simp
    rw [hempty, sum_singleton, card_empty, pow_zero, mul_one]
  · intro s _ hs
    obtain ⟨t, htX, hst⟩ := hcover s hs
    rw [← mul_sum]
    -- The subsets of `X` above `s` are the subsets of `X_s = {t ∈ X : s ≤ t}`, which is nonempty.
    have hfilter : (X.powerset.filter fun Y => ∀ u ∈ Y, s ≤ u) =
        (X.filter fun u => s ≤ u).powerset := by
      ext Y
      simp only [mem_filter, mem_powerset, subset_iff]
      constructor
      · rintro ⟨hYX, hY⟩ u hu
        exact ⟨hYX hu, hY u hu⟩
      · intro hY
        exact ⟨fun u hu => (hY hu).1, fun u hu => (hY hu).2⟩
    have hne : (X.filter fun u => s ≤ u).Nonempty := ⟨t, mem_filter.mpr ⟨htX, hst⟩⟩
    have hcast : ∑ Y ∈ (X.filter fun u => s ≤ u).powerset, ((-1 : 𝕜) ^ Y.card) =
        ((∑ Y ∈ (X.filter fun u => s ≤ u).powerset, (-1 : ℤ) ^ Y.card : ℤ) : 𝕜) := by
      push_cast; rfl
    rw [hfilter, hcast, sum_powerset_neg_one_pow_card_of_nonempty hne, Int.cast_zero, mul_zero]
  · intro h
    exact absurd (mem_Icc.mpr ⟨bot_le, le_rfl⟩) h

omit [Fintype L] in
/-- **Crosscut theorem.** Let `L` be a finite lattice with least element `0̂` and greatest element
`1̂`, and let `X ⊆ L` be such that `1̂ ∉ X` and every `s ∈ L` with `s ≠ 1̂` satisfies `s ≤ t` for
some `t ∈ X`. Then `μ(0̂, 1̂) = ∑_k (-1)^k N_k`, where `N_k` is the number of `k`-subsets of `X`
whose meet is `0̂` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of
15 July 2011, Corollary 3.9.4). The meet of the empty subset is `1̂`. -/
theorem mu_bot_top_eq_sum_crosscut (𝕜 : Type*) [Ring 𝕜] (X : Finset L) (hX : ⊤ ∉ X)
    (hcover : ∀ s : L, s ≠ ⊤ → ∃ t ∈ X, s ≤ t) :
    mu 𝕜 (⊥ : L) ⊤ = ∑ k ∈ range (X.card + 1),
      (-1 : 𝕜) ^ k * ((X.powersetCard k).filter fun Y => Y.inf id = ⊥).card := by
  rw [mu_bot_top_eq_sum_powerset 𝕜 X hX hcover,
    ← sum_fiberwise_of_maps_to (g := Finset.card) (t := range (X.card + 1)) (fun Y hY => by
      rw [mem_range, Nat.lt_succ_iff]
      exact card_le_card (mem_powerset.mp hY))]
  refine sum_congr rfl fun k _ => ?_
  rw [card_eq_sum_ones, Nat.cast_sum, mul_sum, sum_filter, sum_filter, powersetCard_eq_filter,
    sum_filter]
  refine sum_congr rfl fun Y _ => ?_
  by_cases hk : Y.card = k
  · subst hk
    by_cases h : Y.inf id = ⊥ <;> simp [h]
  · simp [hk]

end MathlibExt.Order.IncidenceAlgebra.Lattice
