/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Philip Hall's theorem

For elements `a, b` of a locally finite poset, `chainCount a b i` is the number of chains
`a = t₀ < t₁ < ⋯ < tᵢ = b` of length `i`. Philip Hall's theorem expresses the Möbius function as
the alternating sum `μ(a, b) = c₀ - c₁ + c₂ - ⋯` of these counts (Stanley, *Enumerative
Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011,
https://math.mit.edu/~rstan/ec/ec1.pdf, Proposition 3.8.5).

The proof is by induction on the size of the interval, from the recurrence
`c_{i+1}(a, b) = ∑_{a ≤ x < b} c_i(a, x)` (remove the last step of a chain) and the defining
recurrence `μ(a, b) = -∑_{a ≤ x < b} μ(a, x)` of Mathlib's `IncidenceAlgebra.mu`.
-/

@[expose] public section

open Finset IncidenceAlgebra

namespace MathlibExt.Order.IncidenceAlgebra.PhilipHall

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α]

open Classical in
/-- **Chains of length `i` between two elements.** For elements `a, b` of a locally finite poset
and `i : ℕ`, the finite set of chains `a = t₀ < t₁ < ⋯ < tᵢ = b` of length `i` from `a` to `b`,
each written as the strictly increasing map `j ↦ t_j` on `{0, …, i}` (Stanley, *Enumerative
Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Section 3.8, before
Proposition 3.8.5). Every such chain lies in the interval `[a, b]`, which is finite. -/
noncomputable def chainsBetween (a b : α) (i : ℕ) : Finset (Fin (i + 1) → α) :=
  (Fintype.piFinset fun _ => Icc a b).filter fun f =>
    StrictMono f ∧ f 0 = a ∧ f (Fin.last i) = b

/-- **Number of chains of length `i` between two elements.** `chainCount a b i` is the number
`cᵢ` of chains `a = t₀ < t₁ < ⋯ < tᵢ = b` of length `i` (Stanley, *Enumerative Combinatorics*,
vol. 1, 2nd ed., author's draft of 15 July 2011, Proposition 3.8.5, there for `a = 0̂`,
`b = 1̂`). -/
noncomputable def chainCount (a b : α) (i : ℕ) : ℕ := (chainsBetween a b i).card

/-- **Membership in the chains between two elements.** A map `f : {0, …, i} → P` is a chain of
length `i` from `a` to `b` exactly when it is strictly increasing with `f 0 = a` and `f i = b`;
membership of its values in `[a, b]` is automatic. -/
theorem mem_chainsBetween {a b : α} {i : ℕ} {f : Fin (i + 1) → α} :
    f ∈ chainsBetween a b i ↔ StrictMono f ∧ f 0 = a ∧ f (Fin.last i) = b := by
  classical
  simp only [chainsBetween, mem_filter, Fintype.mem_piFinset, mem_Icc, and_iff_right_iff_imp]
  rintro ⟨hf, h0, hl⟩ j
  exact ⟨h0 ▸ hf.monotone (Fin.zero_le j), hl ▸ hf.monotone (Fin.le_last j)⟩

/-- **Chains of length zero.** There is exactly one chain of length `0` from `a` to `b` if `a = b`,
and none otherwise: `c₀(a, b) = δ(a, b)`. -/
theorem chainCount_zero [DecidableEq α] (a b : α) : chainCount a b 0 = if a = b then 1 else 0 := by
  classical
  unfold chainCount
  split_ifs with hab
  · subst hab
    rw [card_eq_one]
    refine ⟨fun _ => a, ?_⟩
    ext f
    simp only [mem_chainsBetween, mem_singleton]
    constructor
    · rintro ⟨-, h0, -⟩
      funext j
      rw [(Fin.ext (by have := j.isLt; omega) : j = 0), h0]
    · rintro rfl
      refine ⟨fun j k hjk => absurd hjk ?_, rfl, rfl⟩
      rw [(Fin.ext (by have := j.isLt; have := k.isLt; omega) : j = k)]
      exact lt_irrefl k
  · rw [card_eq_zero, eq_empty_iff_forall_notMem]
    intro f hf
    rw [mem_chainsBetween] at hf
    exact hab (hf.2.1.symm.trans hf.2.2)

/-- **Chains are no longer than the interval.** A chain of length `i` from `a` to `b` has `i + 1`
distinct elements of `[a, b]`, so `cᵢ(a, b) = 0` once `i ≥ #[a, b]`. -/
theorem chainCount_eq_zero_of_card_le {a b : α} {i : ℕ} (hi : (Icc a b).card ≤ i) :
    chainCount a b i = 0 := by
  classical
  unfold chainCount
  rw [card_eq_zero, eq_empty_iff_forall_notMem]
  intro f hf
  have hmem : ∀ j ∈ (univ : Finset (Fin (i + 1))), f j ∈ Icc a b := by
    intro j _
    have h := (mem_filter.mp hf).1
    rw [Fintype.mem_piFinset] at h
    exact h j
  have hinj : Set.InjOn f (univ : Finset (Fin (i + 1))) :=
    ((mem_chainsBetween.mp hf).1.injective).injOn
  have := card_le_card_of_injOn f hmem hinj
  simp at this
  omega

/-- **Removing the last step of a chain.** `c_{i+1}(a, b) = ∑_{a ≤ x < b} c_i(a, x)`. -/
theorem chainCount_succ (a b : α) (i : ℕ) :
    chainCount a b (i + 1) = ∑ x ∈ Ico a b, chainCount a x i := by
  classical
  unfold chainCount
  rw [← card_sigma]
  refine card_nbij' (fun f => ⟨f (Fin.last i).castSucc, Fin.init f⟩)
    (fun p => Fin.snoc p.2 b) ?_ ?_ ?_ ?_
  · intro f hf
    rw [mem_coe, mem_chainsBetween] at hf
    obtain ⟨hf, h0, hl⟩ := hf
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_Ico, mem_chainsBetween]
    refine ⟨⟨h0 ▸ hf.monotone (Fin.zero_le _), hl ▸ hf (Fin.castSucc_lt_last _)⟩, ?_, ?_, rfl⟩
    · exact fun j k hjk => hf (Fin.castSucc_lt_castSucc_iff.mpr hjk)
    · simpa [Fin.init] using h0
  · rintro ⟨x, g⟩ hp
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_Ico, mem_chainsBetween] at hp
    obtain ⟨⟨hax, hxb⟩, hg, h0, hl⟩ := hp
    rw [mem_coe, mem_chainsBetween]
    refine ⟨?_, ?_, by simp⟩
    · rw [Fin.strictMono_iff_lt_succ]
      intro j
      induction j using Fin.lastCases with
      | last =>
        dsimp only
        rw [Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, hl]
        exact hxb
      | cast j =>
        dsimp only
        rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hg Fin.castSucc_lt_succ
    · change Fin.snoc (α := fun _ => α) g b (Fin.castSucc 0) = a
      rw [Fin.snoc_castSucc]
      exact h0
  · intro f hf
    rw [mem_coe, mem_chainsBetween] at hf
    simp only
    rw [← hf.2.2]
    exact Fin.snoc_init_self f
  · rintro ⟨x, g⟩ hp
    simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_Ico, mem_chainsBetween] at hp
    simp [hp.2.2.2, Fin.init_snoc]

/-- **Philip Hall's theorem, truncated at any bound.** `μ(a, b) = ∑_{i < n} (-1)^i cᵢ(a, b)` for
every `n ≥ #[a, b]`, since the terms with `i ≥ #[a, b]` vanish. -/
theorem mu_eq_sum_chainCount_of_card_le {𝕜 : Type*} [Ring 𝕜] [DecidableEq α] (a b : α) {n : ℕ}
    (hn : (Icc a b).card ≤ n) :
    mu 𝕜 a b = ∑ i ∈ range n, (-1) ^ i * (chainCount a b i : 𝕜) := by
  induction hcard : (Icc a b).card using Nat.strong_induction_on generalizing b with
  | _ m ih =>
  by_cases hab : a ≤ b
  swap
  · rw [apply_eq_zero_of_not_le hab]
    refine (sum_eq_zero fun i _ => ?_).symm
    rw [chainCount_eq_zero_of_card_le (by simp [Icc_eq_empty hab]), Nat.cast_zero, mul_zero]
  rcases eq_or_ne a b with rfl | hne
  · have h1 : (Icc a a).card = 1 := by simp
    have hn1 : 1 ≤ n := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn1
    rw [sum_range_succ', mu_self, chainCount_zero]
    rw [sum_eq_zero fun i _ => by
      rw [chainCount_eq_zero_of_card_le (by simp), Nat.cast_zero, mul_zero]]
    simp
  have hlt : a < b := lt_of_le_of_ne hab hne
  have h1 : 0 < (Icc a b).card := card_pos.mpr ⟨a, mem_Icc.mpr ⟨le_rfl, hab⟩⟩
  have hn2 : 1 ≤ n := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn2
  rw [mu_eq_neg_sum_Ico_of_ne hne]
  have hIH : ∀ x ∈ Ico a b,
      mu 𝕜 a x = ∑ i ∈ range (k + 1), (-1) ^ i * (chainCount a x i : 𝕜) := by
    intro x hx
    rw [mem_Ico] at hx
    have hsub : Icc a x ⊂ Icc a b := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Icc_subset_Icc_right hx.2.le, fun he => ?_⟩
      have : b ∈ Icc a x := he ▸ mem_Icc.mpr ⟨hab, le_rfl⟩
      exact absurd hx.2 (not_lt_of_ge (mem_Icc.mp this).2)
    have hc := card_lt_card hsub
    exact ih _ (hcard ▸ hc) x (by omega) rfl
  rw [sum_congr rfl hIH, sum_comm, ← sum_neg_distrib]
  have hc0 : chainCount a b 0 = 0 := by
    rw [chainCount_zero]
    exact ite_eq_right_iff.mpr fun h => absurd h hne
  rw [sum_range_succ' (fun i => (-1) ^ i * (chainCount a b i : 𝕜)), hc0, Nat.cast_zero,
    mul_zero, add_zero]
  rw [sum_range_succ (fun i => -∑ x ∈ Ico a b, (-1) ^ i * (chainCount a x i : 𝕜))]
  have hlast : ∑ x ∈ Ico a b, (-1) ^ k * (chainCount a x k : 𝕜) =
      (-1) ^ k * (chainCount a b (k + 1) : 𝕜) := by
    rw [chainCount_succ, Nat.cast_sum, mul_sum]
  rw [hlast, chainCount_eq_zero_of_card_le (by omega), Nat.cast_zero, mul_zero, neg_zero,
    add_zero]
  refine sum_congr rfl fun i _ => ?_
  rw [chainCount_succ, Nat.cast_sum, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [pow_succ, mul_neg_one, neg_mul]

/-- **Philip Hall's theorem.** For elements `a, b` of a locally finite poset, let `cᵢ` be the
number of chains `a = t₀ < t₁ < ⋯ < tᵢ = b` of length `i`. Then
`μ(a, b) = c₀ - c₁ + c₂ - c₃ + ⋯`, the sum being finite since `cᵢ = 0` once `i ≥ #[a, b]`
(Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011,
Proposition 3.8.5, stated there for `μ_{P̂}(0̂, 1̂)` with `P̂` a finite poset `P` with `0̂` and `1̂`
adjoined; for `a < b` the interval `[a, b]` is `P̂` for `P` the open interval `(a, b)`, and for
`a = b` both sides equal `1`). -/
theorem mu_eq_sum_chainCount {𝕜 : Type*} [Ring 𝕜] [DecidableEq α] (a b : α) :
    mu 𝕜 a b = ∑ i ∈ range (Icc a b).card, (-1) ^ i * (chainCount a b i : 𝕜) :=
  mu_eq_sum_chainCount_of_card_le a b le_rfl

/-- **Philip Hall's theorem for a bounded poset.** If `P̂` is a locally finite poset with a least
element `0̂` and a greatest element `1̂` (hence finite), then `μ(0̂, 1̂) = c₀ - c₁ + c₂ - ⋯` where
`cᵢ` is the number of chains `0̂ = t₀ < ⋯ < tᵢ = 1̂` (Stanley, *Enumerative Combinatorics*,
vol. 1, 2nd ed., author's draft of 15 July 2011, Proposition 3.8.5). Here `μ(0̂, 1̂)` is
Mathlib's `IncidenceAlgebra.eulerChar`. -/
theorem eulerChar_eq_sum_chainCount (𝕜 : Type*) [Ring 𝕜] [DecidableEq α] [BoundedOrder α] :
    eulerChar 𝕜 α =
      ∑ i ∈ range (Icc (⊥ : α) ⊤).card, (-1) ^ i * (chainCount (⊥ : α) ⊤ i : 𝕜) :=
  mu_eq_sum_chainCount ⊥ ⊤

end MathlibExt.Order.IncidenceAlgebra.PhilipHall
