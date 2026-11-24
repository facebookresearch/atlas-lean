/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot.lean`
and
`P2M/Sol/S_IsLocalRing_exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

import Mathlib.RingTheory.HopkinsLevitzki

@[expose] public section

universe u

open IsLocalRing

section Helpers

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

private theorem iInf_sup_pow_eq (K : Ideal A) :
    (⨅ t : ℕ, K ⊔ maximalIdeal A ^ t) = K := by
  refine le_antisymm ?_ (le_iInf fun t => le_sup_left)
  intro x hx
  rw [Submodule.mem_iInf] at hx
  have hK : ∀ t : ℕ, K.mkQ x ∈ (maximalIdeal A ^ t • ⊤ : Submodule A (A ⧸ K)) := fun t => by
    have hmt : Submodule.map K.mkQ (maximalIdeal A ^ t) =
        (maximalIdeal A ^ t • ⊤ : Submodule A (A ⧸ K)) := by
      have h1 : (maximalIdeal A ^ t : Ideal A) = maximalIdeal A ^ t • (⊤ : Submodule A A) := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      conv_lhs => rw [h1]
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
    have h := Submodule.mem_map_of_mem (f := K.mkQ) (hx t)
    rwa [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, hmt] at h
  have h0 : K.mkQ x ∈ (⨅ t : ℕ, maximalIdeal A ^ t • ⊤ : Submodule A (A ⧸ K)) :=
    (Submodule.mem_iInf _).2 hK
  have hKr : (⨅ t : ℕ, maximalIdeal A ^ t • ⊤ : Submodule A (A ⧸ K)) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := maximalIdeal A) (M := A ⧸ K)
      (maximalIdeal.isMaximal A).ne_top
  rw [hKr, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  exact h0

private theorem isArtinianRing_quotient_pow (n : ℕ) (hn : 0 < n) :
    IsArtinianRing (A ⧸ maximalIdeal A ^ n) := by
  set 𝔞 : Ideal A := maximalIdeal A ^ n with h𝔞
  have h𝔞le : 𝔞 ≤ maximalIdeal A := Ideal.pow_le_self (Nat.pos_iff_ne_zero.1 hn)
  have h𝔞top : 𝔞 ≠ ⊤ := fun h => (maximalIdeal.isMaximal A).ne_top (top_le_iff.1 (h ▸ h𝔞le))
  haveI : Nontrivial (A ⧸ 𝔞) := Ideal.Quotient.nontrivial_iff.2 h𝔞top
  haveI : IsLocalRing (A ⧸ 𝔞) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk 𝔞) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing (A ⧸ 𝔞) :=
    isNoetherianRing_of_surjective A (A ⧸ 𝔞) (Ideal.Quotient.mk 𝔞)
      Ideal.Quotient.mk_surjective
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n, ?_⟩
  have hle : maximalIdeal (A ⧸ 𝔞) ≤ (maximalIdeal A).map (Ideal.Quotient.mk 𝔞) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.mem_map_of_mem _ ?_
    by_contra hxm
    exact (IsLocalRing.mem_maximalIdeal _).1 hx
      ((IsLocalRing.notMem_maximalIdeal.1 hxm).map (Ideal.Quotient.mk 𝔞))
  rw [Submodule.zero_eq_bot, ← le_bot_iff]
  calc maximalIdeal (A ⧸ 𝔞) ^ n ≤ ((maximalIdeal A).map (Ideal.Quotient.mk 𝔞)) ^ n :=
        Ideal.pow_right_mono hle n
    _ = (maximalIdeal A ^ n).map (Ideal.Quotient.mk 𝔞) := (Ideal.map_pow _ _ n).symm
    _ = ⊥ := by rw [← h𝔞, Ideal.map_quotient_self]

private theorem exists_stable (K : ℕ → Ideal A) (hK : Antitone K) (n : ℕ) (hn : 0 < n) :
    ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w → K w ⊔ maximalIdeal A ^ n = K w₀ ⊔ maximalIdeal A ^ n := by
  haveI := isArtinianRing_quotient_pow (A := A) n hn
  set π := Ideal.Quotient.mk (maximalIdeal A ^ n) with hπ
  let f : ℕ →o (Ideal (A ⧸ maximalIdeal A ^ n))ᵒᵈ :=
    ⟨fun w => OrderDual.toDual ((K w ⊔ maximalIdeal A ^ n).map π), fun w w' hww' =>
      OrderDual.toDual_le_toDual.2 (Ideal.map_mono (sup_le_sup_right (hK hww') _))⟩
  obtain ⟨w₀, hw₀⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨w₀, fun w hw => ?_⟩
  have h := hw₀ w hw
  change OrderDual.toDual ((K w₀ ⊔ maximalIdeal A ^ n).map π) =
    OrderDual.toDual ((K w ⊔ maximalIdeal A ^ n).map π) at h
  have h' : (K w₀ ⊔ maximalIdeal A ^ n).map π = (K w ⊔ maximalIdeal A ^ n).map π :=
    OrderDual.toDual.injective h
  have hback : ∀ v : ℕ, (Ideal.map π (K v ⊔ maximalIdeal A ^ n)).comap π =
      K v ⊔ maximalIdeal A ^ n := by
    intro v
    rw [Ideal.comap_map_of_surjective' π Ideal.Quotient.mk_surjective, hπ, Ideal.mk_ker,
      sup_assoc, sup_idem]
  rw [← hback w, ← h', hback w₀]

end Helpers

namespace IsLocalRing

/-- Chevalley's cofinality lemma: in a complete Noetherian local ring, a
descending sequence of ideals with zero intersection is eventually contained
in every power of the maximal ideal. -/
public theorem exists_le_maximalIdeal_pow_of_antitone_of_iInf_eq_bot
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : ℕ → Ideal A) (hK : Antitone K) (hinf : ⨅ w, K w = ⊥) (N : ℕ) :
    ∃ w : ℕ, K w ≤ IsLocalRing.maximalIdeal A ^ N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨0, by rw [pow_zero, Ideal.one_eq_top]; exact le_top⟩
  have hst : ∀ t : ℕ, ∃ w₀ : ℕ, ∀ w : ℕ, w₀ ≤ w →
      K w ⊔ maximalIdeal A ^ (N + t) = K w₀ ⊔ maximalIdeal A ^ (N + t) := fun t =>
    exists_stable K hK (N + t) (Nat.add_pos_left hN t)
  choose ws hws using hst
  set L : ℕ → Ideal A := fun t => K (ws t) ⊔ maximalIdeal A ^ (N + t) with hL
  have hLdef : ∀ t, L t = K (ws t) ⊔ maximalIdeal A ^ (N + t) := fun t => rfl
  have hi : ∀ t, maximalIdeal A ^ (N + t) ≤ L t := fun t => le_sup_right
  have hii : ∀ t, L (t + 1) ⊔ maximalIdeal A ^ (N + t) = L t := by
    intro t
    have h1 := hws (t + 1) (max (ws t) (ws (t + 1))) (le_max_right _ _)
    have h2 := hws t (max (ws t) (ws (t + 1))) (le_max_left _ _)
    have h3 : maximalIdeal A ^ (N + (t + 1)) ⊔ maximalIdeal A ^ (N + t) =
        maximalIdeal A ^ (N + t) :=
      sup_eq_right.2 (Ideal.pow_le_pow_right (Nat.le_succ (N + t)))
    rw [hLdef, hLdef, ← h1, ← h2, sup_assoc, h3]
  have hiii : (⨅ t, L t) = ⊥ := by
    rw [← le_bot_iff, ← hinf]
    refine le_iInf fun w => ?_
    rw [← iInf_sup_pow_eq (K w)]
    refine le_iInf fun t => (iInf_le L t).trans ?_
    rw [hLdef, ← hws t (max w (ws t)) (le_max_right _ _)]
    exact sup_le_sup (hK (le_max_left _ _)) (Ideal.pow_le_pow_right (Nat.le_add_left t N))
  suffices hL0 : L 0 ≤ maximalIdeal A ^ N by
    refine ⟨ws 0, le_trans ?_ hL0⟩
    rw [hLdef]
    exact le_sup_left
  intro x hx
  have step : ∀ (t : ℕ) (y : A), y ∈ L t →
      ∃ y' : A, y' ∈ L (t + 1) ∧ y - y' ∈ maximalIdeal A ^ (N + t) := by
    intro t y hy
    rw [← hii t] at hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    exact ⟨a, ha, by rwa [add_sub_cancel_left]⟩
  choose next hnext using step
  let seq : (t : ℕ) → {y : A // y ∈ L t} := fun t =>
    Nat.rec (motive := fun t => {y : A // y ∈ L t}) ⟨x, hx⟩
      (fun t y => ⟨next t y.1 y.2, (hnext t y.1 y.2).1⟩) t
  have hseq0 : (seq 0).1 = x := rfl
  have hdiff : ∀ t, (seq t).1 - (seq (t + 1)).1 ∈ maximalIdeal A ^ (N + t) := fun t =>
    (hnext t (seq t).1 (seq t).2).2
  have htel : ∀ t s : ℕ, (seq t).1 - (seq (t + s)).1 ∈ maximalIdeal A ^ (N + t) := by
    intro t s
    induction s with
    | zero => rw [Nat.add_zero, sub_self]; exact Ideal.zero_mem _
    | succ s ih =>
      have h2 : (seq (t + s)).1 - (seq (t + s + 1)).1 ∈ maximalIdeal A ^ (N + t) :=
        Ideal.pow_le_pow_right (by omega) (hdiff (t + s))
      have h3 := Ideal.add_mem _ ih h2
      rwa [sub_add_sub_cancel] at h3
  let f : ℕ → A := fun a => (seq (a - N)).1
  have hf : ∀ {a b : ℕ}, a ≤ b →
      f a ≡ f b [SMOD (maximalIdeal A ^ a • ⊤ : Submodule A A)] := by
    intro a b hab
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    obtain ⟨s, hs⟩ : ∃ s, b - N = (a - N) + s := ⟨b - N - (a - N), by omega⟩
    have h := htel (a - N) s
    rw [← hs] at h
    exact Ideal.pow_le_pow_right (by omega) h
  obtain ⟨ξ, hξ⟩ := IsPrecomplete.prec' f hf
  have hξt : ∀ t, (seq t).1 - ξ ∈ maximalIdeal A ^ (N + t) := by
    intro t
    have h := hξ (N + t)
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at h
    have hft : f (N + t) = (seq t).1 := by
      change (seq (N + t - N)).1 = (seq t).1
      rw [Nat.add_sub_cancel_left]
    rwa [hft] at h
  have hξL : ∀ t, ξ ∈ L t := fun t => by
    have h : ξ = (seq t).1 - ((seq t).1 - ξ) := by ring
    rw [h]
    exact Ideal.sub_mem _ (seq t).2 (hi t (hξt t))
  have hξ0 : ξ = 0 := by
    have h : ξ ∈ (⨅ t, L t) := (Submodule.mem_iInf _).2 hξL
    rwa [hiii, Submodule.mem_bot] at h
  have h := hξt 0
  rwa [hξ0, sub_zero, hseq0, Nat.add_zero] at h

end IsLocalRing
