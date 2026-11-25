/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Tactic.IntervalCases

/-!
# Fully invariant subgroups of every divisor order

We refute MacHale's cyclicity question using Abdollahi's group `C₂ × C₄`. The image and kernel
of squaring give fully invariant subgroups of orders two and four.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.FullyInvariantSubgroupsCyclicKourovka16Problem61Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.61 (D.
MacHale). UnsolvedMath record UM-00701253 (`KOU-16.61`), dataset ulamai/UnsolvedMath v1.8.0.

Endomorphisms are all homomorphisms `G →* G`, and orders are `Nat.card`.
-/

/-- **MacHale's question on fully invariant subgroups (Kourovka 16.61).** The statement that every
finite group $G$ having, for every divisor $d$ of $|G|$, a fully invariant subgroup of order $d$
(a subgroup $H$ with $\varphi(H) \le H$ for every endomorphism $\varphi$ of $G$) is cyclic. -/
def fullyInvariantSubgroupsOfEachOrderCyclic : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ d : ℕ, d ∣ Nat.card G → ∃ H : Subgroup G, Nat.card H = d ∧ ∀ φ : G →* G, H.map φ ≤ H) →
    IsCyclic G

/--
**Fully invariant subgroups of every order do not force cyclicity.** Not every finite group $G$
having, for every divisor $d$ of $|G|$, a fully invariant subgroup of order $d$ (a subgroup $H$
with $\varphi(H) \le H$ for every endomorphism $\varphi$ of $G$) is cyclic.

The Kourovka Archive answers 16.61 "No" (Abdollahi): take $G = C_p \times C_{p^2}$, where $C_p$
and $C_{p^2}$ are cyclic $p$-groups of orders $p$ and $p^2$.

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.61 (D. MacHale); resolution: A.
Abdollahi, letter of 4 March 2009, as recorded in the Kourovka Archive, Kourovka Archive, Problem
16.61 (No: G = C_p × C_{p²}).
-/
theorem fullyInvariantSubgroupsOfEachOrderCyclic_refuted :
    ¬ fullyInvariantSubgroupsOfEachOrderCyclic := by
  intro h
  let G := Multiplicative (ZMod 2) × Multiplicative (ZMod 4)
  let square : G →* G := powMonoidHom 2
  have card_G : Nat.card G = 8 := by rw [Nat.card_eq_fintype_card]; decide
  have card_ker : Nat.card square.ker = 4 := by rw [Nat.card_eq_fintype_card]; decide
  have card_range : Nat.card square.range = 2 := by
    have hc := Subgroup.card_ker_mul_card_range square
    rw [card_ker, card_G] at hc
    omega
  have : IsCyclic G := h G fun d hd ↦ by
    rw [card_G] at hd
    obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 3)).mp hd
    interval_cases k
    · exact ⟨⊥, Subgroup.card_bot, fun φ ↦ (Subgroup.map_bot φ).le⟩
    · refine ⟨square.range, card_range, fun φ ↦ ?_⟩
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨φ x, (map_pow φ x 2).symm⟩
    · refine ⟨square.ker, card_ker, fun φ ↦ ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      change φ x ^ 2 = 1
      rw [← map_pow, show x ^ 2 = 1 from hx, map_one]
    · exact ⟨⊤, (Subgroup.card_top.trans card_G), fun _ ↦ le_top⟩
  -- In a cyclic group of order eight, squaring would have kernel of order two.
  have hcyc : Nat.card square.ker = 2 := by
    rw [IsCyclic.card_powMonoidHom_ker, card_G]
    decide
  omega

end MathlibExt.GroupTheory.FullyInvariantSubgroupsCyclicKourovka16Problem61Wanted
