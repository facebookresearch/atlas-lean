/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Equiv.Fin.Rotate
public import MathlibExt.GameTheory.Matching.StableMechanism

/-!
# Shapley–Scarf housing markets

Each agent brings one distinct house. A coalition may redistribute those houses, not the houses
its members receive under the allocation it is comparing against. The two cores differ in whether
an agent who keeps the same house can take part in a block.

Shapley and Scarf, *On cores and indivisibility* (1974), §2, p. 25, use the core that excludes
strict improvement for every member of a coalition (the **weak core** here). For both blocking
notions see Roth and Postlewaite (1977), §2, pp. 132–133, and the *Handbook of Computational
Social Choice* (2016), §14.3.1, p. 347. The three-agent separation below is a direct calculation.
-/

@[expose] public section

namespace MathlibExt.GameTheory.Matching

/-- A **Shapley–Scarf housing market** on a finite nonempty type `A` of agents and a type `H`
of houses consists of a bijective original endowment and a strict total preference order on all
houses for each agent. An allocation is any bijection `A ≃ H`. The endowment identifies houses
with their initial owners, so a coalition can trade its original houses by permuting its members. -/
structure HousingMarket (A H : Type*) [Finite A] [Nonempty A] where
  /-- The house each agent originally owns; every house has exactly one original owner. -/
  endowment : A ≃ H
  /-- Each agent's strict total order on houses: `(pref i).lt h k` means `i` prefers `h` to `k`. -/
  pref : A → Order.StrictTotalOrder H

namespace HousingMarket

variable {A H : Type*} [Finite A] [Nonempty A] (M : HousingMarket A H)

/-- A coalition `S` **weakly blocks** an allocation `x` in a finite nonempty housing market if
`S` is nonempty and some permutation of its members assigns their original houses so that each
member gets the same house as in `x` or a strictly preferred one, and at least one strictly
prefers the new house. The same permutation must realize both comparisons. -/
def WeaklyBlocks (x : A ≃ H) (S : Finset A) : Prop :=
  S.Nonempty ∧ ∃ σ : Equiv.Perm S,
    (∀ i : S, M.endowment (σ i) = x i ∨ (M.pref i).lt (M.endowment (σ i)) (x i)) ∧
    ∃ i : S, (M.pref i).lt (M.endowment (σ i)) (x i)

/-- A coalition `S` **strictly blocks** (or **strongly blocks**) an allocation `x` in a finite
nonempty housing market if `S` is nonempty and some permutation of its members assigns to every
member an original house of the coalition that this member strictly prefers to its house in `x`. -/
def StrictlyBlocks (x : A ≃ H) (S : Finset A) : Prop :=
  S.Nonempty ∧ ∃ σ : Equiv.Perm S, ∀ i : S, (M.pref i).lt (M.endowment (σ i)) (x i)

/-- The **strict core** of a finite nonempty housing market is the set of bijective allocations
for which no nonempty coalition can permute its original houses to make at least one member
strictly better off and every member at least as well off. -/
def strictCore : Set (A ≃ H) := {x | ∀ S, ¬ M.WeaklyBlocks x S}

/-- The **weak core** of a finite nonempty housing market is the set of bijective allocations
for which no nonempty coalition can permute its original houses so that *each* member strictly
prefers its new house to its assigned one. This is the core of Shapley and Scarf. -/
def weakCore : Set (A ≃ H) := {x | ∀ S, ¬ M.StrictlyBlocks x S}

variable {M} in
/-- If a nonempty coalition strictly blocks an allocation by permuting its original houses, that
same coalition weakly blocks it: every member strictly improves, and there is at least one. -/
theorem StrictlyBlocks.weaklyBlocks {x : A ≃ H} {S : Finset A} (h : M.StrictlyBlocks x S) :
    M.WeaklyBlocks x S := by
  obtain ⟨hS, σ, hσ⟩ := h
  obtain ⟨i, hi⟩ := hS
  exact ⟨⟨i, hi⟩, σ, fun j => Or.inr (hσ j), ⟨i, hi⟩, hσ ⟨i, hi⟩⟩

/-- In every finite nonempty housing market with strict total preferences the strict core is a
subset of the weak core: immunity to weak blocking by any coalition trading its original houses
implies immunity to blocking by a strict improvement for all coalition members. -/
theorem strictCore_subset_weakCore : M.strictCore ⊆ M.weakCore :=
  fun _ hx S h => hx S h.weaklyBlocks

/-- A singleton coalition strictly blocks a bijective allocation `x` exactly when its sole member
`i` strictly prefers its original house to `x i`: reclaiming that house is its only trade. -/
theorem strictlyBlocks_singleton_iff (x : A ≃ H) (i : A) :
    M.StrictlyBlocks x {i} ↔ (M.pref i).lt (M.endowment i) (x i) := by
  constructor
  · rintro ⟨_, σ, h⟩
    let a : ({i} : Finset A) := ⟨i, by simp⟩
    have he : (σ a : A) = i := Finset.mem_singleton.mp (σ a).property
    simpa only [he] using h a
  · intro h
    refine ⟨⟨i, by simp⟩, Equiv.refl _, fun a => ?_⟩
    simpa only [Equiv.refl_apply, Finset.mem_singleton.mp a.property] using h

/-- An allocation `x` in the weak core of a finite nonempty housing market is individually
rational: no agent strictly prefers its original house to `x i`, since that agent alone could
reclaim its original house. No restriction to individually rational allocations is assumed. -/
theorem not_prefers_endowment_of_mem_weakCore {x : A ≃ H} (hx : x ∈ M.weakCore) (i : A) :
    ¬ (M.pref i).lt (M.endowment i) (x i) :=
  fun h => hx {i} ((M.strictlyBlocks_singleton_iff x i).2 h)

/-! ## Three agents separating the two cores -/

open StableMechanism (rankOrder rank3)

/-- A housing market on three agents and houses labelled `0,1,2`. Agent `i` initially owns house
`i`; their strict preferences from best to worst are respectively `1,0,2`, `0,2,1`, and `0,1,2`.
Thus an original house available to a coalition has the label of one of its members. -/
def threeAgentMarket : HousingMarket (Fin 3) (Fin 3) where
  endowment := Equiv.refl _
  pref i := rankOrder (![rank3 1 0, rank3 0 2, rank3 0 1] i) (by revert i; decide)

/-- Strict preference between any two houses is decidable for each agent of the three-agent market
with identity endowment and preference lists `1,0,2`, `0,2,1`, and `0,1,2` (best first). -/
instance threeAgentMarket.decidablePref (i : Fin 3) :
    DecidableRel (threeAgentMarket.pref i).lt := by
  dsimp only [threeAgentMarket]
  infer_instance

private theorem improves_on_rotation : ∀ i h : Fin 3,
    (threeAgentMarket.pref i).lt h (finRotate 3 i) ↔ i = 1 ∧ h = 0 := by decide

/-- In the three-agent market with original houses `0,1,2` and preferences `1,0,2`, `0,2,1`,
`0,1,2` (best first), coalition `{0,1}` weakly blocks the allocation `(1,2,0)`.
Swapping the two original houses keeps `0` at house `1` and improves `1` to house `0`. -/
theorem pair_weaklyBlocks_rotation : threeAgentMarket.WeaklyBlocks (finRotate 3) {0, 1} := by
  let S : Finset (Fin 3) := {0, 1}
  let a : S := ⟨0, by decide⟩
  let b : S := ⟨1, by decide⟩
  have hb : (threeAgentMarket.pref b).lt (threeAgentMarket.endowment (Equiv.swap a b b))
      (finRotate 3 b) := by rw [Equiv.swap_apply_right]; decide
  refine ⟨⟨0, a.property⟩, Equiv.swap a b, ?_, b, hb⟩
  intro i
  rcases Finset.mem_insert.mp i.property with hi | hi
  · have e : i = a := Subtype.ext hi
    subst i
    exact Or.inl (by rw [Equiv.swap_apply_left]; decide)
  · have e : i = b := Subtype.ext (Finset.mem_singleton.mp hi)
    subst i
    exact Or.inr hb

/-- With original houses `0,1,2` and best-first rankings `1,0,2`, `0,2,1`, `0,1,2`, allocation
`(1,2,0)` is in the weak core but not the strict core. Agents `0` and `2` already have their
first choices; agent `1` alone owns only `1`, worse than its assigned `2`. Yet `{0,1}` can exchange
original houses to improve agent `1` while leaving agent `0` equally well off. -/
theorem rotation_mem_weakCore_diff_strictCore :
    finRotate 3 ∈ threeAgentMarket.weakCore \ threeAgentMarket.strictCore := by
  refine ⟨?_, fun hx => hx {0, 1} pair_weaklyBlocks_rotation⟩
  rintro S ⟨⟨i, hi⟩, σ, hσ⟩
  let a : S := ⟨i, hi⟩
  -- To improve, a member needs house 0. Its original owner is then also a member and must improve.
  have donor_zero := ((improves_on_rotation a (σ a)).1 (hσ a)).2
  have donor_one := ((improves_on_rotation (σ a) (σ (σ a))).1 (hσ (σ a))).1
  exact (by decide : (0 : Fin 3) ≠ 1) (donor_zero.symm.trans donor_one)

/-- For the three-agent market with identity endowment and strict best-first preferences `1,0,2`,
`0,2,1`, `0,1,2`, the strict core is a proper subset of the weak core. The separating allocation
is `(1,2,0)`: a coalition's original houses allow a weak block but no strict block. -/
theorem threeAgentMarket_strictCore_ssubset_weakCore :
    threeAgentMarket.strictCore ⊂ threeAgentMarket.weakCore :=
  ⟨threeAgentMarket.strictCore_subset_weakCore, fun h =>
    rotation_mem_weakCore_diff_strictCore.2 (h rotation_mem_weakCore_diff_strictCore.1)⟩

end HousingMarket
end MathlibExt.GameTheory.Matching
