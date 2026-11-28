/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Lattice.Nat

/-!
# Mirsky's theorem

In a finite poset the maximum size of a chain equals the minimum number of antichains covering
it.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.Order.FinitePosets

-- Finite antichain covers.

/-- **Finite antichain covers.** Let $\alpha$ be a partially ordered set. A finite family $C$ of
finite subsets of $\alpha$ is a finite antichain cover of $\alpha$ when every member of $C$ is an
antichain and every element of $\alpha$ belongs to some member of $C$. -/
def IsAntichainCoverFin {α : Type*} [PartialOrder α] (C : Finset (Finset α)) : Prop :=
  (∀ s ∈ C, IsAntichain (· ≤ ·) (s : Set α)) ∧ ∀ a : α, ∃ s ∈ C, a ∈ s

-- Natural-number invariants via sup/inf over powersets (avoids heavy `Fintype (Finset α)`).

open Classical in
/-- **Maximum chain size.** For a finite partially ordered set $\alpha$, the maximum chain size of
$\alpha$ is the largest cardinality of a chain in $\alpha$, that is, of a set of pairwise
comparable elements. -/
noncomputable def maxChainSize
    (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  ((Finset.univ : Finset α).powerset).sup fun s =>
    if IsChain (· ≤ ·) (s : Set α) then s.card else 0

open Classical in
/-- **Minimum antichain cover size.** For a finite partially ordered set $\alpha$, the minimum
antichain cover size of $\alpha$ is the smallest number of antichains in $\alpha$ whose union is
all of $\alpha$. -/
noncomputable def minAntichainCoverSize
    (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  let all : Finset (Finset (Finset α)) := (Finset.univ.powerset).powerset
  let valid := all.filter fun C => IsAntichainCoverFin (α := α) C
  if h : valid.Nonempty then valid.inf' h fun C => C.card else 0

theorem isAntichainCoverFin_iff {α : Type*} [PartialOrder α] (C : Finset (Finset α)) :
    IsAntichainCoverFin C ↔ (∀ s ∈ C, IsAntichain (· ≤ ·) (s : Set α)) ∧ ∀ a : α, ∃ s ∈ C, a ∈ s :=
  Iff.rfl

-- Helpers for Mirsky's theorem: rank each element by the longest chain ending at it.

open Classical in
private noncomputable def chainHeightOf {α : Type*} [Fintype α]
    [PartialOrder α] (a : α) : ℕ :=
  ((Finset.univ : Finset α).powerset).sup fun s =>
    if IsChain (· ≤ ·) (s : Set α) ∧ a ∈ (s : Set α) ∧ ∀ b ∈ (s : Set α), b ≤ a
    then s.card else 0

private theorem chainHeightOf_le_maxChainSize {α : Type*} [Fintype α]
    [PartialOrder α] (a : α) : chainHeightOf (α := α) a ≤ maxChainSize α := by
  classical
  have hsup : ((Finset.univ : Finset α).powerset).sup
      (fun s => if IsChain (· ≤ ·) (s : Set α) ∧ a ∈ (s : Set α) ∧
        ∀ b ∈ (s : Set α), b ≤ a then s.card else 0) ≤ maxChainSize α := by
    refine Finset.sup_le fun s _ => ?_
    change (if IsChain (· ≤ ·) (s : Set α) ∧ a ∈ (s : Set α) ∧
      ∀ b ∈ (s : Set α), b ≤ a then s.card else 0) ≤ _
    by_cases h : IsChain (· ≤ ·) (s : Set α) ∧ a ∈ (s : Set α) ∧
      ∀ b ∈ (s : Set α), b ≤ a
    · rw [ite_eq_left h]
      have hle : (if IsChain (· ≤ ·) (s : Set α) then s.card else 0) ≤ maxChainSize α :=
        Finset.le_sup (f := fun (t : Finset α) => if IsChain (· ≤ ·) (t : Set α) then t.card else 0)
          (Finset.mem_powerset.mpr (Finset.subset_univ s))
      rwa [ite_eq_left h.1] at hle
    · rw [ite_eq_right h]
      exact Nat.zero_le _
  exact hsup

private theorem one_le_chainHeightOf {α : Type*} [Fintype α]
    [PartialOrder α] (a : α) : 1 ≤ chainHeightOf (α := α) a := by
  classical
  have hmem : ({a} : Finset α) ∈ (Finset.univ : Finset α).powerset :=
    Finset.mem_powerset.mpr (Finset.subset_univ _)
  have hle : (if IsChain (· ≤ ·) (({a} : Finset α) : Set α) ∧ a ∈ (({a} : Finset α) : Set α) ∧
    ∀ b ∈ (({a} : Finset α) : Set α), b ≤ a then ({a} : Finset α).card else 0) ≤
    chainHeightOf (α := α) a :=
    Finset.le_sup (f := fun (t : Finset α) => if IsChain (· ≤ ·) (t : Set α) ∧ a ∈ (t : Set α) ∧
      ∀ b ∈ (t : Set α), b ≤ a then t.card else 0) hmem
  have hchain : IsChain (· ≤ ·) ((({a} : Finset α)) : Set α) := by
    rw [Finset.coe_singleton]
    exact IsChain.singleton
  have hmem' : a ∈ ((({a} : Finset α)) : Set α) := by
    rw [Finset.coe_singleton]
    exact Set.mem_singleton a
  have hle' : ∀ b ∈ ((({a} : Finset α)) : Set α), b ≤ a := by
    intro b hb
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hb
    subst hb
    exact le_rfl
  rw [ite_eq_left ⟨hchain, hmem', hle'⟩, Finset.card_singleton] at hle
  exact hle

private theorem exists_chain_card_chainHeightOf {α : Type*} [Fintype α]
    [PartialOrder α] (a : α) : ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧
      a ∈ (s : Set α) ∧ (∀ b ∈ (s : Set α), b ≤ a) ∧
      s.card = chainHeightOf (α := α) a := by
  classical
  obtain ⟨s, -, hseq⟩ := Finset.exists_mem_eq_sup ((Finset.univ : Finset α).powerset)
    (Finset.powerset_nonempty _)
    (fun t => if IsChain (· ≤ ·) (t : Set α) ∧ a ∈ (t : Set α) ∧
      ∀ b ∈ (t : Set α), b ≤ a then t.card else 0)
  by_cases hcon : IsChain (· ≤ ·) (s : Set α) ∧ a ∈ (s : Set α) ∧
    ∀ b ∈ (s : Set α), b ≤ a
  · have h2 : (if IsChain (· ≤ ·) (s : Set α) ∧ a ∈ (s : Set α) ∧
      ∀ b ∈ (s : Set α), b ≤ a then s.card else 0) = chainHeightOf (α := α) a :=
      hseq.symm
    rw [ite_eq_left hcon] at h2
    exact ⟨s, hcon.1, hcon.2.1, hcon.2.2, h2⟩
  · have h2 : (if IsChain (· ≤ ·) (s : Set α) ∧ a ∈ (s : Set α) ∧
      ∀ b ∈ (s : Set α), b ≤ a then s.card else 0) = chainHeightOf (α := α) a :=
      hseq.symm
    rw [ite_eq_right hcon] at h2
    have h1 : 1 ≤ chainHeightOf (α := α) a := one_le_chainHeightOf (α := α) a
    omega

private theorem levelSet_isAntichain {α : Type*} [Fintype α]
    [PartialOrder α] (i : ℕ) : IsAntichain (· ≤ ·)
      ((Finset.univ.filter fun a => chainHeightOf (α := α) a = i : Finset α) : Set α) := by
  classical
  intro x hx y hy hne
  change ¬ x ≤ y
  intro hle
  have hxi : chainHeightOf (α := α) x = i :=
    (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
  have hyi : chainHeightOf (α := α) y = i :=
    (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).2
  obtain ⟨s, hs_chain, _, hs_le, hs_card⟩ := exists_chain_card_chainHeightOf (α := α) x
  have hy_not_mem : y ∉ s := by
    intro hyin
    have h1 : y ≤ x := hs_le y (Finset.mem_coe.mpr hyin)
    exact hne (le_antisymm hle h1)
  have ht_chain : IsChain (· ≤ ·) (((insert y s : Finset α)) : Set α) := by
    intro u hu v hv huv
    rw [Finset.coe_insert, Set.mem_insert_iff] at hu hv
    rcases hu with rfl | hus
    · rcases hv with rfl | hvs
      · exact Or.inl le_rfl
      · exact Or.inr (le_trans (hs_le v hvs) hle)
    · rcases hv with rfl | hvs
      · exact Or.inl (le_trans (hs_le u hus) hle)
      · exact hs_chain hus hvs huv
  have ht_mem : y ∈ (((insert y s : Finset α)) : Set α) := by
    rw [Finset.coe_insert]
    exact Set.mem_insert y _
  have ht_le : ∀ b ∈ (((insert y s : Finset α)) : Set α), b ≤ y := by
    intro b hb
    rw [Finset.coe_insert, Set.mem_insert_iff] at hb
    rcases hb with rfl | hbs
    · exact le_rfl
    · exact le_trans (hs_le b hbs) hle
  have ht_card : (insert y s : Finset α).card = i + 1 := by
    rw [Finset.card_insert_of_notMem hy_not_mem, hs_card, hxi]
  have hge : (insert y s : Finset α).card ≤ chainHeightOf (α := α) y := by
    have hmem : insert y s ∈ (Finset.univ : Finset α).powerset :=
      Finset.mem_powerset.mpr (Finset.subset_univ _)
    have hle2 : (if IsChain (· ≤ ·) (((insert y s : Finset α)) : Set α) ∧
      y ∈ (((insert y s : Finset α)) : Set α) ∧
      ∀ b ∈ (((insert y s : Finset α)) : Set α), b ≤ y then
      (insert y s : Finset α).card else 0) ≤ chainHeightOf (α := α) y :=
      Finset.le_sup (f := fun (t : Finset α) => if IsChain (· ≤ ·) (t : Set α) ∧ y ∈ (t : Set α) ∧
        ∀ b ∈ (t : Set α), b ≤ y then t.card else 0) hmem
    rw [ite_eq_left ⟨ht_chain, ht_mem, ht_le⟩] at hle2
    exact hle2
  omega

private noncomputable def mirskyCover {α : Type*} [Fintype α] [DecidableEq α]
    [PartialOrder α] : Finset (Finset α) :=
  (Finset.Icc 1 (maxChainSize α)).image fun i =>
    Finset.univ.filter fun a => chainHeightOf (α := α) a = i

private theorem mirskyCover_valid {α : Type*} [Fintype α] [DecidableEq α]
    [PartialOrder α] : IsAntichainCoverFin (α := α) (mirskyCover (α := α)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    have ht' : t ∈ (Finset.Icc 1 (maxChainSize α)).image
      (fun i => Finset.univ.filter fun a => chainHeightOf (α := α) a = i) := ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht'
    exact levelSet_isAntichain (α := α) i
  · intro a
    have hmem : a ∈ Finset.univ.filter
      (fun x => chainHeightOf (α := α) x = chainHeightOf (α := α) a) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, rfl⟩
    have himg : (Finset.univ.filter
      (fun x => chainHeightOf (α := α) x = chainHeightOf (α := α) a)) ∈
      mirskyCover (α := α) := by
      change _ ∈ (Finset.Icc 1 (maxChainSize α)).image
        (fun i => Finset.univ.filter fun x => chainHeightOf (α := α) x = i)
      rw [Finset.mem_image]
      exact ⟨chainHeightOf (α := α) a,
        Finset.mem_Icc.mpr ⟨one_le_chainHeightOf (α := α) a,
          chainHeightOf_le_maxChainSize (α := α) a⟩,
        rfl⟩
    exact ⟨_, himg, hmem⟩

private theorem singletons_isAntichainCover {α : Type*} [Fintype α] [DecidableEq α]
    [PartialOrder α] : IsAntichainCoverFin (α := α)
      ((Finset.univ : Finset α).image fun a => ({a} : Finset α)) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    show IsAntichain (· ≤ ·) ((({a} : Finset α)) : Set α)
    rw [Finset.coe_singleton]
    exact IsAntichain.singleton
  · intro a
    exact ⟨{a}, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩,
      Finset.mem_singleton_self a⟩

private theorem chain_card_le_cover {α : Type*} [PartialOrder α] (s : Finset α)
    (C : Finset (Finset α))
    (hs : IsChain (· ≤ ·) (s : Set α))
    (hC : IsAntichainCoverFin (α := α) C) : s.card ≤ C.card := by
  obtain ⟨hCanti, hCcov⟩ := hC
  have hex : ∀ x : α, ∃ A : Finset α,
      x ∈ (s : Set α) → A ∈ C ∧ x ∈ A := by
    intro x
    by_cases hx : x ∈ (s : Set α)
    · obtain ⟨A, hAC, hxA⟩ := hCcov x
      exact ⟨A, fun _ => ⟨hAC, hxA⟩⟩
    · exact ⟨∅, fun h => absurd h hx⟩
  choose f hf using hex
  refine Finset.card_le_card_of_injOn f
    (by intro x hx; exact Finset.mem_coe.mpr (hf x hx).1) ?_
  intro x hx y hy hxy
  by_contra hne
  have hcmp : x ≤ y ∨ y ≤ x := hs hx hy hne
  have hanti : IsAntichain (· ≤ ·) (((f x : Finset α)) : Set α) :=
    hCanti (f x) (hf x hx).1
  have hxm : x ∈ (((f x : Finset α)) : Set α) := Finset.mem_coe.mpr (hf x hx).2
  have hym : y ∈ (((f x : Finset α)) : Set α) := by
    rw [hxy]
    exact Finset.mem_coe.mpr (hf y hy).2
  rcases hcmp with hle | hle
  · exact hanti hxm hym hne hle
  · exact hanti hym hxm (Ne.symm hne) hle

private theorem minAntichainCoverSize_le_maxChainSize {α : Type*} [Fintype α]
    [PartialOrder α] : minAntichainCoverSize α ≤ maxChainSize α := by
  classical
  have hCcard : (mirskyCover (α := α)).card ≤ maxChainSize α := by
    have h1 : ((Finset.Icc 1 (maxChainSize α)).image
      (fun i => Finset.univ.filter fun a => chainHeightOf (α := α) a = i)).card ≤
      (Finset.Icc 1 (maxChainSize α)).card := Finset.card_image_le
    have h2 : (Finset.Icc 1 (maxChainSize α)).card = maxChainSize α := by
      rw [Nat.card_Icc]
      exact Nat.add_sub_cancel _ _
    have hCeq : (mirskyCover (α := α)).card = ((Finset.Icc 1 (maxChainSize α)).image
      (fun i => Finset.univ.filter fun a => chainHeightOf (α := α) a = i)).card := rfl
    rw [hCeq]
    exact le_trans h1 (le_of_eq h2)
  have hCmem : mirskyCover (α := α) ∈ ((((Finset.univ.powerset).powerset :
      Finset (Finset (Finset α)))).filter fun C => IsAntichainCoverFin (α := α) C) := by
    rw [Finset.mem_filter]
    refine ⟨?_, mirskyCover_valid (α := α)⟩
    show mirskyCover (α := α) ∈
      (((Finset.univ.powerset).powerset : Finset (Finset (Finset α))))
    rw [Finset.mem_powerset]
    intro t ht
    have ht' : t ∈ (Finset.Icc 1 (maxChainSize α)).image
      (fun i => Finset.univ.filter fun a => chainHeightOf (α := α) a = i) := ht
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht'
    change (Finset.univ.filter (fun a => chainHeightOf (α := α) a = i)) ∈
      ((Finset.univ : Finset α).powerset)
    rw [Finset.mem_powerset]
    exact Finset.filter_subset _ _
  have hne : ((((Finset.univ.powerset).powerset :
      Finset (Finset (Finset α)))).filter fun C => IsAntichainCoverFin (α := α) C).Nonempty :=
    ⟨_, hCmem⟩
  have heq : minAntichainCoverSize α = ((((Finset.univ.powerset).powerset :
      Finset (Finset (Finset α)))).filter fun C => IsAntichainCoverFin (α := α) C).inf'
      hne (fun C => C.card) := dite_eq_left hne
  rw [heq]
  exact le_trans (Finset.inf'_le _ hCmem) hCcard

private theorem maxChainSize_le_minAntichainCoverSize {α : Type*} [Fintype α]
    [PartialOrder α] : maxChainSize α ≤ minAntichainCoverSize α := by
  classical
  have hC₀ : IsAntichainCoverFin (α := α)
      ((Finset.univ : Finset α).image fun a => ({a} : Finset α)) :=
    singletons_isAntichainCover (α := α)
  have hC₀mem : ((Finset.univ : Finset α).image fun a => ({a} : Finset α)) ∈
      ((((Finset.univ.powerset).powerset : Finset (Finset (Finset α)))).filter
        fun C => IsAntichainCoverFin (α := α) C) := by
    rw [Finset.mem_filter]
    refine ⟨?_, hC₀⟩
    rw [Finset.mem_powerset]
    intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    show (({a} : Finset α)) ∈ ((Finset.univ : Finset α).powerset)
    rw [Finset.mem_powerset]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_univ a)
  have hne : ((((Finset.univ.powerset).powerset : Finset (Finset (Finset α)))).filter
      fun C => IsAntichainCoverFin (α := α) C).Nonempty := ⟨_, hC₀mem⟩
  have heq : minAntichainCoverSize α = ((((Finset.univ.powerset).powerset :
      Finset (Finset (Finset α)))).filter fun C => IsAntichainCoverFin (α := α) C).inf'
      hne (fun C => C.card) := dite_eq_left hne
  rw [heq]
  refine Finset.le_inf' hne _ fun C hC => ?_
  change maxChainSize α ≤ C.card
  obtain ⟨-, hC⟩ := Finset.mem_filter.mp hC
  obtain ⟨hCanti, hCcov⟩ := hC
  have hsup : ((Finset.univ : Finset α).powerset).sup
      (fun s => if IsChain (· ≤ ·) (s : Set α) then s.card else 0) ≤ C.card := by
    refine Finset.sup_le fun s _ => ?_
    change (if IsChain (· ≤ ·) (s : Set α) then s.card else 0) ≤ _
    by_cases hs : IsChain (· ≤ ·) (s : Set α)
    · rw [ite_eq_left hs]
      exact chain_card_le_cover (α := α) s C hs ⟨hCanti, hCcov⟩
    · rw [ite_eq_right hs]
      exact Nat.zero_le _
  exact hsup

theorem card_le_maxChainSize {α : Type*} [Fintype α] [PartialOrder α]
    (s : Finset α) (hs : IsChain (· ≤ ·) (s : Set α)) : s.card ≤ maxChainSize α := by
  classical
  have hle : (if IsChain (· ≤ ·) (s : Set α) then s.card else 0) ≤ maxChainSize α :=
    Finset.le_sup (f := fun (t : Finset α) => if IsChain (· ≤ ·) (t : Set α) then t.card else 0)
      (Finset.mem_powerset.mpr (Finset.subset_univ s))
  rwa [ite_eq_left hs] at hle

theorem exists_chain_card_eq_maxChainSize {α : Type*} [Fintype α]
    [PartialOrder α] : ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = maxChainSize α := by
  classical
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_eq_sup ((Finset.univ : Finset α).powerset)
    (Finset.powerset_nonempty _) (fun t => if IsChain (· ≤ ·) (t : Set α) then t.card else 0)
  have h2 : (if IsChain (· ≤ ·) (s : Set α) then s.card else 0) = maxChainSize α := hs.symm
  by_cases hc : IsChain (· ≤ ·) (s : Set α)
  · rw [ite_eq_left hc] at h2
    exact ⟨s, hc, h2⟩
  · rw [ite_eq_right hc] at h2
    refine ⟨∅, ?_, by rw [Finset.card_empty, h2]⟩
    rw [Finset.coe_empty]
    exact IsChain.empty

theorem minAntichainCoverSize_le_card {α : Type*} [Fintype α] [PartialOrder α]
    (C : Finset (Finset α)) (hC : IsAntichainCoverFin C) : minAntichainCoverSize α ≤ C.card := by
  classical
  have hCmem : C ∈ ((((Finset.univ.powerset).powerset :
      Finset (Finset (Finset α)))).filter fun C => IsAntichainCoverFin (α := α) C) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr fun t _ =>
      Finset.mem_powerset.mpr (Finset.subset_univ t), hC⟩
  have hne : ((((Finset.univ.powerset).powerset :
      Finset (Finset (Finset α)))).filter fun C => IsAntichainCoverFin (α := α) C).Nonempty :=
    ⟨C, hCmem⟩
  have heq : minAntichainCoverSize α = ((((Finset.univ.powerset).powerset :
      Finset (Finset (Finset α)))).filter fun C => IsAntichainCoverFin (α := α) C).inf'
      hne (fun C => C.card) := dite_eq_left hne
  rw [heq]
  exact Finset.inf'_le _ hCmem

theorem exists_antichainCover_card_eq_minAntichainCoverSize {α : Type*} [Fintype α]
    [PartialOrder α] :
    ∃ C : Finset (Finset α), IsAntichainCoverFin C ∧ C.card = minAntichainCoverSize α := by
  classical
  have hC₀mem : ((Finset.univ : Finset α).image fun a => ({a} : Finset α)) ∈
      ((((Finset.univ.powerset).powerset : Finset (Finset (Finset α)))).filter
        fun C => IsAntichainCoverFin (α := α) C) :=
    Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr fun t _ =>
      Finset.mem_powerset.mpr (Finset.subset_univ t), singletons_isAntichainCover (α := α)⟩
  have hne : ((((Finset.univ.powerset).powerset : Finset (Finset (Finset α)))).filter
      fun C => IsAntichainCoverFin (α := α) C).Nonempty := ⟨_, hC₀mem⟩
  obtain ⟨C, hC, hCeq⟩ := Finset.exists_mem_eq_inf' hne (fun C => C.card)
  have heq : minAntichainCoverSize α = ((((Finset.univ.powerset).powerset :
      Finset (Finset (Finset α)))).filter fun C => IsAntichainCoverFin (α := α) C).inf'
      hne (fun C => C.card) := dite_eq_left hne
  exact ⟨C, (Finset.mem_filter.mp hC).2, by rw [heq, hCeq]⟩


/-- **Dual of Dilworth's theorem.** For every finite partially ordered set $\alpha$, the maximum
chain size of $\alpha$ equals its minimum antichain cover size: the largest cardinality of a chain
in $\alpha$ equals the smallest number of antichains whose union is $\alpha$. -/
theorem mirsky_dual_general {α : Type*} [Fintype α] [PartialOrder α] :
    maxChainSize α = minAntichainCoverSize α := by
  exact le_antisymm maxChainSize_le_minAntichainCoverSize
    minAntichainCoverSize_le_maxChainSize

set_option linter.unusedDecidableInType false in
/--
**Mirsky's theorem.** For every finite partially ordered set $\alpha$, the maximum chain size of
$\alpha$ equals its minimum antichain cover size: the largest cardinality of a chain in $\alpha$
equals the smallest number of antichains whose union is $\alpha$.

Proves `Wanted` entry `mirsky_dual`.

Source: L. Mirsky, Amer. Math. Monthly 78 (1971), 876-877, DOI 10.2307/2316481.
It follows from `mirsky_dual_general`; the instance `[DecidableEq α]` is unused and keeps the
Wanted entry's shape.
-/
@[nolint unusedArguments]
theorem mirsky_dual {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] :
    maxChainSize α = minAntichainCoverSize α :=
  mirsky_dual_general

end MathlibExt.Combinatorics.Order.FinitePosets
