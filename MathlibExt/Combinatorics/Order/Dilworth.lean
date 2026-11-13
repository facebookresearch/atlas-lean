/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Antichain
import Mathlib.Order.Lattice.Nat

@[expose] public section

section
namespace MathlibExt.Combinatorics.Order.DilworthWanted

/-!
# Dilworth's decomposition theorem

In a finite partial order, the largest antichain has as many elements as the fewest chains
covering the order: `maxAntichainSize α = minChainCoverSize α`.
-/

/-- **Chain cover.** Let $\alpha$ be a partially ordered set. A finite set $C$ of finite subsets of
$\alpha$ is a chain cover of $\alpha$ when every member of $C$ is a chain and every element of
$\alpha$ lies in some member of $C$. -/
def IsChainCoverFin {α : Type*} [PartialOrder α] (C : Finset (Finset α)) : Prop :=
  (∀ s ∈ C, IsChain (· ≤ ·) (s : Set α)) ∧ ∀ a : α, ∃ s ∈ C, a ∈ s

open Classical in
/-- **Maximum antichain size.** For a finite partially ordered set $\alpha$, the maximum antichain
size of $\alpha$ (its width) is the largest number of elements of an antichain in $\alpha$. -/
noncomputable def maxAntichainSize
    (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  ((Finset.univ : Finset α).powerset).sup fun s =>
    if IsAntichain (· ≤ ·) (s : Set α) then s.card else 0

open Classical in
/-- **Minimum chain cover size.** For a finite partially ordered set $\alpha$, the minimum chain
cover size of $\alpha$ is the smallest number of chains in a chain cover of $\alpha$, that is, in
a finite set of chains of $\alpha$ whose union is $\alpha$. -/
noncomputable def minChainCoverSize
    (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  let all : Finset (Finset (Finset α)) := (Finset.univ.powerset).powerset
  let valid := all.filter fun C => IsChainCoverFin (α := α) C
  if h : valid.Nonempty then valid.inf' h fun C => C.card else 0

-- Helper: width of a finite sub-collection, relativized to a finset.
open Classical in
private noncomputable def widthFin {α : Type*} [Fintype α] [PartialOrder α]
    (s : Finset α) : ℕ :=
  (s.powerset).sup fun t =>
    if IsAntichain (· ≤ ·) (t : Set α) then t.card else 0

-- Helper: chain cover of a finset `s` (chains lie inside `s`).
private def IsChainCoverOf {α : Type*} [PartialOrder α] (s : Finset α)
    (C : Finset (Finset α)) : Prop :=
  (∀ t ∈ C, t ⊆ s) ∧ (∀ t ∈ C, IsChain (· ≤ ·) (t : Set α)) ∧ ∀ a ∈ s, ∃ t ∈ C, a ∈ t

private theorem widthFin_mono {α : Type*} [Fintype α] [PartialOrder α]
    {s t : Finset α} (h : s ⊆ t) : widthFin s ≤ widthFin t := by
  classical
  unfold widthFin
  apply Finset.sup_mono
  exact Finset.powerset_mono.mpr h

private theorem isAntichain_singleton {α : Type*} [PartialOrder α] (a : α) :
    IsAntichain (· ≤ ·) ({a} : Set α) :=
  IsAntichain.singleton (r := (· ≤ ·)) (a := a)

private theorem isAntichain_coe_singleton {α : Type*} [PartialOrder α] (a : α) :
    IsAntichain (· ≤ ·) ((({a} : Finset α)) : Set α) := by
  rw [Finset.coe_singleton]
  exact isAntichain_singleton a

private theorem widthFin_ge_one_of_mem {α : Type*} [Fintype α] [PartialOrder α]
    {s : Finset α} {a : α} (h : a ∈ s) : 1 ≤ widthFin s := by
  classical
  have hm : ({a} : Finset α) ∈ s.powerset := by
    rw [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_singleton] at hx; subst hx; exact h
  have hle := Finset.le_sup (s := s.powerset)
    (f := fun t => if IsAntichain (· ≤ ·) (t : Set α) then t.card else 0) hm
  have hA : IsAntichain (· ≤ ·) (({a} : Finset α) : Set α) :=
    isAntichain_coe_singleton a
  have hif :
      (if IsAntichain (· ≤ ·) (({a} : Finset α) : Set α) then ({a} : Finset α).card else 0) = 1 := by
    rw [ite_eq_left hA, Finset.card_singleton]
  unfold widthFin
  omega

-- Attainment: some antichain inside `s` realizes the width.
private theorem exists_antichain_card_widthFin {α : Type*} [Fintype α]
    [PartialOrder α] (s : Finset α) :
    ∃ A ∈ s.powerset, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = widthFin s := by
  classical
  obtain ⟨t, ht, hsup⟩ := Finset.exists_mem_eq_sup s.powerset
    (Finset.powerset_nonempty s)
    (fun t => if IsAntichain (· ≤ ·) (t : Set α) then t.card else 0)
  have hwidth : widthFin s =
      (if IsAntichain (· ≤ ·) (t : Set α) then t.card else 0) := hsup
  by_cases hanti : IsAntichain (· ≤ ·) (t : Set α)
  · refine ⟨t, ht, hanti, ?_⟩
    rw [hwidth]
    simp [hanti]
  · refine ⟨∅, Finset.empty_mem_powerset s, fun a ha b hb _ => by simp at ha, ?_⟩
    rw [hwidth]
    simp [hanti]

-- Easy direction at the level of finsets: an antichain covered by chains is no bigger.
private theorem card_antichain_le_cover {α : Type*} [PartialOrder α]
    {s : Finset α} {A : Finset α} {C : Finset (Finset α)}
    (hAsub : ↑A ⊆ ↑s) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hC : IsChainCoverOf s C) : A.card ≤ C.card := by
  classical
  have hcov := hC.2.2
  have hchain := hC.2.1
  have hex : ∀ a ∈ A, ∃ t ∈ C, a ∈ t := by
    intro a ha
    have has : a ∈ s := hAsub ha
    exact hcov a has
  choose f hfC hfmem using hex
  let F : ↥A → ↥C := fun a => ⟨f a.1 a.2, hfC a.1 a.2⟩
  have hinj : Function.Injective F := by
    intro a1 a2 heq
    have hfeq : f a1.1 a1.2 = f a2.1 a2.2 := congrArg Subtype.val heq
    by_contra hne
    have hne' : (a1 : α) ≠ (a2 : α) := fun h => hne (Subtype.ext h)
    have m1 : (a1 : α) ∈ (f a1.1 a1.2 : Set α) := hfmem a1.1 a1.2
    have m2 : (a2 : α) ∈ (f a1.1 a1.2 : Set α) := hfeq ▸ hfmem a2.1 a2.2
    have hch : IsChain (· ≤ ·) ((f a1.1 a1.2 : Finset α) : Set α) :=
      hchain (f a1.1 a1.2) (hfC a1.1 a1.2)
    unfold IsChain Set.Pairwise at hch
    have hle : ((a1 : α) ≤ (a2 : α)) ∨ ((a2 : α) ≤ (a1 : α)) := hch m1 m2 hne'
    unfold IsAntichain Set.Pairwise at hA
    have ha1' : (a1 : α) ∈ (A : Set α) := a1.2
    have ha2' : (a2 : α) ∈ (A : Set α) := a2.2
    rcases hle with h | h
    · exact hA ha1' ha2' hne' h
    · exact hA ha2' ha1' (Ne.symm hne') h
  have hle := Fintype.card_le_of_injective F hinj
  rwa [Fintype.card_coe, Fintype.card_coe] at hle

-- Any antichain inside `s` is bounded by the width.
private theorem card_le_widthFin {α : Type*} [Fintype α] [PartialOrder α]
    {s t : Finset α} (ht : t ∈ s.powerset) (hA : IsAntichain (· ≤ ·) (t : Set α)) :
    t.card ≤ widthFin s := by
  classical
  have hle := Finset.le_sup (s := s.powerset)
    (f := fun u => if IsAntichain (· ≤ ·) (u : Set α) then u.card else 0) ht
  have hle2 : (if IsAntichain (· ≤ ·) (t : Set α) then t.card else 0) ≤ widthFin s := hle
  rw [ite_eq_left hA] at hle2
  exact hle2

/-- **Antichains are no larger than the maximum antichain size.** Let $\alpha$ be a finite
partially ordered set. Every antichain $A$ in $\alpha$ has at most as many elements as the
maximum antichain size of $\alpha$. -/
theorem card_le_maxAntichainSize {α : Type*} [Fintype α] [PartialOrder α]
    {A : Finset α} (hA : IsAntichain (· ≤ ·) (A : Set α)) : A.card ≤ maxAntichainSize α :=
  card_le_widthFin (Finset.mem_powerset.mpr (Finset.subset_univ A)) hA

-- Minimal / maximal elements of a finset, and the up/down sets of an antichain.
open Classical in
private noncomputable def minSetOf {α : Type*} [PartialOrder α]
    (s : Finset α) : Finset α :=
  s.filter fun a => ∀ b ∈ s, b ≤ a → a ≤ b

open Classical in
private noncomputable def maxSetOf {α : Type*} [PartialOrder α]
    (s : Finset α) : Finset α :=
  s.filter fun a => ∀ b ∈ s, a ≤ b → b ≤ a

open Classical in
private noncomputable def upSetOf {α : Type*} [PartialOrder α]
    (s A : Finset α) : Finset α :=
  s.filter fun x => ∃ a ∈ A, a ≤ x

open Classical in
private noncomputable def downSetOf {α : Type*} [PartialOrder α]
    (s A : Finset α) : Finset α :=
  s.filter fun x => ∃ a ∈ A, x ≤ a

private theorem upSetOf_subset {α : Type*} [PartialOrder α]
    (s A : Finset α) : upSetOf s A ⊆ s := by
  classical
  unfold upSetOf
  exact Finset.filter_subset _ _

private theorem downSetOf_subset {α : Type*} [PartialOrder α]
    (s A : Finset α) : downSetOf s A ⊆ s := by
  classical
  unfold downSetOf
  exact Finset.filter_subset _ _

private theorem subset_upSetOf {α : Type*} [PartialOrder α]
    {s A : Finset α} (h : A ⊆ s) : A ⊆ upSetOf s A := by
  classical
  intro a ha
  unfold upSetOf
  rw [Finset.mem_filter]
  exact ⟨h ha, a, ha, le_rfl⟩

private theorem subset_downSetOf {α : Type*} [PartialOrder α]
    {s A : Finset α} (h : A ⊆ s) : A ⊆ downSetOf s A := by
  classical
  intro a ha
  unfold downSetOf
  rw [Finset.mem_filter]
  exact ⟨h ha, a, ha, le_rfl⟩

private theorem mem_upSetOf_of_mem {α : Type*} [PartialOrder α]
    {s A : Finset α} {x : α} (hx : x ∈ s) (hex : ∃ a ∈ A, a ≤ x) :
    x ∈ upSetOf s A := by
  classical
  unfold upSetOf
  rw [Finset.mem_filter]
  exact ⟨hx, hex⟩

private theorem mem_downSetOf_of_mem {α : Type*} [PartialOrder α]
    {s A : Finset α} {x : α} (hx : x ∈ s) (hex : ∃ a ∈ A, x ≤ a) :
    x ∈ downSetOf s A := by
  classical
  unfold downSetOf
  rw [Finset.mem_filter]
  exact ⟨hx, hex⟩

-- Membership characterizations.
private theorem mem_minSetOf_iff {α : Type*} [PartialOrder α]
    {s : Finset α} {a : α} :
    a ∈ minSetOf s ↔ a ∈ s ∧ ∀ b ∈ s, b ≤ a → a ≤ b := by
  classical
  unfold minSetOf
  rw [Finset.mem_filter]

private theorem mem_maxSetOf_iff {α : Type*} [PartialOrder α]
    {s : Finset α} {a : α} :
    a ∈ maxSetOf s ↔ a ∈ s ∧ ∀ b ∈ s, a ≤ b → b ≤ a := by
  classical
  unfold maxSetOf
  rw [Finset.mem_filter]

private theorem mem_upSetOf_iff {α : Type*} [PartialOrder α]
    {s A : Finset α} {x : α} :
    x ∈ upSetOf s A ↔ x ∈ s ∧ ∃ a ∈ A, a ≤ x := by
  classical
  unfold upSetOf
  rw [Finset.mem_filter]

private theorem mem_downSetOf_iff {α : Type*} [PartialOrder α]
    {s A : Finset α} {x : α} :
    x ∈ downSetOf s A ↔ x ∈ s ∧ ∃ a ∈ A, x ≤ a := by
  classical
  unfold downSetOf
  rw [Finset.mem_filter]

-- A maximum antichain's up/down sets cover `s`.
open Classical in
private theorem union_up_down_of_maximal {α : Type*} [Fintype α] [PartialOrder α]
    {s A : Finset α} (hmem : A ∈ s.powerset) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hcard : A.card = widthFin s) :
    upSetOf s A ∪ downSetOf s A = s := by
  classical
  have hAsub : A ⊆ s := Finset.mem_powerset.mp hmem
  apply le_antisymm
  · exact Finset.union_subset (upSetOf_subset s A) (downSetOf_subset s A)
  · intro x hxs
    by_cases hup : x ∈ upSetOf s A
    · exact Finset.mem_union_left _ hup
    · by_cases hdown : x ∈ downSetOf s A
      · exact Finset.mem_union_right _ hdown
      · exfalso
        have hxA : x ∉ A := by
          intro hxA
          exact hup (subset_upSetOf hAsub hxA)
        have hBanti : IsAntichain (· ≤ ·) ((insert x A : Finset α) : Set α) := by
          unfold IsAntichain Set.Pairwise
          intro u hu v hv hne
          rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu hv
          rcases hu with rfl | huA <;> rcases hv with rfl | hvA
          · exact absurd rfl hne
          · intro hle
            exact hdown (mem_downSetOf_of_mem hxs ⟨v, hvA, hle⟩)
          · intro hle
            exact hup (mem_upSetOf_of_mem hxs ⟨u, huA, hle⟩)
          · intro hle
            exact hA (Finset.mem_coe.mpr huA) (Finset.mem_coe.mpr hvA) hne hle
        have hBmem : insert x A ∈ s.powerset := by
          rw [Finset.mem_powerset]
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyA
          · exact hxs
          · exact hAsub hyA
        have hBle := card_le_widthFin hBmem hBanti
        rw [Finset.card_insert_of_notMem hxA] at hBle
        omega

-- If `A` differs from the minima, its up-set is a proper subset (and dually).
private theorem upSetOf_ssubset_of_ne_min {α : Type*} [Fintype α] [PartialOrder α]
    {s A : Finset α} (hmem : A ∈ s.powerset) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hcard : A.card = widthFin s) (hne : minSetOf s ≠ A) :
    upSetOf s A ⊂ s := by
  classical
  have hAsub : A ⊆ s := Finset.mem_powerset.mp hmem
  have hsub : upSetOf s A ⊆ s := upSetOf_subset s A
  have hwit : ∃ b ∈ s, b ∉ upSetOf s A := by
    have hdisj : (∃ a ∈ A, a ∉ minSetOf s) ∨ (∃ m ∈ minSetOf s, m ∉ A) := by
      by_contra hc
      obtain ⟨hcA, hcm⟩ := not_or.mp hc
      have hAsubmin : A ⊆ minSetOf s := by
        intro a ha
        by_contra hcon
        exact (not_exists.mp hcA) a ⟨ha, hcon⟩
      have hminsubA : minSetOf s ⊆ A := by
        intro m hm
        by_contra hcon
        exact (not_exists.mp hcm) m ⟨hm, hcon⟩
      exact hne (le_antisymm hminsubA hAsubmin)
    rcases hdisj with ⟨a, haA, hanmin⟩ | ⟨m, hmmin, hmA⟩
    · have has : a ∈ s := hAsub haA
      have hnpred : ¬ ∀ b ∈ s, b ≤ a → a ≤ b := by
        intro hpred
        exact hanmin (mem_minSetOf_iff.mpr ⟨has, hpred⟩)
      obtain ⟨b, hb⟩ := not_forall.mp hnpred
      obtain ⟨hbs, hb2⟩ := not_imp.mp hb
      obtain ⟨hba, hnle⟩ := not_imp.mp hb2
      refine ⟨b, hbs, ?_⟩
      intro hbup
      obtain ⟨a', ha'A, hale⟩ := (mem_upSetOf_iff.mp hbup).2
      have hle : a' ≤ a := le_trans hale hba
      by_cases heq : a' = a
      · subst heq
        exact hnle hale
      · exact hA (Finset.mem_coe.mpr ha'A) (Finset.mem_coe.mpr haA) heq hle
    · obtain ⟨hms, hminprop⟩ := mem_minSetOf_iff.mp hmmin
      have hmdown : m ∈ downSetOf s A := by
        by_contra hcon
        have hBanti : IsAntichain (· ≤ ·) ((insert m A : Finset α) : Set α) := by
          unfold IsAntichain Set.Pairwise
          intro u hu v hv hne2
          rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu hv
          rcases hu with hu_eq | huA <;> rcases hv with hv_eq | hvA
          · intro hle
            rw [hu_eq, hv_eq] at hle hne2
            exact hne2 rfl
          · intro hle
            rw [hu_eq] at hle
            exact hcon (mem_downSetOf_of_mem hms ⟨v, hvA, hle⟩)
          · intro hle
            rw [hv_eq] at hle
            have hmu : m ≤ u := hminprop u (hAsub huA) hle
            have heq : u = m := le_antisymm hle hmu
            rw [heq] at huA
            exact hmA huA
          · intro hle
            exact hA (Finset.mem_coe.mpr huA) (Finset.mem_coe.mpr hvA) hne2 hle
        have hBmem : insert m A ∈ s.powerset := by
          rw [Finset.mem_powerset]
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyA
          · exact hms
          · exact hAsub hyA
        have hBle := card_le_widthFin hBmem hBanti
        rw [Finset.card_insert_of_notMem hmA] at hBle
        omega
      have hmup : m ∉ upSetOf s A := by
        intro hup
        obtain ⟨a, haA, hale⟩ := (mem_upSetOf_iff.mp hup).2
        have hma : m ≤ a := hminprop a (hAsub haA) hale
        have heq : a = m := le_antisymm hale hma
        subst heq
        exact hmA haA
      exact ⟨m, hms, hmup⟩
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsub, fun heq => ?_⟩
  obtain ⟨b, hbs, hbup⟩ := hwit
  have hbs' : b ∈ upSetOf s A := by rw [heq]; exact hbs
  exact hbup hbs'

private theorem downSetOf_ssubset_of_ne_max {α : Type*} [Fintype α] [PartialOrder α]
    {s A : Finset α} (hmem : A ∈ s.powerset) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hcard : A.card = widthFin s) (hne : maxSetOf s ≠ A) :
    downSetOf s A ⊂ s := by
  classical
  have hAsub : A ⊆ s := Finset.mem_powerset.mp hmem
  have hsub : downSetOf s A ⊆ s := downSetOf_subset s A
  have hwit : ∃ b ∈ s, b ∉ downSetOf s A := by
    have hdisj : (∃ a ∈ A, a ∉ maxSetOf s) ∨ (∃ m ∈ maxSetOf s, m ∉ A) := by
      by_contra hc
      obtain ⟨hcA, hcm⟩ := not_or.mp hc
      have hAsubmax : A ⊆ maxSetOf s := by
        intro a ha
        by_contra hcon
        exact (not_exists.mp hcA) a ⟨ha, hcon⟩
      have hmaxsubA : maxSetOf s ⊆ A := by
        intro m hm
        by_contra hcon
        exact (not_exists.mp hcm) m ⟨hm, hcon⟩
      exact hne (le_antisymm hmaxsubA hAsubmax)
    rcases hdisj with ⟨a, haA, hanmax⟩ | ⟨m, hmmax, hmA⟩
    · have has : a ∈ s := hAsub haA
      have hnpred : ¬ ∀ b ∈ s, a ≤ b → b ≤ a := by
        intro hpred
        exact hanmax (mem_maxSetOf_iff.mpr ⟨has, hpred⟩)
      obtain ⟨b, hb⟩ := not_forall.mp hnpred
      obtain ⟨hbs, hb2⟩ := not_imp.mp hb
      obtain ⟨hab, hnle⟩ := not_imp.mp hb2
      refine ⟨b, hbs, ?_⟩
      intro hbdown
      obtain ⟨a', ha'A, hale⟩ := (mem_downSetOf_iff.mp hbdown).2
      have hle : a ≤ a' := le_trans hab hale
      by_cases heq : a = a'
      · subst heq
        exact hnle hale
      · exact hA (Finset.mem_coe.mpr haA) (Finset.mem_coe.mpr ha'A) heq hle
    · obtain ⟨hms, hmaxprop⟩ := mem_maxSetOf_iff.mp hmmax
      have hmup : m ∈ upSetOf s A := by
        by_contra hcon
        have hBanti : IsAntichain (· ≤ ·) ((insert m A : Finset α) : Set α) := by
          unfold IsAntichain Set.Pairwise
          intro u hu v hv hne2
          rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hu hv
          rcases hu with hu_eq | huA <;> rcases hv with hv_eq | hvA
          · intro hle
            rw [hu_eq, hv_eq] at hle hne2
            exact hne2 rfl
          · intro hle
            rw [hu_eq] at hle
            have hmv : v ≤ m := hmaxprop v (hAsub hvA) hle
            have heq : v = m := le_antisymm hmv hle
            rw [heq] at hvA
            exact hmA hvA
          · intro hle
            rw [hv_eq] at hle
            exact hcon (mem_upSetOf_of_mem hms ⟨u, huA, hle⟩)
          · intro hle
            exact hA (Finset.mem_coe.mpr huA) (Finset.mem_coe.mpr hvA) hne2 hle
        have hBmem : insert m A ∈ s.powerset := by
          rw [Finset.mem_powerset]
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hyA
          · exact hms
          · exact hAsub hyA
        have hBle := card_le_widthFin hBmem hBanti
        rw [Finset.card_insert_of_notMem hmA] at hBle
        omega
      have hmdown : m ∉ downSetOf s A := by
        intro hdown
        obtain ⟨a, haA, hale⟩ := (mem_downSetOf_iff.mp hdown).2
        have hma : a ≤ m := hmaxprop a (hAsub haA) hale
        have heq : a = m := le_antisymm hma hale
        subst heq
        exact hmA haA
      exact ⟨m, hms, hmdown⟩
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsub, fun heq => ?_⟩
  obtain ⟨b, hbs, hbdown⟩ := hwit
  have hbs' : b ∈ downSetOf s A := by rw [heq]; exact hbs
  exact hbdown hbs'

-- The up/down sets have the same width as `s`.
private theorem widthFin_upSetOf {α : Type*} [Fintype α] [PartialOrder α]
    {s A : Finset α} (hmem : A ∈ s.powerset) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hcard : A.card = widthFin s) :
    widthFin (upSetOf s A) = widthFin s := by
  classical
  apply le_antisymm
  · exact widthFin_mono (upSetOf_subset s A)
  · have hAup : A ∈ (upSetOf s A).powerset :=
      Finset.mem_powerset.mpr (subset_upSetOf (Finset.mem_powerset.mp hmem))
    have hle := card_le_widthFin hAup hA
    omega

private theorem widthFin_downSetOf {α : Type*} [Fintype α] [PartialOrder α]
    {s A : Finset α} (hmem : A ∈ s.powerset) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hcard : A.card = widthFin s) :
    widthFin (downSetOf s A) = widthFin s := by
  classical
  apply le_antisymm
  · exact widthFin_mono (downSetOf_subset s A)
  · have hAdown : A ∈ (downSetOf s A).powerset :=
      Finset.mem_powerset.mpr (subset_downSetOf (Finset.mem_powerset.mp hmem))
    have hle := card_le_widthFin hAdown hA
    omega

-- A down-chain and an up-chain sharing an antichain element glue to a chain.
open Classical in
private theorem union_down_up_chain {α : Type*} [PartialOrder α]
    {s A c₁ c₂ : Finset α} {a : α}
    (hch1 : IsChain (· ≤ ·) (c₁ : Set α)) (hch2 : IsChain (· ≤ ·) (c₂ : Set α))
    (hsub1 : c₁ ⊆ downSetOf s A) (hsub2 : c₂ ⊆ upSetOf s A)
    (hAanti : IsAntichain (· ≤ ·) (A : Set α))
    (haA : a ∈ A) (ha1 : a ∈ c₁) (ha2 : a ∈ c₂) :
    IsChain (· ≤ ·) ((c₁ ∪ c₂ : Finset α) : Set α) := by
  classical
  unfold IsChain Set.Pairwise at hch1 hch2 ⊢
  intro x hx y hy hne
  have hx' : x ∈ c₁ ∪ c₂ := Finset.mem_coe.mp hx
  have hy' : y ∈ c₁ ∪ c₂ := Finset.mem_coe.mp hy
  have ha1' : a ∈ (c₁ : Set α) := Finset.mem_coe.mpr ha1
  have ha2' : a ∈ (c₂ : Set α) := Finset.mem_coe.mpr ha2
  have hcross : ∀ x ∈ c₁, ∀ y ∈ c₂, x ≠ y → (x ≤ y) ∨ (y ≤ x) := by
    intro x hx1 y hy2 hne'
    obtain ⟨a₁, ha₁A, hxle⟩ := (mem_downSetOf_iff.mp (hsub1 hx1)).2
    obtain ⟨a₂, ha₂A, hyle⟩ := (mem_upSetOf_iff.mp (hsub2 hy2)).2
    by_cases hxa : x = a
    · subst hxa
      exact hch2 ha2' (Finset.mem_coe.mpr hy2) hne'
    · by_cases hya : y = a
      · subst hya
        exact hch1 (Finset.mem_coe.mpr hx1) ha1' hne'
      · have oy : (a ≤ y) ∨ (y ≤ a) := hch2 ha2' (Finset.mem_coe.mpr hy2) (Ne.symm hya)
        have ox : (x ≤ a) ∨ (a ≤ x) := hch1 (Finset.mem_coe.mpr hx1) ha1' hxa
        rcases ox with hxa_le | hax <;> rcases oy with hay | hya_le
        · exact Or.inl (le_trans hxa_le hay)
        · have h2a : a₂ ≤ a := le_trans hyle hya_le
          by_cases heq2 : a₂ = a
          · subst heq2
            exact Or.inl (le_trans hxa_le hyle)
          · exact False.elim
              (hAanti (Finset.mem_coe.mpr ha₂A) (Finset.mem_coe.mpr haA) heq2 h2a)
        · have ha1x : a ≤ a₁ := le_trans hax hxle
          by_cases heq1 : a = a₁
          · subst heq1
            exact Or.inl (le_trans hxle hay)
          · exact False.elim
              (hAanti (Finset.mem_coe.mpr haA) (Finset.mem_coe.mpr ha₁A) heq1 ha1x)
        · exact Or.inr (le_trans hya_le hax)
  rcases Finset.mem_union.mp hx' with hx1 | hx2 <;>
    rcases Finset.mem_union.mp hy' with hy1 | hy2
  · exact hch1 (Finset.mem_coe.mpr hx1) (Finset.mem_coe.mpr hy1) hne
  · exact hcross x hx1 y hy2 hne
  · exact (hcross y hy1 x hx2 (Ne.symm hne)).symm
  · exact hch2 (Finset.mem_coe.mpr hx2) (Finset.mem_coe.mpr hy2) hne

-- Gluing covers of the up/down sets along a maximum antichain.
open Classical in
private theorem exists_cover_of_split {α : Type*} [Fintype α] [PartialOrder α]
    {s A : Finset α} (hmem : A ∈ s.powerset) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hcard : A.card = widthFin s)
    (hunion : upSetOf s A ∪ downSetOf s A = s)
    {Cup Cdown : Finset (Finset α)}
    (hCup : IsChainCoverOf (upSetOf s A) Cup) (hCupcard : Cup.card ≤ widthFin s)
    (hCdown : IsChainCoverOf (downSetOf s A) Cdown) (hCdowncard : Cdown.card ≤ widthFin s) :
    ∃ C, IsChainCoverOf s C ∧ C.card ≤ widthFin s := by
  classical
  have hAsub : A ⊆ s := Finset.mem_powerset.mp hmem
  have hAup : A ⊆ upSetOf s A := subset_upSetOf hAsub
  have hAdown : A ⊆ downSetOf s A := subset_downSetOf hAsub
  have hAleU : A.card ≤ Cup.card :=
    card_antichain_le_cover (Finset.coe_subset.mpr hAup) hA hCup
  have hAleL : A.card ≤ Cdown.card :=
    card_antichain_le_cover (Finset.coe_subset.mpr hAdown) hA hCdown
  have hCeqU : Cup.card = A.card := by omega
  have hCeqL : Cdown.card = A.card := by omega
  have hexU : ∀ a ∈ A, ∃ t ∈ Cup, a ∈ t := fun a ha => hCup.2.2 a (hAup ha)
  have hexL : ∀ a ∈ A, ∃ t ∈ Cdown, a ∈ t := fun a ha => hCdown.2.2 a (hAdown ha)
  choose U hUC hUmem using hexU
  choose L hLC hLmem using hexL
  have hAw := hA
  unfold IsAntichain Set.Pairwise at hAw
  let FU : ↥A → ↥Cup := fun a => ⟨U a.1 a.2, hUC a.1 a.2⟩
  let FL : ↥A → ↥Cdown := fun a => ⟨L a.1 a.2, hLC a.1 a.2⟩
  have hUinj : Function.Injective FU := by
    intro a1 a2 heq
    have hfeq : U a1.1 a1.2 = U a2.1 a2.2 := congrArg Subtype.val heq
    by_contra hne
    have hne' : (a1 : α) ≠ (a2 : α) := fun h => hne (Subtype.ext h)
    have m1 : (a1 : α) ∈ (U a1.1 a1.2 : Set α) := hUmem a1.1 a1.2
    have m2 : (a2 : α) ∈ (U a1.1 a1.2 : Set α) := hfeq ▸ hUmem a2.1 a2.2
    have hch : IsChain (· ≤ ·) ((U a1.1 a1.2 : Finset α) : Set α) :=
      hCup.2.1 (U a1.1 a1.2) (hUC a1.1 a1.2)
    unfold IsChain Set.Pairwise at hch
    have hle : ((a1 : α) ≤ (a2 : α)) ∨ ((a2 : α) ≤ (a1 : α)) := hch m1 m2 hne'
    have ha1' : (a1 : α) ∈ (A : Set α) := a1.2
    have ha2' : (a2 : α) ∈ (A : Set α) := a2.2
    rcases hle with h | h
    · exact hAw ha1' ha2' hne' h
    · exact hAw ha2' ha1' (Ne.symm hne') h
  have hLinj : Function.Injective FL := by
    intro a1 a2 heq
    have hfeq : L a1.1 a1.2 = L a2.1 a2.2 := congrArg Subtype.val heq
    by_contra hne
    have hne' : (a1 : α) ≠ (a2 : α) := fun h => hne (Subtype.ext h)
    have m1 : (a1 : α) ∈ (L a1.1 a1.2 : Set α) := hLmem a1.1 a1.2
    have m2 : (a2 : α) ∈ (L a1.1 a1.2 : Set α) := hfeq ▸ hLmem a2.1 a2.2
    have hch : IsChain (· ≤ ·) ((L a1.1 a1.2 : Finset α) : Set α) :=
      hCdown.2.1 (L a1.1 a1.2) (hLC a1.1 a1.2)
    unfold IsChain Set.Pairwise at hch
    have hle : ((a1 : α) ≤ (a2 : α)) ∨ ((a2 : α) ≤ (a1 : α)) := hch m1 m2 hne'
    have ha1' : (a1 : α) ∈ (A : Set α) := a1.2
    have ha2' : (a2 : α) ∈ (A : Set α) := a2.2
    rcases hle with h | h
    · exact hAw ha1' ha2' hne' h
    · exact hAw ha2' ha1' (Ne.symm hne') h
  have hIU : A.attach.image (fun a : ↥A => U a.1 a.2) = Cup := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp ht
      exact hUC a.1 a.2
    · have h1 : (A.attach.image (fun a : ↥A => U a.1 a.2)).card = A.attach.card := by
        apply Finset.card_image_of_injOn
        intro a1 _ a2 _ heq
        exact hUinj (Subtype.ext heq)
      rw [h1, Finset.card_attach, hCeqU]
  have hIL : A.attach.image (fun a : ↥A => L a.1 a.2) = Cdown := by
    apply Finset.eq_of_subset_of_card_le
    · intro t ht
      obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp ht
      exact hLC a.1 a.2
    · have h1 : (A.attach.image (fun a : ↥A => L a.1 a.2)).card = A.attach.card := by
        apply Finset.card_image_of_injOn
        intro a1 _ a2 _ heq
        exact hLinj (Subtype.ext heq)
      rw [h1, Finset.card_attach, hCeqL]
  refine ⟨A.attach.image (fun a : ↥A => L a.1 a.2 ∪ U a.1 a.2), ?_, ?_⟩
  · refine ⟨?sub, ?chain, ?cov⟩
    · intro t ht y hy
      obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp ht
      have hy' : y ∈ L a.1 a.2 ∪ U a.1 a.2 := hy
      rcases Finset.mem_union.mp hy' with h | h
      · exact downSetOf_subset s A (hCdown.1 _ (hLC _ _) h)
      · exact upSetOf_subset s A (hCup.1 _ (hUC _ _) h)
    · intro t ht
      obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp ht
      have hgoal : IsChain (· ≤ ·) ((L a.1 a.2 ∪ U a.1 a.2 : Finset α) : Set α) :=
        union_down_up_chain (hCdown.2.1 _ (hLC a.1 a.2)) (hCup.2.1 _ (hUC a.1 a.2))
          (hCdown.1 _ (hLC a.1 a.2)) (hCup.1 _ (hUC a.1 a.2))
          hA a.2 (hLmem a.1 a.2) (hUmem a.1 a.2)
      exact hgoal
    · intro z hzs
      have hzud : z ∈ upSetOf s A ∪ downSetOf s A := by rw [hunion]; exact hzs
      rcases Finset.mem_union.mp hzud with hup | hdown
      · obtain ⟨t, htC, hzt⟩ := hCup.2.2 z hup
        have htI : t ∈ A.attach.image (fun a : ↥A => U a.1 a.2) := by
          rw [hIU]; exact htC
        obtain ⟨a, haA, hat⟩ := Finset.mem_image.mp htI
        refine ⟨L a.1 a.2 ∪ U a.1 a.2, Finset.mem_image.mpr ⟨a, haA, rfl⟩, ?_⟩
        have hzt' : z ∈ U a.1 a.2 := by
          rw [show U a.1 a.2 = t from hat]
          exact hzt
        exact Finset.mem_union_right _ hzt'
      · obtain ⟨t, htC, hzt⟩ := hCdown.2.2 z hdown
        have htI : t ∈ A.attach.image (fun a : ↥A => L a.1 a.2) := by
          rw [hIL]; exact htC
        obtain ⟨a, haA, hat⟩ := Finset.mem_image.mp htI
        refine ⟨L a.1 a.2 ∪ U a.1 a.2, Finset.mem_image.mpr ⟨a, haA, rfl⟩, ?_⟩
        have hzt' : z ∈ L a.1 a.2 := by
          rw [show L a.1 a.2 = t from hat]
          exact hzt
        exact Finset.mem_union_left _ hzt'
  · have hle : (A.attach.image (fun a : ↥A => L a.1 a.2 ∪ U a.1 a.2)).card ≤
        A.attach.card := Finset.card_image_le
    rw [Finset.card_attach] at hle
    omega

-- The hard direction: every finite sub-poset has a chain cover by its width many chains.
private theorem exists_cover_card_le_width {α : Type*} [Fintype α] [PartialOrder α]
    (s : Finset α) : ∃ C, IsChainCoverOf s C ∧ C.card ≤ widthFin s := by
  classical
  refine Finset.strongInduction
    (p := fun s : Finset α => ∃ C, IsChainCoverOf s C ∧ C.card ≤ widthFin s)
    (fun s IH => ?_) s
  obtain ⟨A₀, hA₀mem, hA₀anti, hA₀card⟩ := exists_antichain_card_widthFin s
  by_cases hcase : ∃ A ∈ s.powerset, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = widthFin s ∧
      minSetOf s ≠ A ∧ maxSetOf s ≠ A
  · obtain ⟨A, hAmem, hAanti, hAcard, hmin, hmax⟩ := hcase
    have hupsub : upSetOf s A ⊂ s := upSetOf_ssubset_of_ne_min hAmem hAanti hAcard hmin
    have hdownsub : downSetOf s A ⊂ s :=
      downSetOf_ssubset_of_ne_max hAmem hAanti hAcard hmax
    have hWup : widthFin (upSetOf s A) = widthFin s :=
      widthFin_upSetOf hAmem hAanti hAcard
    have hWdown : widthFin (downSetOf s A) = widthFin s :=
      widthFin_downSetOf hAmem hAanti hAcard
    obtain ⟨Cup, hCup, hCupcard⟩ := IH _ hupsub
    obtain ⟨Cdown, hCdown, hCdowncard⟩ := IH _ hdownsub
    rw [hWup] at hCupcard
    rw [hWdown] at hCdowncard
    exact exists_cover_of_split hAmem hAanti hAcard
      (union_up_down_of_maximal hAmem hAanti hAcard) hCup hCupcard hCdown hCdowncard
  · have hall : ∀ B ∈ s.powerset, IsAntichain (· ≤ ·) (B : Set α) → B.card = widthFin s →
        minSetOf s = B ∨ maxSetOf s = B := by
      intro B hBmem hBanti hBcard
      by_contra hc
      have hc' : minSetOf s ≠ B ∧ maxSetOf s ≠ B := by
        constructor
        · intro hcon; exact hc (Or.inl hcon)
        · intro hcon; exact hc (Or.inr hcon)
      exact hcase ⟨B, hBmem, hBanti, hBcard, hc'.1, hc'.2⟩
    by_cases hsempty : s = ∅
    · subst hsempty
      refine ⟨∅, ⟨?_, ?_, ?_⟩, ?_⟩
      · intro t ht
        exact (Finset.notMem_empty t ht).elim
      · intro t ht
        exact (Finset.notMem_empty t ht).elim
      · intro a ha
        exact (Finset.notMem_empty a ha).elim
      · rw [Finset.card_empty]
        exact Nat.zero_le _
    · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsempty
      obtain ⟨x, hxmin⟩ := Finset.exists_minimal hsne
      have hxs : x ∈ s := hxmin.1
      have hxprop : ∀ ⦃y⦄, y ∈ s → y ≤ x → x ≤ y := hxmin.2
      have hfilne : (s.filter (x ≤ ·)).Nonempty :=
        ⟨x, Finset.mem_filter.mpr ⟨hxs, le_rfl⟩⟩
      obtain ⟨y, hymax⟩ := Finset.exists_maximal hfilne
      have hyfil : y ∈ s.filter (x ≤ ·) := hymax.1
      have hyprop : ∀ ⦃z⦄, z ∈ s.filter (x ≤ ·) → y ≤ z → z ≤ y := hymax.2
      have hys : y ∈ s := (Finset.mem_filter.mp hyfil).1
      have hxyle : x ≤ y := (Finset.mem_filter.mp hyfil).2
      have hymaxs : Maximal (fun z => z ∈ s) y := by
        refine ⟨hys, fun z hzs hyz => ?_⟩
        exact hyprop (Finset.mem_filter.mpr ⟨hzs, le_trans hxyle hyz⟩) hyz
      have hxmin_mem : x ∈ minSetOf s :=
        mem_minSetOf_iff.mpr ⟨hxs, fun b hbs hbx => hxprop hbs hbx⟩
      have hymax_mem : y ∈ maxSetOf s :=
        mem_maxSetOf_iff.mpr ⟨hys, fun b hbs hyb => hymaxs.2 hbs hyb⟩
      have hw1 : 1 ≤ widthFin s := widthFin_ge_one_of_mem hxs
      have hwidth : widthFin ((s.erase x).erase y) = widthFin s - 1 := by
        apply le_antisymm
        · unfold widthFin
          apply Finset.sup_le
          intro t ht
          have hgoal : (if IsAntichain (· ≤ ·) (t : Set α) then t.card else 0) ≤
              widthFin s - 1 := by
            by_cases hanti : IsAntichain (· ≤ ·) (t : Set α)
            · rw [ite_eq_left hanti]
              have htmem : t ∈ s.powerset := Finset.mem_powerset.mpr
                (Finset.Subset.trans (Finset.mem_powerset.mp ht) (le_of_lt
                  (Finset.ssubset_of_subset_of_ssubset
                    (Finset.erase_subset y (s.erase x)) (Finset.erase_ssubset hxs))))
              by_cases htw : t.card = widthFin s
              · have hextr := hall t htmem hanti htw
                have htx : x ∉ t := by
                  intro hcon
                  have hmemx : x ∈ (s.erase x).erase y :=
                    (Finset.mem_powerset.mp ht) hcon
                  obtain ⟨-, hmemx2⟩ := Finset.mem_erase.mp hmemx
                  obtain ⟨hne, -⟩ := Finset.mem_erase.mp hmemx2
                  exact hne rfl
                have hty : y ∉ t := by
                  intro hcon
                  have hmemx : y ∈ (s.erase x).erase y :=
                    (Finset.mem_powerset.mp ht) hcon
                  obtain ⟨hne, -⟩ := Finset.mem_erase.mp hmemx
                  exact hne rfl
                rcases hextr with heq | heq
                · have hxint : x ∈ t := heq ▸ hxmin_mem
                  exact (htx hxint).elim
                · have hyint : y ∈ t := heq ▸ hymax_mem
                  exact (hty hyint).elim
              · have hle := card_le_widthFin htmem hanti
                omega
            · rw [ite_eq_right hanti]
              exact Nat.zero_le _
          exact hgoal
        · have hA₀sub : A₀ ⊆ s := Finset.mem_powerset.mp hA₀mem
          have hA₀'anti : IsAntichain (· ≤ ·) ((((A₀.erase x).erase y : Finset α)) : Set α) := by
            have hsub : ((A₀.erase x).erase y : Finset α) ⊆ A₀ :=
              Finset.Subset.trans (Finset.erase_subset _ _) (Finset.erase_subset _ _)
            exact IsAntichain.subset hA₀anti (Finset.coe_subset.mpr hsub)
          have hA₀'mem : (A₀.erase x).erase y ∈ ((s.erase x).erase y).powerset := by
            rw [Finset.mem_powerset]
            intro z hz
            obtain ⟨hny, hmemx⟩ := Finset.mem_erase.mp hz
            obtain ⟨hnx, hzA⟩ := Finset.mem_erase.mp hmemx
            exact Finset.mem_erase.mpr ⟨hny, Finset.mem_erase.mpr ⟨hnx, hA₀sub hzA⟩⟩
          have hleA₀' := card_le_widthFin hA₀'mem hA₀'anti
          have hcard' : widthFin s - 1 ≤ ((A₀.erase x).erase y).card := by
            by_cases hxx : x = y
            · subst hxx
              by_cases hxA : x ∈ A₀
              · have h1 : ((A₀.erase x).erase x).card = (A₀.erase x).card :=
                  by rw [Finset.erase_eq_of_notMem (Finset.notMem_erase x A₀)]
                rw [h1, Finset.card_erase_of_mem hxA, hA₀card]
              · have h1 : ((A₀.erase x).erase x) = A₀ := by
                  rw [Finset.erase_eq_of_notMem hxA, Finset.erase_eq_of_notMem hxA]
                rw [h1, hA₀card]
                omega
            · have hnotboth : ¬(x ∈ A₀ ∧ y ∈ A₀) := by
                rintro ⟨hxA, hyA⟩
                have hxy_eq : x = y := by
                  by_contra hne
                  exact hA₀anti (Finset.mem_coe.mpr hxA) (Finset.mem_coe.mpr hyA)
                    hne hxyle
                exact hxx hxy_eq
              by_cases hxA : x ∈ A₀ <;> by_cases hyA : y ∈ A₀
              · exact absurd ⟨hxA, hyA⟩ hnotboth
              · have hyA' : y ∉ A₀.erase x := by
                  intro hcon
                  exact hyA (Finset.mem_of_mem_erase hcon)
                rw [Finset.erase_eq_of_notMem hyA', Finset.card_erase_of_mem hxA, hA₀card]
              · have hxA' : x ∉ A₀.erase y := by
                  intro hcon
                  exact hxA (Finset.mem_of_mem_erase hcon)
                have h1 : (A₀.erase x) = A₀ := Finset.erase_eq_of_notMem hxA
                rw [h1, Finset.card_erase_of_mem hyA, hA₀card]
              · have h1 : ((A₀.erase x).erase y) = A₀ := by
                  rw [Finset.erase_eq_of_notMem hxA, Finset.erase_eq_of_notMem hyA]
                rw [h1, hA₀card]
                omega
          omega
      obtain ⟨C', hC', hC'card⟩ := IH _ (Finset.ssubset_of_subset_of_ssubset
        (Finset.erase_subset y (s.erase x)) (Finset.erase_ssubset hxs))
      rw [hwidth] at hC'card
      refine ⟨insert {x, y} C', ⟨?_, ?_, ?_⟩, ?_⟩
      · intro t ht z hz
        rcases Finset.mem_insert.mp ht with rfl | htC
        · rcases Finset.mem_insert.mp hz with rfl | hz2
          · exact hxs
          · rw [Finset.mem_singleton.mp hz2]; exact hys
        · exact Finset.Subset.trans (hC'.1 t htC) (le_of_lt
            (Finset.ssubset_of_subset_of_ssubset
              (Finset.erase_subset y (s.erase x)) (Finset.erase_ssubset hxs))) hz
      · intro t ht
        rcases Finset.mem_insert.mp ht with rfl | htC
        · have hpair : IsChain (· ≤ ·) ((({x, y} : Finset α)) : Set α) := by
            rw [Finset.coe_insert, Finset.coe_singleton]
            exact IsChain.pair hxyle
          exact hpair
        · exact hC'.2.1 t htC
      · intro z hzs
        by_cases hzx : z = x
        · refine ⟨{x, y}, Finset.mem_insert_self {x, y} C', ?_⟩
          rw [hzx]
          exact Finset.mem_insert_self x {y}
        · by_cases hzy : z = y
          · refine ⟨{x, y}, Finset.mem_insert_self {x, y} C', ?_⟩
            rw [hzy, Finset.mem_insert, Finset.mem_singleton]
            exact Or.inr rfl
          · have hzs' : z ∈ (s.erase x).erase y :=
              Finset.mem_erase.mpr ⟨hzy, Finset.mem_erase.mpr ⟨hzx, hzs⟩⟩
            obtain ⟨t, htC, hzt⟩ := hC'.2.2 z hzs'
            exact ⟨t, Finset.mem_insert_of_mem htC, hzt⟩
      · have hle := Finset.card_insert_le {x, y} C'
        omega

/-- **Chain covers bound the minimum chain cover size.** Let $\alpha$ be a finite partially
ordered set. If $C$ is a chain cover of $\alpha$, that is, a finite set of chains of $\alpha$ whose
union is $\alpha$, then the minimum chain cover size of $\alpha$ is at most the number of chains
in $C$. -/
theorem minChainCoverSize_le_card {α : Type*} [Fintype α] [PartialOrder α]
    {C : Finset (Finset α)} (hC : IsChainCoverFin (α := α) C) :
    minChainCoverSize α ≤ C.card := by
  classical
  have hmem : C ∈ (Finset.univ.powerset).powerset :=
    Finset.mem_powerset.mpr fun t _ => Finset.mem_powerset.mpr (Finset.subset_univ t)
  have hmem' : C ∈ ((((Finset.univ.powerset).powerset).filter
      fun C => IsChainCoverFin (α := α) C)) := Finset.mem_filter.mpr ⟨hmem, hC⟩
  unfold minChainCoverSize
  change (if h : ((((Finset.univ.powerset).powerset).filter
      fun C => IsChainCoverFin (α := α) C)).Nonempty
    then ((((Finset.univ.powerset).powerset).filter
      fun C => IsChainCoverFin (α := α) C)).inf' h fun C => C.card else 0) ≤ C.card
  rw [dite_eq_left ⟨C, hmem'⟩]
  exact Finset.inf'_le _ hmem'

-- The singleton chains form a valid cover (so the minimum is over a nonempty set).
private theorem exists_valid_cover {α : Type*} [Fintype α] [PartialOrder α] :
    ∃ C, IsChainCoverFin (α := α) C ∧ C ∈ (Finset.univ.powerset).powerset := by
  classical
  refine ⟨Finset.univ.image fun a => ({a} : Finset α), ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    have h1 : IsChain (· ≤ ·) ((({a} : Finset α)) : Set α) := by
      rw [Finset.coe_singleton]
      exact IsChain.singleton (r := (· ≤ ·)) (a := a)
    exact h1
  · intro a
    exact ⟨{a}, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩,
      Finset.mem_singleton_self a⟩
  · rw [Finset.mem_powerset]
    intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_powerset]
    exact Finset.subset_univ _

/--
**Dilworth's theorem.** Let $\alpha$ be a finite partially ordered set. The maximum antichain
size of $\alpha$ equals its minimum chain cover size: the largest number of elements of an
antichain in $\alpha$ equals the smallest number of chains whose union is $\alpha$.

Proves `Wanted` entry `dilworth_decomposition`.

Source: R. P. Dilworth, A decomposition theorem for partially ordered sets, Annals of Mathematics 51
(1950), 161-166, DOI 10.2307/1969503.
-/
theorem dilworth_decomposition
    {α : Type*} [Fintype α] [PartialOrder α] :
    maxAntichainSize α = minChainCoverSize α := by
  classical
  have hmax : widthFin (Finset.univ : Finset α) = maxAntichainSize α := rfl
  obtain ⟨C, hC, hCcard⟩ := exists_cover_card_le_width (Finset.univ : Finset α)
  have hCfin : IsChainCoverFin (α := α) C := by
    refine ⟨hC.2.1, fun a => ?_⟩
    obtain ⟨t, htC, hat⟩ := hC.2.2 a (Finset.mem_univ a)
    exact ⟨t, htC, hat⟩
  have hle1 : minChainCoverSize α ≤ maxAntichainSize α := by
    have hmin_le := minChainCoverSize_le_card hCfin
    rw [hmax] at hCcard
    omega
  have hle2 : maxAntichainSize α ≤ minChainCoverSize α := by
    obtain ⟨C₀, hC₀, hC₀mem⟩ := exists_valid_cover (α := α)
    have hne : ((((Finset.univ.powerset).powerset).filter
        fun C => IsChainCoverFin (α := α) C)).Nonempty :=
      ⟨C₀, Finset.mem_filter.mpr ⟨hC₀mem, hC₀⟩⟩
    have hsup : maxAntichainSize α =
        (((Finset.univ : Finset α).powerset).sup fun u =>
          if IsAntichain (· ≤ ·) (u : Set α) then u.card else 0) := rfl
    unfold minChainCoverSize
    change maxAntichainSize α ≤ (if h : ((((Finset.univ.powerset).powerset).filter
        fun C => IsChainCoverFin (α := α) C)).Nonempty
      then ((((Finset.univ.powerset).powerset).filter
        fun C => IsChainCoverFin (α := α) C)).inf' h fun C => C.card else 0)
    rw [dite_eq_left hne, hsup]
    apply Finset.sup_le
    intro u hu
    have hgoal2 : (if IsAntichain (· ≤ ·) (u : Set α) then u.card else 0) ≤
        ((((Finset.univ.powerset).powerset).filter
          fun C => IsChainCoverFin (α := α) C)).inf' hne fun C => C.card := by
      refine Finset.le_inf' hne _ ?_
      intro t ht
      obtain ⟨htmem, htC⟩ := Finset.mem_filter.mp ht
      have hgoal3 : (if IsAntichain (· ≤ ·) (u : Set α) then u.card else 0) ≤ t.card := by
        by_cases hanti : IsAntichain (· ≤ ·) (u : Set α)
        · rw [ite_eq_left hanti]
          have hcov : IsChainCoverOf (Finset.univ : Finset α) t :=
            ⟨fun u _ => Finset.subset_univ u, htC.1, fun a _ => htC.2 a⟩
          exact card_antichain_le_cover
            (Finset.coe_subset.mpr (Finset.mem_powerset.mp hu)) hanti hcov
        · rw [ite_eq_right hanti]
          exact Nat.zero_le _
      exact hgoal3
    exact hgoal2
  exact le_antisymm hle2 hle1

/-- **The maximum antichain size is attained.** Let $\alpha$ be a finite partially ordered set.
Some antichain in $\alpha$ has exactly as many elements as the maximum antichain size of
$\alpha$. -/
theorem exists_isAntichain_card_eq_maxAntichainSize {α : Type*} [Fintype α]
    [PartialOrder α] :
    ∃ A : Finset α, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = maxAntichainSize α := by
  obtain ⟨A, -, hA, hcard⟩ := exists_antichain_card_widthFin (Finset.univ : Finset α)
  exact ⟨A, hA, hcard⟩

/-- **The minimum chain cover size is attained.** Let $\alpha$ be a finite partially ordered set.
Some chain cover $C$ of $\alpha$, a finite set of chains of $\alpha$ whose union is $\alpha$,
consists of exactly as many chains as the minimum chain cover size of $\alpha$. -/
theorem exists_isChainCoverFin_card_eq_minChainCoverSize {α : Type*} [Fintype α]
    [PartialOrder α] :
    ∃ C : Finset (Finset α), IsChainCoverFin C ∧ C.card = minChainCoverSize α := by
  obtain ⟨C, hC, hCcard⟩ := exists_cover_card_le_width (Finset.univ : Finset α)
  have hCfin : IsChainCoverFin C := ⟨hC.2.1, fun a => hC.2.2 a (Finset.mem_univ a)⟩
  refine ⟨C, hCfin, le_antisymm ?_ (minChainCoverSize_le_card hCfin)⟩
  rw [← dilworth_decomposition]
  exact hCcard

end MathlibExt.Combinatorics.Order.DilworthWanted
