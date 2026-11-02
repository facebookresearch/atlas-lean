/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Nam Trang
-/
module

public import Mathlib.Data.Set.Countable
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 37, Logic 39, Logic 40, Logic 41, Logic 51, Logic 579

/-!
# `MathlibExt.SetTheory.Cardinal.Cofinality.CountableSubsets`

## References

* Jech (for `IsClubOmega`, `IsStationaryOmega`, `ClosurePoints`, `ClosurePointsSeq`)
* 1. closurePointsSeq_const — the closure points of a constant family $\lambda _ : \mathbb{N},, F$
  are exactly the closure points of the single operation $F$. Source: direct observation, original
  to this formalization. Background: Kueker's closure-point clubs, D. W. Kueker, "Countable
  approximations and Löwenheim–Skolem theorems", Annals of, Mathematical Logic 11 (1977), 57–103.
  2. notMem_closurePoints_empty — $\emptyset$ is never a closure point of any finitary $F$ (since
  $F(\emptyset)$ would have to belong to it). Source: direct observation, original to this
  formalization. 3. countable_iUnion_countable — a countable union of countable sets is countable.
  Source: Mathlib, Set.countable_iUnion, Mathlib/Data/Set/Countable.lean:214: theorem
  countable_iUnion {t : ι → Set α} [Countable ι] (ht : ∀ i, (t i).Countable). 4.
  isClubOmega_countableSubsets — $[\alpha]^\omega$ is itself a club, so clubs exist and
  stationarity is not vacuous. Source: direct observation, original to this formalization.
  Background: T. Jech, Set Theory, 3rd ed., Springer, 2003, Chapter 8 (Stationary Sets). 5.
  not_isStationaryOmega_empty — $\emptyset$ is never stationary in $[\alpha]^\omega$. Source:
  direct observation, original to this formalization; one-line corollary of item 4. 6.
  IsStationaryOmega.nonempty — every stationary family is nonempty. Source: direct observation,
  original to this formalization; via item 4. 7. IsStationaryOmega.mono — stationarity is
  upward-closed under $\subseteq$. Source: standard fact; Jech, Set Theory, Chapter 8 (Stationary
  Sets). 8. isStationaryOmega_countableSubsets — $[\alpha]^\omega$ is stationary (every club has a
  countable member). Source: direct observation, original to this formalization. Background: Jech,
  Chapter 8. 9. isClubOmega_mem — for each $a$, the countable sets containing $a$ form a club.
  Source: standard club example; Jech, Set Theory, Chapter 8. 10. Set.Countable.exists_option_enum
  — every countable set admits a total $\mathbb{N}$-indexed Option enumeration hitting each member
  as some a (constantly none when empty). Source: original to this formalization; routes through,
  Mathlib's exists_surjective_nat, Mathlib/Basic/Countable/Defs.lean:62: theorem
  exists_surjective_nat (α : Sort u) [Nonempty α] [Countable α] : ∃ f : ℕ → α, Surjective f. 11.
  isClubOmega_closurePointsSeq — the closure points of a countable family of finitary operations
  form a club, (cofinal by $\omega$-iteration; closed since every finite subset of a chain-union
  lands in some stage). Source: the easy direction of Kueker's theorem in sequence-indexed form;
  original, Kueker 1977 (as in item 1); textbook, Jech, Chapter 8. The countability of the
  finite-subset stages routes through Mathlib's, Set.countable_ofPred_finite_subset
  (Mathlib/Data/Set/Countable.lean:273), Set.countable_univ_iff (:137), and, Set.countable_iUnion
  (item 3's source). (for `closurePointsSeq_const`)
-/

open Set Order

namespace MetaMathlibExt

-- Logic 37: Countable subsets of $\alpha$

/-- [α]^ω or P_{ω₁}(α) is the set of countable subsets of α -/
def CountableSubsets.{u} (α : Type u) : Set (Set α) := {x | x.Countable}

-- Logic 39: Club in $[X]^\omega$

/-- **Club families of countable sets.** Let $X$ be a set. A family $C$ of subsets of $X$ is club
in the countable subsets of $X$ when every member of $C$ is countable (finite or countably
infinite), every countable set $x \subseteq X$ is contained in some member of $C$, and for every
sequence $x_0 \subseteq x_1 \subseteq x_2 \subseteq \cdots$ of members of $C$ the union
$\bigcup_{n \in \mathbb{N}} x_n$ belongs to $C$.
-/
structure IsClubOmega {α : Type*} (C : Set (Set α)) : Prop where
  mem_countable : ∀ x ∈ C, x.Countable
  cofinal : ∀ x : Set α, x.Countable → ∃ y ∈ C, x ⊆ y
  closed : ∀ f : ℕ → Set α, (∀ n, f n ∈ C) → Monotone f → (⋃ n, f n) ∈ C

-- Logic 40: Stationarity in $[X]^\omega$

/-- **Stationary families of countable sets.** Let $X$ be a set. A family $S$ of subsets of $X$ is
stationary in the countable subsets of $X$ when $S$ meets every family $C$ that is club in the
countable subsets of $X$, that is, some set belongs to both $S$ and $C$.
-/
def IsStationaryOmega {α : Type*} (S : Set (Set α)) : Prop :=
  ∀ ⦃C : Set (Set α)⦄, IsClubOmega C → (S ∩ C).Nonempty

-- Logic 41: Closure points

/-- **Closure points of a finitary function.** Let $X$ be a set and let $F$ be a function
assigning an element of $X$ to every finite subset of $X$. The closure points of $F$ are the
countable (finite or countably infinite) sets $a \subseteq X$ such that $F(s) \in a$ for every
finite set $s \subseteq a$.
-/
def ClosurePoints {α : Type*} (F : Finset α → α) : Set (Set α) :=
  {x | x.Countable ∧ ∀ s : Finset α, ↑s ⊆ x → F s ∈ x}

-- Logic 51: Closure Points Sequence

/-- **Closure points of a sequence of finitary functions.** Let $X$ be a set and let
$(F_n)_{n \in \mathbb{N}}$ be a sequence of functions, each assigning an element of $X$ to every
finite subset of $X$. The closure points of $(F_n)$ are the countable (finite or countably
infinite) sets $x \subseteq X$ such that $F_n(s) \in x$ for every $n \in \mathbb{N}$ and every
finite set $s \subseteq x$.
-/
def ClosurePointsSeq {α : Type*} (F : ℕ → Finset α → α) : Set (Set α) :=
  {x | x.Countable ∧ ∀ (n : ℕ) (s : Finset α), ↑s ⊆ x → F n s ∈ x}

-- Logic 579: Theorems about subsets of $[X]^\omega$

/-! ### Informal statement of `closurePointsSeq_const`

1. Let F : Finset(α) → α. Then ClosurePointsSeq(λ n : ℕ,, F) =
     ClosurePoints(F).
  2. For every finitary operation F, ∅ ∉ ClosurePoints(F).
  3. Let f : ℕ → 𝒫(α) with each f(n) countable. Then ⋃_{n ∈ ℕ} f(n)
     is countable.
  4. [α]^ω is club in [α]^ω.
  5. ∅ is not stationary in [α]^ω.
  6. If S is stationary in [α]^ω then S ≠ ∅.
  7. If S is stationary and S ⊆ T then T is stationary.
  8. [α]^ω is stationary in [α]^ω.
  9. For each a ∈ α, x ∈ [α]^ω : a ∈ x is club.
  10. If s ⊆ α is countable then ∃, e : ℕ → Option(s),; ∀ a ∈ s,;
      ∃ n,; e(n) = some(a).
  11. For F : ℕ → (Finset(α) → α), ClosurePointsSeq(F) is club in
      [α]^ω.
-/

/-- 1. Let F : Finset(α) → α. Then ClosurePointsSeq(λ n : ℕ,, F) =      ClosurePoints(F).   2. For
   every finitary operation F, ∅ ∉ ClosurePoints(F).   3. Let f : ℕ → 𝒫(α) with each f(n) countable.
   Then ⋃_{n ∈ ℕ} f(n)      is countable.   4. [α]^ω is club in [α]^ω.   5. ∅ is not stationary in
   [α]^ω.   6. If S is stationary in [α]^ω then S ≠ ∅.   7.

The full informal statement is in the module documentation directly above.
-/
theorem closurePointsSeq_const.{u} {α : Type u} (F : Finset α → α) :
    ClosurePointsSeq (fun _ : ℕ => F) = ClosurePoints F := by
  ext x
  simp only [ClosurePointsSeq, ClosurePoints, Set.mem_ofPred_eq]
  exact and_congr_right fun _ => ⟨fun h s hs => h 0 s hs, fun h _ s hs => h s hs⟩

theorem notMem_closurePoints_empty.{u} {α : Type u} (F : Finset α → α) :
    (∅ : Set α) ∉ ClosurePoints F :=
  fun h => h.2 ∅ (by simp)

theorem countable_iUnion_countable.{u} {α : Type u} (f : ℕ → Set α)
    (hf : ∀ n, (f n).Countable) : (⋃ n, f n).Countable :=
  Set.countable_iUnion hf

theorem isClubOmega_countableSubsets.{u} (α : Type u) :
    IsClubOmega (CountableSubsets α) where
  mem_countable := fun _ hx => hx
  cofinal := fun x hx => ⟨x, hx, subset_rfl⟩
  closed := fun _ hf _ => Set.countable_iUnion hf

theorem not_isStationaryOmega_empty.{u} {α : Type u} :
    ¬ IsStationaryOmega (∅ : Set (Set α)) := by
  intro h
  obtain ⟨x, hx, -⟩ := h (isClubOmega_countableSubsets α)
  exact hx

theorem IsStationaryOmega.nonempty.{u} {α : Type u} {S : Set (Set α)}
    (h : IsStationaryOmega S) : S.Nonempty :=
  (h (isClubOmega_countableSubsets α)).imp fun _ hx => hx.1

theorem IsStationaryOmega.mono.{u} {α : Type u} {S T : Set (Set α)}
    (hS : IsStationaryOmega S) (hST : S ⊆ T) : IsStationaryOmega T :=
  fun _ hC => (hS hC).imp fun _ hx => ⟨hST hx.1, hx.2⟩

theorem isStationaryOmega_countableSubsets.{u} (α : Type u) :
    IsStationaryOmega (CountableSubsets α) :=
  fun _ hC => ((hC.cofinal ∅ Set.countable_empty).imp
    fun y hy => ⟨hC.mem_countable y hy.1, hy.1⟩)

theorem isClubOmega_mem.{u} {α : Type u} (a : α) :
    IsClubOmega {x : Set α | x.Countable ∧ a ∈ x} where
  mem_countable _ hx := hx.1
  cofinal x hx := ⟨insert a x, ⟨hx.insert a, Set.mem_insert a x⟩, Set.subset_insert a x⟩
  closed _f hf _ := ⟨Set.countable_iUnion fun n => (hf n).1, Set.mem_iUnion.2 ⟨0, (hf 0).2⟩⟩

theorem _root_.Set.Countable.exists_option_enum.{u} {α : Type u} {s : Set α}
    (hs : s.Countable) : ∃ e : ℕ → Option ↥s, ∀ a, ∃ n, e n = some a := by
  by_cases h : Nonempty ↥s
  · obtain ⟨f, hf⟩ :=
      @exists_surjective_nat ↥s h (Set.countable_coe_iff.mp hs)
    refine ⟨fun n => some (f n), fun a => ?_⟩
    obtain ⟨n, hn⟩ := hf a
    exact ⟨n, congrArg some hn⟩
  · exact ⟨fun _ => none, fun a => absurd ⟨a⟩ h⟩

theorem isClubOmega_closurePointsSeq.{u} {α : Type u} (F : ℕ → Finset α → α) :
    IsClubOmega (ClosurePointsSeq F) := by
  have hfin : ∀ s : Finset α, ∀ f : ℕ → Set α, Monotone f → ↑s ⊆ ⋃ n, f n →
      ∃ N, ↑s ⊆ f N := by
    set_option linter.style.haveILetI false in
    haveI := Classical.decEq α
    intro s
    induction s using Finset.induction with
    | empty =>
      intro f _ _
      exact ⟨0, by simp⟩
    | insert _ s _ ih =>
      intro f hmono hsub
      have hsub' : ↑s ⊆ ⋃ n, f n := fun x hx =>
        hsub (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)))
      obtain ⟨N', hN'⟩ := ih f hmono hsub'
      obtain ⟨na, hna⟩ :=
        Set.mem_iUnion.mp (hsub (Finset.mem_coe.mpr (Finset.mem_insert_self _ _)))
      refine ⟨max N' na, fun x hx => ?_⟩
      rw [Finset.mem_coe, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hmono (Nat.le_max_right _ _) hna
      · exact hmono (Nat.le_max_left _ _) (hN' (Finset.mem_coe.mpr hx))
  refine ⟨fun x hx => hx.1, fun Y hY => ?_, fun f hf hmono => ?_⟩
  · set Ys : ℕ → Set α :=
      Nat.rec Y (fun _ Yk => Yk ∪ (fun p : ℕ × {s : Finset α // ↑s ⊆ Yk} =>
        F p.1 p.2.val) '' univ)
    have hY0 : Ys 0 = Y := rfl
    have hYS : ∀ k, Ys (k + 1) = Ys k ∪
        (fun p : ℕ × {s : Finset α // ↑s ⊆ Ys k} => F p.1 p.2.val) '' univ :=
      fun k => rfl
    have hYcount : ∀ k, (Ys k).Countable := by
      intro k
      induction k with
      | zero => rw [hY0]; exact hY
      | succ k ih =>
        rw [hYS k]
        have hsub : Countable {s : Finset α // ↑s ⊆ Ys k} := by
          refine @Function.Injective.countable _ _
            (Set.countable_coe_iff.mp (Set.countable_ofPred_finite_subset ih))
            (fun s => (⟨↑s.val, Finset.finite_toSet s.val, s.property⟩ :
              ↥{t : Set α | t.Finite ∧ t ⊆ Ys k})) ?_
          intro a b h
          exact Subtype.ext (Finset.coe_injective (congrArg Subtype.val h))
        have key : ∀ [Countable {s : Finset α // ↑s ⊆ Ys k}],
            (univ : Set (ℕ × {s : Finset α // ↑s ⊆ Ys k})).Countable :=
          fun [Countable {s : Finset α // ↑s ⊆ Ys k}] =>
            Set.countable_univ_iff.mpr inferInstance
        have huniv : (univ : Set (ℕ × {s : Finset α // ↑s ⊆ Ys k})).Countable :=
          @key hsub
        have himg : ((fun p : ℕ × {s : Finset α // ↑s ⊆ Ys k} => F p.1 p.2.val) ''
            univ).Countable := huniv.image _
        exact Set.Countable.union ih himg
    have hmonY : Monotone Ys :=
      monotone_nat_of_le_succ fun k => by rw [hYS k]; exact Set.subset_union_left
    refine ⟨⋃ k, Ys k, ⟨Set.countable_iUnion hYcount, fun n s hsub => ?_⟩, ?_⟩
    · obtain ⟨K, hK⟩ := hfin s Ys hmonY hsub
      have hmem : F n s ∈ Ys (K + 1) := by
        rw [hYS K]
        exact Set.subset_union_right (Set.mem_image_of_mem
          (fun p : ℕ × {s : Finset α // ↑s ⊆ Ys K} => F p.1 p.2.val)
          (Set.mem_univ (n, (⟨s, hK⟩ : {s : Finset α // ↑s ⊆ Ys K}))))
      exact Set.mem_iUnion.mpr ⟨K + 1, hmem⟩
    · intro x hx
      have hx0 : x ∈ Ys 0 := by rw [hY0]; exact hx
      exact Set.mem_iUnion.mpr ⟨0, hx0⟩
  · refine ⟨Set.countable_iUnion fun n => (hf n).1, fun n s hsub => ?_⟩
    obtain ⟨N, hN⟩ := hfin s f hmono hsub
    exact Set.mem_iUnion.mpr ⟨N, (hf N).2 n s hN⟩

end MetaMathlibExt

end
