/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.WellFounded
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Ranged hash functions

A bucket view is a nonempty set, not a list with a prescribed enumeration. A ranged hash
function selects a member of every view for every item. Monotonicity here concerns changes
of *view*, not an order on the buckets: an item cannot move between two old buckets when
the view grows. An item-specific ranking of a finite bucket universe gives such a function.

A family is simply `S → RangedHashFunction I B`. For a discrete law `μ : PMF S` on its
indices, `μ.map family` is a law on whole functions. Evaluations in different views or at
different items use the same sampled function; there is no hypothesis of uniformity,
independence, or finiteness of the index type.

Source: D. Karger et al., “Consistent Hashing and Random Trees: Distributed Caching Protocols
for Relieving Hot Spots on the World Wide Web”, STOC 1997, §4.1 (p. 659) and §4.4 (p. 660).
-/

@[expose] public section

namespace Cslib.Algorithms.Lean

universe u v w

/-- A ranged hash function assigns each item a bucket in each nonempty view. The result
belongs to the supplied view by its type; neither items nor buckets have to be enumerable. -/
def RangedHashFunction (I : Type u) (B : Type v) :=
  (V : Set B) → V.Nonempty → I → V

namespace RangedHashFunction

variable {I : Type u} {B : Type v}

/-- A ranged hash function is monotone if, whenever a view `V` expands to `W` and the
choice in `W` is still a member of `V`, both views choose the same bucket for the item. -/
def IsMonotone (f : RangedHashFunction I B) : Prop :=
  ∀ {V W : Set B} (hV : V.Nonempty) (hW : W.Nonempty), V ⊆ W →
    ∀ i, (f W hW i).val ∈ V → (f V hV i).val = (f W hW i).val

/-- Monotonicity is equivalent to saying that every item that moves on expansion
moves to a newly available bucket. -/
theorem isMonotone_iff_moves_to_new (f : RangedHashFunction I B) :
    f.IsMonotone ↔ ∀ {V W : Set B} (hV : V.Nonempty) (hW : W.Nonempty), V ⊆ W →
      ∀ i, (f V hV i).val ≠ (f W hW i).val → (f W hW i).val ∈ W \ V := by
  constructor
  · intro h V W hV hW hVW i hm
    exact ⟨(f W hW i).property, fun hmem => hm (h hV hW hVW i hmem)⟩
  · intro h V W hV hW hVW i hmem
    by_contra hm
    exact (h hV hW hVW i hm).2 hmem

variable {n : ℕ}

/-- Given for each item a bijection from buckets to ranks `0, …, n − 1`, choose the bucket
of least rank in the supplied nonempty view. Rank zero comes first. -/
noncomputable def ofRanks (rank : I → B ≃ Fin n) : RangedHashFunction I B :=
  fun V hV i =>
    let wf := (measure fun b => (rank i b).val).wf
    ⟨wf.min V hV, wf.min_mem V hV⟩

/-- The bucket chosen by `ofRanks` is `b` exactly when `b` is available and has rank
no greater than that of any available bucket for this item. -/
theorem ofRanks_eq_iff (rank : I → B ≃ Fin n) {V : Set B} (hV : V.Nonempty) (i : I) (b : B) :
    (ofRanks rank V hV i).val = b ↔ b ∈ V ∧ ∀ c ∈ V, rank i b ≤ rank i c := by
  have least (c : B) (hc : c ∈ V) : rank i (ofRanks rank V hV i).val ≤ rank i c :=
    le_of_not_gt ((measure fun b => (rank i b).val).wf.not_lt_min V hc)
  constructor
  · rintro rfl
    exact ⟨(ofRanks rank V hV i).property, least⟩
  · rintro ⟨hb, h⟩
    exact (rank i).injective (le_antisymm (least b hb) (h _ (ofRanks rank V hV i).property))

/-- Every item-specific ranking gives a monotone ranged hash function: the least-ranked
member of a larger view is also least in any smaller view containing it. -/
theorem isMonotone_ofRanks (rank : I → B ≃ Fin n) : (ofRanks rank).IsMonotone := by
  intro V W hV hW hVW i hmem
  obtain ⟨_, least⟩ := (ofRanks_eq_iff rank hW i _).1 rfl
  exact (ofRanks_eq_iff rank hV i _).2 ⟨hmem, fun c hc => least c (hVW hc)⟩

/-- Draw one index from a discrete law, take its ranged function, and evaluate it in two
nested views at the same item. If each supported index gives a monotone function, every
unequal pair in the support of this joint law ends at a newly available bucket. -/
theorem mem_diff_of_joint_move {S : Type w} (family : S → RangedHashFunction I B) (μ : PMF S)
    (h : ∀ s ∈ μ.support, (family s).IsMonotone) {V W : Set B} (hV : V.Nonempty)
    (hW : W.Nonempty) (hVW : V ⊆ W) (i : I) {p : B × B}
    (hp : p ∈ ((μ.map family).map fun f => ((f V hV i).val, (f W hW i).val)).support)
    (hm : p.1 ≠ p.2) : p.2 ∈ W \ V := by
  rw [PMF.support_map, PMF.support_map] at hp
  obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hp
  exact (isMonotone_iff_moves_to_new _).1 (h s hs) hV hW hVW i hm

end RangedHashFunction
end Cslib.Algorithms.Lean
