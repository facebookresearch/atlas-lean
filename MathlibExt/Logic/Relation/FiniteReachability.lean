/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Reachability in finite relations
-/
module

public import MathlibExt.Order.FixedPoints.Finset
public import Mathlib.Logic.Relation

/-!
# Reachability in finite relations

For a decidable relation `r` on a finite type, the set of elements reachable from `a` in one or
more `r`-steps is computed as a finite least fixed point (`Relation.transGenFin`, iterating
`Z ↦ post {a} ∪ post Z` with `Finset.lfpFin`), and likewise from a finite set of sources
(`Relation.transGenFinFrom`). Membership is `Relation.TransGen r a` (`Relation.mem_transGenFin`,
`Relation.mem_transGenFinFrom`), which makes `TransGen r` and `ReflTransGen r` decidable
(`Relation.decidableTransGen`, `Relation.decidableReflTransGen`). These are definitions rather
than global instances, so that they never compete with instances Mathlib may add.

First client: Büchi emptiness in `CSLibExt.Computability.Automata.NA.BuchiEmptiness`.
-/

@[expose] public section

namespace Relation

variable {α : Type*} [Fintype α] (r : α → α → Prop) [DecidableRel r]

/-- The `r`-successors of a finite set. -/
def postFin (Z : Finset α) : Finset α :=
  Finset.univ.filter fun t => ∃ z ∈ Z, r z t

variable {r}

theorem mem_postFin {Z : Finset α} {t : α} : t ∈ postFin r Z ↔ ∃ z ∈ Z, r z t := by
  simp [postFin]

theorem postFin_mono : Monotone (postFin r) := by
  intro Z₁ Z₂ h t ht
  rw [mem_postFin] at ht ⊢
  obtain ⟨z, hz, hzt⟩ := ht
  exact ⟨z, h hz, hzt⟩

variable (r) [DecidableEq α]

/-- The functional whose least fixed point is the set reachable from `A` in one or more steps. -/
def transGenStep (A Z : Finset α) : Finset α :=
  postFin r A ∪ postFin r Z

theorem transGenStep_mono (A : Finset α) : Monotone (transGenStep r A) := fun _ _ h =>
  Finset.union_subset_union (Finset.Subset.refl _) (postFin_mono h)

/-- The finite set of elements reachable from some element of `A` in one or more `r`-steps,
computed by one finite least fixed point (`Fintype.card α` rounds of `postFin`). -/
def transGenFinFrom (A : Finset α) : Finset α :=
  Finset.lfpFin (transGenStep r A)

/-- The finite set of elements reachable from `a` in one or more `r`-steps. -/
def transGenFin (a : α) : Finset α :=
  transGenFinFrom r {a}

variable {r}

/-- `transGenFinFrom r A` is exactly the set of `t` with `Relation.TransGen r a t` for some
`a ∈ A`. -/
theorem mem_transGenFinFrom {A : Finset α} {t : α} :
    t ∈ transGenFinFrom r A ↔ ∃ a ∈ A, TransGen r a t := by
  classical
  have hfix := Finset.lfpFin_fixed (transGenStep_mono r A)
  constructor
  · intro ht
    have hle : transGenFinFrom r A ⊆
        Finset.univ.filter (fun u => ∃ a ∈ A, TransGen r a u) := by
      apply Finset.lfpFin_le (transGenStep_mono r A)
      intro u hu
      simp only [transGenStep, Finset.mem_union, mem_postFin] at hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hu with ⟨a, ha, hau⟩ | ⟨z, hz, hzu⟩
      · exact ⟨a, ha, TransGen.single hau⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨a, ha, haz⟩ := hz
        exact ⟨a, ha, haz.tail hzu⟩
    simpa using hle ht
  · rintro ⟨a, ha, h⟩
    induction h with
    | single hab =>
        rw [transGenFinFrom, ← hfix]
        exact Finset.mem_union_left _ (mem_postFin.2 ⟨a, ha, hab⟩)
    | tail _ hbc ih =>
        rw [transGenFinFrom, ← hfix]
        exact Finset.mem_union_right _ (mem_postFin.2 ⟨_, ih, hbc⟩)

/-- `transGenFin r a` is exactly the set of `t` with `Relation.TransGen r a t`. -/
theorem mem_transGenFin {a t : α} : t ∈ transGenFin r a ↔ TransGen r a t := by
  rw [transGenFin, mem_transGenFinFrom]
  simp

variable (r)

/-- `Relation.TransGen` of a decidable relation on a finite type is decidable. -/
@[instance_reducible]
def decidableTransGen : DecidableRel (TransGen r) := fun a t =>
  decidable_of_iff (t ∈ transGenFin r a) mem_transGenFin

/-- `Relation.ReflTransGen` of a decidable relation on a finite type is decidable. -/
@[instance_reducible]
def decidableReflTransGen : DecidableRel (ReflTransGen r) := fun a t =>
  haveI := decidableTransGen r
  decidable_of_iff (t = a ∨ TransGen r a t) reflTransGen_iff_eq_or_transGen.symm

end Relation
