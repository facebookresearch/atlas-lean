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

/-- **Successors of a finite set.** Let $\alpha$ be a finite type and let $r$ be a decidable
relation on $\alpha$. For a finite set $Z \subseteq \alpha$, the set of $r$-successors of $Z$ is
the finite set $\mathrm{post}_r(Z) = \{t \in \alpha \mid r(z, t) \text{ for some } z \in Z\}$. -/
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

/-- **One step of the reachability iteration.** Let $\alpha$ be a finite type with decidable
equality, let $r$ be a decidable relation on $\alpha$, and write $\mathrm{post}_r(Z)$ for the set
of $r$-successors of elements of a finite set $Z \subseteq \alpha$. For a finite set
$A \subseteq \alpha$, the step map sends a finite set $Z \subseteq \alpha$ to
$\mathrm{post}_r(A) \cup \mathrm{post}_r(Z)$.

Its least fixed point is the set of elements reachable from $A$ in one or more $r$-steps. -/
def transGenStep (A Z : Finset α) : Finset α :=
  postFin r A ∪ postFin r Z

theorem transGenStep_mono (A : Finset α) : Monotone (transGenStep r A) := fun _ _ h =>
  Finset.union_subset_union (Finset.Subset.refl _) (postFin_mono h)

/-- **Elements reachable from a finite set of sources.** Let $\alpha$ be a finite type with
decidable equality, let $r$ be a decidable relation on $\alpha$, and let $A \subseteq \alpha$ be a
finite set. Write $\mathrm{post}_r(Z)$ for the set of $r$-successors of elements of a finite set
$Z \subseteq \alpha$, and let $f$ be the step map
$f(Z) = \mathrm{post}_r(A) \cup \mathrm{post}_r(Z)$. The finite set of elements reachable from
$A$ is $f^{|\alpha|}(\emptyset)$, obtained by applying $f$ to the empty set $|\alpha|$ times,
where $|\alpha|$ is the number of elements of $\alpha$.

Since $f$ is monotone, this is the least fixed point of $f$; it consists of the elements
reachable from some element of $A$ in one or more $r$-steps. -/
def transGenFinFrom (A : Finset α) : Finset α :=
  Finset.lfpFin (transGenStep r A)

/-- **Elements reachable from a point.** Let $\alpha$ be a finite type with decidable equality,
let $r$ be a decidable relation on $\alpha$, and let $a \in \alpha$. The finite set of elements
reachable from $a$ is the finite set of elements reachable from the source set $\{a\}$, that is,
the elements reachable from $a$ in one or more $r$-steps. -/
def transGenFin (a : α) : Finset α :=
  transGenFinFrom r {a}

variable {r}

/-- **Membership in the set reachable from finitely many sources.** Let $\alpha$ be a finite type
with decidable equality, let $r$ be a decidable relation on $\alpha$, and let $A \subseteq \alpha$
be a finite set. An element $t \in \alpha$ lies in the finite set of elements reachable from $A$
in one or more $r$-steps (computed as a finite least fixed point) if and only if there is some
$a \in A$ such that $(a, t)$ lies in the transitive closure of $r$. -/
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

/-- **Membership in the set reachable from a point.** Let $\alpha$ be a finite type with
decidable equality, let $r$ be a decidable relation on $\alpha$, and let $a \in \alpha$. An
element $t \in \alpha$ lies in the finite set of elements reachable from $a$ in one or more
$r$-steps (computed as a finite least fixed point) if and only if $(a, t)$ lies in the transitive
closure of $r$. -/
theorem mem_transGenFin {a t : α} : t ∈ transGenFin r a ↔ TransGen r a t := by
  rw [transGenFin, mem_transGenFinFrom]
  simp

variable (r)

/-- **Decidability of the transitive closure on a finite type.** Let $\alpha$ be a finite type
with decidable equality and let $r$ be a decidable relation on $\alpha$. Then the transitive
closure of $r$ is decidable: for all $a, t \in \alpha$ it is decidable whether $t$ is reachable
from $a$ in one or more $r$-steps.

The decision is membership of $t$ in the finite set of elements reachable from $a$. -/
@[instance_reducible]
def decidableTransGen : DecidableRel (TransGen r) := fun a t =>
  decidable_of_iff (t ∈ transGenFin r a) mem_transGenFin

/-- **Decidability of the reflexive-transitive closure on a finite type.** Let $\alpha$ be a
finite type with decidable equality and let $r$ be a decidable relation on $\alpha$. Then the
reflexive-transitive closure of $r$ is decidable: for all $a, t \in \alpha$ it is decidable
whether $t$ is reachable from $a$ in zero or more $r$-steps. -/
@[instance_reducible]
def decidableReflTransGen : DecidableRel (ReflTransGen r) := fun a t =>
  haveI := decidableTransGen r
  decidable_of_iff (t = a ∨ TransGen r a t) reflTransGen_iff_eq_or_transGen.symm

end Relation
