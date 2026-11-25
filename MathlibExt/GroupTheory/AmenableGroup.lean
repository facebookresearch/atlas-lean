/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Algebra.Group.PUnit

@[expose] public section

open scoped Pointwise Classical symmDiff

/-! # Amenable groups via the Følner condition

A discrete group `G` is *amenable* when it satisfies the **Følner condition**: for
every finite subset `K ⊆ G` and every `ε > 0` there is a finite nonempty subset
`F ⊆ G` that is *almost invariant* under left translation by the elements of `K`,
i.e. `|s • F ∆ F| / |F| < ε` for every `s ∈ K`.

This is the measure-theory-free characterization of amenability. It is classically
equivalent to the existence of a finitely-additive left-invariant probability
measure (an invariant mean / Banach mean) on `G`; that equivalence is not proved
here. Mathlib's `Mathlib.MeasureTheory.Group.FoelnerFilter` develops a
*measure-theoretic* Følner filter for a group action `MulAction G X` on a measure
space and derives an invariant mean on `Set X` (`IsFoelner.amenable`), but it does
not provide this combinatorial predicate on a discrete group; hence the definition
below.

Reference: Følner, *On groups with full Banach mean value* (1955);
cf. Ceccherini-Silberstein–Coornaert, *Cellular Automata and Groups*, Ch. 4. -/

/-- **Amenable group (Følner condition).** A discrete group $G$ is *amenable* if it satisfies the
Følner condition: for every finite subset $K \subseteq G$ and every real $\varepsilon > 0$ there is
a finite nonempty subset $F \subseteq G$ such that
$|sF \mathbin{\triangle} F| / |F| < \varepsilon$ for every $s \in K$. Here
$sF = \{sf : f \in F\}$ is the left translate of $F$ by $s$, $\triangle$ is symmetric difference
and $|\cdot|$ is cardinality. -/
def IsAmenable (G : Type*) [Group G] : Prop :=
  ∀ (K : Finset G) (ε : ℝ), 0 < ε →
    ∃ F : Finset G, F.Nonempty ∧
      ∀ s ∈ K, (((s • F) ∆ F).card : ℝ) / (F.card : ℝ) < ε

/-- **Finite groups are amenable.** Every finite group is amenable.

The whole group $F = G$ is invariant under left translation, so it is a Følner set whose
symmetric-difference ratio is $0$. -/
theorem isAmenable_of_finite (G : Type*) [Group G] [Finite G] : IsAmenable G := by
  letI := Fintype.ofFinite G
  intro K ε hε
  refine ⟨Finset.univ, ⟨1, Finset.mem_univ 1⟩, fun s _ => ?_⟩
  rw [Finset.smul_finset_univ, symmDiff_self]
  simpa using hε

/-- **Trivial groups are amenable.** Every group with at most one element is amenable; the set
$F = \{1\}$ witnesses the Følner condition. -/
theorem isAmenable_of_subsingleton (G : Type*) [Group G] [Subsingleton G] :
    IsAmenable G := by
  intro K ε hε
  refine ⟨{1}, Finset.singleton_nonempty 1, fun s _ => ?_⟩
  rw [Finset.smul_finset_singleton, Subsingleton.elim (s • (1 : G)) 1, symmDiff_self]
  simpa using hε

/-- The symmetric group `S₃` is amenable (an ordinary finite example). -/
example : IsAmenable (Equiv.Perm (Fin 3)) := isAmenable_of_finite _

/-- The trivial group is amenable (a boundary example). -/
example : IsAmenable PUnit := isAmenable_of_subsingleton _
