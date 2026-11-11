/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.ComplexBalanced
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Logic.Relation
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Reaction-network structure for the deficiency-zero theorem

This file is the production API for the graph-theoretic structure of a chemical reaction
network `N : ReactionNetwork S ρ` (defined, with its stoichiometric subspace, in
`MathlibExt.Biology.Dynamics.ComplexBalanced`):

* `complexes`: the complexes, i.e. the sources and products of the reactions;
* `Reacts`: the directed reaction relation `y ⟶ y'` on complexes;
* `linkageGraph`: the undirected reaction graph on the complexes (self-reactions `y → y`
  contribute no edge, parallel reactions contribute one edge);
* `numLinkageClasses`: the number of its connected components (linkage classes);
* `deficiency`: `δ = n - ℓ - s`;
* `IsWeaklyReversible`: every reaction `y → y'` can be undone by a directed path `y' ⟶* y`.

These definitions previously lived in `WantedExt/Biology/Dynamics/DeficiencyZeroWanted.lean`;
that file now imports this one and states the deficiency-zero theorems against them.

## Main results

* `linkageGraph_adj`, `Reacts.reachable`, `reachable_of_reflTransGen`: directed reaction paths
  stay inside a linkage class.
* `reachable_imp_iff_of_reacts`: a property of complexes preserved by every reaction is
  constant on each linkage class (the usual way to separate linkage classes).
* `card_le_numLinkageClasses`, `numLinkageClasses_le_card`: counting linkage classes by
  pairwise unreachable complexes and by complexes reaching every complex.
* `numLinkageClasses_le_card_complexes`, `numLinkageClasses_le_card_reactions`,
  `numLinkageClasses_pos`; the empty network has no complexes, no linkage classes and
  deficiency `0` (`numLinkageClasses_of_isEmpty`, `deficiency_of_isEmpty`).
* `IsWeaklyReversible.reflTransGen_symm`, `IsWeaklyReversible.reflTransGen_iff_reachable`,
  `isWeaklyReversible_iff_reachable`: a network is weakly reversible iff each linkage class is
  strongly connected, i.e. directed reachability coincides with linkage-class membership.
* `isWeaklyReversible_of_reversible`: reversible networks are weakly reversible.

## References

* M. Feinberg, "Chemical reaction network structure and the stability of complex isothermal
  reactors — I. The deficiency zero and deficiency one theorems", Chem. Eng. Sci. 42 (1987)
  2229–2268, §§2–3.
* M. Feinberg, *Foundations of Chemical Reaction Network Theory*, Springer (2019), ch. 3, 6.
-/

@[expose] public section

namespace MathlibExt.Biology.Dynamics.ComplexBalanced

variable {S ρ : Type*}

namespace ReactionNetwork

variable (N : ReactionNetwork S ρ)

/-- The complexes of the network: the sources and products of its reactions.

Source: Feinberg (1987), §2; Feinberg (2019), Def. 3.1.1. -/
def complexes : Set (S → ℕ) :=
  Set.range N.src ∪ Set.range N.prod

/-- The directed reaction relation on complexes: `y ⟶ y'` if some reaction has source `y` and
product `y'`.

Source: Feinberg (2019), §3.1. -/
def Reacts (y y' : S → ℕ) : Prop :=
  ∃ r, N.src r = y ∧ N.prod r = y'

/-- The undirected reaction graph on the complexes: distinct complexes are adjacent when one
reacts to the other.

Source: Feinberg (1987), §2.2 (the standard reaction diagram, undirected). -/
def linkageGraph : SimpleGraph N.complexes :=
  SimpleGraph.fromRel fun c c' => N.Reacts c c'

/-- The number of linkage classes: connected components of the undirected reaction graph.

Source: Feinberg (1987), §2.2; Feinberg (2019), Def. 3.1.4. -/
noncomputable def numLinkageClasses : ℕ :=
  Nat.card N.linkageGraph.ConnectedComponent

/-- The deficiency `δ = n - ℓ - s` (number of complexes, linkage classes, dimension of the
stoichiometric subspace).

Source: Feinberg (1987), §3; Feinberg (2019), Def. 6.1.1. -/
noncomputable def deficiency : ℤ :=
  (Nat.card N.complexes : ℤ) - N.numLinkageClasses -
    Module.finrank ℝ N.stoichiometricSubspace

/-- The network is weakly reversible: for every reaction `y → y'` there is a directed path of
reactions from `y'` back to `y`.

Source: Feinberg (1987), §2.4; Feinberg (2019), Def. 3.4.1. -/
def IsWeaklyReversible : Prop :=
  ∀ r, Relation.ReflTransGen N.Reacts (N.prod r) (N.src r)

/-! ### Complexes and the reaction relation -/

variable {N}

theorem src_mem_complexes (r : ρ) : N.src r ∈ N.complexes :=
  Or.inl ⟨r, rfl⟩

theorem prod_mem_complexes (r : ρ) : N.prod r ∈ N.complexes :=
  Or.inr ⟨r, rfl⟩

theorem mem_complexes {y : S → ℕ} : y ∈ N.complexes ↔ ∃ r, N.src r = y ∨ N.prod r = y := by
  simp only [complexes, Set.mem_union, Set.mem_range]
  exact ⟨fun h => h.elim (fun ⟨r, hr⟩ => ⟨r, .inl hr⟩) fun ⟨r, hr⟩ => ⟨r, .inr hr⟩,
    fun ⟨r, hr⟩ => hr.elim (fun h => .inl ⟨r, h⟩) fun h => .inr ⟨r, h⟩⟩

theorem reacts_src_prod (r : ρ) : N.Reacts (N.src r) (N.prod r) :=
  ⟨r, rfl, rfl⟩

theorem Reacts.left_mem {y y' : S → ℕ} (h : N.Reacts y y') : y ∈ N.complexes := by
  obtain ⟨r, rfl, -⟩ := h
  exact src_mem_complexes r

theorem Reacts.right_mem {y y' : S → ℕ} (h : N.Reacts y y') : y' ∈ N.complexes := by
  obtain ⟨r, -, rfl⟩ := h
  exact prod_mem_complexes r

theorem complexes_eq_empty [IsEmpty ρ] : N.complexes = ∅ := by
  simp [complexes, Set.range_eq_empty]

theorem finite_complexes [Finite ρ] : N.complexes.Finite :=
  (Set.finite_range _).union (Set.finite_range _)

instance [Finite ρ] : Finite N.complexes :=
  N.finite_complexes.to_subtype

/-! ### The linkage graph -/

theorem linkageGraph_adj {c c' : N.complexes} :
    N.linkageGraph.Adj c c' ↔ c ≠ c' ∧ (N.Reacts c c' ∨ N.Reacts c' c) := by
  simp [linkageGraph, SimpleGraph.fromRel_adj]

/-- The two ends of a reaction lie in the same linkage class. -/
theorem Reacts.reachable {c c' : N.complexes} (h : N.Reacts c c') :
    N.linkageGraph.Reachable c c' := by
  by_cases hcc' : c = c'
  · exact hcc' ▸ SimpleGraph.Reachable.refl c
  · exact (linkageGraph_adj.2 ⟨hcc', .inl h⟩).reachable

theorem src_reachable_prod (r : ρ) :
    N.linkageGraph.Reachable ⟨N.src r, src_mem_complexes r⟩ ⟨N.prod r, prod_mem_complexes r⟩ :=
  Reacts.reachable (reacts_src_prod r)

/-- A directed reaction path starting at a complex stays inside its linkage class. -/
theorem reachable_of_reflTransGen {y y' : S → ℕ} (h : Relation.ReflTransGen N.Reacts y y')
    (hy : y ∈ N.complexes) :
    ∃ hy' : y' ∈ N.complexes, N.linkageGraph.Reachable ⟨y, hy⟩ ⟨y', hy'⟩ := by
  induction h with
  | refl => exact ⟨hy, .rfl⟩
  | tail _ hbc ih =>
    obtain ⟨hb, hreach⟩ := ih
    exact ⟨hbc.right_mem,
      hreach.trans (Reacts.reachable (c := ⟨_, hb⟩) (c' := ⟨_, hbc.right_mem⟩) hbc)⟩

/-- A property of complexes that every reaction preserves is constant on each linkage class.
This is the standard way to show that two complexes lie in different linkage classes. -/
theorem reachable_imp_iff_of_reacts (P : (S → ℕ) → Prop)
    (hP : ∀ y y', N.Reacts y y' → (P y ↔ P y')) {c c' : N.complexes}
    (h : N.linkageGraph.Reachable c c') : P c ↔ P c' := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .rfl
  | cons hadj _ ih =>
    refine Iff.trans ?_ ih
    rcases (linkageGraph_adj.1 hadj).2 with h | h
    · exact hP _ _ h
    · exact (hP _ _ h).symm

/-- A complex not adjacent to any other complex (e.g. one occurring only in self-reactions
`y → y`) is alone in its linkage class. -/
theorem reachable_iff_eq_of_forall_not_adj {c : N.complexes}
    (hc : ∀ c', ¬ N.linkageGraph.Adj c c') {c' : N.complexes} :
    N.linkageGraph.Reachable c c' ↔ c = c' := by
  refine ⟨fun ⟨p⟩ => ?_, fun h => h ▸ .rfl⟩
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hc _)

/-! ### Counting linkage classes -/

/-- Pairwise unreachable complexes lie in distinct linkage classes. -/
theorem card_le_numLinkageClasses [Finite N.complexes] (T : Finset N.complexes)
    (hT : ∀ c ∈ T, ∀ c' ∈ T, N.linkageGraph.Reachable c c' → c = c') :
    T.card ≤ N.numLinkageClasses := by
  classical
  have := Fintype.ofFinite N.linkageGraph.ConnectedComponent
  rw [numLinkageClasses, Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine Finset.card_le_card_of_injOn N.linkageGraph.connectedComponentMk
    (fun _ _ => Finset.mem_univ _) fun c hc c' hc' h => hT c hc c' hc' ?_
  exact SimpleGraph.ConnectedComponent.eq.1 h

/-- If every complex reaches one of the complexes in `T`, there are at most `#T` linkage
classes. -/
theorem numLinkageClasses_le_card [Finite N.complexes] (T : Finset N.complexes)
    (hT : ∀ c, ∃ c' ∈ T, N.linkageGraph.Reachable c c') :
    N.numLinkageClasses ≤ T.card := by
  classical
  have := Fintype.ofFinite N.linkageGraph.ConnectedComponent
  rw [numLinkageClasses, Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine (Finset.card_le_card (t := T.image N.linkageGraph.connectedComponentMk)
    fun C _ => ?_).trans Finset.card_image_le
  induction C using SimpleGraph.ConnectedComponent.ind with
  | h c =>
    obtain ⟨c', hc', hreach⟩ := hT c
    exact Finset.mem_image.2 ⟨c', hc', (SimpleGraph.ConnectedComponent.eq.2 hreach).symm⟩

theorem numLinkageClasses_le_card_complexes [Finite N.complexes] :
    N.numLinkageClasses ≤ Nat.card N.complexes := by
  classical
  have := Fintype.ofFinite N.complexes
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  exact numLinkageClasses_le_card _ fun c => ⟨c, Finset.mem_univ _, .rfl⟩

/-- Every linkage class contains the source of some reaction, so there are at most as many
linkage classes as reactions. -/
theorem numLinkageClasses_le_card_reactions [Fintype ρ] :
    N.numLinkageClasses ≤ Fintype.card ρ := by
  classical
  let T : Finset N.complexes := Finset.univ.image fun r => ⟨N.src r, src_mem_complexes r⟩
  refine (numLinkageClasses_le_card T fun c => ?_).trans Finset.card_image_le
  obtain ⟨y, hy⟩ := c
  obtain ⟨r, hr | hr⟩ := mem_complexes.1 hy
  · subst hr
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ r), .rfl⟩
  · subst hr
    exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ r), (src_reachable_prod r).symm⟩

theorem numLinkageClasses_pos [Finite ρ] [Nonempty ρ] : 0 < N.numLinkageClasses := by
  have : Nonempty N.complexes := ⟨⟨_, src_mem_complexes (Classical.arbitrary ρ)⟩⟩
  exact Nat.card_pos

theorem numLinkageClasses_of_isEmpty [IsEmpty ρ] : N.numLinkageClasses = 0 := by
  have : IsEmpty N.complexes := by
    rw [complexes_eq_empty]
    infer_instance
  exact Nat.card_of_isEmpty

theorem stoichiometricSubspace_of_isEmpty [IsEmpty ρ] : N.stoichiometricSubspace = ⊥ := by
  simp [stoichiometricSubspace, Set.range_eq_empty]

/-- The empty network has deficiency `0`. -/
theorem deficiency_of_isEmpty [IsEmpty ρ] : N.deficiency = 0 := by
  have hs : Module.finrank ℝ N.stoichiometricSubspace = 0 := by
    rw [stoichiometricSubspace_of_isEmpty]
    exact finrank_bot ℝ _
  simp [deficiency, numLinkageClasses_of_isEmpty, complexes_eq_empty, hs]

/-! ### Weak reversibility -/

theorem isWeaklyReversible_iff :
    N.IsWeaklyReversible ↔ ∀ y y', N.Reacts y y' → Relation.ReflTransGen N.Reacts y' y :=
  ⟨fun h _ _ ⟨r, hy, hy'⟩ => hy ▸ hy' ▸ h r, fun h r => h _ _ (reacts_src_prod r)⟩

/-- A network in which every reaction has a reverse reaction is weakly reversible. -/
theorem isWeaklyReversible_of_reversible
    (h : ∀ r, ∃ r', N.src r' = N.prod r ∧ N.prod r' = N.src r) : N.IsWeaklyReversible :=
  fun r => .single (h r)

theorem isWeaklyReversible_of_isEmpty [IsEmpty ρ] : N.IsWeaklyReversible :=
  fun r => isEmptyElim r

/-- In a weakly reversible network directed reachability is symmetric. -/
theorem IsWeaklyReversible.reflTransGen_symm (hN : N.IsWeaklyReversible) {y y' : S → ℕ}
    (h : Relation.ReflTransGen N.Reacts y y') : Relation.ReflTransGen N.Reacts y' y := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact (isWeaklyReversible_iff.1 hN _ _ hbc).trans ih

/-- In a weakly reversible network, two complexes lie in the same linkage class iff there is a
directed reaction path from one to the other: linkage classes are strongly connected. -/
theorem IsWeaklyReversible.reflTransGen_iff_reachable (hN : N.IsWeaklyReversible)
    {c c' : N.complexes} :
    Relation.ReflTransGen N.Reacts c c' ↔ N.linkageGraph.Reachable c c' := by
  refine ⟨fun h => (reachable_of_reflTransGen h c.2).2, fun ⟨p⟩ => ?_⟩
  induction p with
  | nil => exact .refl
  | cons hadj p ih =>
    refine Relation.ReflTransGen.trans ?_ (ih ⟨p⟩)
    rcases (linkageGraph_adj.1 hadj).2 with h | h
    · exact .single h
    · exact isWeaklyReversible_iff.1 hN _ _ h

/-- A network is weakly reversible iff every linkage class is strongly connected. -/
theorem isWeaklyReversible_iff_reachable :
    N.IsWeaklyReversible ↔
      ∀ c c' : N.complexes, N.linkageGraph.Reachable c c' →
        Relation.ReflTransGen N.Reacts c c' := by
  refine ⟨fun hN _ _ => hN.reflTransGen_iff_reachable.2, fun h r => ?_⟩
  exact h ⟨_, prod_mem_complexes r⟩ ⟨_, src_mem_complexes r⟩ (src_reachable_prod r).symm

end ReactionNetwork

end MathlibExt.Biology.Dynamics.ComplexBalanced
