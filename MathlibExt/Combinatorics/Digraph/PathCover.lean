/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `2a4dcd009357b93b103d542487dfaa3fa6765d77`.

Original formalization by vonbers (@vonbo) and Avocado; ported with attribution.
Source: formal-math commit `e369bf2e` (PR #5951).
-/

module

public import Mathlib.Combinatorics.Digraph.Basic
public import MathlibExt.Combinatorics.Order.Dilworth
public import MathlibExt.Combinatorics.Digraph.FiniteDAG
import Mathlib.Logic.Relation
import Mathlib.Order.Preorder.Finite

@[expose] public section

section
namespace MathlibExt.Combinatorics.Digraph.PathCoverWanted

open MathlibExt.Combinatorics.Order.DilworthWanted (IsChainCoverFin
  dilworth_decomposition exists_isAntichain_card_eq_maxAntichainSize
  exists_isChainCoverFin_card_eq_minChainCoverSize minChainCoverSize)

/-!
# Minimum path cover of a finite transitive DAG

Gallai and Milgram's path-cover theorem (Diestel, *Graph Theory* §2.5,
Theorem 2.5.1) implies Dilworth's decomposition by applying it to the
comparability digraph of a partial order. This file travels the reverse
direction: for a finite digraph that is irreflexive and transitive — equivalently,
the comparability digraph of a finite partial order — directed paths are exactly
nonempty chains, and a chain cover (which permits overlapping chains) is turned
into a vertex-disjoint path cover by assigning each vertex to one of its chains
and discarding empty members, so the landed order-side Dilworth development yields
the path-cover min-max: the minimum number of vertex-disjoint paths covering
all vertices equals the maximum size of an antichain
(`minPathCover_eq_maxAntichain`).

## Representation

Vertices live in a `Fintype`; arcs are a Mathlib `Digraph`. Mathlib's `Digraph`
API is relation-only (no walk, path, or acyclicity theory), so a path is defined
directly as the vertex set of a duplicate-free vertex list with consecutive
adjacency (`List.IsChain`), and DAG-ness is the explicit hypothesis
`IsTransitiveDAG` (irreflexive and transitive) rather than a new carrier type.
Consecutive adjacency is the honest notion of directed path: only successive
vertices need joining arcs, so `0 → 1 → 2` is a path even without a `0 → 2`
arc, whereas `List.Pairwise` would demand arcs between every earlier/later
pair. Transitivity is used solely inside the path/chain correspondence lemmas,
where it upgrades consecutive adjacency to pairwise reachability and so
identifies paths with chains in both directions.

Transitivity is load-bearing, not a convenience: in a general (non-transitive)
DAG the minimum path cover can strictly exceed the reachability width — e.g. two
sources feeding one middle vertex feeding two sinks needs three paths but has
width two — so no Dilworth reduction is possible there. The matching-based
formula for general DAGs is out of scope.
-/

variable {V : Type*}

/-- A digraph is a transitive DAG when its arcs are irreflexive and transitive.
Together these imply acyclicity (a directed cycle would compose to a loop), so
this is exactly the class of comparability digraphs of partial orders. -/
structure IsTransitiveDAG (D : Digraph V) : Prop where
  /-- No loops. -/
  irrefl : ∀ x, ¬ D.Adj x x
  /-- Arcs compose. -/
  trans : ∀ x y z, D.Adj x y → D.Adj y z → D.Adj x z

/-- The transitive closure of a digraph as a digraph: arcs are reachability
(`Relation.TransGen`) steps. -/
def transClosure (D : Digraph V) : Digraph V :=
  ⟨Relation.TransGen D.Adj⟩

/-- Arcs of the transitive closure are exactly reachability steps. -/
@[simp]
theorem transClosure_adj (D : Digraph V) (a b : V) :
    (transClosure D).Adj a b ↔ Relation.TransGen D.Adj a b :=
  Iff.rfl

/-- The transitive closure of a DAG is a transitive DAG. -/
theorem isTransitiveDAG_transClosure (D : Digraph V) (hD : D.IsAcyclic) :
    IsTransitiveDAG (transClosure D) where
  irrefl := fun x h => hD x h
  trans := fun _ _ _ hab hbc => Relation.TransGen.trans hab hbc

/-- The transitive closure of a DAG is again a DAG: a reachability cycle in
the closure collapses to a reachability cycle in the original digraph. -/
theorem isAcyclic_transClosure (D : Digraph V) (hD : D.IsAcyclic) :
    (transClosure D).IsAcyclic := by
  have collapse : ∀ a b, Relation.TransGen (transClosure D).Adj a b →
      Relation.TransGen D.Adj a b := by
    intro a b hab
    induction hab with
    | single h => exact h
    | tail _ hbc ih => exact Relation.TransGen.trans ih hbc
  intro x h
  exact hD x (collapse x x h)

/-- A transitive DAG is a DAG: a reachability cycle would compose (by
transitivity) to a loop, contradicting irreflexivity. -/
theorem isAcyclic_of_isTransitiveDAG (D : Digraph V) (hD : IsTransitiveDAG D) :
    D.IsAcyclic := by
  have collapse : ∀ a b, Relation.TransGen D.Adj a b → D.Adj a b := by
    intro a b hab
    induction hab with
    | single h => exact h
    | tail _ hbc ih => exact hD.trans _ _ _ ih hbc
  intro x h
  exact hD.irrefl x (collapse x x h)

/-- The reachability relation of a transitive DAG: `x` reaches `y` iff they are
equal or joined by an arc. This is the relation underlying `toPartialOrder`,
kept as a private shorthand for the antichain-counting lemmas; the public
correspondence lemmas are stated through `(toPartialOrder D hD).le` instead. -/
private abbrev dagLE (D : Digraph V) (x y : V) : Prop := x = y ∨ D.Adj x y

/-- The partial order of a transitive DAG: `x ≤ y` iff `x = y` or there is an
arc `x → y`. Reflexivity and transitivity are immediate; antisymmetry uses
acyclicity, since mutual arcs would compose to a loop. -/
@[instance_reducible]
def toPartialOrder (D : Digraph V) (hD : IsTransitiveDAG D) : PartialOrder V where
  le := fun x y => x = y ∨ D.Adj x y
  le_refl := fun _ => Or.inl rfl
  le_trans := fun x y z hxy hyz => by
    rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
    · exact Or.inl (hxy.trans hyz)
    · rw [hxy]; exact Or.inr hyz
    · rw [← hyz]; exact Or.inr hxy
    · exact Or.inr (hD.trans x y z hxy hyz)
  le_antisymm := fun x y hxy hyx => by
    rcases hxy with hxy | hxy <;> rcases hyx with hyx | hyx
    · exact hxy
    · rw [hxy] at hyx; exact absurd hyx (hD.irrefl y)
    · rw [hyx] at hxy; exact absurd hxy (hD.irrefl x)
    · exact absurd (hD.trans x y x hxy hyx) (hD.irrefl x)
  lt_iff_le_not_ge := fun _ _ => Iff.rfl

/-- Reachability in `toPartialOrder`: `x ≤ y` iff `x = y` or there is an arc
`x → y`. This is `Iff.rfl`; it lets downstream users apply the public
correspondence lemmas without unfolding the order. -/
@[simp]
theorem toPartialOrder_le (D : Digraph V) (hD : IsTransitiveDAG D) (x y : V) :
    (toPartialOrder D hD).le x y ↔ x = y ∨ D.Adj x y := Iff.rfl

open Classical in
/-- A vertex set is a directed path when it is exactly the vertex set of a
nonempty duplicate-free vertex list with consecutive adjacency (`List.IsChain`):
arcs join each vertex to the next, with no requirement on non-consecutive pairs.
Following Diestel, there is no empty path: a zero-edge path still has one
vertex, so the witnessing list is required to be nonempty. -/
def IsPath (D : Digraph V) (s : Finset V) : Prop :=
  ∃ l : List V, l.Nodup ∧ List.IsChain D.Adj l ∧ l ≠ [] ∧ l.toFinset = s

/-- A path cover is a family of pairwise vertex-disjoint nonempty paths whose
union is all vertices. Empty paths are excluded (Diestel convention); they
could never help minimize the count. -/
def IsPathCover (D : Digraph V) (P : Finset (Finset V)) : Prop :=
  (∀ s ∈ P, IsPath D s ∧ s.Nonempty) ∧
    (∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t) ∧
    ∀ a : V, ∃ s ∈ P, a ∈ s

open Classical in
/-- The minimum number of vertex-disjoint paths covering all vertices (`0` if
no path cover exists, which never happens since singleton paths always form
one). -/
noncomputable def minPathCoverSize (D : Digraph V) [Fintype V] : ℕ :=
  let all : Finset (Finset (Finset V)) := Finset.univ.powerset.powerset
  let valid := all.filter fun P => IsPathCover D P
  if h : valid.Nonempty then valid.inf' h fun P => P.card else 0

/-- The maximum size of an antichain in the reachability order of a transitive
DAG, transported from the order-side Dilworth development. -/
noncomputable def maxAntichainSize (D : Digraph V) [Fintype V]
    (hD : IsTransitiveDAG D) : ℕ :=
  @MathlibExt.Combinatorics.Order.DilworthWanted.maxAntichainSize V _
    (toPartialOrder D hD)

/-- Consecutive adjacency upgrades to pairwise adjacency along a transitive
digraph: the head of a chain reaches every later vertex by composing arcs. -/
private theorem pairwise_of_isChain (D : Digraph V) (hD : IsTransitiveDAG D)
    {l : List V} (h : List.IsChain D.Adj l) : List.Pairwise D.Adj l := by
  induction h with
  | nil => exact List.Pairwise.nil
  | singleton a => exact List.pairwise_singleton _ a
  | cons_cons hab _ ih =>
    rw [List.pairwise_cons]
    refine ⟨fun c hc => ?_, ih⟩
    rcases List.mem_cons.mp hc with rfl | hcl
    · exact hab
    · exact hD.trans _ _ _ hab ((List.pairwise_cons.mp ih).1 c hcl)

/-- Paths are chains in the reachability order: consecutive arcs compose (by
transitivity) to pairwise reachability, hence pairwise comparability. Stated
through `toPartialOrder` (see `toPartialOrder_le`) so downstream users never
unfold internals. -/
theorem isChain_of_isPath (D : Digraph V) (hD : IsTransitiveDAG D)
    {s : Finset V} (h : IsPath D s) :
    @IsChain V (toPartialOrder D hD).le (s : Set V) := by
  classical
  obtain ⟨l, -, hch, -, rfl⟩ := h
  have hpw := pairwise_of_isChain D hD hch
  have chain : ∀ (l : List V),
      List.Pairwise D.Adj l →
        @IsChain V (toPartialOrder D hD).le (l.toFinset : Set V) := by
    intro l
    induction l with
    | nil =>
      intro _
      rw [List.toFinset_nil, Finset.coe_empty]
      exact IsChain.empty
    | cons x l ih =>
      intro hpw
      rw [List.pairwise_cons] at hpw
      rw [List.toFinset_cons, Finset.coe_insert]
      refine IsChain.insert (ih hpw.2) ?_
      intro b hb hxb
      have hb' : b ∈ l := List.mem_toFinset.mp (Finset.mem_coe.mp hb)
      change (x = b ∨ D.Adj x b) ∨ (toPartialOrder D hD).le b x
      exact Or.inl (Or.inr (hpw.1 b hb'))
  exact chain l hpw

/-- Nonempty chains in the reachability order are paths: a chain lists in
reachability order by peeling off a minimal element, and the minimal element
is joined by an arc to the head of the tail list since distinct comparable
vertices are adjacent. Only consecutive adjacency is needed, so this direction
uses no transitivity. -/
theorem isPath_of_isChain (D : Digraph V) (hD : IsTransitiveDAG D)
    {s : Finset V} (hs : s.Nonempty)
    (h : @IsChain V (toPartialOrder D hD).le (s : Set V)) : IsPath D s := by
  classical
  let _ord := toPartialOrder D hD
  refine Finset.strongInduction
    (p := fun s : Finset V => s.Nonempty →
      @IsChain V (toPartialOrder D hD).le (s : Set V) → IsPath D s)
    (fun s IH hs h => ?_) s hs h
  obtain ⟨x, hxmin⟩ := Finset.exists_minimal hs
  have hxmem : x ∈ s := hxmin.1
  have hxprop : ∀ ⦃y⦄, y ∈ s → y ≤ x → x ≤ y := hxmin.2
  have hchain := h
  unfold IsChain Set.Pairwise at hchain
  have hxle : ∀ y ∈ s, x = y ∨ D.Adj x y := by
    intro y hy
    by_cases hxy : x = y
    · exact Or.inl hxy
    · have hcomp :=
        hchain (Finset.mem_coe.mpr hxmem) (Finset.mem_coe.mpr hy) hxy
      rcases hcomp with hcomp | hcomp
      · exact hcomp
      · have hyx : y ≤ x := hcomp
        have hxy' : x ≤ y := hxprop hy hyx
        exact hxy'
  have hsub : (↑(s.erase x) : Set V) ⊆ ↑s :=
    Finset.coe_subset.mpr (Finset.erase_subset x s)
  have hchain' : @IsChain V (toPartialOrder D hD).le ↑(s.erase x) :=
    IsChain.mono hsub h
  by_cases htail : (s.erase x).Nonempty
  · obtain ⟨l, hnod, hch, hne, hl⟩ :=
      IH (s.erase x) (Finset.erase_ssubset hxmem) htail hchain'
    refine ⟨x :: l, ?_, ?_, List.cons_ne_nil _ _, ?_⟩
    · rw [List.nodup_cons]
      refine ⟨?_, hnod⟩
      intro hxl
      rw [← List.mem_toFinset, hl, Finset.mem_erase] at hxl
      exact hxl.1 rfl
    · clear hne
      revert hnod hl hch
      cases l with
      | nil =>
        intro _ _ _
        exact List.isChain_singleton x
      | cons y l' =>
        intro _ hch hl
        rw [List.isChain_cons_cons]
        refine ⟨?_, hch⟩
        have hb2 : y ∈ s.erase x := by
          rw [← hl]
          exact List.mem_toFinset.mpr (List.mem_cons.mpr (Or.inl rfl))
        have hbs : y ∈ s := Finset.mem_of_mem_erase hb2
        have hbx : y ≠ x := (Finset.mem_erase.mp hb2).1
        have hle := hxle y hbs
        rcases hle with hxy | hadj
        · exact absurd hxy.symm hbx
        · exact hadj
    · rw [List.toFinset_cons, hl]
      exact Finset.insert_erase hxmem
  · have hempty : s.erase x = ∅ := Finset.not_nonempty_iff_eq_empty.mp htail
    have hsing : s = {x} := by
      rw [← Finset.insert_erase hxmem, hempty, Finset.insert_empty]
    subst hsing
    refine ⟨[x], List.nodup_singleton x, List.isChain_singleton x,
      List.cons_ne_nil _ _, ?_⟩
    ext y
    simp

/-- Every path cover is a chain cover (forgetting disjointness). -/
private theorem isChainCover_of_pathCover (D : Digraph V) (hD : IsTransitiveDAG D)
    {P : Finset (Finset V)} (hP : IsPathCover D P) :
    @IsChainCoverFin V (toPartialOrder D hD) P := by
  refine ⟨fun s hs => ?_, fun a => hP.2.2 a⟩
  exact isChain_of_isPath D hD (hP.1 s hs).1

/-- Every chain cover yields a path cover with no more paths: assigning each
vertex to one of its chains (by choice) disjointifies the cover, each nonempty
piece lists as a path, and empty fibers are discarded. -/
private theorem exists_pathCover_of_chainCover (D : Digraph V)
    (hD : IsTransitiveDAG D) {C : Finset (Finset V)}
    (hC : @IsChainCoverFin V (toPartialOrder D hD) C) :
    ∃ P, IsPathCover D P ∧ P.card ≤ C.card := by
  classical
  have hex : ∀ a : V, ∃ t ∈ C, a ∈ t := fun a => hC.2 a
  choose f hfC hfmem using hex
  refine ⟨(C.image (fun t => t.filter fun a => f a = t)).filter (·.Nonempty),
    ⟨?_, ?_, ?_⟩, (Finset.card_filter_le _ _).trans Finset.card_image_le⟩
  · intro s hs
    obtain ⟨hsimg, hsne⟩ := Finset.mem_filter.mp hs
    obtain ⟨t, htC, rfl⟩ := Finset.mem_image.mp hsimg
    refine ⟨?_, hsne⟩
    apply isPath_of_isChain D hD hsne
    apply IsChain.mono _ (hC.1 t htC)
    exact Finset.coe_subset.mpr (Finset.filter_subset _ _)
  · intro s hs t ht hne
    obtain ⟨hsimg, -⟩ := Finset.mem_filter.mp hs
    obtain ⟨htimg, -⟩ := Finset.mem_filter.mp ht
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hsimg
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp htimg
    rw [Finset.disjoint_left]
    intro a ha₁ ha₂
    rw [Finset.mem_filter] at ha₁ ha₂
    have heq : u = v := ha₁.2.symm.trans ha₂.2
    subst heq
    exact absurd rfl hne
  · intro a
    have hmem : a ∈ (f a).filter (fun b => f b = f a) := by
      rw [Finset.mem_filter]
      exact ⟨hfmem a, rfl⟩
    have hne : ((f a).filter (fun b => f b = f a)).Nonempty := ⟨a, hmem⟩
    refine ⟨(f a).filter (fun b => f b = f a), ?_, hmem⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_image.mpr ⟨f a, hfC a, rfl⟩, hne⟩

/-- An antichain meets each path at most once, so it is no larger than any
path cover. -/
private theorem card_antichain_le_pathCover (D : Digraph V)
    (hD : IsTransitiveDAG D)
    {A : Finset V} {P : Finset (Finset V)}
    (hA : IsAntichain (dagLE D) (A : Set V)) (hP : IsPathCover D P) :
    A.card ≤ P.card := by
  classical
  have hex : ∀ a ∈ A, ∃ t ∈ P, a ∈ t := fun a _ => hP.2.2 a
  choose f hfP hfmem using hex
  let F : ↥A → ↥P := fun a => ⟨f a.1 a.2, hfP a.1 a.2⟩
  have hinj : Function.Injective F := by
    intro a1 a2 heq
    have hfeq : f a1.1 a1.2 = f a2.1 a2.2 := congrArg Subtype.val heq
    by_contra hne
    have hne' : (a1 : V) ≠ (a2 : V) := fun h => hne (Subtype.ext h)
    have hch := isChain_of_isPath D hD (hP.1 _ (hfP a1.1 a1.2)).1
    have m1 : (a1 : V) ∈ ((f a1.1 a1.2 : Finset V) : Set V) := hfmem a1.1 a1.2
    have m2 : (a2 : V) ∈ ((f a1.1 a1.2 : Finset V) : Set V) :=
      hfeq ▸ hfmem a2.1 a2.2
    unfold IsChain Set.Pairwise at hch
    unfold IsAntichain Set.Pairwise at hA
    have hle := hch m1 m2 hne'
    have ha1' : (a1 : V) ∈ (A : Set V) := a1.2
    have ha2' : (a2 : V) ∈ (A : Set V) := a2.2
    rcases hle with h | h
    · exact hA ha1' ha2' hne' h
    · exact hA ha2' ha1' (Ne.symm hne') h
  have hle := Fintype.card_le_of_injective F hinj
  rwa [Fintype.card_coe, Fintype.card_coe] at hle

/-- Singleton paths always form a path cover. -/
private theorem exists_valid_pathCover (D : Digraph V) [Fintype V] :
    ∃ P, IsPathCover D P ∧ P ∈ Finset.univ.powerset.powerset := by
  classical
  refine ⟨Finset.univ.image fun a => ({a} : Finset V), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    refine ⟨⟨[a], List.nodup_singleton a, List.isChain_singleton a,
      List.cons_ne_nil _ _, ?_⟩, Finset.singleton_nonempty a⟩
    ext x
    simp
  · intro s hs t ht hne
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.disjoint_singleton]
    intro hab
    apply hne
    rw [hab]
  · intro a
    exact ⟨{a}, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩,
      Finset.mem_singleton_self a⟩
  · rw [Finset.mem_powerset]
    intro t ht
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_powerset]
    exact Finset.subset_univ _

/-- A path cover bounds `minPathCoverSize` from above. -/
theorem minPathCoverSize_le_card (D : Digraph V) [Fintype V]
    {P : Finset (Finset V)}
    (hP : IsPathCover D P) : minPathCoverSize D ≤ P.card := by
  classical
  have hmem : P ∈ Finset.univ.powerset.powerset :=
    Finset.mem_powerset.mpr fun t _ => Finset.mem_powerset.mpr (Finset.subset_univ t)
  have hmem' : P ∈ (Finset.univ.powerset.powerset.filter
      fun P => IsPathCover D P) :=
    Finset.mem_filter.mpr ⟨hmem, hP⟩
  unfold minPathCoverSize
  change (if h : ((Finset.univ.powerset.powerset.filter
      fun P => IsPathCover D P)).Nonempty
    then ((Finset.univ.powerset.powerset.filter
      fun P => IsPathCover D P)).inf' h fun P => P.card else 0) ≤ P.card
  rw [dite_eq_left ⟨P, hmem'⟩]
  exact Finset.inf'_le _ hmem'

/-- Some path cover attains `minPathCoverSize`. -/
theorem exists_isPathCover_card_eq_minPathCoverSize (D : Digraph V) [Fintype V] :
    ∃ P, IsPathCover D P ∧ P.card = minPathCoverSize D := by
  classical
  obtain ⟨P₀, hP₀, hP₀mem⟩ := exists_valid_pathCover D
  have hne : (Finset.univ.powerset.powerset.filter
      fun P => IsPathCover D P).Nonempty :=
    ⟨P₀, Finset.mem_filter.mpr ⟨hP₀mem, hP₀⟩⟩
  obtain ⟨P, hPmem, hPeq⟩ := Finset.exists_mem_eq_inf' hne fun P => P.card
  obtain ⟨-, hP⟩ := Finset.mem_filter.mp hPmem
  refine ⟨P, hP, ?_⟩
  unfold minPathCoverSize
  change P.card = (if h : ((Finset.univ.powerset.powerset.filter
      fun P => IsPathCover D P)).Nonempty
    then ((Finset.univ.powerset.powerset.filter
      fun P => IsPathCover D P)).inf' h fun P => P.card else 0)
  rw [dite_eq_left hne]
  exact hPeq.symm

/-- The easy direction: a largest antichain is smaller than every path cover. -/
private theorem maxAntichain_le_minPath (D : Digraph V) [Fintype V]
    (hD : IsTransitiveDAG D) : maxAntichainSize D hD ≤ minPathCoverSize D := by
  classical
  obtain ⟨A₀, hA₀, hA₀card⟩ :=
    @exists_isAntichain_card_eq_maxAntichainSize V _ (toPartialOrder D hD)
  obtain ⟨P, hP, hPcard⟩ := exists_isPathCover_card_eq_minPathCoverSize D
  have hA₀' : IsAntichain (dagLE D) (A₀ : Set V) := hA₀
  have hle := card_antichain_le_pathCover D hD hA₀' hP
  change @MathlibExt.Combinatorics.Order.DilworthWanted.maxAntichainSize V _
    (toPartialOrder D hD) ≤ minPathCoverSize D
  omega

/-- The hard direction via Dilworth: an optimal chain cover becomes a path
cover with no more paths. -/
private theorem minPath_le_maxAnti (D : Digraph V) [Fintype V]
    (hD : IsTransitiveDAG D) : minPathCoverSize D ≤ maxAntichainSize D hD := by
  classical
  obtain ⟨C, hC, hCcard⟩ :=
    @exists_isChainCoverFin_card_eq_minChainCoverSize V _ (toPartialOrder D hD)
  obtain ⟨P, hP, hPcard⟩ := exists_pathCover_of_chainCover D hD hC
  have hle1 := minPathCoverSize_le_card D hP
  have hdil : @MathlibExt.Combinatorics.Order.DilworthWanted.maxAntichainSize V _
      (toPartialOrder D hD) = @minChainCoverSize V _ (toPartialOrder D hD) :=
    @dilworth_decomposition V _ (toPartialOrder D hD)
  have hmain : minPathCoverSize D ≤
      @MathlibExt.Combinatorics.Order.DilworthWanted.maxAntichainSize V _
        (toPartialOrder D hD) := by
    omega
  exact hmain

/-- Minimum path cover min-max for finite transitive DAGs: the smallest number
of vertex-disjoint paths covering all vertices equals the largest size of an
antichain in the reachability order. This is the converse direction of
Diestel's Corollary 2.5.2: here Dilworth's decomposition implies the path-cover
min-max, via the identification of paths with chains. -/
theorem minPathCover_eq_maxAntichain (D : Digraph V) [Fintype V]
    (hD : IsTransitiveDAG D) : minPathCoverSize D = maxAntichainSize D hD :=
  le_antisymm (minPath_le_maxAnti D hD) (maxAntichain_le_minPath D hD)

/-- Regression check for the consecutive-adjacency fix: in the digraph
`0 → 1 → 2` with no `0 → 2` arc, the full vertex set is a directed path.
Under the old `List.Pairwise` definition no ordering of `[0, 1, 2]` would
qualify, since pairwise adjacency demands the missing `0 → 2` arc. -/
private example : IsPath (V := Fin 3) ⟨fun x y => x.val + 1 = y.val⟩
    {0, 1, 2} := by
  refine ⟨[0, 1, 2], by decide, ?_, List.cons_ne_nil _ _, ?_⟩
  · change List.IsChain (fun x y : Fin 3 => x.val + 1 = y.val) [0, 1, 2]
    decide
  · ext a
    simp

end MathlibExt.Combinatorics.Digraph.PathCoverWanted
