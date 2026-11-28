/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`WantedExt/Combinatorics/HamidouneReverseConnectivityAIMCombinatoricsProblem191Wanted.lean`
(ATLAS, from Formal-Math):
Copyright (c) Meta Platforms, Inc. and affiliates. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Formal-Math contributors.
Adapted portions: the path definitions, the conjecture and the statement of its refutation.
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Basic.Finite.Sum
import Mathlib.Data.List.Basic

/-!
# Hamidoune's reverse-connectivity conjecture

For every `r ≥ 3`, `hamidouneSomeRAtLeastThree_refuted` gives a counterexample to the
reverse-connectivity conjecture. We construct digraphs of increasing minimum out-degree in
which two vertices suffice to separate the ends of each arc in the reverse direction.
At each step, we pair copies of a rooted digraph. A new root points to every old root, and
each nonroot vertex points to the root of its partner copy. This raises the out-degree
while preserving the two-vertex separators. Joining a reversed copy of the resulting
digraph to the original supplies the minimum in-degree as well.

The original formalization cites the UnsolvedMath record UM-20001066 (v1.8.0).
`IsDirectedPath` follows the OpenConjectures entry `DirectedPathTwiceMinimumOutdegree`.
`internalVertices` and `HasInternallyDisjointPaths` follow `AIMCombinatoricsProblem191`.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.HamidouneReverseConnectivityAIMCombinatoricsProblem191Wanted

/-- **Directed paths.** A directed path in a digraph $D$ is a finite, possibly empty, sequence of
vertices of $D$ with no vertex repeated in which each vertex is joined to the next by an arc of
$D$. -/
def IsDirectedPath {V : Type} (D : Digraph V) (p : List V) : Prop :=
  p.Nodup ∧ p.IsChain D.Adj

/-- The internal vertices of a path given as a vertex list (all but the first and the last). -/
def internalVertices {V : Type} (p : List V) : List V :=
  p.tail.dropLast

/-- **Internally disjoint directed paths.** Let $D$ be a digraph, $r$ a natural number and $y$, $x$
vertices of $D$. We write $\kappa(y, x) \ge r$ when there are $r$ pairwise distinct directed paths
in $D$ from $y$ to $x$, no two of which share an internal vertex. Here a directed path from $y$ to
$x$ is a sequence of distinct vertices starting at $y$ and ending at $x$ in which each vertex is
joined to the next by an arc of $D$, and its internal vertices are all its vertices except the
first and the last. -/
def HasInternallyDisjointPaths {V : Type} (D : Digraph V) (r : ℕ) (y x : V) : Prop :=
  ∃ P : Fin r → List V,
    (∀ i, IsDirectedPath D (P i) ∧ (P i).head? = some y ∧ (P i).getLast? = some x) ∧
      ∀ i j, i ≠ j → P i ≠ P j ∧ ∀ v ∈ internalVertices (P i), v ∉ internalVertices (P j)

/-- **Hamidoune's reverse-connectivity conjecture for some $r \ge 3$.** The statement that there
is a natural number $r \ge 3$ such that every digraph $D$ without loops or parallel arcs on a
finite nonempty vertex set, in which every vertex has at least $r$ out-neighbours and at least
$r$ in-neighbours, has an arc $(x, y)$ from $x$ to $y$ with $\kappa(y, x) \ge r$, that is, with
$r$ pairwise distinct directed paths from $y$ to $x$, no two of which share an internal vertex.
Here a directed path is a sequence of distinct vertices in which each vertex is joined to the
next by an arc, and its internal vertices are all its vertices except the first and the last. -/
def hamidouneSomeRAtLeastThree : Prop :=
  ∃ r : ℕ, 3 ≤ r ∧ ∀ (V : Type) [Finite V] [Nonempty V] (D : Digraph V), (∀ v : V, ¬ D.Adj v v) →
    (∀ v : V, r ≤ {w | D.Adj v w}.ncard) → (∀ v : V, r ≤ {u | D.Adj u v}.ncard) →
      ∃ x y : V, D.Adj x y ∧ HasInternallyDisjointPaths D r y x

/- A region around the tail of an arc excludes every head. Every arc entering the region
from outside it comes from a guard, and neither endpoint of the original arc is a guard. -/
private structure Cut {V : Type} (D : Digraph V) (x : V) where
  region : Set V
  guards : Set V
  small : guards.ncard ≤ 2
  inside : x ∈ region
  unguarded : x ∉ guards
  outside : ∀ y, D.Adj x y → y ∉ region ∧ y ∉ guards
  enter : ∀ u v, D.Adj u v → u ∉ region → v ∈ region → u ∈ guards

private def sourceCut {V : Type} {D : Digraph V} (o : V) (h : ∀ v, ¬ D.Adj v o) :
    Cut D o where
  region := {o}
  guards := ∅
  small := by simp
  inside := rfl
  unguarded := by simp
  outside := by rintro y hy; exact ⟨fun e ↦ h o (e ▸ hy), by simp⟩
  enter := by rintro u v huv _ rfl; exact (h u huv).elim

/- The root has no incoming arcs and at least r outgoing arcs. Other regions exclude the
root, so the cuts can be reused when copies of the digraph are joined at their roots. -/
private structure Rooted (r k : ℕ) where
  V : Type
  [finite : Finite V]
  D : Digraph V
  root : V
  source : ∀ x, ¬ D.Adj x root
  degreeRoot : r ≤ {y | D.Adj root y}.ncard
  degree : ∀ x, k ≤ {y | D.Adj x y}.ncard
  cut : ∀ x, Cut D x
  excludesRoot : ∀ x, x ≠ root → root ∉ (cut x).region

attribute [local instance] Rooted.finite

private theorem degree_of_embedding {V W : Type} [Finite W] {s : Set V} {t : Set W}
    (f : V → W) (hf : Function.Injective f) (h : ∀ v ∈ s, f v ∈ t) : s.ncard ≤ t.ncard :=
  Set.ncard_le_ncard_of_injOn f h hf.injOn

private def star (r : ℕ) : Digraph (Option (Fin r)) where
  Adj x y := x = none ∧ y ≠ none

private def starCut {r : ℕ} : (x : Option (Fin r)) → Cut (star r) x
  | none => sourceCut none (by simp [star])
  | some i =>
    { region := {some i}
      guards := {none}
      small := by simp
      inside := rfl
      unguarded := by simp
      outside := by simp [star]
      enter := fun _ _ huv _ _ ↦ huv.1 }

private def base (r : ℕ) : Rooted r 0 where
  V := Option (Fin r)
  D := star r
  root := none
  source := by simp [star]
  degreeRoot := by
    simpa using degree_of_embedding (s := Set.univ) (t := {y | (star r).Adj none y})
      some (Option.some_injective _) (by simp [star])
  degree _ := Nat.zero_le _
  cut := starCut
  excludesRoot := by rintro (_ | i) h <;> simp_all [starCut]

private abbrev Index (r : ℕ) := Fin r × Bool

private def partner {r : ℕ} (i : Index r) : Index r := (i.1, !i.2)

private theorem partner_ne {r : ℕ} (i : Index r) : partner i ≠ i := by
  rcases i with ⟨i, _ | _⟩ <;> simp [partner]

private theorem partner_partner {r : ℕ} (i : Index r) : partner (partner i) = i := by
  simp [partner]

private abbrev CopyVertex (r : ℕ) (V : Type) := Option (Index r × V)

private def copy {r : ℕ} {V : Type} (i : Index r) (v : V) : CopyVertex r V := some (i, v)

private theorem copy_injective {r : ℕ} {V : Type} (i : Index r) :
    Function.Injective (copy (V := V) i) := by
  intro u v h
  simpa [copy] using h

/- A new root enters each copy at its old root. Each nonroot vertex gets one new
out-neighbour, the root of the paired copy. -/
private def extend {r k : ℕ} (G : Rooted r k) : Digraph (CopyVertex r G.V) where
  Adj
    | _, none => False
    | none, some (_, w) => w = G.root
    | some (i, v), some (j, w) =>
      (i = j ∧ G.D.Adj v w) ∨ (partner i = j ∧ v ≠ G.root ∧ w = G.root)

private theorem copy_arc {r k : ℕ} (G : Rooted r k) (i : Index r) {u v : G.V}
    (h : G.D.Adj u v) : (extend G).Adj (copy i u) (copy i v) :=
  Or.inl ⟨rfl, h⟩

private theorem copy_degree {r k : ℕ} (G : Rooted r k) (i : Index r) (x : G.V) :
    {y | G.D.Adj x y}.ncard ≤ {y | (extend G).Adj (copy i x) y}.ncard :=
  degree_of_embedding (copy i) (copy_injective i) (fun _ h ↦ copy_arc G i h)

private theorem extend_degree {r k : ℕ} (G : Rooted r k) (hk : k < r) (i : Index r) (x : G.V) :
    k + 1 ≤ {y | (extend G).Adj (copy i x) y}.ncard := by
  classical
  by_cases hx : x = G.root
  · subst x
    exact hk.trans_le (G.degreeRoot.trans (copy_degree G i G.root))
  let old := copy i '' {v | G.D.Adj x v}
  have hfresh : copy (partner i) G.root ∉ old := by
    simp [old, copy, Set.mem_image, (partner_ne i).symm]
  calc
    k + 1 ≤ old.ncard + 1 := by
      simpa [old, Set.ncard_image_of_injective _ (copy_injective i)] using
        Nat.succ_le_succ (G.degree x)
    _ = (insert (copy (partner i) G.root) old).ncard := (Set.ncard_insert_of_notMem hfresh).symm
    _ ≤ _ := by
      refine Set.ncard_le_ncard ?_
      rintro y (rfl | ⟨v, hv, rfl⟩)
      · exact Or.inr ⟨rfl, hx, rfl⟩
      · exact copy_arc G i hv

private def innerCut {r k : ℕ} (G : Rooted r k) (i : Index r) (x : G.V) (hx : x ≠ G.root) :
    Cut (extend G) (copy i x) where
  region := copy i '' (G.cut x).region
  guards := copy i '' (G.cut x).guards
  small := by rw [Set.ncard_image_of_injective _ (copy_injective i)]; exact (G.cut x).small
  inside := Set.mem_image_of_mem _ (G.cut x).inside
  unguarded := by simpa [copy] using (G.cut x).unguarded
  outside := by
    rintro (_ | ⟨j, y⟩) h
    · exact h.elim
    rcases h with ⟨rfl, hy⟩ | ⟨rfl, -, rfl⟩
    · simpa [copy] using (G.cut x).outside y hy
    · simp [copy, (partner_ne i).symm]
  enter := by
    rintro u _ h hu ⟨v, hv, rfl⟩
    obtain _ | ⟨j, w⟩ := u
    · exact (G.excludesRoot x hx (h ▸ hv)).elim
    rcases h with ⟨rfl, hw⟩ | ⟨-, -, he⟩
    · apply Set.mem_image_of_mem
      exact (G.cut x).enter w v hw (fun hw' ↦ hu (Set.mem_image_of_mem _ hw')) hv
    · exact (G.excludesRoot x hx (he ▸ hv)).elim

/- To reach the old root in copy i, include the nonroot vertices of its partner in the
region. Entry is then possible only from the new root or from the partner's old root. -/
private def rootRegion {r k : ℕ} (G : Rooted r k) (i : Index r) : Set (CopyVertex r G.V) :=
  {z | match z with
    | none => False
    | some (j, w) => (j = i ∧ w = G.root) ∨ (j = partner i ∧ w ≠ G.root)}

private def outerCut {r k : ℕ} (G : Rooted r k) (i : Index r) :
    Cut (extend G) (copy i G.root) where
  region := rootRegion G i
  guards := {none, copy (partner i) G.root}
  small := by simp [copy]
  inside := Or.inl ⟨rfl, rfl⟩
  unguarded := by simp [copy, (partner_ne i).symm]
  outside := by
    rintro (_ | ⟨j, w⟩) h
    · exact h.elim
    rcases h with ⟨rfl, hw⟩ | ⟨-, hf, -⟩
    · have hne : w ≠ G.root := fun e ↦ G.source G.root (e ▸ hw)
      constructor
      · change ¬ ((i = i ∧ w = G.root) ∨ (i = partner i ∧ w ≠ G.root))
        simp [hne, (partner_ne i).symm]
      · simp [copy, (partner_ne i).symm]
    · exact (hf rfl).elim
  enter := by
    rintro (_ | ⟨j, w⟩) (_ | ⟨l, v⟩) h hu hv
    · exact h.elim
    · simp
    · exact h.elim
    change ¬ ((j = i ∧ w = G.root) ∨ (j = partner i ∧ w ≠ G.root)) at hu
    change (l = i ∧ v = G.root) ∨ (l = partner i ∧ v ≠ G.root) at hv
    change (j = l ∧ G.D.Adj w v) ∨ (partner j = l ∧ w ≠ G.root ∧ v = G.root) at h
    have := G.source w
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, copy, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq, false_or]
    grind [partner_partner]

private noncomputable def step {r k : ℕ} (G : Rooted r k) (hk : k < r) : Rooted r (k + 1) := by
  classical
  have rootDegree : r ≤ {y | (extend G).Adj none y}.ncard := by
    let f (j : Fin r) := copy (j, false) G.root
    have hf : Function.Injective f := by intro j l h; simpa [f, copy] using h
    simpa using degree_of_embedding (s := Set.univ) (t := {y | (extend G).Adj none y})
      f hf (fun _ _ ↦ rfl)
  exact {
    V := CopyVertex r G.V
    D := extend G
    root := none
    source _ := id
    degreeRoot := rootDegree
    degree
      | none => hk.trans_le rootDegree
      | some (i, x) => extend_degree G hk i x
    cut
      | none => sourceCut none (fun _ ↦ id)
      | some (i, x) => if h : x = G.root then h ▸ outerCut G i else innerCut G i x h
    excludesRoot := by
      rintro (_ | ⟨i, x⟩) h
      · exact (h rfl).elim
      dsimp only
      by_cases he : x = G.root
      · subst x; simp [outerCut, rootRegion]
      · simp [he, innerCut, copy] }

private noncomputable def family (r : ℕ) : (k : ℕ) → k ≤ r → Rooted r k
  | 0, _ => base r
  | k + 1, hk => step (family r k (by omega)) hk

/- A path crossing from outside S to inside S meets K if each entering arc meets K. -/
private theorem chain_meets {V : Type} {D : Digraph V} {S K : Set V}
    (cross : ∀ u v, D.Adj u v → u ∉ S → v ∈ S → u ∈ K ∨ v ∈ K)
    {a b : V} {l : List V} (h : (a :: l).IsChain D.Adj) (ha : a ∉ S)
    (hb : b ∈ S) (hl : (a :: l).getLast? = some b) : ∃ v ∈ a :: l, v ∈ K := by
  induction l generalizing a with
  | nil => simp_all
  | cons c l ih =>
    obtain ⟨hac, hc⟩ := List.isChain_cons_cons.mp h
    by_cases hs : c ∈ S
    · rcases cross a c hac ha hs with h | h
      · exact ⟨a, by simp, h⟩
      · exact ⟨c, by simp, h⟩
    · obtain ⟨v, hv, hK⟩ := ih hc hs hl
      exact ⟨v, List.mem_cons_of_mem _ hv, hK⟩

private theorem paths_le_guards {V : Type} [Finite V] {D : Digraph V} {n : ℕ} {a b : V}
    (h : HasInternallyDisjointPaths D n a b) (S K : Set V)
    (ha : a ∉ S) (hb : b ∈ S) (hKa : a ∉ K) (hKb : b ∉ K)
    (cross : ∀ u v, D.Adj u v → u ∉ S → v ∈ S → u ∈ K ∨ v ∈ K) : n ≤ K.ncard := by
  classical
  obtain ⟨P, hP, disj⟩ := h
  have meets (i : Fin n) : ∃ v ∈ internalVertices (P i), v ∈ K := by
    obtain ⟨⟨_, hc⟩, hh, hl⟩ := hP i
    cases he : P i with
    | nil => simp [he] at hh
    | cons c l =>
      simp only [he, List.head?_cons, Option.some.injEq] at hh
      subst c
      rw [he] at hc hl
      obtain ⟨v, hv, hK⟩ := chain_meets cross hc ha hb hl
      have hva : v ≠ a := fun e ↦ hKa (e ▸ hK)
      have hvb : v ≠ b := fun e ↦ hKb (e ▸ hK)
      have hm : v ∈ l := (List.mem_cons.mp hv).resolve_left hva
      obtain _ | ⟨w, ws⟩ := l
      · simp at hm
      · refine ⟨v, List.mem_dropLast_of_mem_of_ne_getLast? hm ?_, hK⟩
        change (some v : Option V) ≠ (w :: ws).getLast?
        change (w :: ws).getLast? = some b at hl
        simpa [hl] using hvb
  choose v hv hK using meets
  have inj : Function.Injective v := by
    intro i j he
    by_contra hij
    exact (disj i j hij).2 (v i) (hv i) (he ▸ hv j)
  simpa using degree_of_embedding (s := Set.univ) (t := K) v inj (fun i _ ↦ hK i)

/- All cross arcs go from the reversed copy (right) to the original (left). -/
private def double {V : Type} (D : Digraph V) : Digraph (V ⊕ V) where
  Adj
    | .inl x, .inl y => D.Adj x y
    | .inr x, .inr y => D.Adj y x
    | .inr _, .inl _ => True
    | .inl _, .inr _ => False

private theorem double_bound {V : Type} [Finite V] {D : Digraph V} (cuts : ∀ x, Cut D x)
    {x y : V ⊕ V} (h : (double D).Adj x y) {n : ℕ}
    (hp : HasInternallyDisjointPaths (double D) n y x) : n ≤ 2 := by
  cases x with
  | inl x =>
    cases y with
    | inr y => exact h.elim
    | inl y =>
      let C := cuts x
      obtain ⟨hyS, hyK⟩ := C.outside y h
      let S : Set (V ⊕ V) := {z | z.elim (· ∈ C.region) (fun _ ↦ True)}
      have bound := paths_le_guards hp S (Sum.inl '' C.guards) hyS C.inside
        (by simpa using hyK) (by simpa using C.unguarded) (by
          rintro (u | u) (v | v) huv hu hv
          · exact Or.inl (Set.mem_image_of_mem _ (C.enter u v huv hu hv))
          · exact huv.elim
          all_goals exact (hu trivial).elim)
      rw [Set.ncard_image_of_injective _ Sum.inl_injective] at bound
      exact bound.trans C.small
  | inr x =>
    cases y with
    | inl y =>
      let S : Set (V ⊕ V) := {z | z.isRight}
      have bound := paths_le_guards hp S ∅ (by simp [S]) rfl (by simp) (by simp) (by
        rintro (u | u) (v | v) huv hu hv
        · exact Bool.noConfusion hv
        · exact huv.elim
        all_goals exact (hu rfl).elim)
      exact bound.trans (by simp)
    | inr y =>
      let C := cuts y
      obtain ⟨hxS, hxK⟩ := C.outside x h
      let S : Set (V ⊕ V) := {z | z.elim (fun _ ↦ False) (· ∉ C.region)}
      have bound := paths_le_guards hp S (Sum.inr '' C.guards)
        (fun hy ↦ hy C.inside) hxS (by simpa using C.unguarded) (by simpa using hxK) (by
          rintro (u | u) (v | v) huv hu hv
          · exact hv.elim
          · exact huv.elim
          · exact hv.elim
          · have huS : u ∈ C.region := Classical.byContradiction hu
            exact Or.inr (Set.mem_image_of_mem _ (C.enter v u huv hv huS)))
      rw [Set.ncard_image_of_injective _ Sum.inr_injective] at bound
      exact bound.trans C.small

private theorem double_degrees {r : ℕ} (G : Rooted r r) (x : G.V ⊕ G.V) :
    r ≤ {y | (double G.D).Adj x y}.ncard ∧ r ≤ {y | (double G.D).Adj y x}.ncard := by
  cases x with
  | inl x =>
    exact ⟨(G.degree x).trans (degree_of_embedding Sum.inl Sum.inl_injective (fun _ h ↦ h)),
      (G.degree x).trans (degree_of_embedding Sum.inr Sum.inr_injective (fun _ _ ↦ trivial))⟩
  | inr x =>
    exact ⟨(G.degree x).trans (degree_of_embedding Sum.inl Sum.inl_injective (fun _ _ ↦ trivial)),
      (G.degree x).trans (degree_of_embedding Sum.inr Sum.inr_injective (fun _ h ↦ h))⟩

/-- **Hamidoune's reverse-connectivity conjecture fails for every $r \ge 3$.** For no natural
number $r \ge 3$ does the following hold: every digraph $D$ without loops or parallel arcs on a
finite nonempty vertex set, in which every vertex has at least $r$ out-neighbours and at least
$r$ in-neighbours, has an arc $(x, y)$ from $x$ to $y$ with $\kappa(y, x) \ge r$, that is, with
$r$ pairwise distinct directed paths from $y$ to $x$, no two of which share an internal vertex.
Here a directed path is a sequence of distinct vertices in which each vertex is joined to the
next by an arc, and its internal vertices are all its vertices except the first and the last.

Thomassen constructed, for every positive integer $r$, a digraph without digons with minimum
out-degree and minimum in-degree at least $r$ in which no arc $(x, y)$ has $\kappa(y, x) \ge 3$;
the report notes after Conjecture 6.21 that this is a counterexample for all $r \ge 3$.

Source: B. D. Sullivan, A Summary of Problems and Results related to
the Caccetta-Haggkvist Conjecture, arXiv:math/0605646, Conjecture 6.21; resolution: C. Thomassen,
Even cycles in directed graphs, European J. Combin. 6 (1985) 85-89, as stated in the report's
Theorem 5.2 (part ii) and the note after Conjecture 6.21,
https://doi.org/10.1016/S0195-6698(85)80025-1.
-/
theorem hamidouneSomeRAtLeastThree_refuted : ¬ hamidouneSomeRAtLeastThree := by
  rintro ⟨r, hr, universal⟩
  let G := family r r le_rfl
  let : Nonempty (G.V ⊕ G.V) := ⟨Sum.inl G.root⟩
  have loopless (v : G.V) (h : G.D.Adj v v) : False :=
    ((G.cut v).outside v h).1 (G.cut v).inside
  obtain ⟨x, y, hxy, paths⟩ := universal _ (double G.D)
    (by rintro (v | v) <;> exact loopless v)
    (fun x ↦ (double_degrees G x).1) (fun x ↦ (double_degrees G x).2)
  have := double_bound G.cut hxy paths
  omega

end MathlibExt.Combinatorics.HamidouneReverseConnectivityAIMCombinatoricsProblem191Wanted
