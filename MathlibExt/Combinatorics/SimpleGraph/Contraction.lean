/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.VertexConnectivity

/-!
# Contracting the complement of a vertex set

This file contracts every vertex outside a set to one new vertex. The construction is used by
the induction in Fleischner's theorem.
-/

@[expose] public section

namespace SimpleGraph

/-- A reachable pair remains reachable after mapping a graph by an arbitrary function, even when
some edges collapse to vertices. -/
private theorem Reachable.map_function {V W : Type*} {G : SimpleGraph V} {u v : V}
    (h : G.Reachable u v) (f : V → W) :
    (G.map f).Reachable (f u) (f v) := by
  rw [reachable_iff_reflTransGen] at h ⊢
  apply h.lift' f
  intro a b hab
  change Relation.ReflTransGen (G.map f).Adj (f a) (f b)
  by_cases heq : f a = f b
  · rw [heq]
  · exact Relation.ReflTransGen.single ⟨heq, a, b, hab, rfl, rfl⟩

/-- A surjective vertex map that sends every edge to an edge or collapses it to one vertex sends
a connected graph to a connected graph. -/
private theorem Connected.of_surjective_map_or_eq {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (hG : G.Connected) (f : V → W) (hf : Function.Surjective f)
    (hadj : ∀ ⦃a b⦄, G.Adj a b → f a = f b ∨ H.Adj (f a) (f b)) : H.Connected := by
  refine { preconnected := ?_, nonempty := Nonempty.map f hG.nonempty }
  intro a b
  obtain ⟨u, rfl⟩ := hf a
  obtain ⟨v, rfl⟩ := hf b
  rw [reachable_iff_reflTransGen] at ⊢
  have huv := hG u v
  rw [reachable_iff_reflTransGen] at huv
  apply huv.lift' f
  intro y z hyz
  change Relation.ReflTransGen H.Adj (f y) (f z)
  rcases hadj hyz with heq | h
  · rw [heq]
  · exact Relation.ReflTransGen.single h

/-- **Collapsing the complement of a set.** For a set $D \subseteq V$, the collapse map sends $V$
to $D$ together with one new vertex, the contraction vertex: each $v \in D$ is sent to itself,
and each $v \notin D$ is sent to the contraction vertex. -/
public noncomputable def collapseOutside {V : Type*} (D : Set V) : V → Option D := by
  classical
  exact fun v ↦ if hv : v ∈ D then some ⟨v, hv⟩ else none

/-- **The collapse map fixes the retained set.** For a set $D \subseteq V$, the collapse map from
$V$ to $D$ together with the contraction vertex sends each $v \in D$ to $v$ itself. -/
@[simp]
public theorem collapseOutside_of_mem {V : Type*} (D : Set V) {v : V} (hv : v ∈ D) :
    collapseOutside D v = some ⟨v, hv⟩ := by
  classical
  simp [collapseOutside, hv]

/-- **The collapse map sends the complement to the contraction vertex.** For a set
$D \subseteq V$, the collapse map from $V$ to $D$ together with the contraction vertex sends each
vertex $v \notin D$ to the contraction vertex. -/
@[simp]
public theorem collapseOutside_of_notMem {V : Type*} (D : Set V) {v : V} (hv : v ∉ D) :
    collapseOutside D v = none := by
  classical
  simp [collapseOutside, hv]

/-- **Preimages of retained vertices under the collapse map.** For a set $D \subseteq V$, a vertex
$v \in V$ and an element $a \in D$, the collapse map from $V$ to $D$ together with the
contraction vertex sends $v$ to $a$ if and only if $v = a$. -/
@[simp]
public theorem collapseOutside_eq_some_iff {V : Type*} (D : Set V) (v : V) (a : D) :
    collapseOutside D v = some a ↔ v = a := by
  classical
  by_cases hv : v ∈ D
  · rw [collapseOutside_of_mem D hv]
    simp only [Option.some.injEq]
    constructor
    · exact fun h ↦ congrArg Subtype.val h
    · intro h
      apply Subtype.ext
      exact h
  · rw [collapseOutside_of_notMem D hv]
    constructor
    · intro h
      contradiction
    · intro h
      exfalso
      apply hv
      rw [h]
      exact a.property

/-- **Preimage of the contraction vertex under the collapse map.** For a set $D \subseteq V$ and a
vertex $v \in V$, the collapse map from $V$ to $D$ together with the contraction vertex sends $v$
to the contraction vertex if and only if $v \notin D$. -/
@[simp]
public theorem collapseOutside_eq_none_iff {V : Type*} (D : Set V) (v : V) :
    collapseOutside D v = none ↔ v ∉ D := by
  classical
  by_cases hv : v ∈ D
  · rw [collapseOutside_of_mem D hv]
    simp [hv]
  · rw [collapseOutside_of_notMem D hv]
    simp [hv]

/-- **The collapse map is surjective.** For a set $D \subseteq V$ whose complement $V \setminus D$
is nonempty, the collapse map from $V$ to $D$ together with the contraction vertex is
surjective. -/
public theorem collapseOutside_surjective {V : Type*} {D : Set V} (hD : Dᶜ.Nonempty) :
    Function.Surjective (collapseOutside D) := by
  obtain ⟨w, hw⟩ := hD
  intro z
  cases z with
  | none =>
      exact ⟨w, collapseOutside_of_notMem D hw⟩
  | some a =>
      exact ⟨a, collapseOutside_of_mem D a.property⟩

/-- **Contracting the complement of a vertex set.** Let $G$ be a simple graph on a vertex set $V$
and let $D \subseteq V$. Contracting the complement of $D$ to a single vertex gives the simple
graph whose vertices are the elements of $D$ together with one new vertex $\ast$, in which two
vertices $a, b \in D$ are adjacent exactly when they are adjacent in $G$, and a vertex $a \in D$
is adjacent to $\ast$ exactly when $a$ has a neighbour in $G$ outside $D$. The new vertex $\ast$
is present even when $D = V$, and is then isolated. -/
public noncomputable def contractOutside {V : Type*} (G : SimpleGraph V) (D : Set V) :
    SimpleGraph (Option D) :=
  G.map (collapseOutside D)

/-- **Contraction preserves adjacency among retained vertices.** Let $G$ be a graph on $V$, let
$D \subseteq V$, and contract $V \setminus D$ to a single vertex. Two vertices $a, b \in D$ are
adjacent in the contracted graph if and only if they are adjacent in $G$. -/
@[simp]
public theorem contractOutside_adj_some {V : Type*} (G : SimpleGraph V) (D : Set V)
    (a b : D) :
    (G.contractOutside D).Adj (some a) (some b) ↔ G.Adj a b := by
  classical
  rw [contractOutside, map_adj']
  constructor
  · rintro ⟨_, u, v, huv, hu, hv⟩
    rw [collapseOutside_eq_some_iff] at hu hv
    simpa [hu, hv] using huv
  · intro hab
    refine ⟨?_, a, b, hab, ?_, ?_⟩
    · intro h
      exact G.ne_of_adj hab (congrArg Subtype.val (Option.some.inj h))
    · exact collapseOutside_of_mem D a.property
    · exact collapseOutside_of_mem D b.property

/-- **Neighbors of the contraction vertex.** Let $G$ be a graph on $V$, let $D \subseteq V$, and
contract $V \setminus D$ to a single vertex. A vertex $a \in D$ is adjacent to the contraction
vertex in the contracted graph if and only if $a$ is adjacent in $G$ to some vertex
$v \notin D$. -/
@[simp]
public theorem contractOutside_adj_none {V : Type*} (G : SimpleGraph V) (D : Set V)
    (a : D) :
    (G.contractOutside D).Adj (some a) none ↔ ∃ v ∉ D, G.Adj a v := by
  classical
  rw [contractOutside, map_adj']
  constructor
  · rintro ⟨_, u, v, huv, hu, hv⟩
    rw [collapseOutside_eq_some_iff] at hu
    rw [collapseOutside_eq_none_iff] at hv
    exact ⟨v, hv, hu ▸ huv⟩
  · rintro ⟨v, hv, hav⟩
    refine ⟨Option.some_ne_none a, a, v, hav, ?_, ?_⟩
    · exact collapseOutside_of_mem D a.property
    · exact collapseOutside_of_notMem D hv

/-- Contracting a nonempty complement preserves connectedness. -/
private theorem Connected.contractOutside {V : Type*} {G : SimpleGraph V} {D : Set V}
    (hG : G.Connected) (hD : Dᶜ.Nonempty) : (G.contractOutside D).Connected := by
  let f := collapseOutside D
  have hf : Function.Surjective f := collapseOutside_surjective hD
  refine { preconnected := ?_, nonempty := ⟨none⟩ }
  intro a b
  obtain ⟨u, rfl⟩ := hf a
  obtain ⟨v, rfl⟩ := hf b
  exact (hG u v).map_function f

private noncomputable def induceContractOutsideSomeHom {V : Type*}
    (G : SimpleGraph V) (D : Set V) :
    G.induce D →g
      (G.contractOutside D).induce
        (↑({none} : Finset (Option D)) : Set (Option D))ᶜ where
  toFun a := ⟨some a, by simp⟩
  map_rel' := by
    intro a b hab
    exact contractOutside_adj_some G D a b |>.mpr (induce_adj.mp hab)

/-- Deleting the contraction vertex leaves the original induced graph on the retained set. -/
private theorem Connected.contractOutside_delete_none {V : Type*} {G : SimpleGraph V}
    {D : Set V} (hD : (G.induce D).Connected) :
    ((G.contractOutside D).induce
      (↑({none} : Finset (Option D)) : Set (Option D))ᶜ).Connected := by
  classical
  apply hD.map (induceContractOutsideSomeHom G D)
  rintro ⟨z, hz⟩
  cases z with
  | none => simp at hz
  | some a => exact ⟨a, rfl⟩

/-- If deleting one vertex from `G` leaves it connected, then deleting a surviving vertex from
the contraction also leaves it connected. -/
private theorem IsVertexConnected.contractOutside_delete_some {V : Type*} [Fintype V]
    {G : SimpleGraph V} {D : Set V} (hG : G.IsVertexConnected 2) (hD : Dᶜ.Nonempty)
    (d : D) :
    ((G.contractOutside D).induce
      (↑({some d} : Finset (Option D)) : Set (Option D))ᶜ).Connected := by
  classical
  let S : Set V := (↑({(d : V)} : Finset V) : Set V)ᶜ
  let T : Set (Option D) := (↑({some d} : Finset (Option D)) : Set (Option D))ᶜ
  let f : S → T := fun v ↦ ⟨collapseOutside D v, by
    have hne : collapseOutside D v ≠ some d := by
      intro h
      have hvd := (collapseOutside_eq_some_iff D v d).mp h
      exact v.property (by simpa [S] using hvd)
    simpa [T] using hne⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    cases z with
    | none =>
        obtain ⟨w, hw⟩ := hD
        have hwd : w ≠ d := fun h ↦ hw (h ▸ d.property)
        let w' : S := ⟨w, by simpa [S] using hwd⟩
        refine ⟨w', Subtype.ext ?_⟩
        exact collapseOutside_of_notMem D hw
    | some a =>
        have had : a ≠ d := by simpa [T] using hz
        have haval : (a : V) ≠ d := fun h ↦ had (Subtype.ext h)
        let a' : S := ⟨a, by simpa [S] using haval⟩
        refine ⟨a', Subtype.ext ?_⟩
        exact collapseOutside_of_mem D a.property
  apply (hG.connected_compl_singleton (by omega) d).of_surjective_map_or_eq f hf
  intro a b hab
  by_cases heq : collapseOutside D a = collapseOutside D b
  · exact Or.inl (Subtype.ext heq)
  · right
    exact map_adj_apply' (induce_adj.mp hab) heq

/-- **Contracting the complement preserves 2-connectivity.** Let $G$ be a 2-vertex-connected
graph on a finite vertex set $V$, and let $D \subseteq V$ be a set with at least two elements
that induces a connected subgraph of $G$ and whose complement $V \setminus D$ is nonempty. Then
the graph obtained from $G$ by contracting $V \setminus D$ to a single vertex is
2-vertex-connected. -/
public theorem IsVertexConnected.contractOutside {V : Type*} [Fintype V]
    {G : SimpleGraph V} {D : Set V} [Fintype D] (hG : G.IsVertexConnected 2)
    (hDcard : 1 < Fintype.card D) (hDconn : (G.induce D).Connected)
    (hDout : Dᶜ.Nonempty) : (G.contractOutside D).IsVertexConnected 2 := by
  classical
  rw [isVertexConnected_two_iff]
  refine ⟨?_, hG.connected (by omega) |>.contractOutside hDout, ?_⟩
  · simp only [Fintype.card_option]
    omega
  · intro z
    cases z with
    | none => exact hDconn.contractOutside_delete_none
    | some d => exact hG.contractOutside_delete_some hDout d

/-- **Cardinality bound for contracting the complement.** Let $V$ be a finite set and
$D \subseteq V$. If the complement $V \setminus D$ has at least two elements, then $D$ together
with one new vertex has fewer elements than $V$, that is, $|D| + 1 < |V|$.

This counts the vertices of the graph obtained by contracting $V \setminus D$ to a single
vertex. -/
public theorem card_contractOutside_lt {V : Type*} [Fintype V] (D : Set V)
    [Fintype D] [Fintype ↥(Dᶜ : Set V)] (hD : 2 ≤ Fintype.card ↥(Dᶜ : Set V)) :
    Fintype.card (Option D) < Fintype.card V := by
  have hcomp := Fintype.card_compl_set D
  have hle : Fintype.card D ≤ Fintype.card V :=
    Fintype.card_le_of_injective (fun x : D ↦ (x : V)) Subtype.val_injective
  simp only [Fintype.card_option]
  omega

end SimpleGraph
