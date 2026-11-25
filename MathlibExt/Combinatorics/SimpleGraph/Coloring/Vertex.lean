/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Set.Card

@[expose] public section

variable {V α : Type*} {G : SimpleGraph V} {n : ℕ}

namespace SimpleGraph

@[inherit_doc] scoped notation "χ(" G ")" => chromaticNumber G

lemma lt_chromaticNumber_iff_not_colorable : n < G.chromaticNumber ↔ ¬ G.Colorable n := by
  rw [← chromaticNumber_le_iff_colorable, not_le]

lemma le_chromaticNumber_iff_not_colorable (hn : n ≠ 0) :
    n ≤ G.chromaticNumber ↔ ¬ G.Colorable (n - 1) := by
  let n + 1 := n; simp [ENat.add_one_le_iff, lt_chromaticNumber_iff_not_colorable]

lemma card_div_indepNum_le_chromaticNumber : ⌈(Nat.card V / α(G) : ℚ≥0)⌉₊ ≤ G.chromaticNumber := by
  cases finite_or_infinite V
  swap; · simp
  cases nonempty_fintype V
  simp only [Nat.card_eq_fintype_card, le_chromaticNumber_iff_coloring, Nat.ceil_le]
  refine fun m c ↦ div_le_of_le_mul₀ (by simp) (by simp) ?_
  norm_cast
  rw [← mul_one (Fintype.card V), ← Fintype.card_fin m]
  refine Finset.card_mul_le_card_mul (c · = ·)
    (by simp [Finset.bipartiteAbove, Finset.filter_nonempty_iff])
    fun b _ ↦ IsIndepSet.card_le_indepNum ?_
  simpa [IsIndepSet, Set.Pairwise, Coloring.colorClass] using
    fun x hx y hy _ ↦ c.not_adj_of_mem_colorClass hx hy

variable (G) in
/-- **Critical edge sets.** Let $G$ be a graph and $S$ a set of unordered pairs of its
vertices. Then $S$ is critical for $G$ if deleting the edges of $G$ that lie in $S$ strictly
lowers the chromatic number, as an element of $\mathbb{N} \cup \{\infty\}$. -/
def IsCriticalEdges (edges : Set (Sym2 V)) : Prop :=
  (G.deleteEdges edges).chromaticNumber < G.chromaticNumber

variable (G) in
/-- **Critical edge.** For a graph $G$ and an unordered pair $e$ of vertices, $e$ is a critical
edge of $G$ if removing $e$ from the edge set of $G$ strictly lowers the chromatic number of $G$,
taken in $\mathbb{N} \cup \{\infty\}$.

Only edges of $G$ can be critical. -/
def IsCriticalEdge (e : Sym2 V) : Prop := G.IsCriticalEdges ({e} : Set (Sym2 V))

/--
**Critical vertex sets of a subgraph.** Let $G'$ be a subgraph of a graph $G$. A set $S$ of
vertices is critical for $G'$ if deleting the vertices in $S$ from $G'$ strictly lowers the
chromatic number of $G'$, viewed as a graph on its own vertex set, with chromatic numbers taken
in $\mathbb{N} \cup \{\infty\}$.
-/
def Subgraph.IsCriticalVerts (verts : Set V) (G' : G.Subgraph) : Prop :=
  (G'.deleteVerts verts).coe.chromaticNumber < G'.coe.chromaticNumber

/--
**Critical vertices of a subgraph.** Let $G'$ be a subgraph of a graph $G$. A vertex $v$ is
critical for $G'$ if $\{v\}$ is a critical vertex set of $G'$, that is, deleting $v$ from $G'$
strictly lowers the chromatic number of $G'$, viewed as a graph on its own vertex set, with
chromatic numbers taken in $\mathbb{N} \cup \{\infty\}$.
-/
def Subgraph.IsCriticalVertex (v : V) (G' : G.Subgraph) : Prop := G'.IsCriticalVerts {v}

variable (G)

/--
**Vertex-critical graphs.** Let $k$ be a natural number. A graph $G$ is $k$-critical (or
vertex-critical) if its chromatic number equals $k$ and every vertex $v$ of $G$ is critical,
that is, deleting $v$ from $G$ strictly lowers the chromatic number.
-/
def IsCritical (k : ℕ) : Prop := G.chromaticNumber = k ∧ ∀ v, (⊤ : G.Subgraph).IsCriticalVertex v

theorem not_isCritical_of_fintype_lt [Fintype V] (k : ℕ) (hk : Fintype.card V < k) :
   ¬G.IsCritical k := by
  simp only [IsCritical, not_and, not_forall]
  intro h
  have := h ▸ SimpleGraph.chromaticNumber_le_iff_colorable.2 G.colorable_of_fintype
  simp at this
  grind

open SimpleGraph

set_option backward.isDefEq.respectTransparency false in
theorem colorable_iff_induce_eq_bot (G : SimpleGraph V) (n : ℕ) :
    G.Colorable n ↔ ∃ coloring : V → Fin n, ∀ i, G.induce {v | coloring v = i} = ⊥ := by
  refine ⟨fun ⟨a, h⟩ ↦ ⟨a, fun i ↦ ?_⟩, fun ⟨w, h⟩ ↦ ⟨w, @fun a b h_adj ↦ ?_⟩⟩
  · rw [SimpleGraph.eq_bot_iff_forall_not_adj]
    rintro ⟨u, huv⟩ ⟨v, rfl⟩ huv'
    exact (h huv').ne huv
  specialize h (w a)
  contrapose h
  intro hG
  have : ¬ ((SimpleGraph.induce {v | w v = w a} G).Adj ⟨a, by rfl⟩ ⟨b, by simp_all⟩) :=
    hG ▸ fun a ↦ a
  exact this h_adj

/--
**Cocolorable graphs.** A graph $G$ is cocolorable with $n$ colors if there is a map from its
vertices to the colors $\{0, \dots, n-1\}$ such that each color class induces either an
independent set or a complete graph in $G$.
-/
def Cocolorable (G : SimpleGraph V) (n : ℕ) : Prop := ∃ coloring : V → Fin n,
  ∀ i, G.induce {v | coloring v = i} = ⊥ ∨ G.induce {v | coloring v = i} = ⊤

/-- **Colorable graphs are cocolorable.** For every natural number $n$, if a graph $G$ has a
proper coloring with $n$ colors, then $G$ is cocolorable with $n$ colors.

Each color class of a proper coloring induces an independent set. -/
theorem Colorable.cocolorable {n : ℕ} (hc : G.Colorable n) : G.Cocolorable n := by
  obtain ⟨coloring, hcol⟩ := (colorable_iff_induce_eq_bot G n).mp hc
  exact ⟨coloring, fun i => Or.inl (hcol i)⟩

/-- **Finite graphs are cocolorable.** Every graph $G$ on a finite vertex set $V$ is cocolorable
with $|V|$ colors.

Giving every vertex its own color is a proper coloring. -/
theorem cocolorable_of_fintype [Fintype V] (G : SimpleGraph V) :
    G.Cocolorable (Fintype.card V) :=
  (colorable_of_fintype G).cocolorable

/--
**Cochromatic number.** The cochromatic number of a graph $G$, an element of
$\mathbb{N} \cup \{\infty\}$, is the least natural number $n$ such that $G$ is cocolorable with
$n$ colors, that is, the least number of colors in a coloring of the vertices of $G$ in which
each color class induces either an independent set or a complete graph. It is $\infty$ exactly
when $G$ is not cocolorable with any finite number of colors.
-/
noncomputable def cochromaticNumber (G : SimpleGraph V) : ℕ∞ := ⨅ n ∈ Set.ofPred G.Cocolorable,
  (n : ℕ∞)

/-- **Cochromatic number as a minimum.** If a graph $G$ is cocolorable with $n$ colors for some
natural number $n$, then the cochromatic number of $G$ equals the least natural number $m$ such
that $G$ is cocolorable with $m$ colors. -/
theorem Cocolorable.cochromaticNumber_eq_sInf {n : ℕ} (h : G.Cocolorable n) :
    G.cochromaticNumber = sInf {n' : ℕ | G.Cocolorable n'} := by
  rw [ENat.natCast_sInf, cochromaticNumber]
  exact ⟨_, h⟩

/-- **Cochromatic number of a finite graph.** For every graph $G$ on a finite vertex set, the
cochromatic number of $G$, converted from $\mathbb{N} \cup \{\infty\}$ to $\mathbb{N}$ by sending
$\infty$ to $0$, equals the least natural number $m$ such that $G$ is cocolorable with $m$
colors. -/
theorem cochromaticNumber_toNat_eq_sInf [Fintype V] (G : SimpleGraph V) :
    G.cochromaticNumber.toNat = sInf {n : ℕ | G.Cocolorable n} := by
  rw [(cocolorable_of_fintype G).cochromaticNumber_eq_sInf, ENat.toNat_natCast]

/-- The chromatic cardinal is the minimal number of colors need to color it. In contrast to
`chromaticNumber`, which assigns `⊤ : ℕ∞` to all non-finitely colorable graphs, this definition
returns a `Cardinal` and can therefore distinguish between different infinite chromatic numbers. -/
noncomputable def chromaticCardinal.{u} {V : Type u} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type u) (_ : Cardinal.mk C = κ), Nonempty (G.Coloring C)}

/-- **Largest union of independent sets.** For a graph $G$ on a finite vertex set and a
natural number $k$, this is the maximum number of vertices in a union of $k$ (possibly empty,
possibly overlapping) independent sets of $G$. -/
noncomputable def indepNumK (G : SimpleGraph V) [Fintype V] (k : ℕ) : ℕ :=
  sSup {n | ∃ f : Fin k → Set V, (∀ i, G.IsIndepSet (f i)) ∧ (⋃ i, f i).ncard = n}

theorem indepNumK_le_card [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    indepNumK G k ≤ Fintype.card V := by
  refine csSup_le ⟨0, fun _ => ∅, fun _ _ hx => False.elim hx, by simp⟩ ?_
  rintro n ⟨f, _, rfl⟩
  simpa using Set.ncard_le_card (⋃ i, f i)

/-- **CDS-colorable graphs.** A graph $G$ on a finite vertex set is CDS-colorable if it has a
proper coloring $C$ with colors in $\mathbb{N}$ such that for every $k \in \mathbb{N}$, the number
of vertices whose color under $C$ is less than $k$ equals the maximum size of a union of $k$
independent sets of $G$. -/
def CDSColorable [Fintype α] (G : SimpleGraph α) : Prop :=
    ∃ (C : G.Coloring Nat), ∀ k : Nat,
   ∑ i < k, (C.colorClass i).ncard = indepNumK G k

/-- **Rainbow homomorphisms.** Let $f$ be a graph homomorphism from $H$ to $G$ and let $c$ be a
labeling of the edges of $G$ by elements of a type $K$. Then $f$ is rainbow for $c$ if distinct
edges of $H$ are mapped to edges of $G$ with distinct labels, that is, the labeling
$e \mapsto c(f(e))$ of the edges of $H$ is injective. -/
def IsRainbow {α V K : Type*} {H : SimpleGraph α} {G : SimpleGraph V} (f : H →g G)
    (c : G.EdgeLabeling K) : Prop :=
  Function.Injective (c.pullback f)

/--
**Anti-Ramsey number.** For a graph $H$ on a finite vertex type and a natural number $n$, the
anti-Ramsey number $\mathrm{AR}(n, H)$ is the largest $k$ for which there is a coloring of the edges
of the complete graph $K_n$ on $\{0, \dots, n-1\}$ with colors $\{0, \dots, k-1\}$, every color
used, that contains no rainbow copy of $H$. Here a copy of $H$ is an injective homomorphism from
$H$ to $K_n$, and it is rainbow when distinct edges of $H$ are sent to edges of distinct colors.
If no such $k$ exists, $\mathrm{AR}(n, H) = 0$.
-/
noncomputable def antiRamseyNum {α : Type*} [Fintype α] (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {k | ∃ c : TopEdgeLabeling (Fin n) (Fin k), Function.Surjective c ∧
    ∀ f : H.Copy ⊤, ¬IsRainbow f.toHom c}

end SimpleGraph
