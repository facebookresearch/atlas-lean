/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.DeriveFintype

/-!
# Triangle-free wheel-free graphs with large chromatic number

Davies's theorem gives finite triangle-free graphs of arbitrarily large chromatic number with
no induced wheel. In the recursive construction of the Burling graphs, every proper colouring
of the graph at stage `k` uses at least `k` colours on one of its distinguished stable sets,
called probes. [Davies, *Triangle-free graphs with large chromatic number and no induced
wheel*](https://arxiv.org/abs/2104.05907v3).

We equip each stage with the arc and descendant relations of a Burling set. On any induced rim
there is a vertex `p` such that every rim vertex outside its closed neighbourhood lies below it.
Deleting `p` leaves a path with no internal source, consisting of two directed arms. An outside
vertex can meet each arm at most once. If it also meets `p`, the descendant relation rules out
two further spokes. [Pournajafi and Trotignon, *Burling graphs revisited, part I: New
characterizations*](https://arxiv.org/abs/2104.07001).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromaticWanted

/-- **Induced wheels.** A simple graph $G$ has an induced wheel if there are a natural
number $\ell \ge 4$, distinct vertices $r_0, \dots, r_{\ell-1}$ of $G$ (the rim) and a vertex
$h$ of $G$ (the hub) with $h \ne r_i$ for every $i$, such that for all $i, j < \ell$ the
vertices $r_i$ and $r_j$ are adjacent in $G$ exactly when $i - j \equiv \pm 1 \pmod{\ell}$,
and $h$ is adjacent to $r_i$, $r_j$ and $r_k$ for some pairwise distinct $i, j, k < \ell$.
The hub may have further neighbours on the rim.

Source: James Davies, *Triangle-free graphs with large chromatic number and no
induced wheel*, arXiv:2104.05907v3, page 1, defining paragraph,
https://arxiv.org/pdf/2104.05907v3. -/
def hasInducedWheel {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (ℓ : ℕ) (rim : Fin ℓ ↪ V) (hub : V),
    4 ≤ ℓ ∧
    (∀ i : Fin ℓ, rim i ≠ hub) ∧
    (∀ i j : Fin ℓ, G.Adj (rim i) (rim j) ↔ (SimpleGraph.cycleGraph ℓ).Adj i j) ∧
    ∃ i j k : Fin ℓ, i ≠ j ∧ j ≠ k ∧ k ≠ i ∧
      G.Adj hub (rim i) ∧ G.Adj hub (rim j) ∧ G.Adj hub (rim k)

/-- **Wheel-free graphs.** A simple graph $G$ is wheel-free if it has no induced wheel, that
is, no induced cycle of length at least four together with a vertex outside the cycle that is
adjacent to at least three vertices of the cycle.

Source: James Davies, arXiv:2104.05907v3, page 1, wheel definition,
https://arxiv.org/pdf/2104.05907v3. -/
def wheelFree {V : Type*} (G : SimpleGraph V) : Prop := ¬ hasInducedWheel G

/-- **Triangle-free wheel-free graphs of large chromatic number (proposition).** This is the
proposition that for every positive integer $k$ there are a natural number $n$ and a simple
graph $G$ on the vertex set $\{0, \dots, n - 1\}$ such that $G$ contains no triangle, $G$ is
wheel-free (it has no induced wheel) and the chromatic number of $G$ is at least $k$.

Since $G$ is finite, its chromatic number is finite.

Source: Davies, arXiv:2104.05907v3, Corollary 2, page 1; the finite constructions
are given on pages 5 and 6, https://arxiv.org/pdf/2104.05907v3. -/
def largeChromaticTriangleFreeWheelFree : Prop :=
  ∀ k : ℕ, 0 < k → ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.CliqueFree 3 ∧ wheelFree G ∧ (k : ℕ∞) ≤ G.chromaticNumber

private structure PairData (V P : Type) where
  graph : SimpleGraph V
  probe : P → Finset V

-- A copy of the old graph for each outer probe, with one new tip for each probe of the copy.
private inductive Vertex (V P : Type)
  | outer (v : V)
  | inner (s : P) (v : V)
  | tip (s t : P)

private instance vertexFintype {V P : Type} [Fintype V] [Fintype P] : Fintype (Vertex V P) :=
  derive_fintype% _

private def nextAdj {V P : Type} (d : PairData V P) :
    Vertex V P → Vertex V P → Prop
  | .outer x, .outer y => d.graph.Adj x y
  | .inner s x, .inner t y => s = t ∧ d.graph.Adj x y
  | .tip s t, .inner u x | .inner u x, .tip s t => s = u ∧ x ∈ d.probe t
  | _, _ => False

private def nextGraph {V P : Type} (d : PairData V P) : SimpleGraph (Vertex V P) where
  Adj := nextAdj d
  symm := by
    constructor
    intro a b h
    cases a <;> cases b <;> simp [nextAdj] at h ⊢ <;> grind [SimpleGraph.adj_comm]
  loopless := by
    constructor
    intro a
    cases a <;> simp [nextAdj]

private noncomputable def nextPair {V P : Type} (d : PairData V P) :
    PairData (Vertex V P) (P × P × Bool) := by
  classical
  exact ⟨nextGraph d, fun (s, t, b) =>
    (d.probe s).image .outer ∪ if b then {.tip s t} else (d.probe t).image (.inner s)⟩

-- Every colouring has a probe whose palette has at least the specified number of colours.
private def Rich {V P : Type} (d : PairData V P) (k : ℕ) : Prop :=
  ∀ m (c : V → Fin m), (∀ x y, d.graph.Adj x y → c x ≠ c y) →
    ∃ s, k ≤ ((d.probe s).image c).card

private theorem next_rich {V P : Type} {d : PairData V P} {k : ℕ} (h : Rich d k) :
    Rich (nextPair d) (k + 1) := by
  classical
  intro m c hc
  obtain ⟨s, hs⟩ := h m (fun v => c (.outer v)) (fun x y hxy => hc _ _ hxy)
  obtain ⟨t, ht⟩ := h m (fun v => c (.inner s v)) (fun x y hxy => hc _ _ ⟨rfl, hxy⟩)
  let A := (d.probe s).image (fun v => c (.outer v))
  let B := (d.probe t).image (fun v => c (.inner s v))
  change k ≤ A.card at hs
  change k ≤ B.card at ht
  -- Equal palettes force the tip to have a new colour. Distinct palettes grow by taking the union.
  by_cases hab : A = B
  · have hnew : c (.tip s t) ∉ B := by
      intro ha
      obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ha
      exact hc (.inner s x) (.tip s t) ⟨rfl, hx⟩ he
    refine ⟨(s, t, true), ?_⟩
    have heq : (((nextPair d).probe (s, t, true)).image c) = insert (c (.tip s t)) A := by
      simp [nextPair, Function.comp_def, Finset.image_image, A]
    rw [heq, hab, Finset.card_insert_of_notMem hnew]
    omega
  · refine ⟨(s, t, false), ?_⟩
    have heq : (((nextPair d).probe (s, t, false)).image c) = A ∪ B := by
      simp [nextPair, Finset.image_union, Function.comp_def, Finset.image_image, A, B]
    rw [heq]
    have hA : A ⊆ A ∪ B := Finset.subset_union_left
    have hB : B ⊆ A ∪ B := Finset.subset_union_right
    by_contra! hsmall
    have ea := Finset.eq_of_subset_of_card_le hA (by omega)
    have eb := Finset.eq_of_subset_of_card_le hB (by omega)
    exact hab (ea.trans eb.symm)

-- An arc points from a vertex to one of its out-neighbours. The relation `below x y` reads
-- “x is a proper descendant of y”. Each probe is an upward-closed chain.
private structure Layout {V P : Type} (d : PairData V P) where
  arc : V → V → Prop
  below : V → V → Prop
  rank : V → ℕ
  adj : ∀ x y, d.graph.Adj x y ↔ arc x y ∨ arc y x
  inc : ∀ {x y}, arc x y → rank x < rank y
  irrefl : ∀ x, ¬below x x
  trans : ∀ {x y z}, below x y → below y z → below x z
  apart : ∀ {x y}, arc x y → ¬below x y ∧ ¬below y x
  chain : ∀ {x y z}, arc x y → arc x z → y ≠ z → below y z ∨ below z y
  down : ∀ {x y z}, arc x y → below x z → below y z
  up : ∀ {x y z}, arc x y → below y z → arc x z ∨ below x z
  probe_chain : ∀ {s x y}, x ∈ d.probe s → y ∈ d.probe s → x ≠ y → below x y ∨ below y x
  probe_up : ∀ {s x y}, x ∈ d.probe s → below x y → y ∈ d.probe s

private def nextArc {V P : Type} {d : PairData V P} (l : Layout d) :
    Vertex V P → Vertex V P → Prop
  | .outer x, .outer y => l.arc x y
  | .inner s x, .inner t y => s = t ∧ l.arc x y
  | .tip s t, .inner u x => s = u ∧ x ∈ d.probe t
  | _, _ => False

-- The vertices in the copy at s and its tips lie below every vertex of the outer probe s.
private def nextBelow {V P : Type} {d : PairData V P} (l : Layout d) :
    Vertex V P → Vertex V P → Prop
  | .outer x, .outer y => l.below x y
  | .inner s x, .inner t y => s = t ∧ l.below x y
  | .inner s _, .outer y | .tip s _, .outer y => y ∈ d.probe s
  | _, _ => False

private noncomputable def nextLayout {V P : Type} {d : PairData V P} (l : Layout d) :
    Layout (nextPair d) where
  arc := nextArc l
  below := nextBelow l
  rank
    | .outer x | .inner _ x => l.rank x + 1
    | .tip _ _ => 0
  adj x y := by
    cases x <;> cases y <;> simp [nextPair, nextGraph, nextArc, nextAdj, l.adj]
    grind
  inc := by
    intro x y h
    cases x <;> cases y <;> simp only [nextArc] at h
    · exact Nat.succ_lt_succ (l.inc h)
    · exact Nat.succ_lt_succ (l.inc h.2)
    · exact Nat.zero_lt_succ _
  irrefl x := by cases x <;> simp [nextBelow, l.irrefl]
  trans := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp [nextBelow] <;> grind [l.trans, l.probe_up]
  apart := by
    intro x y
    cases x <;> cases y <;> simp [nextArc, nextBelow] <;> grind [l.apart]
  chain := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp [nextArc, nextBelow] <;>
      grind [l.chain, l.probe_chain]
  down := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp [nextArc, nextBelow] <;> grind [l.down]
  up := by
    intro x y z
    cases x <;> cases y <;> cases z <;> simp [nextArc, nextBelow] <;>
      grind [l.up, l.probe_up]
  probe_chain := by
    classical
    rintro ⟨s, t, b⟩ x y
    cases b <;> cases x <;> cases y <;> simp [nextPair, nextBelow] <;> grind [l.probe_chain]
  probe_up := by
    classical
    rintro ⟨s, t, b⟩ x y
    cases b <;> cases x <;> cases y <;> simp [nextPair, nextBelow] <;> grind [l.probe_up]

private theorem rank_path {V P : Type} {d : PairData V P} (l : Layout d)
    {a b : V} (p : Relation.ReflTransGen l.arc a b) : l.rank a ≤ l.rank b := by
  induction p with
  | refl => rfl
  | tail _ h ih => exact ih.trans (l.inc h).le

private theorem below_path {V P : Type} {d : PairData V P} (l : Layout d)
    {a b z : V} (p : Relation.ReflTransGen l.arc a b) (h : l.below a z) : l.below b z := by
  induction p with
  | refl => exact h
  | tail _ e ih => exact l.down e ih

private theorem path_not_below {V P : Type} {d : PairData V P} (l : Layout d)
    {a b : V} (p : Relation.ReflTransGen l.arc a b) : ¬l.below b a := by
  induction p with
  | refl => exact l.irrefl _
  | tail p e ih =>
    intro h
    rcases l.up e h with h' | h'
    · exact (l.inc h').not_ge (rank_path l p)
    · exact ih h'

-- A vertex outside a directed path cannot see both endpoints. The first edge of the path and
-- the edge to the outside vertex either force comparable out-neighbours or contradict the rank.
private theorem path_neighbors {V P : Type} {d : PairData V P} (l : Layout d)
    {a b c z : V} (e : l.arc a b) (p : Relation.ReflTransGen l.arc b c) (hz : z ≠ b)
    (ha : d.graph.Adj z a) (hc : d.graph.Adj z c) : False := by
  have q := Relation.ReflTransGen.head e p
  have hbc := rank_path l p
  rcases (l.adj _ _).mp ha with hza | haz
  · rcases (l.adj _ _).mp hc with hzc | hcz
    · have hne : a ≠ c := fun he => by
        have := l.inc e
        rw [he] at this
        omega
      rcases l.chain hza hzc hne with hac | hca
      · exact l.irrefl c (below_path l q hac)
      · exact path_not_below l q hca
    · have := l.inc hza
      have := l.inc e
      have := l.inc hcz
      omega
  · rcases l.chain haz e hz with hzb | hbz
    · rcases (l.adj _ _).mp hc with hzc | hcz
      · exact path_not_below l p (l.down hzc hzb)
      · rcases l.up hcz hzb with hcb | hcb
        · exact (l.inc hcb).not_ge hbc
        · exact path_not_below l p hcb
    · have hcz := below_path l p hbz
      exact ((l.adj _ _).mp hc).elim (fun h => (l.apart h).2 hcz) (fun h => (l.apart h).1 hcz)

-- The single-edge case already excludes triangles.
private theorem no_triangle {V P : Type} {d : PairData V P} (l : Layout d)
    {x y z : V} (hxy : d.graph.Adj x y) (hxz : d.graph.Adj x z) (hyz : d.graph.Adj y z) :
    False := by
  rcases (l.adj x y).mp hxy with e | e
  · exact path_neighbors l e .refl hyz.ne.symm hxz.symm hyz.symm
  · exact path_neighbors l e .refl hxz.ne.symm hyz.symm hxz.symm

private structure Rim {V : Type} (G : SimpleGraph V) (n : ℕ) where
  v : Fin (n + 4) ↪ V
  adj : ∀ i j, G.Adj (v i) (v j) ↔ (SimpleGraph.cycleGraph (n + 4)).Adj i j

-- Number the rim cyclically starting at p.
private def idx {n : ℕ} (p : Fin (n + 4)) (i : ℕ) : Fin (n + 4) :=
  p + ⟨i % (n + 4), Nat.mod_lt _ (by omega)⟩

private theorem idx_surj {n : ℕ} (p u : Fin (n + 4)) :
    ∃ i < n + 4, idx p i = u := by
  exact ⟨(u - p).val, (u - p).isLt, by
    have he : (⟨(u - p).val % (n + 4), Nat.mod_lt _ (by omega)⟩ : Fin (n + 4)) = u - p :=
      Fin.ext (Nat.mod_eq_of_lt (u - p).isLt)
    simp [idx, he]⟩

private theorem idx_inj {n : ℕ} {p : Fin (n + 4)} {i j : ℕ}
    (hi : i < n + 4) (hj : j < n + 4) : idx p i = idx p j ↔ i = j := by
  simp only [idx, add_right_inj, Fin.ext_iff, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hj]

private theorem idx_adj {V : Type} {G : SimpleGraph V} {n : ℕ} (r : Rim G n)
    (p : Fin (n + 4)) {i j : ℕ} (hi : i < n + 4) (hj : j < n + 4) :
    G.Adj (r.v (idx p i)) (r.v (idx p j)) ↔
      i + 1 = j ∨ j + 1 = i ∨ (i = 0 ∧ j = n + 3) ∨ (j = 0 ∧ i = n + 3) := by
  rw [r.adj, SimpleGraph.cycleGraph_adj']
  simp only [idx, add_sub_add_left_eq_sub]
  set x : Fin (n + 4) := ⟨i % (n + 4), _⟩
  set y : Fin (n + 4) := ⟨j % (n + 4), _⟩
  have vx : x.val = i := Nat.mod_eq_of_lt hi
  have vy : y.val = j := Nat.mod_eq_of_lt hj
  have hxy := Fin.coe_int_sub_eq_ite x y
  have hyx := Fin.coe_int_sub_eq_ite y x
  simp only [Fin.le_iff_val_le_val, vx, vy] at hxy hyx
  split_ifs at hxy hyx <;> omega

private theorem propagate {V P : Type} {d : PairData V P} (l : Layout d)
    {x y z : V} (hxy : d.graph.Adj x y) (hx : l.below x z) (hy : ¬d.graph.Adj y z) :
    l.below y z := by
  rcases (l.adj x y).mp hxy with e | e
  · exact l.down e hx
  · exact (l.up e hx).resolve_left fun e' => hy ((l.adj _ _).mpr (.inl e'))

-- A big vertex lies above every rim vertex outside its closed neighbourhood.
private def Big {V P : Type} {d : PairData V P} (l : Layout d) {n : ℕ}
    (r : Rim d.graph n) (p : Fin (n + 4)) : Prop :=
  ∀ i, i ≠ p → ¬d.graph.Adj (r.v i) (r.v p) → l.below (r.v i) (r.v p)

private theorem big_of_below {V P : Type} {d : PairData V P} (l : Layout d) {n : ℕ}
    (r : Rim d.graph n) {p u : Fin (n + 4)} (hu : l.below (r.v u) (r.v p)) : Big l r p := by
  have zero : idx p 0 = p := by simp [idx]
  let f := fun i => r.v (idx p i)
  have geo (i j : ℕ) (hi : i < n + 4) (hj : j < n + 4) := idx_adj r p hi hj
  have noedge (i : ℕ) (h₁ : 2 ≤ i) (h₂ : i ≤ n + 2) : ¬d.graph.Adj (f i) (r.v p) := by
    rw [← zero]
    apply mt (geo i 0 (by omega) (by omega)).mp
    omega
  let Q := fun i => l.below (f i) (r.v p)
  -- The complement of the closed neighbourhood is the interval of offsets from 2 to n + 2.
  -- Membership below p propagates across each of its edges in both directions.
  have step {i : ℕ} (lo : 2 ≤ i) (hi : i < n + 2) : Q i ↔ Q (i + 1) := by
    have e := (geo i (i + 1) (by omega) (by omega)).mpr (Or.inl rfl)
    exact ⟨fun h => propagate l e h (noedge _ (by omega) (by omega)),
      fun h => propagate l e.symm h (noedge _ lo hi.le)⟩
  have eqv (i : ℕ) (lo : 2 ≤ i) (hi : i ≤ n + 2) : Q 2 ↔ Q i := by
    induction i, lo using Nat.le_induction with
    | base => rfl
    | succ i hi' ih => exact (ih (by omega)).trans (step hi' (by omega))
  have bounds {i : ℕ} (hi : i < n + 4) (hn : idx p i ≠ p)
      (ha : ¬d.graph.Adj (f i) (r.v p)) : 2 ≤ i ∧ i ≤ n + 2 := by
    have ne : i ≠ 0 := fun h => hn (h ▸ zero)
    have he := mt (geo i 0 hi (by omega)).mpr (show ¬d.graph.Adj (f i) (f 0) by
      simpa only [f, zero] using ha)
    omega
  obtain ⟨j, hj, rfl⟩ := idx_surj p u
  have hn : idx p j ≠ p := fun h => l.irrefl _ (h ▸ hu)
  have ha : ¬d.graph.Adj (f j) (r.v p) := fun h => ((l.adj _ _).mp h).elim
    (fun e => (l.apart e).1 hu) (fun e => (l.apart e).2 hu)
  obtain ⟨hlo, hhi⟩ := bounds hj hn ha
  have h2 := (eqv j hlo hhi).mpr hu
  intro v hv hne
  obtain ⟨i, hi, rfl⟩ := idx_surj p v
  obtain ⟨hl, hh⟩ := bounds hi hv hne
  exact (eqv i hl hh).mp h2

private theorem no_big_below {V P : Type} {d : PairData V P} (l : Layout d) {n : ℕ}
    (r : Rim d.graph n) {p q : Fin (n + 4)}
    (hq : Big l r q) (h : l.below (r.v q) (r.v p)) : False := by
  have ne : p ≠ q := fun e => l.irrefl _ (e ▸ h)
  have na : ¬d.graph.Adj (r.v p) (r.v q) := fun ha => ((l.adj _ _).mp ha).elim
    (fun e => (l.apart e).2 h) (fun e => (l.apart e).1 h)
  exact l.irrefl _ (l.trans h (hq p ne na))

private theorem big_at_source {V P : Type} {d : PairData V P} (l : Layout d) {n : ℕ}
    (r : Rim d.graph n) {s a b : Fin (n + 4)} (hab : a ≠ b)
    (ha : l.arc (r.v s) (r.v a)) (hb : l.arc (r.v s) (r.v b)) :
    ∃ p, Big l r p ∧ l.arc (r.v s) (r.v p) := by
  rcases l.chain ha hb (r.v.injective.ne hab) with h | h
  · exact ⟨_, big_of_below l r h, hb⟩
  · exact ⟨_, big_of_below l r h, ha⟩

-- At a minimum of the rank, both rim edges point out. Their targets are comparable.
private theorem exists_big {V P : Type} {d : PairData V P} (l : Layout d) {n : ℕ}
    (r : Rim d.graph n) : ∃ p, Big l r p := by
  classical
  obtain ⟨s, hs⟩ := Finite.exists_min (fun i => l.rank (r.v i))
  have out (i : ℕ) (hi : i < n + 4) (ha : 1 = i ∨ i = n + 3) :
      l.arc (r.v s) (r.v (idx s i)) := by
    have adj := (idx_adj r s (i := 0) (by omega) hi).mpr (by omega)
    rw [show idx s 0 = s by simp [idx]] at adj
    exact ((l.adj _ _).mp adj).resolve_right fun e => (l.inc e).not_ge (hs _)
  have ne : idx s 1 ≠ idx s (n + 3) := mt (idx_inj (by omega) (by omega)).mp (by omega)
  obtain ⟨p, hp, _⟩ := big_at_source l r ne (out 1 (by omega) (by omega))
    (out (n + 3) (by omega) (by omega))
  exact ⟨p, hp⟩

-- Forward edges on the rim form a prefix between the two neighbours of a big vertex.
private theorem path_spokes {V P : Type} {d : PairData V P} (l : Layout d)
    (f : ℕ → V) {a b c : ℕ} (hab : a < b) (hbc : b < c)
    (edge : ∀ i, a ≤ i → i < c → d.graph.Adj (f i) (f (i + 1)))
    (nosrc : ∀ i, a ≤ i → i + 1 < c →
      l.arc (f (i + 1)) (f i) → ¬l.arc (f (i + 1)) (f (i + 2)))
    {z : V} (hz : ∀ i, z ≠ f i) (ha : d.graph.Adj z (f a))
    (hb : d.graph.Adj z (f b)) (hc : d.graph.Adj z (f c)) : False := by
  rcases (l.adj _ _).mp (edge b hab.le hbc) with right | left
  · have reach (i : ℕ) (lo : a + 1 ≤ i) (hi : i ≤ b) (e : l.arc (f i) (f (i + 1))) :
        l.arc (f a) (f (a + 1)) ∧ Relation.ReflTransGen l.arc (f (a + 1)) (f i) := by
      induction i, lo using Nat.le_induction with
      | base =>
        refine ⟨((l.adj _ _).mp (edge a (by omega) (by omega))).resolve_right ?_, .refl⟩
        exact fun back => nosrc a le_rfl (by omega) back e
      | succ i lo ih =>
        have forward := ((l.adj _ _).mp (edge i (by omega) (by omega))).resolve_right
          (fun back => nosrc i (by omega) (by omega) back e)
        have prev := ih (by omega) forward
        exact ⟨prev.1, prev.2.tail forward⟩
    obtain ⟨e, p⟩ := reach b (by omega) le_rfl right
    exact path_neighbors l e p (hz _) ha hb
  · have reach (i : ℕ) (lo : b ≤ i) (hi : i < c) :
        l.arc (f (i + 1)) (f i) ∧ Relation.ReflTransGen l.arc (f i) (f b) := by
      induction i, lo using Nat.le_induction with
      | base => exact ⟨left, .refl⟩
      | succ i lo ih =>
        obtain ⟨back, p⟩ := ih (by omega)
        exact ⟨((l.adj _ _).mp (edge (i + 1) (by omega) hi)).resolve_left
          (nosrc i (by omega) hi back), .head back p⟩
    obtain ⟨e, p⟩ := reach (c - 1) (by omega) (by omega)
    rw [show c - 1 + 1 = c by omega] at e
    exact path_neighbors l e p (hz _) hc hb

private theorem sorted_spokes {V P : Type} {d : PairData V P} (l : Layout d)
    {n : ℕ} (r : Rim d.graph n) {p : Fin (n + 4)}
    (hp : Big l r p) {z : V} (hz : ∀ i, r.v i ≠ z)
    {a b c : ℕ} (hab : a < b) (hbc : b < c) (hcn : c < n + 4)
    (ha : d.graph.Adj z (r.v (idx p a))) (hb : d.graph.Adj z (r.v (idx p b)))
    (hc : d.graph.Adj z (r.v (idx p c))) : False := by
  let f := fun i => r.v (idx p i)
  have zero : idx p 0 = p := by simp [idx]
  have inside (i : ℕ) (hl : 2 ≤ i) (hi : i ≤ n + 2) : l.below (f i) (r.v p) := by
    apply hp
    · exact fun h => (mt (idx_inj (p := p) (i := i) (j := 0) (by omega) (by omega)).mp
        (by omega)) (h.trans zero.symm)
    · simpa only [zero] using mt (idx_adj r p (i := i) (j := 0) (by omega) (by omega)).mp
        (by omega)
  -- A hub incident to p must send the other two spokes into the interior, by triangle-freeness.
  -- Its two targets are comparable, making one of them both big and below p.
  by_cases h0 : a = 0
  · subst a
    rw [zero] at ha
    have out (i : ℕ) (lo : 0 < i) (hi : i < n + 4) (e : d.graph.Adj z (f i)) :
        l.below (f i) (r.v p) ∧ l.arc z (f i) := by
      have hno := no_triangle l ha e
      rw [← zero] at hno
      have hbound := mt (idx_adj r p (i := 0) (j := i) (by omega) hi).mpr hno
      have h := inside i (by omega) (by omega)
      refine ⟨h, ((l.adj _ _).mp e).resolve_right fun back => ?_⟩
      have hz' := l.down back h
      exact ((l.adj _ _).mp ha).elim (fun t => (l.apart t).1 hz') (fun t => (l.apart t).2 hz')
    obtain ⟨ib, eb⟩ := out b hab (by omega) hb
    obtain ⟨ic, ec⟩ := out c (by omega) hcn hc
    have ne := r.v.injective.ne (mt (idx_inj (p := p) (i := b) (j := c) (by omega) hcn).mp
      (by omega))
    rcases l.chain eb ec ne with h | h
    · exact no_big_below l r (big_of_below l r h) ic
    · exact no_big_below l r (big_of_below l r h) ib
  -- If all three spokes miss p, they lie on the path between its two neighbours.
  · apply path_spokes l f hab hbc _ _ (fun i => (hz _).symm) ha hb hc
    · exact fun i hlo hhi => (idx_adj r p (by omega) (by omega)).mpr (Or.inl rfl)
    · intro i hlo hhi back forward
      have ne : idx p i ≠ idx p (i + 2) := mt (idx_inj (by omega) (by omega)).mp (by omega)
      obtain ⟨q, hq, e⟩ := big_at_source l r ne back forward
      exact no_big_below l r hq (l.down e (inside (i + 1) (by omega) (by omega)))

private theorem layout_free {V P : Type} {d : PairData V P} (l : Layout d) :
    wheelFree d.graph := by
  rintro ⟨m, v, z, hm, hz, rim, i, j, k, hij, hjk, hki, hi, hj, hk⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 4 := ⟨m - 4, by omega⟩
  let r : Rim d.graph n := ⟨v, rim⟩
  obtain ⟨p, hp⟩ := exists_big l r
  obtain ⟨a, han, rfl⟩ := idx_surj p i
  obtain ⟨b, hbn, rfl⟩ := idx_surj p j
  obtain ⟨c, hcn, rfl⟩ := idx_surj p k
  have neab := mt (idx_inj han hbn).mpr hij
  have nebc := mt (idx_inj hbn hcn).mpr hjk
  have neca := mt (idx_inj hcn han).mpr hki
  have elim := @sorted_spokes _ _ _ l _ r p hp z hz
  rcases lt_or_gt_of_ne neab with h | h <;> rcases lt_or_gt_of_ne nebc with h' | h'
  · exact elim h h' hcn hi hj hk
  · rcases lt_or_gt_of_ne neca with h'' | h''
    · exact elim h'' h hbn hk hi hj
    · exact elim h'' h' hbn hi hk hj
  · rcases lt_or_gt_of_ne neca with h'' | h''
    · exact elim h' h'' han hj hk hi
    · exact elim h h'' hcn hj hi hk
  · exact elim h' h han hk hj hi

private def initial : PairData Unit Unit := ⟨⊥, fun _ => {()}⟩

private structure Stage (k : ℕ) where
  V : Type
  P : Type
  finV : Fintype V
  finP : Fintype P
  d : PairData V P
  rich : Rich d k
  layout : Layout d

private noncomputable def stages : (k : ℕ) → Stage (k + 1)
  | 0 =>
    { V := Unit, P := Unit, finV := inferInstance, finP := inferInstance, d := initial
      rich := by intro m c _; exact ⟨(), by simp [initial]⟩
      layout :=
        { arc := fun _ _ => False, below := fun _ _ => False, rank := fun _ => 0
          adj := by simp [initial]
          inc := by simp
          irrefl := by simp
          trans := by simp
          apart := by simp
          chain := by simp
          down := by simp
          up := by simp
          probe_chain := by simp
          probe_up := by simp } }
  | k + 1 => by
    classical
    let s := stages k
    letI := s.finV
    letI := s.finP
    exact ⟨Vertex s.V s.P, s.P × s.P × Bool, inferInstance, inferInstance,
      nextPair s.d, next_rich s.rich, nextLayout s.layout⟩

/-- **Davies's theorem on triangle-free wheel-free graphs.** For every positive integer $k$
there are a natural number $n$ and a simple graph $G$ on the vertex set $\{0, \dots, n - 1\}$
such that $G$ contains no triangle, $G$ is wheel-free (it has no induced wheel) and the
chromatic number of $G$ is at least $k$.

Source: James Davies, arXiv:2104.05907v3, Corollary 2, page 1,
https://arxiv.org/pdf/2104.05907v3. -/
theorem largeChromaticTriangleFreeWheelFree_holds :
    largeChromaticTriangleFreeWheelFree := by
  classical
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let s := stages j
  let := s.finV
  let e := Fintype.equivFin s.V
  let G := s.d.graph.comap e.symm
  refine ⟨_, G, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp ht
    exact no_triangle s.layout hab hac hbc
  · rintro ⟨l, rim, hub, hl, hout, hrim, hspokes⟩
    apply layout_free s.layout
    exact ⟨l, rim.trans e.symm.toEmbedding, e.symm hub, hl,
      fun i => e.symm.injective.ne (hout i), hrim, hspokes⟩
  · apply SimpleGraph.le_chromaticNumber_iff_coloring.mpr
    intro m c
    obtain ⟨t, ht⟩ := s.rich m (fun x => c (e x)) fun x y hxy => by
      apply c.valid
      simpa [G] using hxy
    exact ht.trans (Finset.card_le_univ _ |>.trans_eq (Fintype.card_fin m))

end MathlibExt.Combinatorics.SimpleGraph.DaviesWheelFreeChromaticWanted
