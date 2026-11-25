/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph
import Mathlib.Data.ZMod.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Positivity

/-!
# Triple systems with few triples on every small vertex set (Erdős Problem 1076)

Erdős Problem 1076: let `k ≥ 5` and let `𝓕_k` be the family of all `3`-uniform hypergraphs with
`k` vertices and `k - 2` edges. Is it true that `ex₃(n, 𝓕_k) ∼ n² / 6`?

We prove that the claim as worded fails (`singleFamilyAsymptotic_refuted`): an explicit
construction gives `ex₃(64 m, 𝓕_5) ≥ 720 m²` for every `m`, so
`ex₃(n, 𝓕_5) / n² ≥ 45 / 256 > 1 / 6` along `n = 64 m`.

Source: T. F. Bloom, Erdős Problems, Problem #1076, https://www.erdosproblems.com/1076 (status
PROVED). UnsolvedMath record UM-30007153 (`EP-1076`), dataset ulamai/UnsolvedMath v1.8.0.

A triple system on `n` vertices is a `3`-uniform family of subsets of `Fin n` (MathlibExt's
`SetFamily.IsUniform`). It contains a member of `𝓕_k` exactly when some `k` vertices span at least
`k - 2` triples (MathlibExt's `SetFamily.ContainsSubgraph`; a member may have isolated vertices,
and extra triples can be dropped), so `ex₃(n, 𝓕_k)` is Brown-Erdős-Sós's `f⁽³⁾(n; k, k - 2)`.
Glock's theorem gives `f⁽³⁾(n; 5, 3) = (1 + o(1)) n² / 5`, so the claim as worded fails at `k =
5`; his §1 asks exactly whether the lower bound `1/6` is sharp for every `k` (it is for `k = 4`,
by Brown, Erdős and Sós). The page lists the problem as proved, saying that the asymptotic version
'asked for here' was proved by Bohman and Warnke and by Glock, Kühn, Lo and Osthus. Their theorem
forbids `j` vertices with `j - 2` triples for every `4 ≤ j ≤ k` at once (partial Steiner triple
systems of girth larger than `k`), and both papers present it as the answer to Erdős's 1973
question on high-girth Steiner triple systems (Problems and results in combinatorial analysis,
Rome 1973), not to this problem, so that reading is not stated here. The teorth/erdosproblems
database note on a Lean contribution separates the same two readings (positive under simultaneous
sparsity, negative for the literal single-`k` reading). formal-conjectures has no statement of
this problem.

## Proof

Rather than Glock's asymptotic formula, the proof uses an explicit construction, which gives the
weaker bound `45 / 256`. Call a family of triples sparse when, for any two triples sharing two
points, every other triple meets their union in at most one point; in a sparse `3`-uniform family
any three triples span at least six points, so no five points span three triples. On `ZMod 8`, the
three pairs of triples `{0, a, b}, {1, a, b}` for `{a, b} = {2, 3}, {4, 5}, {6, 7}` and the four
edge-disjoint triangles `{2, 4, 6}, {2, 5, 7}, {3, 4, 7}, {3, 5, 6}` form a sparse family of `10`
triples. Given sparse `3`-uniform families `H` on `V` and `G` on a finite abelian group `W`, the
family on `V × W` made of the triples `{(x, a), (y, b), (z, c)}` with `{x, y, z} ∈ H` and
`a + b + c = 0`, together with a copy of `G` in each group `{x} × W`, is again sparse, with at least
`|H| |W|² + |V| |G|` triples. Taking `H = G` the `10`-triple family and `W = ZMod 8` gives `720`
triples on `64` points; taking `H` this `720`-triple family, `W = ZMod m` and `G` empty then gives
at least `720 m²` triples on `64 m` points.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted

open Filter Topology

/-- **Extremal number for $k$ vertices spanning $k - 2$ triples.** For $k, n \in \mathbb{N}$ let
$\mathcal{F}_k$ be the family of all $3$-uniform hypergraphs with $k$ vertices and $k - 2$ edges.
Then $\mathrm{ex}_3(n, \mathcal{F}_k)$ is the largest number of triples in a $3$-uniform
hypergraph $E$ on the vertex set $\{0, \dots, n-1\}$ that contains no member of $\mathcal{F}_k$,
meaning that no set of exactly $k$ vertices contains $k - 2$ or more triples of $E$ (a member may
have isolated vertices, and extra triples can be dropped). Here $k - 2$ is read as $0$ when
$k < 2$, and $\mathrm{ex}_3(n, \mathcal{F}_k) = 0$ when no such hypergraph exists, which happens
exactly when $k \le 2$ and $k \le n$. -/
noncomputable def exSingle (k n : ℕ) : ℕ :=
  sSup {m | ∃ E : Finset (Finset (Fin n)), SetFamily.IsUniform E 3 ∧
    ¬ SetFamily.ContainsSubgraph E k (k - 2) ∧ E.card = m}

/-- **Erdős Problem 1076 as worded.** For $k, n \in \mathbb{N}$ let
$\mathrm{ex}_3(n, \mathcal{F}_k)$ be the largest number of triples in a $3$-uniform hypergraph on
$n$ vertices in which no $k$ vertices span $k - 2$ or more triples, that is, which contains no
member of the family $\mathcal{F}_k$ of $3$-graphs with $k$ vertices and $k - 2$ edges. This is
the statement that for every $k \ge 5$, $\mathrm{ex}_3(n, \mathcal{F}_k) / n^2 \to 1/6$ as
$n \to \infty$, that is, $\mathrm{ex}_3(n, \mathcal{F}_k) \sim n^2 / 6$. -/
def singleFamilyAsymptotic : Prop :=
  ∀ k : ℕ, 5 ≤ k → Tendsto (fun n : ℕ => (exSingle k n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 6))

open Finset

section Sparse

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Whenever two distinct triples share two points, every other triple meets their union in at
most one point. -/
private def Sparse (E : Finset (Finset α)) : Prop :=
  ∀ t₁ ∈ E, ∀ t₂ ∈ E, ∀ t₃ ∈ E, t₁ ≠ t₂ → t₃ ≠ t₁ → t₃ ≠ t₂ →
    2 ≤ (t₁ ∩ t₂).card → (t₃ ∩ (t₁ ∪ t₂)).card ≤ 1

private instance (E : Finset (Finset α)) : Decidable (Sparse E) := by
  unfold Sparse; infer_instance

private lemma Sparse.eq {E : Finset (Finset α)} (hE : Sparse E) {t₁ t₂ t₃ : Finset α}
    (h₁ : t₁ ∈ E) (h₂ : t₂ ∈ E) (h₃ : t₃ ∈ E) (h12 : t₁ ≠ t₂) (h31 : t₃ ≠ t₁)
    (h32 : t₃ ≠ t₂) {a b x y : α} (ha₁ : a ∈ t₁) (ha₂ : a ∈ t₂) (hb₁ : b ∈ t₁) (hb₂ : b ∈ t₂)
    (hab : a ≠ b) (hx : x ∈ t₃) (hy : y ∈ t₃) (hx' : x ∈ t₁ ∨ x ∈ t₂)
    (hy' : y ∈ t₁ ∨ y ∈ t₂) : x = y := by
  have h2 : 2 ≤ (t₁ ∩ t₂).card :=
    one_lt_card_iff.mpr ⟨a, b, mem_inter.mpr ⟨ha₁, ha₂⟩, mem_inter.mpr ⟨hb₁, hb₂⟩, hab⟩
  exact card_le_one.mp (hE t₁ h₁ t₂ h₂ t₃ h₃ h12 h31 h32 h2) x
    (mem_inter.mpr ⟨hx, mem_union.mpr hx'⟩) y (mem_inter.mpr ⟨hy, mem_union.mpr hy'⟩)

private lemma sparse_of_forall {E : Finset (Finset α)}
    (h : ∀ t₁ ∈ E, ∀ t₂ ∈ E, ∀ t₃ ∈ E, t₁ ≠ t₂ → t₃ ≠ t₁ → t₃ ≠ t₂ →
      ∀ a b x y : α, a ∈ t₁ → a ∈ t₂ → b ∈ t₁ → b ∈ t₂ → a ≠ b → x ∈ t₃ → y ∈ t₃ →
        (x ∈ t₁ ∨ x ∈ t₂) → (y ∈ t₁ ∨ y ∈ t₂) → x = y) : Sparse E := by
  intro t₁ h₁ t₂ h₂ t₃ h₃ h12 h31 h32 h2
  obtain ⟨a, b, ha, hb, hab⟩ := one_lt_card_iff.mp h2
  rw [mem_inter] at ha hb
  refine card_le_one.mpr fun x hx y hy => ?_
  rw [mem_inter, mem_union] at hx hy
  exact h t₁ h₁ t₂ h₂ t₃ h₃ h12 h31 h32 a b x y ha.1 ha.2 hb.1 hb.2 hab hx.1 hy.1 hx.2 hy.2

/-- Any three distinct triples span at least six points. -/
private def Good (E : Finset (Finset α)) : Prop :=
  ∀ t₁ ∈ E, ∀ t₂ ∈ E, ∀ t₃ ∈ E, t₁ ≠ t₂ → t₁ ≠ t₃ → t₂ ≠ t₃ → 6 ≤ (t₁ ∪ t₂ ∪ t₃).card

private lemma card_inter_le_two {s t : Finset α} (hs : s.card = 3) (ht : t.card = 3)
    (hst : s ≠ t) : (s ∩ t).card ≤ 2 := by
  by_contra! h
  have h1 : s ∩ t = s := eq_of_subset_of_card_le inter_subset_left (by omega)
  have h2 : s ∩ t = t := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact hst (h1.symm.trans h2)

private lemma six_le_card_union {s t u : Finset α} (hs : s.card = 3) (ht : t.card = 3)
    (hu : u.card = 3) (hst : s ≠ t) (h : (u ∩ (s ∪ t)).card ≤ 1) : 6 ≤ (s ∪ t ∪ u).card := by
  have h1 := card_union_add_card_inter s t
  have h2 := card_union_add_card_inter (s ∪ t) u
  have h3 := card_inter_le_two hs ht hst
  rw [inter_comm] at h2
  omega

private lemma good_of_sparse {E : Finset (Finset α)} (h3 : SetFamily.IsUniform E 3)
    (hE : Sparse E) : Good E := by
  intro t₁ h₁ t₂ h₂ t₃ h₃ h12 h13 h23
  have c₁ := h3 t₁ h₁
  have c₂ := h3 t₂ h₂
  have c₃ := h3 t₃ h₃
  by_cases a12 : 2 ≤ (t₁ ∩ t₂).card
  · exact six_le_card_union c₁ c₂ c₃ h12
      (hE t₁ h₁ t₂ h₂ t₃ h₃ h12 (Ne.symm h13) (Ne.symm h23) a12)
  by_cases a13 : 2 ≤ (t₁ ∩ t₃).card
  · have := six_le_card_union c₁ c₃ c₂ h13 (hE t₁ h₁ t₃ h₃ t₂ h₂ h13 (Ne.symm h12) h23 a13)
    rwa [union_right_comm] at this
  by_cases a23 : 2 ≤ (t₂ ∩ t₃).card
  · have := six_le_card_union c₂ c₃ c₁ h23 (hE t₂ h₂ t₃ h₃ t₁ h₁ h23 h12 h13 a23)
    have e : t₂ ∪ t₃ ∪ t₁ = t₁ ∪ t₂ ∪ t₃ := by
      ext; simp only [mem_union]; tauto
    rwa [e] at this
  simp only [not_le] at a12 a13 a23
  have h1 := card_union_add_card_inter t₁ t₂
  have h2 := card_union_add_card_inter (t₁ ∪ t₂) t₃
  have h4 : ((t₁ ∪ t₂) ∩ t₃).card ≤ (t₁ ∩ t₃).card + (t₂ ∩ t₃).card := by
    rw [union_inter_distrib_right]; exact card_union_le _ _
  omega

private lemma not_containsSubgraph_of_good {E : Finset (Finset α)} (hE : Good E) :
    ¬ SetFamily.ContainsSubgraph E 5 3 := by
  rintro ⟨S, hS, h3⟩
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ :=
    two_lt_card.mp (by omega : 2 < (E.filter (· ⊆ S)).card)
  rw [mem_filter] at ha hb hc
  have h6 := hE a ha.1 b hb.1 c hc.1 hab hac hbc
  have h5 := card_le_card (union_subset (union_subset ha.2 hb.2) hc.2)
  omega

private lemma good_map {E : Finset (Finset α)} (f : α ↪ β) (hE : Good E) :
    Good (E.map (mapEmbedding f).toEmbedding) := by
  intro t₁ h₁ t₂ h₂ t₃ h₃ h12 h13 h23
  rw [Finset.mem_map] at h₁ h₂ h₃
  obtain ⟨s₁, hs₁, rfl⟩ := h₁
  obtain ⟨s₂, hs₂, rfl⟩ := h₂
  obtain ⟨s₃, hs₃, rfl⟩ := h₃
  simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply] at h12 h13 h23 ⊢
  rw [← map_union, ← map_union, card_map]
  exact hE s₁ hs₁ s₂ hs₂ s₃ hs₃ (fun h => h12 (h ▸ rfl)) (fun h => h13 (h ▸ rfl))
    (fun h => h23 (h ▸ rfl))

omit [DecidableEq α] [DecidableEq β] in
private lemma isUniform_map {E : Finset (Finset α)} (f : α ↪ β)
    (h3 : SetFamily.IsUniform E 3) :
    SetFamily.IsUniform (E.map (mapEmbedding f).toEmbedding) 3 := by
  intro t ht
  rw [Finset.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  simpa using h3 s hs

private lemma eq_of_card_eq_three {s : Finset α} (hs : s.card = 3) {a b c : α} (ha : a ∈ s)
    (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : s = {a, b, c} := by
  symm
  apply eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  · rw [hs, card_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩]

omit [DecidableEq α] in
private lemma exists_third {s : Finset α} (hs : s.card = 3) (a b : α) :
    ∃ c ∈ s, c ≠ a ∧ c ≠ b := by
  classical
  by_contra! h
  have hsub : s ⊆ {a, b} := fun c hc => by
    by_cases hca : c = a
    · simp [hca]
    · simp [h c hc hca]
  have := card_le_card hsub
  have := card_le_two (a := a) (b := b)
  omega

omit [DecidableEq α] in
private lemma eq_or_eq_of_mem_inter {s t : Finset α} (hs : s.card = 3) (ht : t.card = 3)
    (hst : s ≠ t) {a b x : α} (has : a ∈ s) (hat : a ∈ t) (hbs : b ∈ s) (hbt : b ∈ t)
    (hab : a ≠ b) (hxs : x ∈ s) (hxt : x ∈ t) : x = a ∨ x = b := by
  classical
  by_contra! h
  exact hst ((eq_of_card_eq_three hs has hbs hxs hab (Ne.symm h.1) (Ne.symm h.2)).trans
    (eq_of_card_eq_three ht hat hbt hxt hab (Ne.symm h.1) (Ne.symm h.2)).symm)

private lemma sum_triple {M : Type*} [AddCommMonoid M] (f : α → M) {a b c : α} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : ∑ x ∈ ({a, b, c} : Finset α), f x = f a + f b + f c := by
  rw [sum_insert (by simp [hab, hac]), sum_pair hbc, add_assoc]

end Sparse

section Blowup

variable {V W : Type*} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] [AddCommGroup W]

/-- Triples meeting three distinct groups `{x} × W` whose second coordinates sum to zero, above a
triple of `H`. -/
private def crossTriples (H : Finset (Finset V)) : Finset (Finset (V × W)) :=
  univ.filter fun t => t.card = 3 ∧ t.image Prod.fst ∈ H ∧ ∑ p ∈ t, p.2 = 0

/-- Copies of the triples of `G` inside the groups `{x} × W`. -/
private def innerTriples (G : Finset (Finset W)) : Finset (Finset (V × W)) :=
  (univ ×ˢ G).image fun xU => xU.2.map (Function.Embedding.sectR xU.1 W)

/-- The blow-up of `H` along the Latin square `a + b + c = 0` of `W`, with a copy of `G` in each
group. -/
private def blowup (H : Finset (Finset V)) (G : Finset (Finset W)) : Finset (Finset (V × W)) :=
  crossTriples H ∪ innerTriples G

variable {H : Finset (Finset V)} {G : Finset (Finset W)}

private lemma mem_crossTriples {t : Finset (V × W)} :
    t ∈ crossTriples H ↔ t.card = 3 ∧ t.image Prod.fst ∈ H ∧ ∑ p ∈ t, p.2 = 0 := by
  simp [crossTriples]

omit [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] [AddCommGroup W] in
private lemma mem_map_sectR {x : V} {U : Finset W} {p : V × W} :
    p ∈ U.map (Function.Embedding.sectR x W) ↔ p.1 = x ∧ p.2 ∈ U := by
  constructor
  · intro hp
    rw [Finset.mem_map] at hp
    obtain ⟨w, hw, rfl⟩ := hp
    simpa using hw
  · rintro ⟨h1, h2⟩
    rw [Finset.mem_map]
    exact ⟨p.2, h2, by ext <;> simp [h1]⟩

private lemma mem_blowup {t : Finset (V × W)} :
    t ∈ blowup H G ↔
      t ∈ crossTriples H ∨ ∃ x, ∃ U ∈ G, U.map (Function.Embedding.sectR x W) = t := by
  simp [blowup, innerTriples]

private lemma fst_injective_of_mem_crossTriples (hH : SetFamily.IsUniform H 3)
    {t : Finset (V × W)} (ht : t ∈ crossTriples H) ⦃p q : V × W⦄ (hp : p ∈ t) (hq : q ∈ t)
    (hpq : p.1 = q.1) : p = q := by
  rw [mem_crossTriples] at ht
  have : (t.image Prod.fst).card = t.card := by rw [hH _ ht.2.1, ht.1]
  exact card_image_iff.mp this hp hq hpq

/-- Two triples above the same triple of `H` that share two points coincide. -/
private lemma eq_of_mem_crossTriples (hH : SetFamily.IsUniform H 3) {t t' : Finset (V × W)}
    (ht : t ∈ crossTriples H) (ht' : t' ∈ crossTriples H)
    (himg : t.image Prod.fst = t'.image Prod.fst) {u v : V × W} (hut : u ∈ t) (hut' : u ∈ t')
    (hvt : v ∈ t) (hvt' : v ∈ t') (huv : u ≠ v) : t = t' := by
  have inj := fst_injective_of_mem_crossTriples hH ht
  have inj' := fst_injective_of_mem_crossTriples hH ht'
  have c := mem_crossTriples.mp ht
  have c' := mem_crossTriples.mp ht'
  obtain ⟨r, hr, hru, hrv⟩ := exists_third c.1 u v
  obtain ⟨r', hr', hru', hrv'⟩ := exists_third c'.1 u v
  have et := eq_of_card_eq_three c.1 hut hvt hr huv (Ne.symm hru) (Ne.symm hrv)
  have et' := eq_of_card_eq_three c'.1 hut' hvt' hr' huv (Ne.symm hru') (Ne.symm hrv')
  have hr1u' : r'.1 ≠ u.1 := fun h => hru' (inj' hr' hut' h)
  have hr1v' : r'.1 ≠ v.1 := fun h => hrv' (inj' hr' hvt' h)
  have hmem : r'.1 ∈ t.image Prod.fst := himg ▸ mem_image_of_mem _ hr'
  rw [et] at hmem
  simp only [image_insert, image_singleton, mem_insert, mem_singleton] at hmem
  have h1 : r'.1 = r.1 := by tauto
  have s := c.2.2
  have s' := c'.2.2
  rw [et, sum_triple _ huv (Ne.symm hru) (Ne.symm hrv)] at s
  rw [et', sum_triple _ huv (Ne.symm hru') (Ne.symm hrv')] at s'
  have h2 : r'.2 = r.2 := (add_left_cancel (s.trans s'.symm)).symm
  rw [et, et', Prod.ext h1 h2]

private lemma sparse_blowup (hH3 : SetFamily.IsUniform H 3) (hH : Sparse H) (hG : Sparse G) :
    Sparse (blowup H G) := by
  refine sparse_of_forall ?_
  intro t₁ h₁ t₂ h₂ t₃ h₃ h12 h31 h32 a b x y ha₁ ha₂ hb₁ hb₂ hab hx hy hx' hy'
  rcases mem_blowup.mp h₁ with c₁ | ⟨g₁, U₁, hU₁, rfl⟩ <;>
    rcases mem_blowup.mp h₂ with c₂ | ⟨g₂, U₂, hU₂, rfl⟩
  · -- two triples above triples of `H`
    have inj₁ := fst_injective_of_mem_crossTriples hH3 c₁
    have inj₂ := fst_injective_of_mem_crossTriples hH3 c₂
    have hT₁ : t₁.image Prod.fst ∈ H := (mem_crossTriples.mp c₁).2.1
    have hT₂ : t₂.image Prod.fst ∈ H := (mem_crossTriples.mp c₂).2.1
    have hab1 : a.1 ≠ b.1 := fun h => hab (inj₁ ha₁ hb₁ h)
    have hT12 : t₁.image Prod.fst ≠ t₂.image Prod.fst := fun h =>
      h12 (eq_of_mem_crossTriples hH3 c₁ c₂ h ha₁ ha₂ hb₁ hb₂ hab)
    have ha1 := mem_image_of_mem Prod.fst ha₁
    have ha2 := mem_image_of_mem Prod.fst ha₂
    have hb1 := mem_image_of_mem Prod.fst hb₁
    have hb2 := mem_image_of_mem Prod.fst hb₂
    have key₂ : ∀ p ∈ t₂, p.1 ∈ t₁.image Prod.fst → p ∈ t₁ := by
      intro p hp hpT
      rcases eq_or_eq_of_mem_inter (hH3 _ hT₁) (hH3 _ hT₂) hT12 ha1 ha2 hb1 hb2 hab1 hpT
        (mem_image_of_mem _ hp) with h | h
      · rw [inj₂ hp ha₂ h]; exact ha₁
      · rw [inj₂ hp hb₂ h]; exact hb₁
    have key₁ : ∀ p ∈ t₁, p.1 ∈ t₂.image Prod.fst → p ∈ t₂ := by
      intro p hp hpT
      rcases eq_or_eq_of_mem_inter (hH3 _ hT₁) (hH3 _ hT₂) hT12 ha1 ha2 hb1 hb2 hab1
        (mem_image_of_mem _ hp) hpT with h | h
      · rw [inj₁ hp ha₁ h]; exact ha₂
      · rw [inj₁ hp hb₁ h]; exact hb₂
    rcases mem_blowup.mp h₃ with c₃ | ⟨g₃, U₃, hU₃, rfl⟩
    · have inj₃ := fst_injective_of_mem_crossTriples hH3 c₃
      have hT₃ : t₃.image Prod.fst ∈ H := (mem_crossTriples.mp c₃).2.1
      have hx3 := mem_image_of_mem Prod.fst hx
      have hy3 := mem_image_of_mem Prod.fst hy
      by_cases e31 : t₃.image Prod.fst = t₁.image Prod.fst
      · have hx₁ : x ∈ t₁ := hx'.elim id fun h => key₂ x h (e31 ▸ hx3)
        have hy₁ : y ∈ t₁ := hy'.elim id fun h => key₂ y h (e31 ▸ hy3)
        by_contra hxy
        exact h31 (eq_of_mem_crossTriples hH3 c₃ c₁ e31 hx hx₁ hy hy₁ hxy)
      by_cases e32 : t₃.image Prod.fst = t₂.image Prod.fst
      · have hx₂ : x ∈ t₂ := hx'.elim (fun h => key₁ x h (e32 ▸ hx3)) id
        have hy₂ : y ∈ t₂ := hy'.elim (fun h => key₁ y h (e32 ▸ hy3)) id
        by_contra hxy
        exact h32 (eq_of_mem_crossTriples hH3 c₃ c₂ e32 hx hx₂ hy hy₂ hxy)
      exact inj₃ hx hy (hH.eq hT₁ hT₂ hT₃ hT12 e31 e32 ha1 ha2 hb1 hb2 hab1 hx3 hy3
        (hx'.imp (mem_image_of_mem _) (mem_image_of_mem _))
        (hy'.imp (mem_image_of_mem _) (mem_image_of_mem _)))
    · rw [mem_map_sectR] at hx hy
      have hxy : x.1 = y.1 := hx.1.trans hy.1.symm
      rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy'
      · exact inj₁ hx' hy' hxy
      · exact inj₂ (key₁ x hx' (hxy ▸ mem_image_of_mem _ hy')) hy' hxy
      · exact inj₁ (key₂ x hx' (hxy ▸ mem_image_of_mem _ hy')) hy' hxy
      · exact inj₂ hx' hy' hxy
  · rw [mem_map_sectR] at ha₂ hb₂
    exact absurd (fst_injective_of_mem_crossTriples hH3 c₁ ha₁ hb₁ (ha₂.1.trans hb₂.1.symm)) hab
  · rw [mem_map_sectR] at ha₁ hb₁
    exact absurd (fst_injective_of_mem_crossTriples hH3 c₂ ha₂ hb₂ (ha₁.1.trans hb₁.1.symm)) hab
  · -- two triples inside groups
    rw [mem_map_sectR] at ha₁ ha₂ hb₁ hb₂
    have hg : g₁ = g₂ := ha₁.1.symm.trans ha₂.1
    have hU12 : U₁ ≠ U₂ := fun h => h12 (by rw [h, hg])
    have hab2 : a.2 ≠ b.2 := fun h => hab (Prod.ext (ha₁.1.trans hb₁.1.symm) h)
    have fx : x.1 = g₁ := by
      rcases hx' with h | h
      · exact (mem_map_sectR.mp h).1
      · exact (mem_map_sectR.mp h).1.trans hg.symm
    have fy : y.1 = g₁ := by
      rcases hy' with h | h
      · exact (mem_map_sectR.mp h).1
      · exact (mem_map_sectR.mp h).1.trans hg.symm
    rcases mem_blowup.mp h₃ with c₃ | ⟨g₃, U₃, hU₃, rfl⟩
    · exact fst_injective_of_mem_crossTriples hH3 c₃ hx hy (fx.trans fy.symm)
    · rw [mem_map_sectR] at hx hy
      have hg3 : g₃ = g₁ := hx.1.symm.trans fx
      have hU31 : U₃ ≠ U₁ := fun h => h31 (by rw [h, hg3])
      have hU32 : U₃ ≠ U₂ := fun h => h32 (by rw [h, hg3, hg])
      have hx2 : x.2 ∈ U₁ ∨ x.2 ∈ U₂ :=
        hx'.imp (fun h => (mem_map_sectR.mp h).2) (fun h => (mem_map_sectR.mp h).2)
      have hy2 : y.2 ∈ U₁ ∨ y.2 ∈ U₂ :=
        hy'.imp (fun h => (mem_map_sectR.mp h).2) (fun h => (mem_map_sectR.mp h).2)
      exact Prod.ext (fx.trans fy.symm)
        (hG.eq hU₁ hU₂ hU₃ hU12 hU31 hU32 ha₁.2 ha₂.2 hb₁.2 hb₂.2 hab2 hx.2 hy.2 hx2 hy2)

private lemma isUniform_blowup (hG : SetFamily.IsUniform G 3) :
    SetFamily.IsUniform (blowup H G) 3 := by
  intro t ht
  rcases mem_blowup.mp ht with c | ⟨x, U, hU, rfl⟩
  · exact (mem_crossTriples.mp c).1
  · rw [card_map]; exact hG U hU

omit [Fintype W] [AddCommGroup W] in
private lemma card_innerTriples (hG : SetFamily.IsUniform G 3) :
    (innerTriples (V := V) G).card = Fintype.card V * G.card := by
  rw [innerTriples, card_image_of_injOn, card_product, card_univ]
  rintro ⟨x, U⟩ hxU ⟨x', U'⟩ hxU' h
  simp only [coe_product, coe_univ, Set.mem_prod, Set.mem_univ, mem_coe, true_and]
    at hxU hxU'
  simp only at h
  obtain ⟨w, hw⟩ : U.Nonempty := card_pos.mp (by rw [hG U hxU]; norm_num)
  have hx : x = x' := by
    have hmem : (x, w) ∈ U'.map (Function.Embedding.sectR x' W) :=
      h ▸ mem_map_sectR.mpr ⟨rfl, hw⟩
    exact (mem_map_sectR.mp hmem).1
  subst hx
  rw [Finset.map_inj] at h
  rw [h]

private lemma disjoint_crossTriples_innerTriples (hH : SetFamily.IsUniform H 3) :
    Disjoint (crossTriples (W := W) H) (innerTriples G) := by
  rw [disjoint_left]
  intro t ht ht'
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    one_lt_card_iff.mp (by rw [(mem_crossTriples.mp ht).1]; norm_num : 1 < t.card)
  simp only [innerTriples, mem_image, mem_product, mem_univ, true_and] at ht'
  obtain ⟨⟨x, U⟩, hU, rfl⟩ := ht'
  exact hpq (fst_injective_of_mem_crossTriples hH ht hp hq
    ((mem_map_sectR.mp hp).1.trans (mem_map_sectR.mp hq).1.symm))

private lemma card_le_card_crossTriples (hH : SetFamily.IsUniform H 3) :
    H.card * Fintype.card W ^ 2 ≤ (crossTriples (W := W) H).card := by
  let fibre : Finset V → Finset (Finset (V × W)) := fun T =>
    (crossTriples H).filter fun t => t.image Prod.fst = T
  have hdisj : (H : Set (Finset V)).PairwiseDisjoint fibre := by
    intro T _ T' _ hTT'
    refine disjoint_left.mpr fun t ht ht' => ?_
    simp only [fibre, mem_filter] at ht ht'
    exact hTT' (ht.2.symm.trans ht'.2)
  have hsub : H.biUnion fibre ⊆ crossTriples H := by
    intro t ht
    simp only [mem_biUnion, fibre, mem_filter] at ht
    obtain ⟨_, _, h, _⟩ := ht
    exact h
  have hover : ∀ T ∈ H, Fintype.card W ^ 2 ≤ (fibre T).card := by
    intro T hT
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp (hH T hT)
    let f : W × W → Finset (V × W) := fun ab => {(x, ab.1), (y, ab.2), (z, -(ab.1 + ab.2))}
    have hle : (univ : Finset (W × W)).card ≤ (fibre {x, y, z}).card := by
      apply card_le_card_of_injOn f
      · intro ab _
        have hne1 : (x, ab.1) ≠ (y, ab.2) := fun h => hxy (congrArg Prod.fst h)
        have hne2 : (x, ab.1) ≠ (z, -(ab.1 + ab.2)) := fun h => hxz (congrArg Prod.fst h)
        have hne3 : (y, ab.2) ≠ (z, -(ab.1 + ab.2)) := fun h => hyz (congrArg Prod.fst h)
        have himg : (f ab).image Prod.fst = {x, y, z} := by
          simp [f, image_insert]
        rw [mem_coe, mem_filter, mem_crossTriples]
        refine ⟨⟨card_eq_three.mpr ⟨_, _, _, hne1, hne2, hne3, rfl⟩, himg ▸ hT, ?_⟩, himg⟩
        simp only [f]
        rw [sum_triple _ hne1 hne2 hne3]
        exact add_neg_cancel _
      · intro ab _ ab' _ h
        simp only [f] at h
        have h1 : (x, ab.1) ∈ ({(x, ab'.1), (y, ab'.2), (z, -(ab'.1 + ab'.2))} :
            Finset (V × W)) := h ▸ by simp
        have h2 : (y, ab.2) ∈ ({(x, ab'.1), (y, ab'.2), (z, -(ab'.1 + ab'.2))} :
            Finset (V × W)) := h ▸ by simp
        simp only [mem_insert, mem_singleton, Prod.mk.injEq] at h1 h2
        refine Prod.ext ?_ ?_
        · rcases h1 with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
          · exact h1
          · exact absurd h1 hxy
          · exact absurd h1 hxz
        · rcases h2 with ⟨h2, -⟩ | ⟨-, h2⟩ | ⟨h2, -⟩
          · exact absurd h2.symm hxy
          · exact h2
          · exact absurd h2 hyz
    simpa [card_univ, Fintype.card_prod, sq] using hle
  calc H.card * Fintype.card W ^ 2 = ∑ _T ∈ H, Fintype.card W ^ 2 := by
        rw [sum_const, smul_eq_mul]
    _ ≤ ∑ T ∈ H, (fibre T).card := sum_le_sum hover
    _ = (H.biUnion fibre).card := (card_biUnion hdisj).symm
    _ ≤ (crossTriples H).card := card_le_card hsub

private lemma card_blowup (hH : SetFamily.IsUniform H 3) (hG : SetFamily.IsUniform G 3) :
    H.card * Fintype.card W ^ 2 + Fintype.card V * G.card ≤ (blowup H G).card := by
  rw [blowup, card_union_of_disjoint (disjoint_crossTriples_innerTriples hH),
    card_innerTriples hG]
  exact Nat.add_le_add_right (card_le_card_crossTriples hH) _

end Blowup

/-- Ten triples on eight points: three pairs of triples `{a, b, 0}, {a, b, 1}` and four
edge-disjoint triangles among the remaining pairs. -/
private def baseSystem : Finset (Finset (ZMod 8)) :=
  {{0, 2, 3}, {1, 2, 3}, {0, 4, 5}, {1, 4, 5}, {0, 6, 7}, {1, 6, 7},
    {2, 4, 6}, {2, 5, 7}, {3, 4, 7}, {3, 5, 6}}

set_option maxRecDepth 100000 in
private lemma card_baseSystem : baseSystem.card = 10 := by decide

set_option maxRecDepth 100000 in
private lemma isUniform_baseSystem : SetFamily.IsUniform baseSystem 3 := by
  rw [SetFamily.isUniform_iff]; decide

set_option maxRecDepth 100000 in
private lemma sparse_baseSystem : Sparse baseSystem := by decide +kernel

/-- `720` triples on `64` points. -/
private def level₁ : Finset (Finset (ZMod 8 × ZMod 8)) := blowup baseSystem baseSystem

private lemma isUniform_level₁ : SetFamily.IsUniform level₁ 3 :=
  isUniform_blowup isUniform_baseSystem

private lemma sparse_level₁ : Sparse level₁ :=
  sparse_blowup isUniform_baseSystem sparse_baseSystem sparse_baseSystem

private lemma card_level₁ : 720 ≤ level₁.card := by
  have := card_blowup (V := ZMod 8) (W := ZMod 8) isUniform_baseSystem isUniform_baseSystem
  rw [card_baseSystem, ZMod.card] at this
  exact this

private lemma bddAbove_exSingle (k n : ℕ) :
    BddAbove {m | ∃ E : Finset (Finset (Fin n)), SetFamily.IsUniform E 3 ∧
      ¬ SetFamily.ContainsSubgraph E k (k - 2) ∧ E.card = m} := by
  refine ⟨2 ^ n, ?_⟩
  rintro _ ⟨E, -, -, rfl⟩
  calc E.card ≤ Fintype.card (Finset (Fin n)) := card_le_univ E
    _ = 2 ^ n := by simp [Fintype.card_finset]

/-- For every `m` there is a `3`-uniform hypergraph on `64 m` vertices with at least `720 m²`
triples in which no `5` vertices span `3` triples. -/
private lemma le_exSingle_five (m : ℕ) : 720 * m ^ 2 ≤ exSingle 5 (64 * m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have : NeZero m := ⟨hm.ne'⟩
  let P : Finset (Finset ((ZMod 8 × ZMod 8) × ZMod m)) := blowup level₁ ∅
  have hempty : SetFamily.IsUniform (∅ : Finset (Finset (ZMod m))) 3 := by
    simp [SetFamily.IsUniform]
  have hP3 : SetFamily.IsUniform P 3 := isUniform_blowup hempty
  have hPs : Sparse P := sparse_blowup isUniform_level₁ sparse_level₁ (by simp [Sparse])
  have hPc : 720 * m ^ 2 ≤ P.card := by
    have := card_blowup isUniform_level₁ hempty (V := ZMod 8 × ZMod 8) (W := ZMod m)
    rw [ZMod.card] at this
    simp only [card_empty, mul_zero, add_zero] at this
    exact (Nat.mul_le_mul_right _ card_level₁).trans this
  have hcard : Fintype.card ((ZMod 8 × ZMod 8) × ZMod m) = 64 * m := by
    simp only [Fintype.card_prod, ZMod.card]
  let e := Fintype.equivFinOfCardEq hcard
  let E := P.map (mapEmbedding e.toEmbedding).toEmbedding
  have hE : ¬ SetFamily.ContainsSubgraph E 5 (5 - 2) :=
    not_containsSubgraph_of_good (good_map _ (good_of_sparse hP3 hPs))
  calc 720 * m ^ 2 ≤ P.card := hPc
    _ = E.card := (card_map _).symm
    _ ≤ exSingle 5 (64 * m) :=
      le_csSup (bddAbove_exSingle 5 _) ⟨E, isUniform_map _ hP3, hE, rfl⟩

/--
**Erdős Problem 1076 fails as worded.** For $k, n \in \mathbb{N}$ let $\mathcal{F}_k$ be the family
of $3$-graphs with $k$ vertices and $k - 2$ edges, and let $\mathrm{ex}_3(n, \mathcal{F}_k)$ be the
largest number of triples in a $3$-uniform hypergraph on $n$ vertices that contains no member of
$\mathcal{F}_k$, that is, in which no $k$ vertices span $k - 2$ or more triples. It is not true
that for every $k \ge 5$, $\mathrm{ex}_3(n, \mathcal{F}_k) / n^2 \to 1/6$ as $n \to \infty$.

Already $k = 5$ fails: Glock proved that the largest triple system on $n$ vertices with no five
vertices spanning three triples has $(1 + o(1)) n^2 / 5$ triples, so
$\mathrm{ex}_3(n, \mathcal{F}_5) / n^2 \to 1/5$; his §1 states this as the answer to whether $1/6$
is sharp for every $k$.

Source: T. F. Bloom, Erdős Problems, Problem #1076, https://www.erdosproblems.com/1076 (status
PROVED); resolution: S. Glock, Triple systems with no three triples spanning at most five points,
Bull. Lond. Math. Soc. 51 (2019), 230-236, abstract and Theorem 2: lim n⁻² f⁽³⁾(n; 5, 3) = 1/5,
where f⁽³⁾(n; k, s) is the largest number of triples on n points containing no k points spanning s
triples; §1 poses the question whether the lower bound lim inf n⁻² f⁽³⁾(n; k, k - 2) ≥ 1/6 is
sharp in general, and Theorem 2 shows it is not for k = 5 (arXiv:1809.02100),
https://arxiv.org/abs/1809.02100.
-/
theorem singleFamilyAsymptotic_refuted : ¬ singleFamilyAsymptotic := by
  intro h
  have hg : Tendsto (fun m : ℕ => 64 * (m + 1)) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => by omega⟩
  have hc := (h 5 le_rfl).comp hg
  have hbound : ∀ m : ℕ, (45 / 256 : ℝ) ≤
      ((fun n : ℕ => (exSingle 5 n : ℝ) / (n : ℝ) ^ 2) ∘ fun m : ℕ => 64 * (m + 1)) m := by
    intro m
    have hle : ((720 * (m + 1) ^ 2 : ℕ) : ℝ) ≤ (exSingle 5 (64 * (m + 1)) : ℝ) := by
      exact_mod_cast le_exSingle_five (m + 1)
    simp only [Function.comp_apply]
    rw [le_div_iff₀ (by positivity)]
    push_cast at hle ⊢
    nlinarith
  have := ge_of_tendsto hc (Eventually.of_forall hbound)
  norm_num at this

end MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted
