/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Triple systems with few triples on every small vertex set (Erdős Problem 1076)

Erdős Problem 1076: let `k ≥ 5` and let `𝓕_k` be the family of all `3`-uniform hypergraphs with
`k` vertices and `k - 2` edges. Is it true that `ex₃(n, 𝓕_k) ∼ n² / 6`?
-/

module

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import MathlibExt.Combinatorics.SetFamily.UniformHypergraph
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

@[expose] public section

namespace MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted

/-!
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
-/

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


/-! The construction uses the gadget `H₂` and its four triples from Glock,
[Triple systems with no three triples spanning at most five points, §2.2]
(https://arxiv.org/html/1809.02100v1#S2.SS2). Rather than use a general graph packing theorem,
we label its vertices in `ZMod 23` so the oriented supporting pairs have distinct differences.
The cyclic translates and an affine lift then give density `4 / 23` along an unbounded sequence. -/

private abbrev F := ZMod 23

private def coreBlock (i : Fin 2) : Finset F :=
  ![{0, 1, 3, 17}, {0, 1, 5, 13}] i

private def coreTriple (i : Fin 4) : Finset F :=
  ![{0, 3, 17}, {1, 3, 17}, {0, 5, 13}, {1, 5, 13}] i

private def support : Finset (F × F) :=
  ((coreBlock 0 ×ˢ coreBlock 0) ∪ (coreBlock 1 ×ˢ coreBlock 1)).filter fun e => e.1 ≠ e.2

private def difference (e : F × F) : F := e.2 - e.1

private theorem support_card : support.card = 22 := by decide +kernel

private theorem support_differences : support.image difference = Finset.univ.erase 0 := by
  decide +kernel

private theorem difference_injOn : Set.InjOn difference (↑support : Set (F × F)) := by
  apply Finset.card_image_iff.mp
  rw [support_differences, support_card]
  decide +kernel

private theorem mem_support {i : Fin 2} {a b : F} (ha : a ∈ coreBlock i)
    (hb : b ∈ coreBlock i) (hab : a ≠ b) : (a, b) ∈ support := by
  have h : (a, b) ∈ coreBlock i ×ˢ coreBlock i := Finset.mem_product.mpr ⟨ha, hb⟩
  fin_cases i <;> simp_all [support]

private theorem coreTriple_card : ∀ i, (coreTriple i).card = 3 := by decide +kernel

private theorem coreTriple_injective : Function.Injective coreTriple := by decide +kernel

private theorem coreTriple_supported : ∀ i, ∃ p, coreTriple i ⊆ coreBlock p := by
  decide +kernel

private theorem coreTriple_union_supported : ∀ i j, i ≠ j →
    2 ≤ (coreTriple i ∩ coreTriple j).card →
    ∃ p, coreTriple i ∪ coreTriple j ⊆ coreBlock p := by
  decide +kernel

private theorem coreTriple_union_card : ∀ i j, i ≠ j →
    4 ≤ (coreTriple i ∪ coreTriple j).card := by
  decide +kernel

private theorem coreTriple_three_card : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    6 ≤ (coreTriple i ∪ coreTriple j ∪ coreTriple k).card := by
  decide +kernel

private abbrev Vertex (d : ℕ) := F × (Fin d → F)

private abbrev Gadget (d : ℕ) := F × (Fin d → F) × (Fin d → F)

private def lift {d : ℕ} (g : Gadget d) : F ↪ Vertex d where
  toFun i := (g.1 + i, fun j => g.2.1 j + i * g.2.2 j)
  inj' _ _ h := add_left_cancel (congrArg Prod.fst h)

/-- The first coordinates recover the oriented pair of labels and the translate. The second
coordinates at those two labels then recover the affine map, coordinate by coordinate. -/
private theorem gadget_eq_of_pair {d : ℕ} {g h : Gadget d} {a b a' b' : F}
    (hg : (a, b) ∈ support) (hh : (a', b') ∈ support)
    (hx : lift g a = lift h a') (hy : lift g b = lift h b') : g = h := by
  have hx₁ : g.1 + a = h.1 + a' := congrArg Prod.fst hx
  have hy₁ : g.1 + b = h.1 + b' := congrArg Prod.fst hy
  have hd : difference (a, b) = difference (a', b') := by
    change b - a = b' - a'
    linear_combination hy₁ - hx₁
  have hpair := difference_injOn hg hh hd
  have ha : a = a' := congrArg Prod.fst hpair
  have hb : b = b' := congrArg Prod.snd hpair
  subst a'
  subst b'
  have hs := add_right_cancel hx₁
  have hab : a ≠ b := (Finset.mem_filter.mp hg).2
  have : Fact (Nat.Prime 23) := ⟨by decide +kernel⟩
  have hv (j : Fin d) : g.2.2 j = h.2.2 j := by
    have hx₂ : g.2.1 j + a * g.2.2 j = h.2.1 j + a * h.2.2 j :=
      congrArg (fun x => x.2 j) hx
    have hy₂ : g.2.1 j + b * g.2.2 j = h.2.1 j + b * h.2.2 j :=
      congrArg (fun x => x.2 j) hy
    apply mul_left_cancel₀ (sub_ne_zero.mpr hab.symm : b - a ≠ 0)
    linear_combination hy₂ - hx₂
  refine Prod.ext hs (Prod.ext (funext fun j => ?_) (funext hv))
  have hx₂ : g.2.1 j + a * g.2.2 j = h.2.1 j + a * h.2.2 j :=
    congrArg (fun x => x.2 j) hx
  rw [hv j] at hx₂
  exact add_right_cancel hx₂

private def liftedBlock {d : ℕ} (g : Gadget d) (p : Fin 2) : Finset (Vertex d) :=
  (coreBlock p).map (lift g)

private def liftedTriple {d : ℕ} (p : Gadget d × Fin 4) : Finset (Vertex d) :=
  (coreTriple p.2).map (lift p.1)

private theorem liftedTriple_card {d : ℕ} (p : Gadget d × Fin 4) : (liftedTriple p).card = 3 := by
  rw [liftedTriple, Finset.card_map, coreTriple_card]

private theorem liftedTriple_supported {d : ℕ} (p : Gadget d × Fin 4) :
    ∃ b, liftedTriple p ⊆ liftedBlock p.1 b := by
  obtain ⟨b, hb⟩ := coreTriple_supported p.2
  exact ⟨b, Finset.map_subset_map.mpr hb⟩

private theorem gadget_eq_of_overlap {d : ℕ} {g h : Gadget d} {p q : Fin 2}
    {X Y : Finset (Vertex d)} (hX : X ⊆ liftedBlock g p) (hY : Y ⊆ liftedBlock h q)
    (hXY : 2 ≤ (X ∩ Y).card) : g = h := by
  obtain ⟨x, hx, y, hy, hne⟩ := Finset.one_lt_card.mp hXY
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp (hX (Finset.mem_inter.mp hx).1)
  obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp (hX (Finset.mem_inter.mp hy).1)
  obtain ⟨a', ha', hxa⟩ := Finset.mem_map.mp (hY (Finset.mem_inter.mp hx).2)
  obtain ⟨b', hb', hyb⟩ := Finset.mem_map.mp (hY (Finset.mem_inter.mp hy).2)
  exact gadget_eq_of_pair (mem_support ha hb (fun e => hne (congrArg (lift g) e)))
    (mem_support ha' hb' (fun e => hne (hxa.symm.trans ((congrArg (lift h) e).trans hyb))))
    hxa.symm hyb.symm

private theorem liftedTriple_injective {d : ℕ} :
    Function.Injective (liftedTriple (d := d)) := by
  intro ⟨g, i⟩ ⟨h, j⟩ e
  obtain ⟨b, hb⟩ := liftedTriple_supported (g, i)
  obtain ⟨c, hc⟩ := liftedTriple_supported (h, j)
  have hoverlap : 2 ≤ (liftedTriple (g, i) ∩ liftedTriple (h, j)).card := by
    rw [← e, Finset.inter_self, liftedTriple_card]
    decide
  obtain rfl : g = h := gadget_eq_of_overlap hb hc hoverlap
  have hij : i = j := coreTriple_injective (Finset.map_injective _ e)
  rw [hij]

private def family (d : ℕ) : Finset (Finset (Vertex d)) :=
  Finset.univ.map ⟨liftedTriple, liftedTriple_injective⟩

private theorem family_card (d : ℕ) : (family d).card = 4 * 23 * (23 ^ d) ^ 2 := by
  simp only [family, Finset.card_map, Finset.card_univ, Fintype.card_prod, ZMod.card,
    Fintype.card_fun, Fintype.card_fin]
  ring

private theorem family_uniform (d : ℕ) : SetFamily.IsUniform (family d) 3 := by
  intro e he
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp he
  exact liftedTriple_card p

/-- Among three triples in at most five vertices, some pair shares two vertices. -/
private theorem pair_overlap {α : Type*} [DecidableEq α] {A B C : Finset α}
    (hA : A.card = 3) (hB : B.card = 3) (hC : C.card = 3)
    (hU : (A ∪ B ∪ C).card ≤ 5) :
    2 ≤ (A ∩ B).card ∨ 2 ≤ (A ∩ C).card ∨ 2 ≤ (B ∩ C).card := by
  have h₁ := Finset.card_union_add_card_inter A B
  have h₂ := Finset.card_union_add_card_inter (A ∪ B) C
  have h₃ : ((A ∪ B) ∩ C).card ≤ (A ∩ C).card + (B ∩ C).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  omega

private theorem small_union_contradiction {d : ℕ} {p q r : Gadget d × Fin 4}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpair : 2 ≤ (liftedTriple p ∩ liftedTriple q).card)
    (hU : (liftedTriple p ∪ liftedTriple q ∪ liftedTriple r).card ≤ 5) : False := by
  rcases p with ⟨g, i⟩
  rcases q with ⟨h, j⟩
  rcases r with ⟨k, l⟩
  obtain ⟨b, hb⟩ := liftedTriple_supported (g, i)
  obtain ⟨c, hc⟩ := liftedTriple_supported (h, j)
  obtain rfl : g = h := gadget_eq_of_overlap hb hc hpair
  have hij : i ≠ j := fun e => hpq (by rw [e])
  have hi : 2 ≤ (coreTriple i ∩ coreTriple j).card := by
    simpa only [liftedTriple, ← Finset.map_inter, Finset.card_map] using hpair
  obtain ⟨b', hb'⟩ := coreTriple_union_supported i j hij hi
  have hblock : liftedTriple (g, i) ∪ liftedTriple (g, j) ⊆ liftedBlock g b' := by
    rw [liftedTriple, liftedTriple, liftedBlock, ← Finset.map_union]
    exact Finset.map_subset_map.mpr hb'
  have h₁ : 4 ≤ (liftedTriple (g, i) ∪ liftedTriple (g, j)).card := by
    rw [liftedTriple, liftedTriple, ← Finset.map_union, Finset.card_map]
    exact coreTriple_union_card i j hij
  have h₂ : 2 ≤ ((liftedTriple (g, i) ∪ liftedTriple (g, j)) ∩ liftedTriple (k, l)).card := by
    have he := Finset.card_union_add_card_inter
      (liftedTriple (g, i) ∪ liftedTriple (g, j)) (liftedTriple (k, l))
    rw [liftedTriple_card] at he
    omega
  obtain ⟨c', hc'⟩ := liftedTriple_supported (k, l)
  obtain rfl : g = k := gadget_eq_of_overlap hblock hc' h₂
  have hil : i ≠ l := fun e => hpr (by rw [e])
  have hjl : j ≠ l := fun e => hqr (by rw [e])
  have h₃ := coreTriple_three_card i j l hij hil hjl
  rw [liftedTriple, liftedTriple, liftedTriple, ← Finset.map_union, ← Finset.map_union,
    Finset.card_map] at hU
  change (coreTriple i ∪ coreTriple j ∪ coreTriple l).card ≤ 5 at hU
  omega

private theorem family_three_span {d : ℕ} {A B C : Finset (Vertex d)}
    (hA : A ∈ family d) (hB : B ∈ family d) (hC : C ∈ family d)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) : 6 ≤ (A ∪ B ∪ C).card := by
  obtain ⟨p, -, rfl⟩ := Finset.mem_map.mp hA
  obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hB
  obtain ⟨r, -, rfl⟩ := Finset.mem_map.mp hC
  have hpq : p ≠ q := fun e => hAB (congrArg liftedTriple e)
  have hpr : p ≠ r := fun e => hAC (congrArg liftedTriple e)
  have hqr : q ≠ r := fun e => hBC (congrArg liftedTriple e)
  by_contra! hU
  change (liftedTriple p ∪ liftedTriple q ∪ liftedTriple r).card < 6 at hU
  have hbound : (liftedTriple p ∪ liftedTriple q ∪ liftedTriple r).card ≤ 5 := by omega
  obtain hp | hp | hp := pair_overlap (liftedTriple_card p) (liftedTriple_card q)
    (liftedTriple_card r) hbound
  · exact small_union_contradiction hpq hpr hqr hp hbound
  · apply small_union_contradiction hpr hpq hqr.symm hp
    simpa only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hbound
  · apply small_union_contradiction hqr hpq.symm hpr.symm hp
    simpa only [Finset.union_assoc, Finset.union_comm, Finset.union_left_comm] using hbound

private theorem vertex_card (d : ℕ) : Fintype.card (Vertex d) = 23 ^ (d + 1) := by
  simp only [Fintype.card_prod, ZMod.card, Fintype.card_fun, Fintype.card_fin, pow_succ, mul_comm]

private theorem exists_family (d : ℕ) :
    ∃ E : Finset (Finset (Fin (23 ^ (d + 1)))),
      SetFamily.IsUniform E 3 ∧ ¬ SetFamily.ContainsSubgraph E 5 3 ∧
        E.card = 4 * 23 * (23 ^ d) ^ 2 := by
  let e := (Fintype.equivFin (Vertex d)).trans (finCongr (vertex_card d))
  let f : Finset (Vertex d) ↪ Finset (Fin (23 ^ (d + 1))) :=
    ⟨Finset.map e.toEmbedding, Finset.map_injective _⟩
  refine ⟨(family d).map f, ?_, ?_, by rw [Finset.card_map, family_card]⟩
  · intro x hx
    obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp hx
    exact (Finset.card_map e.toEmbedding).trans (family_uniform d A hA)
  · intro ⟨S, hS, hcard⟩
    obtain ⟨u, hu, huc⟩ := Finset.exists_subset_card_eq hcard
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp huc
    have hm {a : Finset (Fin (23 ^ (d + 1)))} (ha : a ∈ ({x, y, z} : Finset _)) :=
      Finset.mem_filter.mp (hu ha)
    obtain ⟨A, hA, rfl⟩ := Finset.mem_map.mp (hm (by simp : x ∈ ({x, y, z} : Finset _))).1
    obtain ⟨B, hB, rfl⟩ := Finset.mem_map.mp (hm (by simp : y ∈ ({f A, y, z} : Finset _))).1
    obtain ⟨C, hC, rfl⟩ := Finset.mem_map.mp (hm (by simp : z ∈ ({f A, f B, z} : Finset _))).1
    have hspan := family_three_span hA hB hC
      (fun h => hxy (congrArg f h)) (fun h => hxz (congrArg f h)) (fun h => hyz (congrArg f h))
    have hsub : f A ∪ f B ∪ f C ⊆ S :=
      Finset.union_subset (Finset.union_subset (hm (by simp)).2 (hm (by simp)).2) (hm (by simp)).2
    have hbound := Finset.card_le_card hsub
    change ((A.map e.toEmbedding) ∪ (B.map e.toEmbedding) ∪ (C.map e.toEmbedding)).card ≤ _
      at hbound
    rw [← Finset.map_union, ← Finset.map_union, Finset.card_map, hS] at hbound
    omega

private theorem exSingle_lower (d : ℕ) : 4 * 23 * (23 ^ d) ^ 2 ≤ exSingle 5 (23 ^ (d + 1)) := by
  obtain ⟨E, hE, hfree, hcard⟩ := exists_family d
  unfold exSingle
  refine le_csSup ?_ ?_
  · refine ⟨Fintype.card (Finset (Fin (23 ^ (d + 1)))), ?_⟩
    rintro _ ⟨A, -, -, rfl⟩
    exact Finset.card_le_univ A
  · exact ⟨E, hE, hfree, hcard⟩

private theorem cofinal : Tendsto (fun d : ℕ => (23 : ℕ) ^ (d + 1)) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro d
  change d ≤ (23 : ℕ) ^ (d + 1)
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ]
    have hpos : 1 ≤ (23 : ℕ) ^ (d + 1) := Nat.one_le_pow _ _ (by decide)
    omega

private theorem density_lower (d : ℕ) :
    (4 / 23 : ℝ) ≤ (exSingle 5 (23 ^ (d + 1)) : ℝ) / ((23 ^ (d + 1) : ℕ) : ℝ) ^ 2 := by
  have hpos : 0 < (((23 ^ (d + 1) : ℕ) : ℝ) ^ 2) := by positivity
  apply (le_div_iff₀ hpos).2
  calc
    (4 / 23 : ℝ) * ((23 ^ (d + 1) : ℕ) : ℝ) ^ 2 =
        ((4 * 23 * (23 ^ d) ^ 2 : ℕ) : ℝ) := by
      push_cast
      rw [pow_succ]
      ring
    _ ≤ (exSingle 5 (23 ^ (d + 1)) : ℝ) := by exact_mod_cast exSingle_lower d

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
public theorem singleFamilyAsymptotic_refuted : ¬ singleFamilyAsymptotic := by
  intro h
  have hsub := (h 5 le_rfl).comp cofinal
  have hle : (4 / 23 : ℝ) ≤ 1 / 6 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hsub density_lower
  norm_num at hle

end MathlibExt.Combinatorics.LocallySparseTripleSystemErdosProblem1076Wanted
