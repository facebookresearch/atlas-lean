/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/ErdosProblems/760.lean` (Formal Conjectures):
Copyright The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: The Formal Conjectures Authors.
Adapted portions: the proposition and the statement that it holds.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import MathlibExt.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import MathlibExt.Combinatorics.SimpleGraph.DegeneracyColoring
import MathlibExt.Probability.Combinatorics.RandomSubset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Subgraphs of large cochromatic number

`conjecture_holds` proves the Alon–Krivelevich–Sudakov bound and its square-root consequence.
In a minimum cocoloring of an `m`-chromatic graph, the clique classes cover at most `m²` vertices.
On those vertices, independently retain edges with probability one half. A union bound gives a
choice for which each homogeneous set induces a graph of degeneracy `O(log m)` in the original
graph. Properly coloring these sets and reusing the original independent classes gives the bound.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosProblem760Wanted

/-- **Erdős Problem 760: subgraphs of large cochromatic number.** The proposition asserts two
statements. First, there is a real number $c > 0$ such that for every simple graph $G$ on a finite
vertex set with chromatic number $m$ there are a subgraph $H$ of $G$ and a natural number $k$ with
$k \ge c\,m / \log m$ such that the cochromatic number of $H$ is at least $k$. Second, there is a
real number $c > 0$ with the same property for the bound $k \ge c\sqrt{m / \log m}$.

Here $\log$ is the natural logarithm, with the conventions $\log 0 = 0$ and $x / 0 = 0$, so both
bounds are $0$ when $m \le 1$. The second statement is the Erdős–Gimbel form. -/
def conjecture : Prop :=
  (∃ c > (0 : ℝ), ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
    G.chromaticNumber = (m : ℕ∞) →
      ∃ H : G.Subgraph, ∃ k : ℕ, ((k : ℕ∞) ≤ H.coe.cochromaticNumber) ∧
        (c * (m : ℝ) / Real.log (m : ℝ) ≤ (k : ℝ))) ∧
  (∃ c > (0 : ℝ), ∀ (V : Type*) [Finite V] (G : SimpleGraph V) (m : ℕ),
    G.chromaticNumber = (m : ℕ∞) →
      ∃ H : G.Subgraph, ∃ k : ℕ, ((k : ℕ∞) ≤ H.coe.cochromaticNumber) ∧
        (c * Real.sqrt ((m : ℝ) / Real.log (m : ℝ)) ≤ (k : ℝ)))

section

open SimpleGraph Finset MeasureTheory unitInterval
open MathlibExt.Probability.Combinatorics.RandomSubset

variable {V : Type*}

/-- Independently color the ground set red and blue. A union bound by subset size
gives a coloring that splits every sufficiently large family of prescribed edges. -/
private lemma split_dense_sets {E : Type*} [Fintype V] [Finite E]
    (edges : Finset V → Finset E) (d : ℕ) (hd : 2 * (Fintype.card V + 1) < 2 ^ d) :
    ∃ ω : E → Bool, ∀ s : Finset V, d * (s.card + 1) ≤ (edges s).card →
      ω ∉ containsEvent (edges s) ∪ avoidEvent (edges s) := by
  classical
  let := Fintype.ofFinite E
  let n := Fintype.card V
  let half : I := ⟨1 / 2, by norm_num, by norm_num⟩
  let μ := randomSubsetLaw (fun _ : E => half)
  let family (j : ℕ) := ((univ : Finset V).powersetCard j).filter
    fun s => d * (j + 1) ≤ (edges s).card
  let mono (s : Finset V) := containsEvent (edges s) ∪ avoidEvent (edges s)
  let bad (j : ℕ) := ⋃ s ∈ family j, mono s
  have hhalf : (half : ℝ) = 1 / 2 := rfl
  have hmono (j : ℕ) (s : Finset V) (hs : s ∈ family j) :
      μ.real (mono s) ≤ 2 / (2 : ℝ) ^ (d * (j + 1)) := by
    have hsize := (mem_filter.mp hs).2
    have hp : (2 : ℝ) ^ (d * (j + 1)) ≤ 2 ^ (edges s).card :=
      pow_le_pow_right₀ (by norm_num) hsize
    calc
      μ.real (mono s) ≤ μ.real (containsEvent (edges s)) + μ.real (avoidEvent (edges s)) :=
        measureReal_union_le _ _
      _ = 2 / 2 ^ (edges s).card := by
        rw [randomSubsetLaw_real_containsEvent, randomSubsetLaw_real_avoidEvent,
          prod_const, prod_const, hhalf, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
          one_div, inv_pow, ← two_mul, div_eq_mul_inv]
      _ ≤ _ := by gcongr
  have hfamily (j : ℕ) : (family j).card ≤ n ^ j :=
    (card_filter_le _ _).trans ((card_powersetCard ..) ▸ Nat.choose_le_pow _ _)
  have hn : (n : ℝ) ≤ 2 ^ d := by exact_mod_cast (by dsimp [n]; omega : n ≤ 2 ^ d)
  have hbad (j : ℕ) : μ.real (bad j) ≤ 2 / (2 : ℝ) ^ d := by
    calc
      μ.real (bad j) ≤ ∑ s ∈ family j, μ.real (mono s) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _s ∈ family j, 2 / (2 : ℝ) ^ (d * (j + 1)) := sum_le_sum (hmono j)
      _ ≤ (2 ^ d : ℝ) ^ j * (2 / 2 ^ (d * (j + 1))) := by
        rw [sum_const, nsmul_eq_mul]
        gcongr
        exact (show ((family j).card : ℝ) ≤ (n : ℝ) ^ j by exact_mod_cast hfamily j).trans
          (pow_le_pow_left₀ (by positivity) hn j)
      _ = _ := by rw [pow_mul, pow_succ]; field_simp
  let allBad := ⋃ j ∈ range (n + 1), bad j
  have hall : μ.real allBad < 1 := calc
    μ.real allBad ≤ ∑ j ∈ range (n + 1), μ.real (bad j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ range (n + 1), 2 / (2 : ℝ) ^ d := sum_le_sum fun j _ => hbad j
    _ < 1 := by
      simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      rw [← mul_div_assoc, div_lt_one (by positivity)]
      simpa [mul_comm, n] using (show (2 : ℝ) * (Fintype.card V + 1) < 2 ^ d by exact_mod_cast hd)
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ allBad := by
    by_contra! h
    rw [Set.eq_univ_of_forall h, probReal_univ] at hall
    exact lt_irrefl _ hall
  refine ⟨ω, fun s hs h => ?_⟩
  have hj : s.card ∈ range (n + 1) := mem_range.mpr (Nat.lt_succ_of_le (card_le_univ s))
  have hmem : s ∈ family s.card :=
    mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _, rfl⟩, hs⟩
  exact hω (Set.mem_biUnion hj (Set.mem_biUnion hmem h))

/-- The degree-sum formula turns sparsity on every subset into degeneracy. -/
private lemma degenerate_of_sparse [Finite V] (G : SimpleGraph V) (U : Set V) (d : ℕ)
    [DecidableRel G.Adj]
    (hs : ∀ (s : Finset V), (s : Set V) ⊆ U → s.Nonempty →
      (G.induce (↑s : Set V)).edgeFinset.card < d * (s.card + 1)) :
    G.IsDegenerateOn U (4 * d) := by
  classical
  let := Fintype.ofFinite V
  intro W hW hWU
  let s := W.toFinset
  have he := hs s (by simpa [s] using hWU) (by simpa [s] using hW)
  let J := G.induce (↑s : Set V)
  have hpos : 0 < s.card := card_pos.mpr (by simpa [s] using hW)
  have hv : ∃ v : (↑s : Set V), J.degree v ≤ 4 * d := by
    by_contra! h
    have hsum : ∑ _v : (↑s : Set V), 4 * d ≤ ∑ v, J.degree v :=
      sum_le_sum fun v _ => (h v).le
    rw [J.sum_degrees_eq_twice_card_edges, sum_const, nsmul_eq_mul] at hsum
    have hcard : Fintype.card (↑s : Set V) = s.card := Fintype.card_coe _
    rw [card_univ, hcard] at hsum
    change _ ≤ 2 * (G.induce (↑s : Set V)).edgeFinset.card at hsum
    nlinarith [Nat.mul_le_mul_left d hpos]
  obtain ⟨v, hv⟩ := hv
  refine ⟨v, by simpa [s] using v.property, ?_⟩
  rw [← J.ncard_neighborSet] at hv
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective] at hv
  simpa [J, G.neighborSet_induce, Set.image_preimage_eq_inter_range, s] using hv

private lemma cocoloring_classes {G : SimpleGraph V} {k : ℕ} (h : G.Cocolorable k) :
    ∃ f : V → Fin k, ∀ i, G.IsIndepSet {v | f v = i} ∨ G.IsClique {v | f v = i} := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun i => (hf i).imp (fun h a ha b hb _ => ?_) induce_eq_top.mp⟩
  exact eq_bot_iff_forall_not_adj.mp h ⟨a, ha⟩ ⟨b, hb⟩

/-- A random edge subgraph can be chosen so that each homogeneous color class
in it admits a proper coloring of the original edges with at most `4 * d + 1` colors. -/
private lemma refine_cocoloring [Fintype V] (G : SimpleGraph V) (d : ℕ)
    (hd : 2 * (Fintype.card V + 1) < 2 ^ d) :
    ∃ R ≤ G, ∀ k, R.Cocolorable k → G.Colorable (k * (4 * d + 1)) := by
  classical
  let edges (s : Finset V) := G.edgeFinset.filter fun e => e.toFinset ⊆ s
  obtain ⟨ω, hω⟩ := split_dense_sets edges d hd
  let R := G ⊓ fromEdgeSet {e | ω e = true}
  refine ⟨R, inf_le_left, fun k h => ?_⟩
  obtain ⟨f, hf⟩ := cocoloring_classes h
  let U (i : Fin k) := {v | f v = i}
  have hdeg (i) : G.IsDegenerateOn (U i) (4 * d) := by
    apply degenerate_of_sparse
    intro s hs _
    rw [← G.card_filter_edgeFinset_toFinset_subset s]
    by_contra! hsize
    apply hω s hsize
    have hpair {a b : V} (he : s(a, b) ∈ edges s) : G.Adj a b ∧ a ∈ U i ∧ b ∈ U i := by
      obtain ⟨hab, hsub⟩ := mem_filter.mp he
      exact ⟨G.mem_edgeFinset.mp hab, hs (hsub (by simp)), hs (hsub (by simp))⟩
    rcases hf i with hi | hi
    · right
      intro e he
      induction e using Sym2.ind with | _ a b =>
        obtain ⟨hab, ha, hb⟩ := hpair he
        cases hval : ω s(a, b) with
        | false => rfl
        | true => exact (hi ha hb hab.ne ⟨hab, hval, hab.ne⟩).elim
    · left
      intro e he
      induction e using Sym2.ind with | _ a b =>
        obtain ⟨hab, ha, hb⟩ := hpair he
        exact (hi ha hb hab.ne : R.Adj a b).2.1
  have hlocal (i : Fin k) := IsDegenerateOn.exists_coloringFun (U i).toFinset
    (show G.IsDegenerateOn (↑(U i).toFinset : Set V) (4 * d) by simpa using hdeg i)
  choose g hg using hlocal
  let c : G.Coloring (Fin k × Fin (4 * d + 1)) :=
    Coloring.mk (fun v => (f v, g (f v) v)) (by
      intro a b hab heq
      obtain ⟨hf', hg'⟩ := Prod.mk.inj heq
      rw [← hf'] at hg'
      exact hg (f a) a (by simp [U]) b (by simp [U, hf']) hab hg')
  simpa using c.colorable

private lemma least_cocoloring {G : SimpleGraph V} {m : ℕ} (h : G.Cocolorable m) :
    ∃ n ≤ m, G.Cocolorable n ∧ (n : ℕ∞) = G.cochromaticNumber := by
  let S := {n | G.Cocolorable n}
  have hm : m ∈ S := h
  exact ⟨sInf S, Nat.sInf_le hm, Nat.sInf_mem ⟨m, hm⟩, h.cochromaticNumber_eq_sInf.symm⟩

/-- Realize an edge subgraph of an induced graph on its given vertex set. -/
private lemma realize_restriction (G : SimpleGraph V) {W : Set V} (R : SimpleGraph W)
    (hle : R ≤ G.induce W) : ∃ H : G.Subgraph, H.coe.cochromaticNumber = R.cochromaticNumber := by
  let H : G.Subgraph :=
    { verts := W
      Adj := fun a b => ∃ (ha : a ∈ W) (hb : b ∈ W), R.Adj ⟨a, ha⟩ ⟨b, hb⟩
      adj_sub := fun ⟨_, _, h⟩ => hle h
      edge_vert := fun ⟨ha, _, _⟩ => ha
      symm := ⟨fun _ _ ⟨ha, hb, h⟩ => ⟨hb, ha, h.symm⟩⟩ }
  have heq : H.coe = R := by
    ext a b
    exact ⟨fun ⟨_, _, hab⟩ => hab, fun hab => ⟨a.property, b.property, hab⟩⟩
  exact ⟨H, congrArg cochromaticNumber heq⟩

/-- In a minimum cocoloring, the clique classes together have at most `m²` vertices.
The other classes retain their colors while the clique classes are recolored. -/
private lemma subgraph_bound [Finite V] (G : SimpleGraph V) (m d : ℕ)
    (hm : G.chromaticNumber = (m : ℕ∞)) (hd : 2 * (m ^ 2 + 1) < 2 ^ d) :
    ∃ H : G.Subgraph, ∃ k : ℕ, (k : ℕ∞) ≤ H.coe.cochromaticNumber ∧ m ≤ k * (4 * d + 2) := by
  classical
  let := Fintype.ofFinite V
  have hcol : G.Colorable m := chromaticNumber_le_iff_colorable.mp hm.le
  let T : G.Subgraph := ⊤
  have hcolT := hcol.of_hom T.hom
  obtain ⟨n, hnm, hcn, hn⟩ := least_cocoloring hcolT.cocolorable
  obtain ⟨f, hf⟩ := cocoloring_classes hcn
  let liftV (v : V) : T.verts := ⟨v, Set.mem_univ _⟩
  let W : Set V := {v | T.coe.IsClique {x | f x = f (liftV v)}}
  let p := hcol.some
  have hcard : Fintype.card W ≤ n * m := by
    let key (v : W) := (f (liftV v.val), p v.val)
    have hinj : Function.Injective key := by
      intro a b he
      obtain ⟨h1, h2⟩ := Prod.mk.inj he
      by_contra hab
      have hne : liftV a.val ≠ liftV b.val :=
        fun h => hab (Subtype.ext (congrArg (fun x : T.verts => x.val) h))
      have hc := a.property
      exact p.valid (hc (show f (liftV a.val) = _ from rfl) h1.symm hne) h2
    simpa using Fintype.card_le_of_injective key hinj
  have hsmall : 2 * (Fintype.card W + 1) < 2 ^ d := by
    have hle := hcard.trans (Nat.mul_le_mul_right m hnm)
    rw [sq] at hd
    omega
  obtain ⟨R, hRG, hR⟩ := refine_cocoloring (G.induce W) d hsmall
  obtain ⟨k, _, hck, hk⟩ := least_cocoloring (cocolorable_of_fintype R)
  let q := k * (4 * d + 1)
  let g : (G.induce W).Coloring (Fin q) := (hR k hck).some
  let color (v : V) : Fin n ⊕ Fin q :=
    if hv : v ∈ W then Sum.inr (g ⟨v, hv⟩) else Sum.inl (f (liftV v))
  have proper : ∀ {a b}, G.Adj a b → color a ≠ color b := by
    intro a b hab heq
    dsimp only [color] at heq
    split_ifs at heq with ha hb hb
    · exact g.valid (show (G.induce W).Adj ⟨a, ha⟩ ⟨b, hb⟩ from hab) (Sum.inr.inj heq)
    · have he := Sum.inl.inj heq
      have hi := (hf (f (liftV a))).resolve_right ha
      exact hi (show f (liftV a) = _ from rfl) he.symm
        (fun h => hab.ne (congrArg (fun x : T.verts => x.val) h)) hab
  have hc : G.Colorable (n + q) := by simpa using (Coloring.mk color proper).colorable
  have hmq : m ≤ n + q := by exact_mod_cast (hm ▸ hc.chromaticNumber_le)
  by_cases hnk : n ≤ k
  · obtain ⟨H, hH⟩ := realize_restriction G R hRG
    exact ⟨H, k, (hk.trans hH.symm).le, by dsimp [q] at hmq; nlinarith⟩
  · exact ⟨T, n, hn.le, by
      have hkn := Nat.mul_le_mul_right (4 * d + 1) (Nat.le_of_not_ge hnk)
      dsimp [q] at hmq
      nlinarith⟩

private lemma linear_bound [Finite V] (G : SimpleGraph V) (m : ℕ)
    (hm : G.chromaticNumber = (m : ℕ∞)) :
    ∃ H : G.Subgraph, ∃ k : ℕ, ((k : ℕ∞) ≤ H.coe.cochromaticNumber) ∧
      Real.log 2 / 26 * m / Real.log m ≤ (k : ℝ) := by
  classical
  by_cases hm2 : 2 ≤ m
  · let l := Nat.log 2 m
    let d := 2 * (l + 1) + 2
    have hpow : m < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by decide) m
    have hd : 2 * (m ^ 2 + 1) < 2 ^ d := by
      rw [show d = (l + 1) * 2 + 2 by dsimp [d]; ring, pow_add, pow_mul]
      nlinarith [Nat.pow_le_pow_left hpow.le 2]
    obtain ⟨H, k, hk, hb⟩ := subgraph_bound G m d hm hd
    refine ⟨H, k, hk, ?_⟩
    have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm2
    have hlog : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm'
    have hlogpos : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
    have hl : (l : ℝ) * Real.log 2 ≤ Real.log m := by
      rw [← Real.log_pow]
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : m ≠ 0)
    have hfactor : (4 * (d : ℝ) + 2) * Real.log 2 ≤ 26 * Real.log m := by
      dsimp [d]
      push_cast
      linarith
    have hb' : (m : ℝ) ≤ k * (4 * (d : ℝ) + 2) := by exact_mod_cast hb
    rw [div_le_iff₀ hlogpos]
    nlinarith [mul_le_mul_of_nonneg_right hb' (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)),
      mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg (α := ℝ) k)]
  · have hsmall : m = 0 ∨ m = 1 := by omega
    rcases hsmall with rfl | rfl <;> exact ⟨⊥, 0, by simp, by simp⟩

end

/--
**Alon–Krivelevich–Sudakov theorem on subgraphs of large cochromatic number.** There is a real
number $c > 0$ such that for every simple graph $G$ on a finite vertex set with chromatic number
$m$ there are a subgraph $H$ of $G$ and a natural number $k$ with $k \ge c\,m / \log m$ such that
the cochromatic number of $H$ is at least $k$. Moreover, there is a real number $c > 0$ with the
same property for the bound $k \ge c\sqrt{m / \log m}$.

Here $\log$ is the natural logarithm, with the conventions $\log 0 = 0$ and $x / 0 = 0$, so both
bounds are $0$ when $m \le 1$. This answers Erdős Problem 760 affirmatively.

Source:
plby/lean-proofs, src/v4.29.1/ErdosProblems/Erdos760.lean (theorem erdos_760, following Alon,
Krivelevich and Sudakov, Subgraphs with a large cochromatic number, 1997), pinned revision
8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/v4.29.1/ErdosProblems/Erdos760.lean#L1306.
Moved from `OpenConjectures/Combinatorics/ErdosProblem760`.
-/
public theorem conjecture_holds : conjecture := by
  have hc : 0 < Real.log 2 / 26 := by positivity
  constructor
  · exact ⟨_, hc, fun _ _ G m => linear_bound G m⟩
  · refine ⟨_, hc, fun _ _ G m hm => ?_⟩
    obtain ⟨H, k, hk, hb⟩ := linear_bound G m hm
    refine ⟨H, k, hk, ?_⟩
    rw [mul_div_assoc] at hb
    apply le_trans (mul_le_mul_of_nonneg_left _ hc.le) hb
    apply Real.sqrt_le_self_iff.mpr
    by_cases hm2 : 2 ≤ m
    · right
      have hm' : (1 : ℝ) < m := by exact_mod_cast (by omega : 1 < m)
      exact (one_le_div (Real.log_pos hm')).mpr
        (by linarith [Real.log_le_sub_one_of_pos (zero_lt_one.trans hm')])
    · have hsmall : m = 0 ∨ m = 1 := by omega
      rcases hsmall with rfl | rfl <;> simp

end MathlibExt.Combinatorics.ErdosProblem760Wanted
