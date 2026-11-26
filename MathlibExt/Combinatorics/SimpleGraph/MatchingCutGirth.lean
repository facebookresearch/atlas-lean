/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Data.Rat.Init
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Matching cuts in sparse high-girth graphs

A matching cut of a graph is a matching whose deletion disconnects the graph. The Open Problem
Garden asks whether for every real `d` there is `g` such that every graph of average degree
below `d` and girth at least `g` has a matching cut. This file proves `conjecture_refuted`: the
answer is negative, already for `d = 400`.

Feghali, Lucke, Paulusma and Ries (Lemma 5) answer the question with the 14-regular bipartite
Ramanujan graphs of Lubotzky, Phillips and Sarnak. The proof here is elementary and
probabilistic instead. In the random graph on `n = 4 m` vertices in which each pair is an edge
independently with probability `8 / m`, a first-moment computation shows that, for some
outcome, there are few cycles of length below `g`, there are fewer than `512 m` edges, and every
set `A` of between `m` and `2 m` vertices sends more than `3 |A|` edges to its complement.
Deleting every edge of a cycle of length below `g` leaves a graph of girth at least `g`.
Repeatedly cutting off a side of a sparse cut, a vertex set `S` sending at most
`min (|S|, |T|)` edges to the rest `T`, then removes fewer than `m` vertices in total, by the
expansion property. What remains has no sparse cut, hence no matching cut, and has more than
`3 m` vertices and average degree below `400`. This last step is a robust form of Observation 2
of Feghali, Lucke, Paulusma and Ries: every connected graph whose edge expansion exceeds `1` has
no matching cut. The weight and cycle-counting lemmas adapt the private helpers of
`MathlibExt.Combinatorics.SimpleGraph.ErdosGirthChromatic`.

## Main declarations

* `avgDegree`, `HasMatchingCut`, `conjecture`: average degree, matching cuts and the
  affirmative form of the question.
* `conjecture_refuted`: the question has a negative answer.

## References

* C. Feghali, F. Lucke, D. Paulusma and B. Ries, Matching Cuts in Graphs of High Girth and
  H-Free Graphs, ISAAC 2023, arXiv:2212.12317.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.MatchingCutGirthWanted

/-! Source record `OPG-37364`, ported from the Open Problem Garden entry
"Matching cut and girth"
(http://www.openproblemgarden.org/op/matching_cut_and_girth).

For every real `d` there is `g` such that every graph of average degree below `d`
and girth at least `g` has a matching-cut.

Average degree uses the canonical `edgeFinset` count; the girth bound uses
`egirth` (which is `⊤` for acyclic graphs); a matching-cut is a matching
subgraph (`Subgraph.IsMatching`) whose edge deletion (`deleteEdges`)
disconnects the graph.

Adequacy gaps: the source poses a question, formalized here as the
affirmative answer; the matching-cut may be empty (then the graph is already
disconnected); graphs are finite with at least two vertices (matching cuts
need two sides; the singleton refutes the unguarded form). -/

/-- **Average degree of a finite graph.** For a simple graph $G$ on a finite vertex set $V$ with
edge set $E$, the average degree of $G$ is the rational number $2|E|/|V|$; it equals $0$ when $V$
is empty. -/
noncomputable def avgDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  (2 * G.edgeFinset.card : ℚ) / Fintype.card V

/-- **Matching cut.** A simple graph $G$ has a matching cut if some matching $M$ of $G$, that is,
a set of pairwise disjoint edges of $G$, is such that deleting the edges of $M$ from $G$ leaves
two vertices $u$ and $v$ that are not joined by any path. The matching may be empty, in which
case this says that $G$ itself has two vertices not joined by any path. -/
def HasMatchingCut {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ H : G.Subgraph, H.IsMatching ∧
    ∃ u v : V, ¬ (G.deleteEdges H.edgeSet).Reachable u v

/-- **Matching cut and girth question, affirmative form.** For every real number $d$ there is a
natural number $g$ such that every simple graph $G$ on a finite vertex set with at least two
vertices, whose average degree is less than $d$ and whose girth is at least $g$, has a matching
cut. An acyclic graph has infinite girth, so it meets the girth bound for every $g$.

Source: [OPG-37364], Open Problem Garden, "Matching cut and girth". -/
def conjecture : Prop :=
  ∀ d : ℝ, ∃ g : ℕ, ∀ (V : Type*) [Fintype V] [Nontrivial V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (avgDegree G : ℝ) < d →
    ((g : ℕ∞) ≤ G.egirth) →
    HasMatchingCut G

/-! ### The random-graph weights -/

section Weights

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The probability of the outcome `E` when each element of `α` is chosen independently with
probability `p`. -/
private noncomputable def weight (p : ℝ) (E : Finset α) : ℝ :=
  p ^ E.card * (1 - p) ^ Eᶜ.card

private theorem weight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : Finset α) :
    0 ≤ weight p E :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

/-- The expectation of a product of independent factors. -/
private theorem sum_weight_mul_prod (p : ℝ) (s r : α → ℝ) :
    ∑ E : Finset α, weight p E * ((∏ x ∈ E, s x) * ∏ x ∈ Eᶜ, r x) =
      ∏ x, (p * s x + (1 - p) * r x) := by
  rw [Fintype.prod_add]
  refine Finset.sum_congr rfl fun E _ => ?_
  simp only [weight, Finset.prod_mul_distrib, Finset.prod_const]
  ring

private theorem sum_weight (p : ℝ) : ∑ E : Finset α, weight p E = 1 := by
  have h := sum_weight_mul_prod (α := α) p (fun _ => 1) (fun _ => 1)
  simpa using h

/-- The probability that the outcome contains `F` is `p ^ |F|`. -/
private theorem sum_weight_superset (p : ℝ) (F : Finset α) :
    ∑ E : Finset α, (if F ⊆ E then weight p E else 0) = p ^ F.card := by
  have h := sum_weight_mul_prod (α := α) p (fun _ => 1) (fun x => if x ∈ F then 0 else 1)
  have hl : ∀ E : Finset α, weight p E * ((∏ x ∈ E, (fun _ => (1 : ℝ)) x) *
      ∏ x ∈ Eᶜ, (fun x => if x ∈ F then (0 : ℝ) else 1) x) =
      if F ⊆ E then weight p E else 0 := by
    intro E
    by_cases hFE : F ⊆ E
    · rw [ite_eq_left hFE, Finset.prod_const_one, one_mul, Finset.prod_eq_one, mul_one]
      intro x hx
      have hxF : x ∉ F := fun hxF => (Finset.mem_compl.mp hx) (hFE hxF)
      simp [hxF]
    · rw [ite_eq_right hFE]
      obtain ⟨x, hxF, hxE⟩ := Finset.not_subset.mp hFE
      rw [Finset.prod_eq_zero (i := x) (Finset.mem_compl.mpr hxE) (by simp [hxF]), mul_zero,
        mul_zero]
  have hr : ∀ x : α, p * (fun _ => (1 : ℝ)) x + (1 - p) * (fun x => if x ∈ F then 0 else 1) x =
      if x ∈ F then p else 1 := by
    intro x
    by_cases hx : x ∈ F <;> simp [hx]
  rw [Finset.sum_congr rfl fun E _ => hl E, Finset.prod_congr rfl fun x _ => hr x,
    Fintype.prod_ite_mem, Finset.prod_const] at h
  exact h

/-- The exponential moment of the number of chosen elements of `C`. -/
private theorem sum_weight_mul_pow (p t : ℝ) (C : Finset α) :
    ∑ E : Finset α, weight p E * t ^ (E ∩ C).card = (1 - p + p * t) ^ C.card := by
  have h := sum_weight_mul_prod (α := α) p (fun x => if x ∈ C then t else 1) (fun _ => 1)
  have hl : ∀ E : Finset α, weight p E * ((∏ x ∈ E, (fun x => if x ∈ C then t else 1) x) *
      ∏ x ∈ Eᶜ, (fun _ => (1 : ℝ)) x) = weight p E * t ^ (E ∩ C).card := by
    intro E
    rw [Finset.prod_const_one, mul_one, Finset.prod_ite_mem, Finset.prod_const]
  have hr : ∀ x : α, p * (fun x => if x ∈ C then t else 1) x + (1 - p) * (fun _ => (1 : ℝ)) x =
      if x ∈ C then 1 - p + p * t else 1 := by
    intro x
    by_cases hx : x ∈ C
    · simp only [hx, ite_true]
      ring
    · simp only [hx, ite_false]
      ring
  rw [Finset.sum_congr rfl fun E _ => hl E, Finset.prod_congr rfl fun x _ => hr x,
    Fintype.prod_ite_mem, Finset.prod_const] at h
  exact h

/-- The expected number of chosen elements. -/
private theorem sum_weight_mul_card (p : ℝ) :
    ∑ E : Finset α, weight p E * (E.card : ℝ) = p * Fintype.card α := by
  have hcard : ∀ E : Finset α, (E.card : ℝ) = ∑ x : α, if {x} ⊆ E then (1 : ℝ) else 0 := by
    intro E
    rw [Finset.sum_boole]
    congr 2
    ext x
    simp
  calc ∑ E : Finset α, weight p E * (E.card : ℝ)
      = ∑ x : α, ∑ E : Finset α, (if {x} ⊆ E then weight p E else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun E _ => ?_
        rw [hcard E, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp
    _ = ∑ _x : α, p := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [sum_weight_superset, Finset.card_singleton, pow_one]
    _ = p * Fintype.card α := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- If a random variable has expectation below `1`, some outcome takes a value below `1`. -/
private theorem exists_lt_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Z : Finset α → ℝ)
    (h : ∑ E : Finset α, weight p E * Z E < 1) : ∃ E, Z E < 1 := by
  by_contra hcon
  push Not at hcon
  have hle : ∑ E : Finset α, weight p E * 1 ≤ ∑ E : Finset α, weight p E * Z E :=
    Finset.sum_le_sum fun E _ => mul_le_mul_of_nonneg_left (hcon E) (weight_nonneg hp0 hp1 E)
  simp only [mul_one, sum_weight] at hle
  linarith

end Weights

/-! ### Cuts and the peeling argument -/

section Cuts

variable {V : Type*} [DecidableEq V]

/-- The unordered pairs with one element in `A` and the other in `B`. -/
private def bpairs (A B : Finset V) : Finset (Sym2 V) :=
  (A ×ˢ B).image fun q => s(q.1, q.2)

private theorem mk_mem_bpairs {A B : Finset V} {x y : V} (hx : x ∈ A) (hy : y ∈ B) :
    s(x, y) ∈ bpairs A B :=
  Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩

private theorem exists_of_mem_bpairs {A B : Finset V} {e : Sym2 V} (he : e ∈ bpairs A B) :
    ∃ x ∈ A, ∃ y ∈ B, e = s(x, y) := by
  obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp he
  exact ⟨x, (Finset.mem_product.mp hxy).1, y, (Finset.mem_product.mp hxy).2, rfl⟩

private theorem bpairs_comm (A B : Finset V) : bpairs A B = bpairs B A := by
  ext e
  constructor
  · intro he
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_mem_bpairs he
    rw [Sym2.eq_swap]
    exact mk_mem_bpairs hy hx
  · intro he
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_mem_bpairs he
    rw [Sym2.eq_swap]
    exact mk_mem_bpairs hy hx

private theorem card_bpairs (A B : Finset V) (h : Disjoint A B) :
    (bpairs A B).card = A.card * B.card := by
  rw [bpairs, Finset.card_image_of_injOn, Finset.card_product]
  rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' heq
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hxy hxy'
  have heq' : s(x, y) = s(x', y') := heq
  rcases Sym2.eq_iff.mp heq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hxy'.2 (Finset.disjoint_left.mp h hxy.1)

private theorem card_inter_union_le (F X Y : Finset (Sym2 V)) :
    (F ∩ (X ∪ Y)).card ≤ (F ∩ X).card + (F ∩ Y).card := by
  rw [Finset.inter_union_distrib_left]
  exact Finset.card_union_le _ _

private theorem card_inter_le_of_subset (F : Finset (Sym2 V)) {X Y : Finset (Sym2 V)}
    (h : X ⊆ Y) : (F ∩ X).card ≤ (F ∩ Y).card :=
  Finset.card_le_card (Finset.inter_subset_inter_left h)

variable [Fintype V]

/-- One peeling step: adding to a small set `Q` with few outgoing edges a set `A` that sends few
edges to the rest keeps `Q` small with few outgoing edges, by the expansion hypothesis. -/
private theorem peel_step (F : Finset (Sym2 V)) (m : ℕ) (hV : Fintype.card V ≤ 4 * m)
    (hexp : ∀ A : Finset V, m ≤ A.card → A.card ≤ 2 * m →
      A.card + m < (F ∩ bpairs A Aᶜ).card)
    {Q A : Finset V} (hQm : Q.card < m) (hQcut : (F ∩ bpairs Q Qᶜ).card ≤ Q.card)
    (hAQ : A ⊆ Qᶜ) (hAhalf : 2 * A.card ≤ Qᶜ.card)
    (hAcut : (F ∩ bpairs A (Qᶜ \ A)).card ≤ A.card) :
    (Q ∪ A).card < m ∧ (F ∩ bpairs (Q ∪ A) (Q ∪ A)ᶜ).card ≤ (Q ∪ A).card := by
  have hdisj : Disjoint Q A := by
    rw [Finset.disjoint_left]
    intro x hxQ hxA
    exact Finset.mem_compl.mp (hAQ hxA) hxQ
  have hcardQA : (Q ∪ A).card = Q.card + A.card := Finset.card_union_of_disjoint hdisj
  have hQc : Qᶜ.card ≤ 4 * m := (Finset.card_le_univ _).trans hV
  have incl1 : bpairs (Q ∪ A) (Q ∪ A)ᶜ ⊆ bpairs Q Qᶜ ∪ bpairs A (Qᶜ \ A) := by
    intro e he
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_mem_bpairs he
    rw [Finset.mem_compl, Finset.mem_union, not_or] at hy
    rcases Finset.mem_union.mp hx with hxQ | hxA
    · exact Finset.mem_union_left _ (mk_mem_bpairs hxQ (Finset.mem_compl.mpr hy.1))
    · exact Finset.mem_union_right _
        (mk_mem_bpairs hxA (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hy.1, hy.2⟩))
  have incl2 : bpairs A Aᶜ ⊆ bpairs A (Qᶜ \ A) ∪ bpairs Q Qᶜ := by
    intro e he
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_mem_bpairs he
    by_cases hyQ : y ∈ Q
    · refine Finset.mem_union_right _ ?_
      rw [Sym2.eq_swap]
      exact mk_mem_bpairs hyQ (hAQ hx)
    · exact Finset.mem_union_left _
        (mk_mem_bpairs hx (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hyQ,
          Finset.mem_compl.mp hy⟩))
  have hcut' : (F ∩ bpairs (Q ∪ A) (Q ∪ A)ᶜ).card ≤ Q.card + A.card :=
    ((card_inter_le_of_subset F incl1).trans (card_inter_union_le F _ _)).trans
      (Nat.add_le_add hQcut hAcut)
  have hA : A.card < m := by
    by_contra hcon
    push Not at hcon
    have h1 := hexp A hcon (by omega)
    have h2 := (card_inter_le_of_subset F incl2).trans (card_inter_union_le F _ _)
    omega
  refine ⟨?_, hcardQA ▸ hcut'⟩
  by_contra hcon
  push Not at hcon
  have h1 := hexp (Q ∪ A) hcon (by omega)
  omega

/-- The peeling argument: under the expansion hypothesis, some set `Q` of fewer than `m`
vertices has a complement without sparse cuts. -/
private theorem exists_core (F : Finset (Sym2 V)) (m : ℕ) (hm : 0 < m)
    (hV : Fintype.card V ≤ 4 * m)
    (hexp : ∀ A : Finset V, m ≤ A.card → A.card ≤ 2 * m →
      A.card + m < (F ∩ bpairs A Aᶜ).card) :
    ∃ Q : Finset V, Q.card < m ∧ ∀ S : Finset V, S ⊆ Qᶜ → S.Nonempty → (Qᶜ \ S).Nonempty →
      S.card < (F ∩ bpairs S (Qᶜ \ S)).card ∨ (Qᶜ \ S).card < (F ∩ bpairs S (Qᶜ \ S)).card := by
  classical
  set 𝒬 := (Finset.univ : Finset (Finset V)).filter
    (fun Q => Q.card < m ∧ (F ∩ bpairs Q Qᶜ).card ≤ Q.card) with h𝒬
  have hne : 𝒬.Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hm, by simp [bpairs]⟩⟩
  obtain ⟨Q, hQ, hmax⟩ := Finset.exists_max_image 𝒬 Finset.card hne
  obtain ⟨-, hQm, hQcut⟩ := Finset.mem_filter.mp hQ
  refine ⟨Q, hQm, fun S hSP hSne hRne => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hsplit : (Qᶜ \ S).card + S.card = Qᶜ.card := Finset.card_sdiff_add_card_eq_card hSP
  -- the smaller side `A` of the sparse cut
  obtain ⟨A, hAQ, hAne, hAhalf, hAcut⟩ : ∃ A : Finset V, A ⊆ Qᶜ ∧ A.Nonempty ∧
      2 * A.card ≤ Qᶜ.card ∧ (F ∩ bpairs A (Qᶜ \ A)).card ≤ A.card := by
    by_cases hle : S.card ≤ (Qᶜ \ S).card
    · exact ⟨S, hSP, hSne, by omega, h1⟩
    · refine ⟨Qᶜ \ S, Finset.sdiff_subset, hRne, by omega, ?_⟩
      rw [Finset.sdiff_sdiff_eq_self hSP, bpairs_comm]
      exact h2
  obtain ⟨hQAm, hQAcut⟩ := peel_step F m hV hexp hQm hQcut hAQ hAhalf hAcut
  have hmem : Q ∪ A ∈ 𝒬 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQAm, hQAcut⟩
  have hdisj : Disjoint Q A := by
    rw [Finset.disjoint_left]
    intro x hxQ hxA
    exact Finset.mem_compl.mp (hAQ hxA) hxQ
  have hgt := hmax _ hmem
  rw [Finset.card_union_of_disjoint hdisj] at hgt
  have := hAne.card_pos
  omega

end Cuts

/-! ### Matching cuts give sparse cuts -/

/-- A matching cut of a graph `H` on a parametrization `ι` of `P` whose adjacency contains the
pairs of `F` yields a set `S ⊆ P` sending at most `min (|S|, |P \ S|)` pairs of `F` to `P \ S`. -/
private theorem exists_sparse_cut {V W : Type*} [DecidableEq V] (F : Finset (Sym2 V))
    (P : Finset V) (ι : W → V) (hι : Function.Injective ι) (hP : ∀ x, x ∈ P ↔ ∃ w, ι w = x)
    (H : SimpleGraph W) (hH : ∀ w w', s(ι w, ι w') ∈ F → ι w ≠ ι w' → H.Adj w w')
    (h : HasMatchingCut H) :
    ∃ S ⊆ P, S.Nonempty ∧ (P \ S).Nonempty ∧ (F ∩ bpairs S (P \ S)).card ≤ S.card ∧
      (F ∩ bpairs S (P \ S)).card ≤ (P \ S).card := by
  classical
  obtain ⟨M, hM, u, v, huv⟩ := h
  have hmemS : ∀ w, ι w ∈ P.filter (fun x => ∃ w, ι w = x ∧
      (H.deleteEdges M.edgeSet).Reachable u w) ↔ (H.deleteEdges M.edgeSet).Reachable u w := by
    intro w
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨-, w', hw', hr⟩
      rwa [← hι hw']
    · intro hr
      exact ⟨(hP _).mpr ⟨w, rfl⟩, w, rfl, hr⟩
  set S : Finset V := P.filter fun x => ∃ w, ι w = x ∧ (H.deleteEdges M.edgeSet).Reachable u w
    with hS
  have hSP : S ⊆ P := Finset.filter_subset _ _
  -- every pair of `F` from `S` to `P \ S` is an edge of the matching
  have hkey : ∀ w w', ι w ∈ S → ι w' ∈ P \ S → s(ι w, ι w') ∈ F → M.Adj w w' := by
    intro w w' hw hw' hF
    have hr := (hmemS w).mp hw
    have hnr : ¬ (H.deleteEdges M.edgeSet).Reachable u w' := fun hr' =>
      (Finset.mem_sdiff.mp hw').2 ((hmemS w').mpr hr')
    have hne : ι w ≠ ι w' := fun heq => (Finset.mem_sdiff.mp hw').2 (heq ▸ hw)
    by_contra hM'
    apply hnr
    refine hr.trans (SimpleGraph.Adj.reachable ?_)
    rw [SimpleGraph.deleteEdges_adj, SimpleGraph.Subgraph.mem_edgeSet]
    exact ⟨hH w w' hF hne, hM'⟩
  set T := (S ×ˢ (P \ S)).filter fun q => s(q.1, q.2) ∈ F with hT
  have hFT : F ∩ bpairs S (P \ S) ⊆ T.image fun q => s(q.1, q.2) := by
    intro e he
    obtain ⟨heF, he⟩ := Finset.mem_inter.mp he
    obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_mem_bpairs he
    exact Finset.mem_image.mpr
      ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hy⟩, heF⟩, rfl⟩
  have hTpre : ∀ q ∈ T, ∃ w w', ι w = q.1 ∧ ι w' = q.2 ∧ M.Adj w w' := by
    intro q hq
    obtain ⟨hq, hqF⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    obtain ⟨w, hw⟩ := (hP _).mp (hSP hq1)
    obtain ⟨w', hw'⟩ := (hP _).mp (Finset.mem_sdiff.mp hq2).1
    refine ⟨w, w', hw, hw', hkey w w' (by rw [hw]; exact hq1) (by rw [hw']; exact hq2) ?_⟩
    rw [hw, hw']
    exact hqF
  have hT1 : T.card ≤ S.card := by
    refine Finset.card_le_card_of_injOn Prod.fst (fun q hq => ?_) (fun q hq q' hq' hqq => ?_)
    · exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
    · obtain ⟨w, w₁, hw, hw₁, hM₁⟩ := hTpre q hq
      obtain ⟨w', w₂, hw', hw₂, hM₂⟩ := hTpre q' hq'
      have hww : w = w' := hι (hw.trans (hqq.trans hw'.symm))
      subst hww
      have h12 : w₁ = w₂ := (hM (M.edge_vert hM₁)).unique hM₁ hM₂
      subst h12
      exact Prod.ext hqq (hw₁.symm.trans hw₂)
  have hT2 : T.card ≤ (P \ S).card := by
    refine Finset.card_le_card_of_injOn Prod.snd (fun q hq => ?_) (fun q hq q' hq' hqq => ?_)
    · exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
    · obtain ⟨w₁, w, hw₁, hw, hM₁⟩ := hTpre q hq
      obtain ⟨w₂, w', hw₂, hw', hM₂⟩ := hTpre q' hq'
      have hww : w = w' := hι (hw.trans (hqq.trans hw'.symm))
      subst hww
      have h12 : w₁ = w₂ := (hM (M.edge_vert hM₁.symm)).unique hM₁.symm hM₂.symm
      subst h12
      exact Prod.ext (hw₁.symm.trans hw₂) hqq
  have hcard := (Finset.card_le_card hFT).trans Finset.card_image_le
  refine ⟨S, hSP, ⟨ι u, (hmemS u).mpr SimpleGraph.Reachable.rfl⟩, ⟨ι v, ?_⟩,
    hcard.trans hT1, hcard.trans hT2⟩
  exact Finset.mem_sdiff.mpr ⟨(hP _).mpr ⟨v, rfl⟩, fun hv => huv ((hmemS v).mp hv)⟩

/-- The graph obtained by restricting `fromEdgeSet F` along an injective map has at most `|F|`
edges. -/
private theorem card_edgeFinset_comap_le {V W : Type*} (F : Finset (Sym2 V)) (ι : W → V)
    (hι : Function.Injective ι)
    [Fintype ((SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).comap ι).edgeSet] :
    ((SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).comap ι).edgeFinset.card ≤ F.card := by
  refine Finset.card_le_card_of_injOn (Sym2.map ι) (fun e he => ?_)
    (fun e _ e' _ h => Sym2.map.injective hι h)
  rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.comap_adj, SimpleGraph.fromEdgeSet_adj] at he
    simpa using he.1

/-! ### Short cycles -/

/-- The pairs `s(f i, f (i + 1))` of consecutive entries of a cyclic tuple `f`. -/
private def cycleEdges {V : Type*} [DecidableEq V] (j : ℕ) (f : Fin (j + 3) → V) :
    Finset (Sym2 V) :=
  Finset.univ.image fun i => s(f i, f (i + 1))

/-- In `Fin (j + 3)`, `a = b + 1` and `a + 1 = b` are contradictory. -/
private theorem fin_add_two_ne {j : ℕ} {a b : Fin (j + 3)} (e1 : a = b + 1) (e2 : a + 1 = b) :
    False := by
  have h : ((b + 1 : Fin (j + 3))).val = (b.val + 1) % (j + 3) := by rw [Fin.val_add]; simp
  rw [← e1] at h
  have h' : ((a + 1 : Fin (j + 3))).val = (a.val + 1) % (j + 3) := by rw [Fin.val_add]; simp
  rw [e2] at h'
  have c1 : b.val + 1 < j + 3 ∨ b.val + 1 = j + 3 := by
    have := Fin.is_lt b
    omega
  have c2 : a.val + 1 < j + 3 ∨ a.val + 1 = j + 3 := by
    have := Fin.is_lt a
    omega
  rcases c1 with hlt | heq <;> rcases c2 with hlt2 | heq2
  · rw [Nat.mod_eq_of_lt hlt] at h
    rw [Nat.mod_eq_of_lt hlt2] at h'
    omega
  · rw [Nat.mod_eq_of_lt hlt] at h
    rw [heq2, Nat.mod_self] at h'
    omega
  · rw [heq, Nat.mod_self] at h
    rw [Nat.mod_eq_of_lt hlt2] at h'
    omega
  · rw [heq, Nat.mod_self] at h
    rw [heq2, Nat.mod_self] at h'
    omega

/-- A cyclic tuple of `j + 3` distinct entries has `j + 3` distinct consecutive pairs. -/
private theorem card_cycleEdges {V : Type*} [DecidableEq V] (j : ℕ) (f : Fin (j + 3) → V)
    (hf : Function.Injective f) : (cycleEdges j f).card = j + 3 := by
  unfold cycleEdges
  rw [Finset.card_image_of_injective _ (by
    intro a b hab
    rcases Sym2.eq_iff.mp hab with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hf h1
    · exact (fin_add_two_ne (hf h1) (hf h2)).elim)]
  simp

/-- The cyclic tuples of `j + 3` distinct vertices whose consecutive pairs all lie in `E`. -/
private def shortCycles {n : ℕ} (E : Finset (Sym2 (Fin n))) (j : ℕ) :
    Finset (Fin (j + 3) → Fin n) :=
  Finset.univ.filter fun f => Function.Injective f ∧ cycleEdges j f ⊆ E

/-- The number of cyclic tuples of fewer than `g` distinct vertices along pairs in `E`. -/
private def shortCycleCount {n : ℕ} (g : ℕ) (E : Finset (Sym2 (Fin n))) : ℕ :=
  ∑ j ∈ Finset.range (g - 3), (shortCycles E j).card

/-- The pairs of `E` lying on a cycle of length less than `g` along pairs in `E`. -/
private def shortCycleEdges {n : ℕ} (g : ℕ) (E : Finset (Sym2 (Fin n))) :
    Finset (Sym2 (Fin n)) :=
  (Finset.range (g - 3)).biUnion fun j => (shortCycles E j).biUnion (cycleEdges j)

private theorem card_shortCycleEdges_le {n : ℕ} (g : ℕ) (E : Finset (Sym2 (Fin n))) :
    (shortCycleEdges g E).card ≤ g * shortCycleCount g E := by
  unfold shortCycleEdges shortCycleCount
  rw [Finset.mul_sum]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j hj => ?_)
  refine Finset.card_biUnion_le.trans ?_
  have hj' : j + 3 ≤ g := by
    rw [Finset.mem_range] at hj
    omega
  calc ∑ f ∈ shortCycles E j, (cycleEdges j f).card ≤ ∑ _f ∈ shortCycles E j, g :=
        Finset.sum_le_sum fun f _ => (Finset.card_image_le.trans (by simp)).trans hj'
    _ = g * (shortCycles E j).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- Deleting the pairs on short cycles leaves a graph of girth at least `g`, also after
restricting along an injective map. -/
private theorem le_egirth_comap {n : ℕ} {W : Type*} (g : ℕ) (E : Finset (Sym2 (Fin n)))
    (ι : W → Fin n) (hι : Function.Injective ι) :
    (g : ℕ∞) ≤ ((SimpleGraph.fromEdgeSet
      ((E \ shortCycleEdges g E : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).comap
        ι).egirth := by
  rw [SimpleGraph.le_egirth]
  intro a w hw
  by_contra hlt
  push Not at hlt
  have hlt' : w.length < g := by exact_mod_cast hlt
  have h3 : 3 ≤ w.length := hw.three_le_length
  obtain ⟨j, hj⟩ : ∃ j, w.length = j + 3 := ⟨w.length - 3, by omega⟩
  set f : Fin (j + 3) → Fin n := fun i => ι (w.getVert i.val) with hf
  have hinj : Function.Injective f := by
    intro i i' hii
    have h := hw.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
      (by simp only [Set.mem_ofPred_eq]; omega) (hι hii)
    exact Fin.ext h
  have hadj : ∀ i : Fin (j + 3), s(f i, f (i + 1)) ∈ E \ shortCycleEdges g E := by
    intro i
    have hi1 : ((i + 1 : Fin (j + 3)) : ℕ) = (i.val + 1) % (j + 3) := by
      rw [Fin.val_add]
      simp
    have hstep : ((SimpleGraph.fromEdgeSet ((E \ shortCycleEdges g E : Finset (Sym2 (Fin n))) :
        Set (Sym2 (Fin n)))).comap ι).Adj (w.getVert i.val)
          (w.getVert (i + 1 : Fin (j + 3)).val) := by
      rcases Nat.lt_or_ge (i.val + 1) (j + 3) with hlt | hge
      · rw [hi1, Nat.mod_eq_of_lt hlt]
        exact w.adj_getVert_succ (by omega)
      · have heq : i.val + 1 = j + 3 := by omega
        rw [hi1, heq, Nat.mod_self, SimpleGraph.Walk.getVert_zero]
        have hlast : w.getVert (j + 3) = a := by rw [← hj, SimpleGraph.Walk.getVert_length]
        have := w.adj_getVert_succ (i := i.val) (by omega)
        rwa [heq, hlast] at this
    rw [SimpleGraph.comap_adj, SimpleGraph.fromEdgeSet_adj] at hstep
    exact hstep.1
  have hj_mem : j ∈ Finset.range (g - 3) := Finset.mem_range.mpr (by omega)
  have hf_mem : f ∈ shortCycles E j := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinj, fun e he => ?_⟩
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_sdiff.mp (hadj i)).1
  have hD : s(f 0, f (0 + 1)) ∈ shortCycleEdges g E :=
    Finset.mem_biUnion.mpr ⟨j, hj_mem, Finset.mem_biUnion.mpr ⟨f, hf_mem,
      Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩⟩
  exact (Finset.mem_sdiff.mp (hadj 0)).2 hD

/-! ### The first-moment computation -/

/-- The expected number of short-cycle tuples is at most `∑ (n p) ^ (j + 3)`. -/
private theorem expected_shortCycleCount_le (n g : ℕ) {p : ℝ} (hp0 : 0 ≤ p) :
    ∑ E : Finset (Sym2 (Fin n)), weight p E * (shortCycleCount g E : ℝ) ≤
      ∑ j ∈ Finset.range (g - 3), ((n : ℝ) * p) ^ (j + 3) := by
  have hexpand : ∀ E : Finset (Sym2 (Fin n)), (shortCycleCount g E : ℝ) =
      ∑ j ∈ Finset.range (g - 3), ∑ f : Fin (j + 3) → Fin n,
        if Function.Injective f ∧ cycleEdges j f ⊆ E then (1 : ℝ) else 0 := by
    intro E
    unfold shortCycleCount shortCycles
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_boole]
  have hinner : ∀ j (f : Fin (j + 3) → Fin n), ∑ E : Finset (Sym2 (Fin n)),
      weight p E * (if Function.Injective f ∧ cycleEdges j f ⊆ E then (1 : ℝ) else 0) ≤
        p ^ (j + 3) := by
    intro j f
    by_cases hf : Function.Injective f
    · have hE : ∀ E : Finset (Sym2 (Fin n)), weight p E *
          (if Function.Injective f ∧ cycleEdges j f ⊆ E then (1 : ℝ) else 0) =
            if cycleEdges j f ⊆ E then weight p E else 0 := by
        intro E
        by_cases h : cycleEdges j f ⊆ E <;> simp [hf, h]
      rw [Finset.sum_congr rfl fun E _ => hE E, sum_weight_superset, card_cycleEdges j f hf]
    · simp only [hf, false_and, ite_false, mul_zero, Finset.sum_const_zero]
      exact pow_nonneg hp0 _
  calc ∑ E : Finset (Sym2 (Fin n)), weight p E * (shortCycleCount g E : ℝ)
      = ∑ j ∈ Finset.range (g - 3), ∑ f : Fin (j + 3) → Fin n, ∑ E : Finset (Sym2 (Fin n)),
          weight p E * (if Function.Injective f ∧ cycleEdges j f ⊆ E then (1 : ℝ) else 0) := by
        simp only [hexpand, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ Finset.range (g - 3), ∑ _f : Fin (j + 3) → Fin n, p ^ (j + 3) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun f _ => hinner j f
    _ = ∑ j ∈ Finset.range (g - 3), ((n : ℝ) * p) ^ (j + 3) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, mul_pow]

/-- With `n = 4 m` and `p = 8 / m`, the expected number of chosen pairs is at most `128 m`. -/
private theorem expected_card_le (m : ℕ) (hm : 8 ≤ m) :
    ∑ E : Finset (Sym2 (Fin (4 * m))), weight (8 / m) E * (E.card : ℝ) ≤ 128 * m := by
  rw [sum_weight_mul_card]
  have hcard : Fintype.card (Sym2 (Fin (4 * m))) ≤ (4 * m) * (4 * m) := by
    calc Fintype.card (Sym2 (Fin (4 * m))) ≤ Fintype.card (Fin (4 * m) × Fin (4 * m)) :=
          Fintype.card_le_of_surjective _ Sym2.mk_surjective
      _ = (4 * m) * (4 * m) := by simp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hcard' : (Fintype.card (Sym2 (Fin (4 * m))) : ℝ) ≤ (4 * m) * (4 * m) := by
    exact_mod_cast hcard
  calc 8 / (m : ℝ) * Fintype.card (Sym2 (Fin (4 * m))) ≤ 8 / m * ((4 * m) * (4 * m)) :=
        mul_le_mul_of_nonneg_left hcard' (by positivity)
    _ = 128 * m := by
        field_simp
        ring

/-- The vertex sets with between `m` and `2 m` elements. -/
private def midSets (n m : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter fun A => m ≤ A.card ∧ A.card ≤ 2 * m

/-- An exponential-moment witness for the sets in `midSets n m` with few outgoing pairs: it is at
least `1` as soon as some such set `A` sends at most `3 |A|` pairs of `E` to its complement. -/
private noncomputable def badCutWeight {n : ℕ} (m : ℕ) (E : Finset (Sym2 (Fin n))) : ℝ :=
  ∑ A ∈ midSets n m, (8 : ℝ) ^ A.card * (1 / 2 : ℝ) ^ (E ∩ bpairs A Aᶜ).card

private theorem expected_badCutWeight (n m : ℕ) (p : ℝ) :
    ∑ E : Finset (Sym2 (Fin n)), weight p E * badCutWeight m E =
      ∑ A ∈ midSets n m, (8 : ℝ) ^ A.card * (1 - p / 2) ^ (bpairs A Aᶜ).card := by
  unfold badCutWeight
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  have hE : ∀ E : Finset (Sym2 (Fin n)),
      weight p E * ((8 : ℝ) ^ A.card * (1 / 2) ^ (E ∩ bpairs A Aᶜ).card) =
        (8 : ℝ) ^ A.card * (weight p E * (1 / 2) ^ (E ∩ bpairs A Aᶜ).card) := fun E => by ring
  rw [Finset.sum_congr rfl fun E _ => hE E, ← Finset.mul_sum, sum_weight_mul_pow]
  congr 2
  ring

/-- With `n = 4 m` and `p = 8 / m`, the expected bad-cut witness is at most `(1 / 2) ^ m`. -/
private theorem expected_badCutWeight_le (m : ℕ) (hm : 8 ≤ m) :
    ∑ E : Finset (Sym2 (Fin (4 * m))), weight (8 / m) E * badCutWeight m E ≤ (1 / 2) ^ m := by
  rw [expected_badCutWeight]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  set q : ℝ := 1 - 8 / (m : ℝ) / 2 with hq
  have hq_eq : q = 1 - 4 / m := by
    rw [hq]
    ring
  have h4m : 4 / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm0]
    linarith
  have hq0 : 0 ≤ q := by
    rw [hq_eq]
    linarith
  have hq1 : q ≤ 1 := by
    rw [hq_eq]
    have : 0 ≤ 4 / (m : ℝ) := by positivity
    linarith
  have hqexp : q ≤ Real.exp (-(4 / m)) := by
    rw [hq_eq]
    exact Real.one_sub_le_exp_neg _
  have hexp8 : 8 * Real.exp (-8) ≤ 1 / 32 := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp 1
      linarith
    have h8 : Real.exp 8 = Real.exp 1 ^ 8 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h256 : (256 : ℝ) ≤ Real.exp 8 := by
      rw [h8]
      calc (256 : ℝ) = 2 ^ 8 := by norm_num
        _ ≤ Real.exp 1 ^ 8 := pow_le_pow_left₀ (by norm_num) h1 8
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos 8)]
    linarith
  have hterm : ∀ A ∈ midSets (4 * m) m,
      (8 : ℝ) ^ A.card * q ^ (bpairs A Aᶜ).card ≤ (1 / 32) ^ m := by
    intro A hA
    obtain ⟨hAm, hA2m⟩ := (Finset.mem_filter.mp hA).2
    have hcard : A.card * (2 * m) ≤ (bpairs A Aᶜ).card := by
      rw [card_bpairs A Aᶜ disjoint_compl_right, Finset.card_compl, Fintype.card_fin]
      exact Nat.mul_le_mul_left _ (by omega)
    calc (8 : ℝ) ^ A.card * q ^ (bpairs A Aᶜ).card
        ≤ 8 ^ A.card * q ^ (A.card * (2 * m)) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hq0 hq1 hcard) (by positivity)
      _ ≤ 8 ^ A.card * Real.exp (-(4 / m)) ^ (A.card * (2 * m)) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hqexp _) (by positivity)
      _ = (8 * Real.exp (-8)) ^ A.card := by
          rw [← Real.exp_nat_mul, mul_pow, ← Real.exp_nat_mul]
          congr 2
          push_cast
          field_simp
          ring
      _ ≤ (1 / 32) ^ A.card := pow_le_pow_left₀ (by positivity) hexp8 _
      _ ≤ (1 / 32) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hAm
  calc ∑ A ∈ midSets (4 * m) m, (8 : ℝ) ^ A.card * q ^ (bpairs A Aᶜ).card
      ≤ ∑ _A ∈ midSets (4 * m) m, ((1 : ℝ) / 32) ^ m := Finset.sum_le_sum hterm
    _ = (midSets (4 * m) m).card * ((1 : ℝ) / 32) ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2 ^ (4 * m) : ℕ) : ℝ) * ((1 : ℝ) / 32) ^ m := by
        gcongr
        calc (midSets (4 * m) m).card ≤ (Finset.univ : Finset (Finset (Fin (4 * m)))).card :=
              Finset.card_le_univ _
          _ = 2 ^ (4 * m) := by rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
    _ = (1 / 2) ^ m := by
        push_cast
        rw [pow_mul, ← mul_pow]
        norm_num

/-- Some outcome of the random graph on `4 m` vertices with edge probability `8 / m` has few
short-cycle tuples, fewer than `512 m` pairs, and sends more than `3 |A|` pairs out of every set
`A` of between `m` and `2 m` vertices. -/
private theorem exists_good_edges (g m : ℕ) (hm : 8 ≤ m) :
    ∃ E : Finset (Sym2 (Fin (4 * m))),
      shortCycleCount g E < 4 * (∑ j ∈ Finset.range (g - 3), 32 ^ (j + 3)) + 1 ∧
      E.card < 512 * m ∧
      ∀ A : Finset (Fin (4 * m)), m ≤ A.card → A.card ≤ 2 * m →
        3 * A.card < (E ∩ bpairs A Aᶜ).card := by
  set S : ℕ := ∑ j ∈ Finset.range (g - 3), 32 ^ (j + 3) with hS
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp0 : (0 : ℝ) ≤ 8 / m := by positivity
  have hp1 : 8 / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm0]
    exact_mod_cast hm
  have hK : (0 : ℝ) < 4 * S + 1 := by positivity
  have hX := expected_shortCycleCount_le (4 * m) g hp0
  have hXS : ∑ j ∈ Finset.range (g - 3), (((4 * m : ℕ) : ℝ) * (8 / m)) ^ (j + 3) = S := by
    rw [hS]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    field_simp
    ring
  rw [hXS] at hX
  have hE := expected_card_le m hm
  have hY := expected_badCutWeight_le m hm
  set Z : Finset (Sym2 (Fin (4 * m))) → ℝ := fun E =>
    (shortCycleCount g E : ℝ) / (4 * S + 1) + (E.card : ℝ) / (512 * m) + badCutWeight m E
    with hZ
  have hsum : ∑ E : Finset (Sym2 (Fin (4 * m))), weight (8 / (m : ℝ)) E * Z E < 1 := by
    have hsplit : ∑ E : Finset (Sym2 (Fin (4 * m))), weight (8 / (m : ℝ)) E * Z E =
        (∑ E : Finset (Sym2 (Fin (4 * m))),
            weight (8 / (m : ℝ)) E * (shortCycleCount g E : ℝ)) / (4 * S + 1) +
          (∑ E : Finset (Sym2 (Fin (4 * m))), weight (8 / (m : ℝ)) E * (E.card : ℝ)) /
            (512 * m) +
          ∑ E : Finset (Sym2 (Fin (4 * m))), weight (8 / (m : ℝ)) E * badCutWeight m E := by
      rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [hZ]
      ring
    rw [hsplit]
    have h1 : (∑ E : Finset (Sym2 (Fin (4 * m))),
        weight (8 / (m : ℝ)) E * (shortCycleCount g E : ℝ)) / (4 * S + 1) ≤ 1 / 4 := by
      rw [div_le_iff₀ hK]
      linarith
    have h2 : (∑ E : Finset (Sym2 (Fin (4 * m))), weight (8 / (m : ℝ)) E * (E.card : ℝ)) /
        (512 * m) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h3 : ((1 : ℝ) / 2) ^ m ≤ 1 / 4 := by
      calc ((1 : ℝ) / 2) ^ m ≤ (1 / 2) ^ 2 :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 4 := by norm_num
    linarith
  obtain ⟨E, hZE⟩ := exists_lt_one hp0 hp1 Z hsum
  have hX0 : 0 ≤ (shortCycleCount g E : ℝ) / (4 * S + 1) := by positivity
  have hE0 : 0 ≤ (E.card : ℝ) / (512 * m) := by positivity
  have hY0 : 0 ≤ badCutWeight m E := Finset.sum_nonneg fun A _ => by positivity
  have hZE' : (shortCycleCount g E : ℝ) / (4 * S + 1) + (E.card : ℝ) / (512 * m) +
      badCutWeight m E < 1 := hZE
  refine ⟨E, ?_, ?_, ?_⟩
  · have h : (shortCycleCount g E : ℝ) / (4 * S + 1) < 1 := by linarith
    rw [div_lt_one hK] at h
    exact_mod_cast h
  · have h : (E.card : ℝ) / (512 * m) < 1 := by linarith
    rw [div_lt_one (by positivity)] at h
    exact_mod_cast h
  · intro A hAm hA2m
    have hA : A ∈ midSets (4 * m) m := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAm, hA2m⟩
    have hle : (8 : ℝ) ^ A.card * (1 / 2) ^ (E ∩ bpairs A Aᶜ).card ≤ badCutWeight m E :=
      Finset.single_le_sum (f := fun A => (8 : ℝ) ^ A.card * (1 / 2) ^ (E ∩ bpairs A Aᶜ).card)
        (fun A _ => by positivity) hA
    have hlt : (8 : ℝ) ^ A.card * (1 / 2) ^ (E ∩ bpairs A Aᶜ).card < 1 := by linarith
    have h8 : (8 : ℝ) ^ A.card = 2 ^ (3 * A.card) := by
      rw [pow_mul]
      norm_num
    rw [h8, one_div, inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)] at hlt
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hlt

/-! ### The counterexamples -/

universe u

/-- For every `g`, some finite graph with at least two vertices, average degree below `400` and
girth at least `g` has no matching cut. -/
private theorem not_forall_hasMatchingCut (g : ℕ)
    (hg : ∀ (V : Type u) [Fintype V] [Nontrivial V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], (avgDegree G : ℝ) < 400 → (g : ℕ∞) ≤ G.egirth → HasMatchingCut G) :
    False := by
  classical
  set K : ℕ := 4 * (∑ j ∈ Finset.range (g - 3), 32 ^ (j + 3)) + 1 with hK
  set m : ℕ := g * K + 8 with hm
  obtain ⟨E, hX, hE, hexpE⟩ := exists_good_edges g m (by omega)
  set D := shortCycleEdges g E with hD
  set F := E \ D with hF
  have hDm : D.card < m := by
    have h1 : D.card ≤ g * shortCycleCount g E := card_shortCycleEdges_le g E
    have h2 : g * shortCycleCount g E ≤ g * K := Nat.mul_le_mul_left _ hX.le
    omega
  have hexpF : ∀ A : Finset (Fin (4 * m)), m ≤ A.card → A.card ≤ 2 * m →
      A.card + m < (F ∩ bpairs A Aᶜ).card := by
    intro A hAm hA2m
    have h1 := hexpE A hAm hA2m
    have h2 : (E ∩ bpairs A Aᶜ).card ≤ (F ∩ bpairs A Aᶜ).card + D.card := by
      refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
      intro e he
      obtain ⟨heE, heA⟩ := Finset.mem_inter.mp he
      by_cases heD : e ∈ D
      · exact Finset.mem_union_right _ heD
      · exact Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨heE, heD⟩, heA⟩)
    omega
  obtain ⟨Q, hQm, hcore⟩ := exists_core F m (by omega) (by simp) hexpF
  have hPcard : 3 * m < Qᶜ.card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  let W : Type u := ULift.{u} {x : Fin (4 * m) // x ∈ Qᶜ}
  let ι : W → Fin (4 * m) := fun a => a.down.1
  have hι : Function.Injective ι := fun a b hab => ULift.ext (Subtype.ext hab)
  have hPι : ∀ x, x ∈ Qᶜ ↔ ∃ w, ι w = x := fun x =>
    ⟨fun hx => ⟨⟨⟨x, hx⟩⟩, rfl⟩, fun ⟨w, hw⟩ => hw ▸ w.down.2⟩
  let H : SimpleGraph W := (SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin (4 * m))))).comap ι
  have hWcard : Fintype.card W = Qᶜ.card := by
    simp only [W, Fintype.card_ulift, Fintype.card_coe]
  have : Nontrivial W := by
    rw [← Fintype.one_lt_card_iff_nontrivial, hWcard]
    omega
  have havg : (avgDegree H : ℝ) < 400 := by
    have hedges : H.edgeFinset.card ≤ F.card := card_edgeFinset_comap_le F ι hι
    have hFE : F.card ≤ E.card := Finset.card_le_card Finset.sdiff_subset
    have h1 : (H.edgeFinset.card : ℝ) < 512 * m := by
      exact_mod_cast (hedges.trans hFE).trans_lt hE
    have h2 : (3 * m : ℝ) < Qᶜ.card := by exact_mod_cast hPcard
    unfold avgDegree
    rw [hWcard]
    push_cast
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have hgirth : (g : ℕ∞) ≤ H.egirth := le_egirth_comap g E ι hι
  have hHadj : ∀ w w', s(ι w, ι w') ∈ F → ι w ≠ ι w' → H.Adj w w' := fun w w' hw hne => by
    simp only [H, SimpleGraph.comap_adj, SimpleGraph.fromEdgeSet_adj]
    exact ⟨hw, hne⟩
  obtain ⟨S, hSP, hSne, hRne, h1, h2⟩ :=
    exists_sparse_cut F Qᶜ ι hι hPι H hHadj (hg W H havg hgirth)
  rcases hcore S hSP hSne hRne with h | h <;> omega

/-- **Negative answer to the matching cut and girth question.** It is not the case that for
every real number $d$ there is a natural number $g$ such that every simple graph on a finite
vertex set with at least two vertices, average degree less than $d$ and girth at least $g$ has a
matching cut. That is, there is a real number $d$ such that for every natural number $g$ some
simple graph on a finite vertex set with at least two vertices, average degree less than $d$ and
girth at least $g$ has no matching cut.

Feghali, Lucke, Paulusma and Ries (Lemma 5) construct, for every $g$, a connected 14-regular
bipartite graph of girth at least $g$ with no matching cut; these graphs give $d = 15$.

Source: C. Feghali, F. Lucke, D. Paulusma and B. Ries, Matching Cuts in Graphs of High
Girth and H-Free Graphs, ISAAC 2023, arXiv:2212.12317, https://arxiv.org/abs/2212.12317. Moved
from `OpenConjectures/Combinatorics/MatchingCutGirth`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  unfold conjecture at h
  obtain ⟨g, hg⟩ := h 400
  exact not_forall_hasMatchingCut g hg

end MathlibExt.Combinatorics.MatchingCutGirthWanted
