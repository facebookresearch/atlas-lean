/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Order.LiminfLimsup

/-!
# De Caen question on `k * (1 - π(K_{k+1}^k))`

This file proves `conjecture_refuted`: de Caen's conjecture that
`k * (1 - π(K_{k+1}^k))` tends to infinity is false. Following the recursive construction in the
proof of Lemma 2.1 of Pikhurko's paper, `Pikhurko.exists_isTuranSystemOn` builds, for every `m`
and every finite set `V` in a linear order, a family of `(2 ^ m - 1)`-subsets of `V` with at most
`12 / 2 ^ m * C(|V|, 2 ^ m - 1)` members such that every `2 ^ m`-subset of `V` contains one of
them. Hence `π(K_{k+1}^k) ≥ 1 - 12 / (k + 1)` for `k = 2 ^ m - 1`
(`one_sub_le_turanDensityComplete`), so `k * (1 - π(K_{k+1}^k)) ≤ 12` along this sequence
(`mul_one_sub_turanDensityComplete_le`).

Source: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source collection AIM Problem Lists, Source URL http://aimpl.org/hypergraphturan/1/.

Clause list from the source; every item appears in the formal text below:
1. Uniformity parameter `k : ℕ` with `k → ∞` via `Filter.atTop`.
2. `K_{k+1}^k` is the complete `k`-uniform hypergraph on `k + 1` vertices.
3. Vertex set `Fin (k + 1)`; edge set is all `k`-element subsets.
4. `F`-free means no embedding `Fin (k + 1) ↪ Fin n` sending each forbidden edge to an edge.
5. Turán number is the maximum edge count among `F`-free `k`-families on `Fin n`.
6. Ratio is `ex / C(n, k)`, with value `0` when `C(n, k) = 0`.
7. Density `π` is the `limsup` of the ratios as `n → ∞`.
8. Sequence `a k = k * (1 - π(K_{k+1}^k))`.
9. Question: does `a k` tend to `∞` as `k → ∞`, i.e. `Tendsto a atTop atTop`.

## Main results

* `Pikhurko.IsTuranSystemOn V r G`: every `(r + 1)`-subset of `V` contains an `r`-element member
  of `G`; for `V = Finset.univ : Finset (Fin n)` this says that `G` contains a Turán
  `(n, r + 1, r)`-system.
* `Pikhurko.exists_isTuranSystemOn`: such families of size at most
  `12 / 2 ^ m * C(|V|, 2 ^ m - 1)` exist for `r = 2 ^ m - 1`.
* `choose_le_turanNumber_add_card`: the complement of such a family in `Fin n` is
  `K_{k+1}^k`-free, so `C(n, k) ≤ turanNumber k n + |G|`.
* `one_sub_le_turanDensityRatio`, `one_sub_le_turanDensityComplete`: the resulting lower bounds
  `1 - 12 / 2 ^ m` on the Turán density ratios and on the Turán density of `K_{2^m}^{2^m - 1}`.
* `mul_one_sub_turanDensityComplete_le`: `k * (1 - π(K_{k+1}^k)) ≤ 12` for `k = 2 ^ m - 1`.
* `conjecture_refuted`: de Caen's conjecture is false.

## Proof

In this section, as in Pikhurko's paper, `r` is the uniformity (the `k` of `conjecture`) and `k`
is the size of an initial segment. Let `r + 1 = 2 ^ m = 2 * k`. Given a family `S` of
`(k - 1)`-subsets of `V`, the family `G` consists of

* all sets `B ∪ Z` with `B ∈ S` and `Z` an `(r - k + 1)`-set of elements above `max B`, and
* all sets `Y ∪ Z` where `Y` is a `k`-set containing no member of `S` and `Z` belongs to a family
  built recursively, for the uniformity `r - k = 2 ^ (m - 1) - 1`, on the elements of `V` above
  `max Y`.

Let `X` be an `(r + 1)`-subset of `V` and `Y` its `k` smallest elements. If `Y` contains some
`B ∈ S`, then `B ∪ (X \ Y)` is an `r`-subset of `X` in `G`. Otherwise the recursive family on the
elements above `max Y` contains an `(r - k)`-subset `Z` of `X \ Y`, and `Y ∪ Z ⊆ X` lies in `G`.

Choose `S` at random, keeping each `(k - 1)`-subset with probability `p = 2 / k`. Since `B`
consists of the `k - 1` smallest elements of `B ∪ Z`, the expected size of `G` is at most
`(p + (1 - p) ^ k * 12 / k) * C(|V|, r)`, where `(1 - p) ^ k` is the probability that a `k`-set
contains no member of `S` and `12 / k = 12 / (r - k + 1)` is the density of the recursive family.
Since `(1 - 2 / k) ^ k ≤ 1 / 3` by Bernoulli's inequality, this is at most
`(2 / k + 4 / k) * C(|V|, r) = 12 / (r + 1) * C(|V|, r)`. The random choice is replaced by a
weighted average over all families `S`, with weights `p ^ |S| * (1 - p) ^ (N - |S|)`, where `N`
is the number of `(k - 1)`-subsets of `V`.

Pikhurko takes `k = ⌊β (r + 1)⌋` for a general proportion `β ∈ (0, 1)`, which gives the constant
`6.239` for every uniformity `r ≥ 1` (Theorem 1.1). Here `β = 1 / 2`, `c = 2` and
`μ = 12` in the paper's notation, `e ^ (-c)` is replaced by the cruder bound `1 / 3`, and the
uniformities are restricted to `r = 2 ^ m - 1`, which keeps every quantity integral; a bounded
value of `r * (1 - π(K_{r+1}^r))` along any unbounded sequence of uniformities refutes the
conjecture.

## References

* O. Pikhurko, *Constructions of Turán systems that are tight up to a multiplicative constant*,
  Advances in Mathematics 464 (2025), 110148; arXiv:2406.07443, Lemma 2.1 and its proof.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.DeCaenTuranDefectGrowthWanted

open scoped Classical in
/-- **Edges of the complete uniform hypergraph.** For natural numbers $k$ and $m$, the edge
family of the complete $k$-uniform hypergraph on the vertex set $\{0, 1, \dots, m-1\}$ is the
family of all $k$-element subsets of $\{0, 1, \dots, m-1\}$.

Source: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
def completeHypergraphEdges (k m : ℕ) : Finset (Finset (Fin m)) :=
  Finset.univ.powersetCard k

open scoped Classical in
/-- **Turán number of the complete $k$-graph on $k+1$ vertices.** For natural numbers $k$ and
$n$, let $K_{k+1}^{(k)}$ be the complete $k$-uniform hypergraph on the vertex set
$\{0, 1, \dots, k\}$, whose edges are all $k$-element subsets of that set. The Turán number
$\mathrm{ex}(n, K_{k+1}^{(k)})$ is the largest size of a family $E$ of $k$-element subsets of
$\{0, 1, \dots, n-1\}$ that contains no copy of $K_{k+1}^{(k)}$, that is, for which there is no
injective map $f \colon \{0, 1, \dots, k\} \to \{0, 1, \dots, n-1\}$ such that the image under
$f$ of every edge of $K_{k+1}^{(k)}$ belongs to $E$.

Source: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
noncomputable def turanNumber (k n : ℕ) : ℕ :=
  let forb : Finset (Finset (Fin (k + 1))) := completeHypergraphEdges k (k + 1)
  let all : Finset (Finset (Finset (Fin n))) :=
    ((Finset.univ : Finset (Fin n)).powersetCard k).powerset
  let free := all.filter (fun E => ¬ ∃ f : Fin (k + 1) ↪ Fin n, ∀ e ∈ forb, Finset.map f e ∈ E)
  free.sup (fun E => E.card)

open scoped Classical in
/-- **Turán density ratio.** For natural numbers $k$ and $n$, the Turán density ratio is the
real number $\mathrm{ex}(n, K_{k+1}^{(k)}) / \binom{n}{k}$, where
$\mathrm{ex}(n, K_{k+1}^{(k)})$ is the Turán number of the complete $k$-uniform hypergraph
$K_{k+1}^{(k)}$ on $k+1$ vertices, the largest number of $k$-element subsets of an $n$-element
set containing no copy of $K_{k+1}^{(k)}$. The ratio is defined to be $0$ when
$\binom{n}{k} = 0$, that is, when $n < k$.

Source: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
noncomputable def turanDensityRatio (k n : ℕ) : ℝ :=
  if n.choose k = 0 then 0 else (turanNumber k n : ℝ) / (n.choose k : ℝ)

open scoped Classical in
/-- **Turán density of the complete $k$-graph on $k+1$ vertices.** For a natural number $k$,
the Turán density $\pi(K_{k+1}^{(k)})$ of the complete $k$-uniform hypergraph $K_{k+1}^{(k)}$
on $k+1$ vertices is the limit superior, as $n \to \infty$, of the Turán density ratios
$\mathrm{ex}(n, K_{k+1}^{(k)}) / \binom{n}{k}$, where $\mathrm{ex}(n, K_{k+1}^{(k)})$ is the
Turán number of $K_{k+1}^{(k)}$ and the ratio is taken to be $0$ when $\binom{n}{k} = 0$.

Source: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
noncomputable def turanDensityComplete (k : ℕ) : ℝ :=
  Filter.limsup (fun n : ℕ => turanDensityRatio k n) Filter.atTop

open scoped Classical in
/-- **De Caen's conjecture on Turán densities of complete hypergraphs.** For a natural number
$k$, let $\pi(K_{k+1}^{(k)})$ be the Turán density of the complete $k$-uniform hypergraph on
$k+1$ vertices. De Caen's conjecture asserts that $k \, (1 - \pi(K_{k+1}^{(k)})) \to \infty$
as $k \to \infty$.

Source: [AIM-COMBINATORICS-0149], aim-combinatorics-notes.json notes[148],
Source item 11.3, Section Complete hypergraphs, Workshop Hypergraph Turan problem,
Source URL http://aimpl.org/hypergraphturan/1/. -/
noncomputable def conjecture : Prop :=
  Filter.Tendsto (fun k : ℕ => (k : ℝ) * (1 - turanDensityComplete k)) Filter.atTop Filter.atTop

namespace Pikhurko

/-!
### Turán systems on finite subsets of a linear order

The recursive construction needs systems on the subsets `above Y V` of the ground set, so it works
with finite subsets `V` of an arbitrary linear order instead of `Fin n`.
-/

section Order

variable {α : Type*}

/-- **Turán systems on a finite set.** For a finite set $V$, a natural number $r$ and a family
$G$ of finite sets, `IsTuranSystemOn V r G` states that every $(r+1)$-element subset $X$ of $V$
contains a member $A$ of $G$ with exactly $r$ elements. When $V$ has $n$ elements, the
$r$-element members of $G$ contained in $V$ then form a Turán $(n, r+1, r)$-system on $V$. -/
def IsTuranSystemOn (V : Finset α) (r : ℕ) (G : Finset (Finset α)) : Prop :=
  ∀ X ⊆ V, X.card = r + 1 → ∃ A ∈ G, A ⊆ X ∧ A.card = r

/-- **The complete family is a Turán system.** For every finite set $V$ and natural number $r$,
the family of all $r$-element subsets of $V$ is a Turán system of uniformity $r$ on $V$. -/
theorem isTuranSystemOn_powersetCard (V : Finset α) (r : ℕ) :
    IsTuranSystemOn V r (V.powersetCard r) := by
  intro X hXV hXc
  obtain ⟨A, hAX, hAc⟩ := Finset.exists_subset_card_eq (show r ≤ X.card by omega)
  exact ⟨A, Finset.mem_powersetCard.mpr ⟨hAX.trans hXV, hAc⟩, hAX, hAc⟩

variable [LinearOrder α]

/-- **Elements above a set.** For finite sets $B$ and $V$ in a linear order, `above B V` is the
set of elements of $V$ that are strictly greater than every element of $B$; for $B = \emptyset$
it is $V$. -/
def above (B V : Finset α) : Finset α := V.filter fun v => ∀ b ∈ B, b < v

/-- **Membership in `above B V`.** An element $v$ lies in `above B V` if and only if $v \in V$
and $b < v$ for every $b \in B$. -/
theorem mem_above {B V : Finset α} {v : α} : v ∈ above B V ↔ v ∈ V ∧ ∀ b ∈ B, b < v :=
  Finset.mem_filter

/-- A set of elements above `B` is disjoint from `B`. -/
private lemma disjoint_of_subset_above {B V Z : Finset α} (h : Z ⊆ above B V) :
    Disjoint B Z := by
  rw [Finset.disjoint_left]
  intro b hb hbZ
  exact lt_irrefl b ((mem_above.mp (h hbZ)).2 b hb)

/-- Every finite set `X` with at least `k` elements has an initial segment of `k` elements: a
`k`-subset `Y` all of whose elements are smaller than every element of `X \ Y`. -/
private lemma exists_initial (X : Finset α) {k : ℕ} (hk : k ≤ X.card) :
    ∃ Y ⊆ X, Y.card = k ∧ ∀ y ∈ Y, ∀ x ∈ X \ Y, y < x := by
  induction k with
  | zero => exact ⟨∅, Finset.empty_subset _, rfl, by simp⟩
  | succ k ih =>
    obtain ⟨Y, hYX, hYc, hY⟩ := ih (Nat.le_of_succ_le hk)
    have hne : (X \ Y).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hYX]
      omega
    have haXY : (X \ Y).min' hne ∈ X \ Y := Finset.min'_mem _ _
    rw [Finset.mem_sdiff] at haXY
    refine ⟨insert ((X \ Y).min' hne) Y, Finset.insert_subset haXY.1 hYX, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem haXY.2, hYc]
    · intro y hy x hx
      rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hx
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact lt_of_le_of_ne (Finset.min'_le _ _ (Finset.mem_sdiff.mpr ⟨hx.1, hx.2.2⟩))
          (Ne.symm hx.2.1)
      · exact hY y hy x (Finset.mem_sdiff.mpr ⟨hx.1, hx.2.2⟩)

/-- Splitting a `(j + s)`-subset of `V` into its `j` smallest elements and the rest is injective:
the number of pairs `(Y, Z)` with `Y` a `j`-subset of `V` and `Z` an `s`-subset of `above Y V` is
at most `C(|V|, j + s)`. -/
private lemma sum_choose_above_le (V : Finset α) (j s : ℕ) :
    ∑ Y ∈ V.powersetCard j, (above Y V).card.choose s ≤ V.card.choose (j + s) := by
  have key : ∀ {Y Z Y' Z' : Finset α}, Z ⊆ above Y V → Z' ⊆ above Y' V → Y ∪ Z = Y' ∪ Z' →
      Y.card = Y'.card → Y ⊆ Y' := by
    intro Y Z Y' Z' hZ hZ' h hc a ha
    by_contra haY'
    have haZ' : a ∈ Z' := by
      have : a ∈ Y' ∪ Z' := h ▸ Finset.mem_union_left _ ha
      exact (Finset.mem_union.mp this).resolve_left haY'
    have hsub : Y' ⊆ Y := by
      intro b hb
      have hba : b < a := (mem_above.mp (hZ' haZ')).2 b hb
      have : b ∈ Y ∪ Z := h.symm ▸ Finset.mem_union_left _ hb
      rcases Finset.mem_union.mp this with hbY | hbZ
      · exact hbY
      · exact absurd ((mem_above.mp (hZ hbZ)).2 a ha) (not_lt.mpr hba.le)
    have := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h' => haY' (h' ▸ ha)⟩)
    omega
  calc ∑ Y ∈ V.powersetCard j, (above Y V).card.choose s
      = ∑ Y ∈ V.powersetCard j, ((above Y V).powersetCard s).card := by
        simp only [Finset.card_powersetCard]
    _ = ((V.powersetCard j).sigma fun Y => (above Y V).powersetCard s).card :=
        (Finset.card_sigma _ _).symm
    _ ≤ (V.powersetCard (j + s)).card := by
        refine Finset.card_le_card_of_injOn (fun p => p.1 ∪ p.2) ?_ ?_
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard,
            Finset.mem_powersetCard] at hp
          obtain ⟨⟨hY, hYc⟩, hZ, hZc⟩ := hp
          have hZV : p.2 ⊆ V := hZ.trans (Finset.filter_subset _ _)
          rw [Finset.mem_coe, Finset.mem_powersetCard]
          refine ⟨Finset.union_subset hY hZV, ?_⟩
          rw [Finset.card_union_of_disjoint (disjoint_of_subset_above hZ), hYc, hZc]
        · intro p hp q hq hpq
          rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_powersetCard,
            Finset.mem_powersetCard] at hp hq
          obtain ⟨⟨hY, hYc⟩, hZ, hZc⟩ := hp
          obtain ⟨⟨hY', hY'c⟩, hZ', hZ'c⟩ := hq
          dsimp only at hpq
          have h1 : p.1 = q.1 :=
            Finset.eq_of_subset_of_card_le (key hZ hZ' hpq (hYc.trans hY'c.symm)) (by omega)
          have h2 : p.2 = q.2 := by
            have e1 := Finset.union_sdiff_cancel_left (disjoint_of_subset_above hZ)
            have e2 := Finset.union_sdiff_cancel_left (disjoint_of_subset_above hZ')
            rw [← e1, ← e2, hpq, h1]
          exact Sigma.ext h1 (heq_of_eq h2)
    _ = V.card.choose (j + s) := Finset.card_powersetCard _ _

end Order

/-!
### Averaging over random subfamilies

Choosing each element of a finite set `U` independently with probability `p` gives the subset
`S ⊆ U` the weight `p ^ |S| * (1 - p) ^ |U \ S|`. The lemmas below compute the needed expectations
as weighted sums over `U.powerset`, without measure theory.
-/

section Weights

variable {β : Type*} [DecidableEq β]

/-- The weight `p ^ |S| * (1 - p) ^ |U \ S|` of a subset `S` of `U` when each element of `U` is
chosen independently with probability `p`. -/
private noncomputable def weight (U : Finset β) (p : ℝ) (S : Finset β) : ℝ :=
  p ^ S.card * (1 - p) ^ (U \ S).card

private lemma weight_nonneg (U : Finset β) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (S : Finset β) :
    0 ≤ weight U p S :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- The probability that a random subset of `U` avoids every element satisfying `Q` is
`(1 - p) ^ |{B ∈ U | Q B}|`. -/
private lemma sum_weight_avoid (U : Finset β) (p : ℝ) (Q : β → Prop) [DecidablePred Q] :
    ∑ S ∈ U.powerset, (if ∀ B ∈ S, ¬ Q B then weight U p S else 0) =
      (1 - p) ^ (U.filter Q).card := by
  have h := Finset.prod_add (fun a => if Q a then (0 : ℝ) else p) (fun _ => 1 - p) U
  have lhs : ∏ a ∈ U, ((if Q a then (0 : ℝ) else p) + (1 - p)) =
      (1 - p) ^ (U.filter Q).card := by
    rw [Finset.prod_congr rfl fun a _ => (show (if Q a then (0 : ℝ) else p) + (1 - p) =
      if Q a then 1 - p else 1 by split_ifs <;> ring), ← Finset.prod_filter, Finset.prod_const]
  rw [lhs] at h
  rw [h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.prod_const]
  split_ifs with ht
  · rw [Finset.prod_congr rfl fun a ha => ite_eq_right (ht a ha), Finset.prod_const]
    rfl
  · push Not at ht
    obtain ⟨a, ha, hQa⟩ := ht
    rw [Finset.prod_eq_zero ha (by simp [hQa]), zero_mul]

/-- The weights sum to `1`. -/
private lemma sum_weight (U : Finset β) (p : ℝ) : ∑ S ∈ U.powerset, weight U p S = 1 := by
  simpa using sum_weight_avoid U p (fun _ => False)

/-- Each element of `U` lies in the random subset with probability `p`. -/
private lemma sum_weight_mem (U : Finset β) (p : ℝ) {B : β} (hB : B ∈ U) :
    ∑ S ∈ U.powerset, (if B ∈ S then weight U p S else 0) = p := by
  have h1 := sum_weight U p
  have h2 := sum_weight_avoid U p (fun B' => B' = B)
  rw [Finset.filter_eq' U B, ite_eq_left hB, Finset.card_singleton, pow_one] at h2
  have : ∀ S, (if B ∈ S then weight U p S else 0) =
      weight U p S - (if ∀ B' ∈ S, ¬ B' = B then weight U p S else 0) := by
    intro S
    by_cases hS : B ∈ S
    · rw [ite_eq_left hS, ite_eq_right (fun h => h B hS rfl)]; ring
    · rw [ite_eq_right hS, ite_eq_left (by rintro B' hB' rfl; exact hS hB')]; ring
  rw [Finset.sum_congr rfl fun S _ => this S, Finset.sum_sub_distrib, h1, h2]
  ring

/-- Linearity of expectation: the expected value of `∑ B ∈ S, f B` is `p * ∑ B ∈ U, f B`. -/
private lemma sum_weight_mul_sum (U : Finset β) (p : ℝ) (f : β → ℝ) :
    ∑ S ∈ U.powerset, weight U p S * ∑ B ∈ S, f B = p * ∑ B ∈ U, f B := by
  calc ∑ S ∈ U.powerset, weight U p S * ∑ B ∈ S, f B
      = ∑ S ∈ U.powerset, ∑ B ∈ U, (if B ∈ S then weight U p S else 0) * f B := by
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [Finset.mem_powerset] at hS
        rw [Finset.mul_sum]
        refine Finset.sum_subset_zero_on_sdiff hS (fun B hB => ?_) (fun B hB => ?_)
        · rw [ite_eq_right (Finset.mem_sdiff.mp hB).2, zero_mul]
        · rw [ite_eq_left hB]
    _ = ∑ B ∈ U, ∑ S ∈ U.powerset, (if B ∈ S then weight U p S else 0) * f B := Finset.sum_comm
    _ = ∑ B ∈ U, p * f B := by
        refine Finset.sum_congr rfl fun B hB => ?_
        rw [← Finset.sum_mul, sum_weight_mem U p hB]
    _ = p * ∑ B ∈ U, f B := (Finset.mul_sum _ _ _).symm

/-- The expected value of the sum of `h` over the elements `Y ∈ W` that are in relation `R` with no
element of the random subset. -/
private lemma sum_weight_mul_sum_avoid {γ : Type*} (U : Finset β) (p : ℝ) (W : Finset γ)
    (R : γ → β → Prop) [∀ Y B, Decidable (R Y B)] (h : γ → ℝ) :
    ∑ S ∈ U.powerset, weight U p S * ∑ Y ∈ W.filter (fun Y => ∀ B ∈ S, ¬ R Y B), h Y =
      ∑ Y ∈ W, (1 - p) ^ (U.filter (R Y)).card * h Y := by
  calc ∑ S ∈ U.powerset, weight U p S * ∑ Y ∈ W.filter (fun Y => ∀ B ∈ S, ¬ R Y B), h Y
      = ∑ S ∈ U.powerset, ∑ Y ∈ W, (if ∀ B ∈ S, ¬ R Y B then weight U p S else 0) * h Y := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun Y _ => ?_
        split_ifs <;> ring
    _ = ∑ Y ∈ W, ∑ S ∈ U.powerset, (if ∀ B ∈ S, ¬ R Y B then weight U p S else 0) * h Y :=
        Finset.sum_comm
    _ = ∑ Y ∈ W, (1 - p) ^ (U.filter (R Y)).card * h Y := by
        refine Finset.sum_congr rfl fun Y _ => ?_
        rw [← Finset.sum_mul, sum_weight_avoid U p (R Y)]

/-- Some value of `F` is at most its weighted average. -/
private lemma exists_le_of_weighted {ι : Type*} (s : Finset ι) (w F : ι → ℝ) (c : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (h1 : ∑ i ∈ s, w i = 1) (h : ∑ i ∈ s, w i * F i ≤ c) :
    ∃ i ∈ s, F i ≤ c := by
  by_contra hcon
  push Not at hcon
  have hpos : ∃ i ∈ s, 0 < w i := by
    by_contra h0
    push Not at h0
    have : ∑ i ∈ s, w i ≤ 0 := Finset.sum_nonpos h0
    linarith
  obtain ⟨i, hi, hwi⟩ := hpos
  have hlt : ∑ i ∈ s, w i * c < ∑ i ∈ s, w i * F i :=
    Finset.sum_lt_sum (fun j hj => mul_le_mul_of_nonneg_left (hcon j hj).le (hw j hj))
      ⟨i, hi, mul_lt_mul_of_pos_left (hcon i hi) hwi⟩
  rw [← Finset.sum_mul, h1, one_mul] at hlt
  linarith

end Weights

section Construction

variable {α : Type*} [LinearOrder α]

/-- A `k`-subset of `V` contains exactly `k` of the `(k - 1)`-subsets of `V`. -/
private lemma card_filter_subset {V Y : Finset α} {k : ℕ} (hk : 1 ≤ k)
    (hY : Y ∈ V.powersetCard k) : ((V.powersetCard (k - 1)).filter (· ⊆ Y)).card = k := by
  rw [Finset.mem_powersetCard] at hY
  have : (V.powersetCard (k - 1)).filter (· ⊆ Y) = Y.powersetCard (k - 1) := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨h.1.trans hY.1, h.2⟩, h.1⟩⟩
  rw [this, Finset.card_powersetCard, hY.2]
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp [Nat.choose_succ_self_right]

/-- **Pikhurko's recursion step** (proof of Lemma 2.1 of Pikhurko's paper). Let `1 ≤ k ≤ r`. If
every finite set `W` carries a Turán system `G' W` of uniformity `r - k` with at most
`M * C(|W|, r - k)` members, then for every `p ∈ [0, 1]` the set `V` carries a Turán system of
uniformity `r` with at most `(p + (1 - p) ^ k * M) * C(|V|, r)` members.

For a family `S` of `(k - 1)`-subsets of `V`, let `T S` be the set of `k`-subsets of `V` containing
no member of `S`. The system `Gs S` consists of the sets `B ∪ Z` with `B ∈ S` and `Z` an
`(r - k + 1)`-subset of `above B V`, and of the sets `Y ∪ Z` with `Y ∈ T S` and
`Z ∈ G' (above Y V)`. Its size is at most `F S`, whose average over random `S` with inclusion
probability `p` is at most `(p + (1 - p) ^ k * M) * C(|V|, r)`. -/
private lemma exists_isTuranSystemOn_step (V : Finset α) {k r : ℕ} (hk : 1 ≤ k) (hkr : k ≤ r)
    (G' : Finset α → Finset (Finset α)) (hG' : ∀ W, IsTuranSystemOn W (r - k) (G' W))
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ W, ((G' W).card : ℝ) ≤ M * (W.card.choose (r - k)))
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ G, IsTuranSystemOn V r G ∧
      (G.card : ℝ) ≤ (p + (1 - p) ^ k * M) * (V.card.choose r) := by
  classical
  set U := V.powersetCard (k - 1)
  set W := V.powersetCard k
  let T : Finset (Finset α) → Finset (Finset α) := fun S =>
    W.filter fun Y => ∀ B ∈ S, ¬ B ⊆ Y
  let Gs : Finset (Finset α) → Finset (Finset α) := fun S =>
    S.biUnion (fun B => ((above B V).powersetCard (r - k + 1)).image (B ∪ ·)) ∪
      (T S).biUnion (fun Y => (G' (above Y V)).image (Y ∪ ·))
  let F : Finset (Finset α) → ℝ := fun S =>
    ∑ B ∈ S, ((above B V).card.choose (r - k + 1) : ℝ) +
      ∑ Y ∈ T S, M * ((above Y V).card.choose (r - k) : ℝ)
  have hcover : ∀ S ∈ U.powerset, IsTuranSystemOn V r (Gs S) := by
    intro S hS X hXV hXc
    rw [Finset.mem_powerset] at hS
    obtain ⟨Y, hYX, hYc, hYlt⟩ := exists_initial X (k := k) (by omega)
    have hZ0c : (X \ Y).card = r - k + 1 := by
      rw [Finset.card_sdiff_of_subset hYX, hXc, hYc]; omega
    by_cases hT : ∀ B ∈ S, ¬ B ⊆ Y
    · have hYT : Y ∈ T S :=
        Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨hYX.trans hXV, hYc⟩, hT⟩
      have hZ0 : X \ Y ⊆ above Y V := fun z hz =>
        mem_above.mpr ⟨hXV (Finset.sdiff_subset hz), fun y hy => hYlt y hy z hz⟩
      obtain ⟨Z, hZG, hZsub, hZc⟩ := hG' (above Y V) (X \ Y) hZ0 hZ0c
      refine ⟨Y ∪ Z, Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨Y, hYT, Finset.mem_image.mpr ⟨Z, hZG, rfl⟩⟩),
        Finset.union_subset hYX (hZsub.trans Finset.sdiff_subset), ?_⟩
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_right hZsub Finset.disjoint_sdiff), hYc, hZc]
      omega
    · push Not at hT
      obtain ⟨B, hBS, hBY⟩ := hT
      have hBc : B.card = k - 1 := (Finset.mem_powersetCard.mp (hS hBS)).2
      have hZB : X \ Y ⊆ above B V := fun z hz =>
        mem_above.mpr ⟨hXV (Finset.sdiff_subset hz), fun b hb => hYlt b (hBY hb) z hz⟩
      refine ⟨B ∪ (X \ Y), Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨B, hBS, Finset.mem_image.mpr ⟨X \ Y, Finset.mem_powersetCard.mpr ⟨hZB, hZ0c⟩, rfl⟩⟩),
        Finset.union_subset (hBY.trans hYX) Finset.sdiff_subset, ?_⟩
      rw [Finset.card_union_of_disjoint
        (Finset.disjoint_of_subset_left hBY Finset.disjoint_sdiff), hBc, hZ0c]
      omega
  have hcard : ∀ S, ((Gs S).card : ℝ) ≤ F S := by
    intro S
    have h1 : ((S.biUnion fun B =>
        ((above B V).powersetCard (r - k + 1)).image (B ∪ ·)).card : ℝ) ≤
          ∑ B ∈ S, ((above B V).card.choose (r - k + 1) : ℝ) := by
      have : (S.biUnion fun B => ((above B V).powersetCard (r - k + 1)).image (B ∪ ·)).card ≤
          ∑ B ∈ S, (above B V).card.choose (r - k + 1) := by
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun B _ => ?_)
        exact Finset.card_image_le.trans (Finset.card_powersetCard _ _).le
      exact_mod_cast this
    have h2 : (((T S).biUnion fun Y => (G' (above Y V)).image (Y ∪ ·)).card : ℝ) ≤
        ∑ Y ∈ T S, M * ((above Y V).card.choose (r - k) : ℝ) := by
      calc (((T S).biUnion fun Y => (G' (above Y V)).image (Y ∪ ·)).card : ℝ)
          ≤ ((∑ Y ∈ T S, (G' (above Y V)).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_biUnion_le.trans
              (Finset.sum_le_sum fun Y _ => Finset.card_image_le)
        _ = ∑ Y ∈ T S, ((G' (above Y V)).card : ℝ) := by push_cast; rfl
        _ ≤ _ := Finset.sum_le_sum fun Y _ => hM _
    calc ((Gs S).card : ℝ) ≤ ((S.biUnion fun B =>
          ((above B V).powersetCard (r - k + 1)).image (B ∪ ·)).card : ℝ) +
          (((T S).biUnion fun Y => (G' (above Y V)).image (Y ∪ ·)).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _
      _ ≤ F S := add_le_add h1 h2
  have hP1 : ∑ S ∈ U.powerset, weight U p S *
      ∑ B ∈ S, ((above B V).card.choose (r - k + 1) : ℝ) ≤ p * (V.card.choose r : ℝ) := by
    rw [sum_weight_mul_sum]
    apply mul_le_mul_of_nonneg_left _ hp0
    have := sum_choose_above_le V (k - 1) (r - k + 1)
    rw [show k - 1 + (r - k + 1) = r by omega] at this
    exact_mod_cast this
  have hP2 : ∑ S ∈ U.powerset, weight U p S *
      ∑ Y ∈ T S, M * ((above Y V).card.choose (r - k) : ℝ) ≤
        (1 - p) ^ k * M * (V.card.choose r : ℝ) := by
    rw [sum_weight_mul_sum_avoid U p W (fun Y B => B ⊆ Y)]
    calc ∑ Y ∈ W, (1 - p) ^ (U.filter (· ⊆ Y)).card *
          (M * ((above Y V).card.choose (r - k) : ℝ))
        = ∑ Y ∈ W, (1 - p) ^ k * M * ((above Y V).card.choose (r - k) : ℝ) := by
          refine Finset.sum_congr rfl fun Y hY => ?_
          rw [card_filter_subset hk hY]; ring
      _ = (1 - p) ^ k * M * ∑ Y ∈ W, ((above Y V).card.choose (r - k) : ℝ) :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (1 - p) ^ k * M * (V.card.choose r : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg (sub_nonneg.mpr hp1) _) hM0)
          have := sum_choose_above_le V k (r - k)
          rw [show k + (r - k) = r by omega] at this
          exact_mod_cast this
  have havg : ∑ S ∈ U.powerset, weight U p S * F S ≤
      (p + (1 - p) ^ k * M) * (V.card.choose r) := by
    calc ∑ S ∈ U.powerset, weight U p S * F S
        = (∑ S ∈ U.powerset, weight U p S *
            ∑ B ∈ S, ((above B V).card.choose (r - k + 1) : ℝ)) +
          ∑ S ∈ U.powerset, weight U p S *
            ∑ Y ∈ T S, M * ((above Y V).card.choose (r - k) : ℝ) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun S _ => mul_add _ _ _
      _ ≤ p * (V.card.choose r : ℝ) + (1 - p) ^ k * M * (V.card.choose r : ℝ) :=
          add_le_add hP1 hP2
      _ = (p + (1 - p) ^ k * M) * (V.card.choose r) := by ring
  obtain ⟨S, hS, hFS⟩ := exists_le_of_weighted U.powerset (weight U p) F _
    (fun S _ => weight_nonneg U hp0 hp1 S) (sum_weight U p) havg
  exact ⟨Gs S, hcover S hS, (hcard S).trans hFS⟩

/-- `(1 - 2 / K) ^ K ≤ 1 / 3` for `K ≥ 2`, from `1 - x ≤ 1 / (1 + x)` and Bernoulli's inequality
`(1 + 2 / K) ^ K ≥ 3`. -/
private lemma one_sub_two_div_pow_le {K : ℕ} (hK : 2 ≤ K) :
    (1 - 2 / (K : ℝ)) ^ K ≤ 1 / 3 := by
  have hKpos : (0 : ℝ) < K := by positivity
  have hx0 : 0 ≤ 1 - 2 / (K : ℝ) := by
    rw [sub_nonneg, div_le_one hKpos]; exact_mod_cast hK
  have h1 : 1 - 2 / (K : ℝ) ≤ 1 / (1 + 2 / K) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 / (K : ℝ))]
  have h2 : (3 : ℝ) ≤ (1 + 2 / K) ^ K := by
    have := one_add_mul_le_pow (a := 2 / (K : ℝ))
      (by linarith [show 0 ≤ 2 / (K : ℝ) by positivity]) K
    rw [mul_div_cancel₀ _ hKpos.ne'] at this
    linarith
  calc (1 - 2 / (K : ℝ)) ^ K ≤ (1 / (1 + 2 / K)) ^ K := pow_le_pow_left₀ hx0 h1 K
    _ = 1 / (1 + 2 / K) ^ K := by rw [div_pow, one_pow]
    _ ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) h2

/-- **Turán systems of size $O(1/k)$** (Pikhurko, proof of Lemma 2.1, with $\beta = 1/2$ and
$c = 2$). For every natural number $m$ and every finite set $V$ in a linear order, there is a
family $G$ of finite sets with at most $\frac{12}{2^m} \binom{|V|}{2^m - 1}$ members such that every
$2^m$-element subset of $V$ contains a member of $G$ with $2^m - 1$ elements. -/
theorem exists_isTuranSystemOn (m : ℕ) (V : Finset α) :
    ∃ G : Finset (Finset α), IsTuranSystemOn V (2 ^ m - 1) G ∧
      (G.card : ℝ) ≤ 12 / 2 ^ m * (V.card.choose (2 ^ m - 1)) := by
  induction m generalizing V with
  | zero =>
    refine ⟨V.powersetCard (2 ^ 0 - 1), isTuranSystemOn_powersetCard V _, ?_⟩
    rw [Finset.card_powersetCard]
    have : (0 : ℝ) ≤ (V.card.choose (2 ^ 0 - 1) : ℝ) := Nat.cast_nonneg _
    norm_num
  | succ m ih =>
    by_cases hsmall : (2 : ℝ) ^ (m + 1) ≤ 12
    · -- For `2 ^ (m + 1) ≤ 12` the family of all `(2 ^ (m + 1) - 1)`-subsets is small enough.
      refine ⟨V.powersetCard (2 ^ (m + 1) - 1), isTuranSystemOn_powersetCard V _, ?_⟩
      rw [Finset.card_powersetCard]
      have h1 : (1 : ℝ) ≤ 12 / 2 ^ (m + 1) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have : (0 : ℝ) ≤ (V.card.choose (2 ^ (m + 1) - 1) : ℝ) := Nat.cast_nonneg _
      nlinarith
    · -- Otherwise apply the recursion step with `k = 2 ^ m`, `p = 2 / k` and `M = 12 / k`.
      push Not at hsmall
      have hK : 2 ≤ 2 ^ m := by
        by_contra hlt
        push Not at hlt
        have : (2 : ℝ) ^ m < 2 := by exact_mod_cast hlt
        have : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
        linarith
      choose G' hG'cover hG'card using ih
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      have hrk : 2 ^ (m + 1) - 1 - 2 ^ m = 2 ^ m - 1 := by omega
      have hKR : (0 : ℝ) < 2 ^ m := by positivity
      obtain ⟨G, hG, hGc⟩ := exists_isTuranSystemOn_step V (k := 2 ^ m)
        (r := 2 ^ (m + 1) - 1) (by omega) (by omega) G'
        (fun W => hrk ▸ hG'cover W) (M := 12 / 2 ^ m) (by positivity)
        (fun W => hrk ▸ hG'card W) (p := 2 / 2 ^ m) (by positivity)
        (by rw [div_le_one hKR]; exact_mod_cast hK)
      refine ⟨G, hG, hGc.trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))⟩
      have hb := one_sub_two_div_pow_le hK
      push_cast at hb
      have hM0 : (0 : ℝ) ≤ 12 / 2 ^ m := by positivity
      calc (2 : ℝ) / 2 ^ m + (1 - 2 / 2 ^ m) ^ 2 ^ m * (12 / 2 ^ m)
          ≤ 2 / 2 ^ m + 1 / 3 * (12 / 2 ^ m) := by gcongr
        _ = 12 / 2 ^ (m + 1) := by rw [pow_succ]; field_simp; ring

end Construction

end Pikhurko

open Pikhurko

/-- **The Turán number is at most a binomial coefficient.** For natural numbers $k$ and $n$,
$\mathrm{ex}(n, K_{k+1}^{(k)}) \le \binom{n}{k}$: every family of $k$-element subsets of
$\{0, 1, \dots, n-1\}$ has at most $\binom{n}{k}$ members. -/
theorem turanNumber_le_choose (k n : ℕ) : turanNumber k n ≤ n.choose k := by
  unfold turanNumber
  apply Finset.sup_le
  intro E hE
  have hE' := (Finset.mem_filter.mp hE).1
  rw [Finset.mem_powerset] at hE'
  calc E.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard k).card := Finset.card_le_card hE'
    _ = n.choose k := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **Complements of Turán systems are $K_{k+1}^{(k)}$-free.** Let $k$ and $n$ be natural numbers
and let $G$ be a family of subsets of $\{0, 1, \dots, n-1\}$ such that every $(k+1)$-element
subset contains a $k$-element member of $G$. Then the $k$-element sets not in $G$ form a
$K_{k+1}^{(k)}$-free family, so $\binom{n}{k} \le \mathrm{ex}(n, K_{k+1}^{(k)}) + |G|$. -/
theorem choose_le_turanNumber_add_card {k n : ℕ} {G : Finset (Finset (Fin n))}
    (hG : IsTuranSystemOn Finset.univ k G) : n.choose k ≤ turanNumber k n + G.card := by
  have h1 : (((Finset.univ : Finset (Fin n)).powersetCard k) \ G).card ≤ turanNumber k n := by
    unfold turanNumber
    dsimp only
    refine Finset.le_sup (f := fun E : Finset (Finset (Fin n)) => E.card) ?_
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.sdiff_subset, ?_⟩
    rintro ⟨f, hf⟩
    -- The image of `f` contains a member `A` of `G`, the image of a `k`-subset of `Fin (k + 1)`.
    obtain ⟨A, hAG, hAX, hAc⟩ := hG (Finset.univ.map f) (Finset.subset_univ _) (by simp)
    have hmap : (Finset.univ.filter (fun i => f i ∈ A)).map f = A := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact hi
      · intro hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp (hAX hx)
        exact ⟨i, hx, rfl⟩
    have he : Finset.univ.filter (fun i => f i ∈ A) ∈ completeHypergraphEdges k (k + 1) := by
      rw [completeHypergraphEdges, Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [← Finset.card_map f, hmap, hAc]
    have := hf _ he
    rw [hmap, Finset.mem_sdiff] at this
    exact this.2 hAG
  have h2 := Finset.card_le_card_sdiff_add_card
    (s := (Finset.univ : Finset (Fin n)).powersetCard k) (t := G)
  rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin] at h2
  omega

/-- **Lower bound on the Turán density ratios.** For natural numbers $m$ and $n$ with
$n \ge 2^m - 1$, the Turán density ratio of $K_{2^m}^{(2^m - 1)}$ satisfies
$\mathrm{ex}(n, K_{2^m}^{(2^m-1)}) / \binom{n}{2^m - 1} \ge 1 - 12 / 2^m$. -/
theorem one_sub_le_turanDensityRatio (m n : ℕ) (hn : 2 ^ m - 1 ≤ n) :
    1 - 12 / 2 ^ m ≤ turanDensityRatio (2 ^ m - 1) n := by
  obtain ⟨G, hG, hGc⟩ := exists_isTuranSystemOn m (Finset.univ : Finset (Fin n))
  have h := choose_le_turanNumber_add_card hG
  rw [Finset.card_univ, Fintype.card_fin] at hGc
  have hpos : 0 < n.choose (2 ^ m - 1) := Nat.choose_pos hn
  unfold turanDensityRatio
  rw [ite_eq_right hpos.ne', le_div_iff₀ (by exact_mod_cast hpos)]
  have h' : (n.choose (2 ^ m - 1) : ℝ) ≤ turanNumber (2 ^ m - 1) n + G.card := by
    exact_mod_cast h
  rw [sub_mul, one_mul]
  linarith

/-- **Lower bound on the Turán density.** For every natural number $m$, the Turán density of the
complete $(2^m - 1)$-uniform hypergraph on $2^m$ vertices satisfies
$\pi(K_{2^m}^{(2^m - 1)}) \ge 1 - 12 / 2^m$. -/
theorem one_sub_le_turanDensityComplete (m : ℕ) :
    1 - 12 / 2 ^ m ≤ turanDensityComplete (2 ^ m - 1) := by
  unfold turanDensityComplete
  apply Filter.le_limsup_of_frequently_le
  · exact (Filter.eventually_atTop.mpr
      ⟨2 ^ m - 1, fun n hn => one_sub_le_turanDensityRatio m n hn⟩).frequently
  · refine Filter.isBoundedUnder_of ⟨1, fun n => ?_⟩
    unfold turanDensityRatio
    split_ifs with h
    · norm_num
    · rw [div_le_one (by positivity)]
      exact_mod_cast turanNumber_le_choose _ _

/-- **De Caen's quantity stays bounded along $k = 2^m - 1$.** For every natural number $m$ and
$k = 2^m - 1$, the Turán density of the complete $k$-uniform hypergraph on $k + 1$ vertices
satisfies $k \, (1 - \pi(K_{k+1}^{(k)})) \le 12$. -/
theorem mul_one_sub_turanDensityComplete_le (m : ℕ) :
    ((2 ^ m - 1 : ℕ) : ℝ) * (1 - turanDensityComplete (2 ^ m - 1)) ≤ 12 := by
  have h := one_sub_le_turanDensityComplete m
  rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
  calc (2 ^ m - 1 : ℝ) * (1 - turanDensityComplete (2 ^ m - 1))
      ≤ (2 ^ m - 1) * (12 / 2 ^ m) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ 12 := by
      rw [mul_div_assoc', div_le_iff₀ hpos]
      nlinarith

/--
**De Caen's conjecture is false.** It is not the case that $k \, (1 - \pi(K_{k+1}^{(k)}))$
tends to $\infty$ as $k \to \infty$, where $\pi(K_{k+1}^{(k)})$ is the Turán density of the
complete $k$-uniform hypergraph $K_{k+1}^{(k)}$ on $k+1$ vertices.

Pikhurko (Adv. Math. 464 (2025) 110148, Theorem 1.1) proves
$T(n, k+1, k) \le \frac{6.239}{k+1} \binom{n}{k}$ for all $n > k \ge 1$, where $T(n, k+1, k)$
is the least number of $k$-element subsets of an $n$-element set such that every
$(k+1)$-element subset contains one of them; hence $k \, (1 - \pi(K_{k+1}^{(k)})) \le 6.239$
for every $k \ge 1$, and the paper states that this disproves de Caen's conjecture.

Source: O. Pikhurko, Constructions
of Turán systems that are tight up to a multiplicative constant, Advances in Mathematics 464
(2025), 110148, https://pikhurko.github.io/E/Pikhurko25am.pdf. Moved from
`OpenConjectures/Combinatorics/DeCaenTuranDefectGrowth`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (h.eventually_gt_atTop 12)
  have hk : N ≤ 2 ^ N - 1 := by have := Nat.lt_two_pow_self (n := N); omega
  exact (hN _ hk).not_ge (mul_one_sub_turanDensityComplete_le N)

end MathlibExt.Combinatorics.DeCaenTuranDefectGrowthWanted
