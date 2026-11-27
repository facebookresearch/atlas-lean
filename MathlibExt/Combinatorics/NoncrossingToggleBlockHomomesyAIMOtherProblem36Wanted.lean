/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring

/-!
# Block-count homomesy for toggling noncrossing partitions (AIM dynamical combinatorics, Conj. 5.8)

AIM workshop Dynamical algebraic combinatorics, pre-workshop document, §5.4, Conjecture 5.8: for a
noncrossing partition of `{1, …, n}` and `i < j`, the toggle `τ_{i,j}` splits a block at consecutive
elements `i, j`, merges a block ending at `i` with one starting at `j` when the result is
noncrossing, and otherwise does nothing; `σ` toggles successively at `(1,2), (2,3), …, (n-1,n),
(1,3), …, (n-2,n), …, (1,n)`. The number of blocks is homomesic under `σ` with average `(n + 1)/2`
on each orbit.

The main result is `noncrossingToggleBlockHomomesy_holds`, which proves the claim
`noncrossingToggleBlockHomomesy` about the toggle composite on arc sets.

Source: AIM workshop Dynamical algebraic combinatorics, pre-workshop document,
http://aimath.org/pastworkshops/dac_preworkshop.pdf, §5.4, Conjecture 5.8. UnsolvedMath record
UM-20003229 (`AIM-OTHER-0036`), dataset ulamai/UnsolvedMath v1.8.0.

A noncrossing partition is its linear representation (Einstein et al., §1): the arcs `(i, j)`, `i <
j`, joining successive elements of a block, with no two arcs crossing or sharing a left or a right
endpoint; it has `n - #arcs` blocks. The toggle at `(i, j)` removes the arc if present and otherwise
adds it when the result is again such a representation, which is the list's split/merge rule.
Homomesy is stated through periods: whenever `σ^L P = P`, `L ≥ 1`, the block counts of `P, …,
σ^{L-1} P` sum to `L (n + 1)/2`. `n ≥ 1`: for `n = 0` the empty partition has `0` blocks. A
computation of `σ` for `n ≤ 8` reproduces the orbit sizes the document lists (`14 = 14`, `42 = 15 +
13 + 5 + 3 + 3 + 3`, …, `1430 = 1240 + 144 + 32 + 8 + 6`). The UnsolvedMath record restates `σ` as
Kreweras complementation; the document's `σ` is the toggle composite above, and the statement
follows the document. MathlibExt's `NoncrossingPartition` (finpartitions of `Fin n`) is not used
because the toggles act on arcs; the linear representations are in bijection with `NC(n)` (Einstein
et al., §1).
-/

@[expose] public section

namespace MathlibExt.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted

/-- **Arc sets.** For a natural number $n$, an arc set on $n$ points is a finite set of ordered
pairs $(i, j)$, called arcs, with $i, j \in \{0, 1, \dots, n - 1\}$. -/
abbrev ArcSet (n : ℕ) := Finset (Fin n × Fin n)

/-- **Noncrossing arc sets.** An arc set $P$ on $n$ points is noncrossing when every arc
$(i, j) \in P$ has $i < j$ and any two distinct arcs $(i, j)$ and $(k, l)$ of $P$ satisfy
$i \ne k$, $j \ne l$, and not $i < k < j < l$. So distinct arcs do not cross and share
neither a left nor a right endpoint.

These arc sets are the linear representations of the noncrossing partitions of
$\{0, 1, \dots, n - 1\}$, in which the arcs join consecutive elements of each block. -/
def IsNoncrossingArcSet {n : ℕ} (P : ArcSet n) : Prop :=
  (∀ a ∈ P, a.1 < a.2) ∧
    ∀ a ∈ P, ∀ b ∈ P, a ≠ b → ¬ (a.1 < b.1 ∧ b.1 < a.2 ∧ a.2 < b.2) ∧ a.1 ≠ b.1 ∧ a.2 ≠ b.2

open Classical in
/-- **Toggle at an arc.** For an arc $a = (i, j)$ and an arc set $P$ on $n$ points, the toggle
$\tau_{i,j}$ sends $P$ to $P \setminus \{a\}$ if $a \in P$; otherwise to $P \cup \{a\}$ if
$P \cup \{a\}$ is a noncrossing arc set; and otherwise it leaves $P$ unchanged. -/
noncomputable def toggle {n : ℕ} (a : Fin n × Fin n) (P : ArcSet n) : ArcSet n :=
  if a ∈ P then P.erase a else if IsNoncrossingArcSet (insert a P) then insert a P else P

/-- **Toggle order.** For a natural number $n$, the toggle order on $n$ points is the list of all
arcs $(i, i + d)$ with $d \ge 1$, $i \ge 0$ and $i + d \le n - 1$, ordered by length
$d = 1, \dots, n - 1$ and, for each length, by increasing left endpoint $i$. In $1$-indexed form it
is $(1,2), (2,3), \dots, (n-1,n), (1,3), \dots, (n-2,n), \dots, (1,n)$. -/
def toggleOrder (n : ℕ) : List (Fin n × Fin n) :=
  (List.range n).tail.flatMap fun d =>
    (List.finRange n).filterMap fun i =>
      if h : i.val + d < n then some (i, ⟨i.val + d, h⟩) else none

/-- **Toggle composite.** The toggle composite $\sigma$ on $n$ points sends an arc set $P$ on $n$
points to the arc set obtained from $P$ by applying the toggles $\tau_{i,j}$ at the arcs
$(i, j)$ of the toggle order on $n$ points one after another, in the order of that list. -/
noncomputable def toggleComposite (n : ℕ) (P : ArcSet n) : ArcSet n :=
  (toggleOrder n).foldl (fun Q a => toggle a Q) P

/-- **Block count.** The block count of an arc set $P$ on $n$ points is $n - |P|$, where the
subtraction is truncated at $0$.

When $P$ is a noncrossing arc set, this is the number of blocks of the noncrossing partition whose
linear representation is $P$. -/
def blockCount {n : ℕ} (P : ArcSet n) : ℕ :=
  n - P.card

/-- **Block-count homomesy claim for toggling noncrossing partitions.** Let $\sigma_n$ be the
toggle composite on $n$ points and $\sigma_n^k$ its $k$-fold iterate. The claim states that for
every $n \ge 1$, every noncrossing arc set $P$ on $n$ points and every $L \ge 1$ with
$\sigma_n^L(P) = P$, twice the sum of the block counts of
$P, \sigma_n(P), \dots, \sigma_n^{L-1}(P)$ equals $L(n + 1)$. That is, the number of blocks is
homomesic under $\sigma_n$ with average $(n + 1)/2$.

Source: AIM workshop Dynamical algebraic combinatorics, pre-workshop document, §5.4,
Conjecture 5.8. -/
def noncrossingToggleBlockHomomesy : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ P : ArcSet n, IsNoncrossingArcSet P → ∀ L : ℕ, 1 ≤ L →
    (toggleComposite n)^[L] P = P →
      2 * ∑ k ∈ Finset.range L, blockCount ((toggleComposite n)^[k] P) = L * (n + 1)

/-- The arc joining the consecutive points `k` and `k + 1`. -/
private def gapArc {n : ℕ} (k : ℕ) (hk : k + 1 < n) : Fin n × Fin n :=
  (⟨k, by omega⟩, ⟨k + 1, hk⟩)

/-- An arc is relevant to the gap between `k` and `k + 1` when it ends at `k + 1` from the
left or starts at `k` to the right; the gap arc itself is relevant. -/
private def IsRelevant {n : ℕ} (k : ℕ) (a : Fin n × Fin n) : Prop :=
  (a.2.val = k + 1 ∧ a.1.val ≤ k) ∨ (a.1.val = k ∧ k + 1 ≤ a.2.val)

private instance {n : ℕ} {k : ℕ} : DecidablePred (IsRelevant (n := n) k) :=
  fun a => by
    change Decidable ((a.2.val = k + 1 ∧ a.1.val ≤ k) ∨ (a.1.val = k ∧ k + 1 ≤ a.2.val))
    infer_instance

private theorem gapArc_val {n : ℕ} {k : ℕ} (hk : k + 1 < n) :
    (gapArc k hk).1.val = k ∧ (gapArc k hk).2.val = k + 1 := ⟨rfl, rfl⟩

private theorem gapArc_relevant {n : ℕ} {k : ℕ} (hk : k + 1 < n) :
    IsRelevant k (gapArc k hk) :=
  Or.inl ⟨(gapArc_val hk).2, by rw [(gapArc_val hk).1]⟩

private theorem isNoncrossing_of_subset {n : ℕ} {P Q : ArcSet n} (h : Q ⊆ P)
    (hP : IsNoncrossingArcSet P) : IsNoncrossingArcSet Q :=
  ⟨fun a ha => hP.1 a (h ha), fun a ha b hb hne => hP.2 a (h ha) b (h hb) hne⟩

/-- Two distinct relevant arcs cannot both lie in a noncrossing arc set: they share an
endpoint or cross. -/
private theorem relevant_eq {n : ℕ} {k : ℕ} {P : ArcSet n} (hP : IsNoncrossingArcSet P)
    {a b : Fin n × Fin n} (ha : a ∈ P) (hb : b ∈ P) (hra : IsRelevant k a)
    (hrb : IsRelevant k b) : a = b := by
  by_contra hne
  obtain ⟨hcross, hleft, hright⟩ := hP.2 a ha b hb hne
  obtain ⟨hcross', -, -⟩ := hP.2 b hb a ha (Ne.symm hne)
  have ha1 : a.1.val < a.2.val := hP.1 a ha
  have hb1 : b.1.val < b.2.val := hP.1 b hb
  have hne1 : a.1.val ≠ b.1.val := fun h => hleft (Fin.ext h)
  have hne2 : a.2.val ≠ b.2.val := fun h => hright (Fin.ext h)
  have hc1 : ¬ (a.1.val < b.1.val ∧ b.1.val < a.2.val ∧ a.2.val < b.2.val) :=
    fun h => hcross ⟨h.1, h.2.1, h.2.2⟩
  have hc2 : ¬ (b.1.val < a.1.val ∧ a.1.val < b.2.val ∧ b.2.val < a.2.val) :=
    fun h => hcross' ⟨h.1, h.2.1, h.2.2⟩
  rcases hra with ⟨h2, h1⟩ | ⟨h1, h2⟩ <;> rcases hrb with ⟨h2', h1'⟩ | ⟨h1', h2'⟩ <;> omega

/-- Toggling an arc different from `a` does not change whether `a` is present. -/
private theorem toggle_mem_of_ne {n : ℕ} {a b : Fin n × Fin n} (hab : b ≠ a) {P : ArcSet n} :
    a ∈ toggle b P ↔ a ∈ P := by
  have hab' : a ≠ b := Ne.symm hab
  unfold toggle
  split_ifs with hb hnc
  · simp [Finset.mem_erase, hab']
  · simp [Finset.mem_insert, hab']
  · exact Iff.rfl

/-- Toggling preserves noncrossing arc sets. -/
private theorem toggle_noncrossing {n : ℕ} {b : Fin n × Fin n} {P : ArcSet n}
    (hP : IsNoncrossingArcSet P) : IsNoncrossingArcSet (toggle b P) := by
  unfold toggle
  split_ifs with hb hnc
  · exact isNoncrossing_of_subset (Finset.erase_subset _ _) hP
  · exact hnc
  · exact hP

/-- Folding toggles whose arcs are all different from `a` does not change whether `a` is
present. -/
private theorem foldl_toggle_mem_of_ne {n : ℕ} {Ls : List (Fin n × Fin n)}
    {a : Fin n × Fin n} {Q : ArcSet n} (h : ∀ c ∈ Ls, c ≠ a) :
    a ∈ Ls.foldl (fun Q c => toggle c Q) Q ↔ a ∈ Q := by
  induction Ls generalizing Q with
  | nil => simp
  | cons c Ls ih =>
    simp only [List.foldl_cons, toggle_mem_of_ne (h c (by simp)),
      ih (fun c' hc' => h c' (List.mem_cons_of_mem c hc'))]

/-- Folding toggles preserves noncrossing arc sets. -/
private theorem foldl_toggle_noncrossing {n : ℕ} {Ls : List (Fin n × Fin n)}
    {Q : ArcSet n} (hQ : IsNoncrossingArcSet Q) :
    IsNoncrossingArcSet (Ls.foldl (fun Q c => toggle c Q) Q) := by
  induction Ls generalizing Q with
  | nil => simpa using hQ
  | cons c Ls ih =>
    rw [List.foldl_cons]
    exact ih (toggle_noncrossing hQ)

/-- The toggle composite preserves noncrossing arc sets. -/
private theorem toggleComposite_noncrossing {n : ℕ} {P : ArcSet n}
    (hP : IsNoncrossingArcSet P) : IsNoncrossingArcSet (toggleComposite n P) :=
  foldl_toggle_noncrossing hP

/-- Membership in one block of the toggle order: the arcs of length `d`. -/
private theorem mem_block {n d : ℕ} {a : Fin n × Fin n} :
    a ∈ (List.finRange n).filterMap (fun i =>
        if h : i.val + d < n then some (i, ⟨i.val + d, h⟩) else none) ↔
      a.1.val + d = a.2.val ∧ a.1.val + d < n := by
  constructor
  · intro h
    rw [List.mem_filterMap] at h
    obtain ⟨i, -, hi⟩ := h
    split_ifs at hi with hd
    obtain rfl := Option.some.inj hi
    exact ⟨rfl, hd⟩
  · rintro ⟨h1, h2⟩
    rw [List.mem_filterMap]
    refine ⟨a.1, List.mem_finRange a.1, ?_⟩
    have hpair : (a.1, ⟨a.1.val + d, h2⟩) = a := Prod.ext rfl (Fin.ext h1)
    rw [← hpair]
    simp [h2]

/-- The toggle order begins with the block of length-one arcs. -/
private theorem toggleOrder_eq {n : ℕ} (hn : 2 ≤ n) :
    toggleOrder n =
      ((List.finRange n).filterMap (fun i =>
          if h : i.val + 1 < n then some (i, ⟨i.val + 1, h⟩) else none)) ++
        (List.range' 2 (n - 2)).flatMap (fun d =>
          (List.finRange n).filterMap (fun i =>
            if h : i.val + d < n then some (i, ⟨i.val + d, h⟩) else none)) := by
  have htail : (List.range n).tail = 1 :: List.range' 2 (n - 2) := by
    rw [List.range_eq_range']
    have h1 : List.range' 0 n = 0 :: List.range' 1 (n - 1) := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [List.range'_succ]
    rw [h1]
    simp [List.range'_succ, show n - 1 = (n - 2) + 1 by omega]
  unfold toggleOrder
  rw [htail, List.flatMap_cons]

/-- The gap arc is compatible with every non-relevant arc of a noncrossing arc set:
they share no endpoint and do not cross it. -/
private theorem gapArc_compatible {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    (hQ : IsNoncrossingArcSet Q) {b : Fin n × Fin n} (hb : b ∈ Q)
    (h : ¬ IsRelevant k b) :
    (gapArc k hk).1 ≠ b.1 ∧ (gapArc k hk).2 ≠ b.2 ∧
      ¬ ((gapArc k hk).1 < b.1 ∧ b.1 < (gapArc k hk).2 ∧ (gapArc k hk).2 < b.2) ∧
      ¬ (b.1 < (gapArc k hk).1 ∧ (gapArc k hk).1 < b.2 ∧ b.2 < (gapArc k hk).2) := by
  have hb12 : b.1.val < b.2.val := hQ.1 b hb
  have hn1 : b.1.val ≠ k := by
    intro h1
    exact h (Or.inr ⟨h1, by omega⟩)
  have hn2 : b.2.val ≠ k + 1 := by
    intro h2
    exact h (Or.inl ⟨h2, by omega⟩)
  obtain ⟨hg1, hg2⟩ := gapArc_val hk
  refine ⟨fun h1 => hn1 (by have h2 := congrArg Fin.val h1; rw [hg1] at h2; exact h2.symm),
    fun h1 => hn2 (by have h2 := congrArg Fin.val h1; rw [hg2] at h2; exact h2.symm), ?_, ?_⟩
  · rintro ⟨h1, h2, -⟩
    have v1 : k < b.1.val := by have h3 : (gapArc k hk).1.val < b.1.val := h1; rwa [hg1] at h3
    have v2 : b.1.val < k + 1 := by have h3 : b.1.val < (gapArc k hk).2.val := h2; rwa [hg2] at h3
    omega
  · rintro ⟨h1, h2, h3⟩
    have v1 : b.1.val < k := by have h4 : b.1.val < (gapArc k hk).1.val := h1; rwa [hg1] at h4
    have v2 : k < b.2.val := by have h4 : (gapArc k hk).1.val < b.2.val := h2; rwa [hg1] at h4
    have v3 : b.2.val < k + 1 := by have h4 : b.2.val < (gapArc k hk).2.val := h3; rwa [hg2] at h4
    omega

/-- Adding the gap arc to a noncrossing arc set with no relevant arc keeps it noncrossing. -/
private theorem insert_gapArc_noncrossing {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    (hQ : IsNoncrossingArcSet Q) (h : ∀ a ∈ Q, ¬ IsRelevant k a) :
    IsNoncrossingArcSet (insert (gapArc k hk) Q) := by
  obtain ⟨hg1, hg2⟩ := gapArc_val hk
  constructor
  · intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · change (gapArc k hk).1.val < (gapArc k hk).2.val
      omega
    · exact hQ.1 a ha
  · intro a ha b hb hne
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hne
    · obtain ⟨h1, h2, h3, -⟩ := gapArc_compatible hk hQ hb (h b hb)
      exact ⟨h3, h1, h2⟩
    · obtain ⟨h1, h2, -, h4⟩ := gapArc_compatible hk hQ ha (h a ha)
      exact ⟨h4, Ne.symm h1, Ne.symm h2⟩
    · exact hQ.2 a ha b hb hne

/-- Toggling the gap arc of a noncrossing arc set with no relevant arc adds it. -/
private theorem gapArc_mem_toggle {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    (hQ : IsNoncrossingArcSet Q) (h : ∀ a ∈ Q, ¬ IsRelevant k a) :
    gapArc k hk ∈ toggle (gapArc k hk) Q := by
  have hgapQ : gapArc k hk ∉ Q := fun hmem => h _ hmem (gapArc_relevant hk)
  have hnc : IsNoncrossingArcSet (insert (gapArc k hk) Q) :=
    insert_gapArc_noncrossing hk hQ h
  unfold toggle
  simp only [hgapQ, ite_false, hnc, ite_true, Finset.mem_insert_self]

/-- Toggling the gap arc of a noncrossing arc set containing a relevant arc never leaves
the gap arc present. -/
private theorem gapArc_not_mem_toggle {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    (_hQ : IsNoncrossingArcSet Q) {a : Fin n × Fin n} (ha : a ∈ Q) (hra : IsRelevant k a) :
    gapArc k hk ∉ toggle (gapArc k hk) Q := by
  intro hmem
  by_cases h1 : gapArc k hk ∈ Q
  · have hmem2 : gapArc k hk ∈ Q.erase (gapArc k hk) := by
      unfold toggle at hmem
      simpa only [h1, ite_true] using hmem
    exact (Finset.mem_erase.mp hmem2).1 rfl
  · by_cases h2 : IsNoncrossingArcSet (insert (gapArc k hk) Q)
    · have hmem2 : gapArc k hk ∈ insert (gapArc k hk) Q := by
        unfold toggle at hmem
        simpa only [h1, ite_false, h2, ite_true] using hmem
      obtain ⟨-, hleft, hright⟩ := h2.2 (gapArc k hk) (Finset.mem_insert_self _ _) a
          (Finset.mem_insert_of_mem ha) (by rintro rfl; exact h1 ha)
      rcases hra with ⟨h2eq, -⟩ | ⟨h1eq, -⟩
      · obtain ⟨hg1, hg2⟩ := gapArc_val hk
        exact hright (Fin.ext (by rw [hg2]; exact h2eq.symm))
      · obtain ⟨hg1, hg2⟩ := gapArc_val hk
        exact hleft (Fin.ext (by rw [hg1]; exact h1eq.symm))
    · unfold toggle at hmem
      simp only [h1, ite_false, h2, ite_false] at hmem

/-- Toggling a relevant arc different from the gap arc cannot add it while the gap arc
is present. -/
private theorem relevant_not_mem_toggle {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    (hQ : IsNoncrossingArcSet Q) {b : Fin n × Fin n} (hb : IsRelevant k b)
    (hne : b ≠ gapArc k hk) (hgap : gapArc k hk ∈ Q) : b ∉ toggle b Q := by
  have hbQ : b ∉ Q := by
    intro hbQ
    exact hne (relevant_eq hQ hgap hbQ (gapArc_relevant hk) hb).symm
  intro hmem
  by_cases h1 : b ∈ Q
  · have hmem2 : b ∈ Q.erase b := by
      unfold toggle at hmem
      simpa only [h1, ite_true] using hmem
    exact hbQ (Finset.mem_erase.mp hmem2).2
  · by_cases h2 : IsNoncrossingArcSet (insert b Q)
    · have hmem2 : b ∈ insert b Q := by
        unfold toggle at hmem
        simpa only [h1, ite_false, h2, ite_true] using hmem
      obtain ⟨-, hleft, hright⟩ := h2.2 b (Finset.mem_insert_self _ _) (gapArc k hk)
          (Finset.mem_insert_of_mem hgap) hne
      rcases hb with ⟨h2eq, -⟩ | ⟨h1eq, -⟩
      · obtain ⟨hg1, hg2⟩ := gapArc_val hk
        exact hright (Fin.ext (by rw [h2eq, hg2]))
      · obtain ⟨hg1, hg2⟩ := gapArc_val hk
        exact hleft (Fin.ext (by rw [h1eq, hg1]))
    · unfold toggle at hmem
      simp only [h1, ite_false, h2, ite_false] at hmem

/-- Folding toggles that never touch the gap arc keeps the gap arc present and keeps a
relevant arc different from it absent. -/
private theorem foldl_toggle_gapArc {n : ℕ} {k : ℕ} (hk : k + 1 < n)
    {Ls : List (Fin n × Fin n)} {Q : ArcSet n} (hQ : IsNoncrossingArcSet Q)
    (hLs : ∀ c ∈ Ls, c ≠ gapArc k hk) (hgap : gapArc k hk ∈ Q)
    {b : Fin n × Fin n} (hb : IsRelevant k b) (hne : b ≠ gapArc k hk) (hbQ : b ∉ Q) :
    gapArc k hk ∈ Ls.foldl (fun Q c => toggle c Q) Q ∧
      b ∉ Ls.foldl (fun Q c => toggle c Q) Q := by
  induction Ls generalizing Q with
  | nil => exact ⟨hgap, hbQ⟩
  | cons c Ls ih =>
    simp only [List.foldl_cons]
    apply ih (toggle_noncrossing hQ) (fun c' hc' => hLs c' (List.mem_cons_of_mem c hc'))
    · exact (toggle_mem_of_ne (hLs c (by simp))).mpr hgap
    · by_cases hcb : c = b
      · subst hcb
        exact relevant_not_mem_toggle hk hQ hb hne hgap
      · exact fun h => hbQ ((toggle_mem_of_ne hcb).mp h)

/-- Folding toggles none of which is relevant keeps every relevant arc absent. -/
private theorem foldl_toggle_no_relevant {n : ℕ} {k : ℕ}
    {Ls : List (Fin n × Fin n)} {Q : ArcSet n}
    (hLs : ∀ c ∈ Ls, ∀ a : Fin n × Fin n, IsRelevant k a → c ≠ a)
    (h : ∀ a ∈ Q, ¬ IsRelevant k a) :
    ∀ a ∈ Ls.foldl (fun Q c => toggle c Q) Q, ¬ IsRelevant k a := by
  induction Ls generalizing Q with
  | nil => exact h
  | cons c Ls ih =>
    simp only [List.foldl_cons]
    apply ih (fun c' hc' => hLs c' (List.mem_cons_of_mem c hc'))
    intro a ha hra
    exact h a ((toggle_mem_of_ne (hLs c (by simp) a hra)).mp ha) hra

/-- The toggle order splits at the gap arc: the arcs before it are not relevant, and the
gap arc does not occur after it. -/
private theorem toggleComposite_split {n : ℕ} {k : ℕ} (hk : k + 1 < n) :
    ∃ L1 L2 : List (Fin n × Fin n),
      toggleOrder n = L1 ++ gapArc k hk :: L2 ∧
      (∀ c ∈ L1, ∀ a : Fin n × Fin n, IsRelevant k a → c ≠ a) ∧
      (∀ c ∈ L2, c ≠ gapArc k hk) := by
  have hn : 2 ≤ n := by omega
  have hgapB1 : gapArc k hk ∈ (List.finRange n).filterMap (fun i =>
      if h : i.val + 1 < n then some (i, ⟨i.val + 1, h⟩) else none) := by
    rw [mem_block]
    obtain ⟨hg1, hg2⟩ := gapArc_val hk
    exact ⟨by rw [hg1, hg2], hk⟩
  have hB1nodup : (((List.finRange n).filterMap (fun i =>
      if h : i.val + 1 < n then some (i, ⟨i.val + 1, h⟩) else none)) :
      List (Fin n × Fin n)).Nodup := by
    apply List.Nodup.filterMap _ (List.nodup_finRange n)
    intro i j b hb hb'
    by_cases hi : i.val + 1 < n
    · by_cases hj : j.val + 1 < n
      · have hbi : (i, ⟨i.val + 1, hi⟩) = b := by simpa [hi] using hb
        have hbj : (j, ⟨j.val + 1, hj⟩) = b := by simpa [hj] using hb'
        rw [← hbi] at hbj
        exact (congrArg Prod.fst hbj).symm
      · simp [hj] at hb'
    · simp [hi] at hb
  obtain ⟨L1, S1, hsplit⟩ := List.append_of_mem hgapB1
  have hnodup : (L1 ++ gapArc k hk :: S1).Nodup := by rwa [hsplit] at hB1nodup
  obtain ⟨-, hnodup2, hdisj⟩ := List.nodup_append.mp hnodup
  have hgapL1 : gapArc k hk ∉ L1 := by
    intro hmem
    exact hdisj _ hmem _ (by simp) rfl
  have hgapS1 : gapArc k hk ∉ S1 := (List.nodup_cons.mp hnodup2).1
  refine ⟨L1, S1 ++ (List.range' 2 (n - 2)).flatMap (fun d =>
    (List.finRange n).filterMap (fun i =>
      if h : i.val + d < n then some (i, ⟨i.val + d, h⟩) else none)), ?_, ?_, ?_⟩
  · simp only [toggleOrder_eq hn, hsplit, List.append_assoc, List.cons_append]
  · intro c hc a hra hca
    subst hca
    have hcB1 : c ∈ (List.finRange n).filterMap (fun i =>
        if h : i.val + 1 < n then some (i, ⟨i.val + 1, h⟩) else none) := by
      rw [hsplit]
      exact List.mem_append_left _ hc
    rw [mem_block] at hcB1
    obtain ⟨hg1, hg2⟩ := gapArc_val hk
    have heq : c = gapArc k hk := by
      apply Prod.ext
      · apply Fin.ext
        rcases hra with ⟨h2, h1⟩ | ⟨h1, -⟩
        · rw [hg1]; omega
        · rw [hg1]; exact h1
      · apply Fin.ext
        rcases hra with ⟨h2, -⟩ | ⟨h1, h2⟩
        · rw [hg2]; exact h2
        · rw [hg2]; omega
    exact hgapL1 (heq ▸ hc)
  · intro c hc
    rw [List.mem_append] at hc
    rcases hc with hc | hc
    · exact fun h => hgapS1 (h ▸ hc)
    · rw [List.mem_flatMap] at hc
      obtain ⟨d, hd, hc⟩ := hc
      rw [mem_block] at hc
      rw [List.mem_range'] at hd
      intro hceq
      have hv1 : c.1.val = k := by rw [hceq]; exact (gapArc_val hk).1
      have hv2 : c.2.val = k + 1 := by rw [hceq]; exact (gapArc_val hk).2
      omega

/-- The weight of an arc for the gap statistic at `k`: the gap arc itself has weight `2`,
every other relevant arc has weight `1`, and every other arc has weight `0`. -/
private def psiWeight {n : ℕ} (k : ℕ) (a : Fin n × Fin n) : ℕ :=
  if a.2.val = k + 1 ∧ a.1.val = k then 2
  else if IsRelevant k a then 1 else 0

/-- The gap statistic at `k`: the sum of the weights of the arcs of an arc set. For a
noncrossing arc set it is `0`, `1` or `2`. -/
private def psi {n : ℕ} (k : ℕ) (P : ArcSet n) : ℕ :=
  ∑ a ∈ P, psiWeight k a

private theorem psiWeight_eq_of_gap {n : ℕ} {k : ℕ} {a : Fin n × Fin n}
    (hga : a.2.val = k + 1 ∧ a.1.val = k) : psiWeight k a = 2 := by
  unfold psiWeight
  simp [hga]

private theorem psiWeight_gapArc {n : ℕ} {k : ℕ} (hk : k + 1 < n) :
    psiWeight k (gapArc k hk) = 2 :=
  psiWeight_eq_of_gap ⟨(gapArc_val hk).2, (gapArc_val hk).1⟩

private theorem psiWeight_eq_of_relevant_not_gap {n : ℕ} {k : ℕ} {a : Fin n × Fin n}
    (hr : IsRelevant k a) (hga : ¬ (a.2.val = k + 1 ∧ a.1.val = k)) : psiWeight k a = 1 := by
  unfold psiWeight
  simp [hga, hr]

private theorem psiWeight_eq_zero_of_not_relevant {n : ℕ} {k : ℕ} {a : Fin n × Fin n}
    (hr : ¬ IsRelevant k a) : psiWeight k a = 0 := by
  have hga : ¬ (a.2.val = k + 1 ∧ a.1.val = k) := by
    rintro ⟨h2, h1⟩
    exact hr (Or.inr ⟨h1, by omega⟩)
  unfold psiWeight
  simp [hga, hr]

private theorem psiWeight_eq_zero_iff {n : ℕ} {k : ℕ} {a : Fin n × Fin n} :
    psiWeight k a = 0 ↔ ¬ IsRelevant k a := by
  constructor
  · intro h hr
    have hga : ¬ (a.2.val = k + 1 ∧ a.1.val = k) := by
      rintro ⟨h2, h1⟩
      rw [psiWeight_eq_of_gap ⟨h2, h1⟩] at h
      omega
    rw [psiWeight_eq_of_relevant_not_gap hr hga] at h
    simp at h
  · intro hr
    exact psiWeight_eq_zero_of_not_relevant hr

private theorem psiWeight_le {n : ℕ} {k : ℕ} (a : Fin n × Fin n) :
    psiWeight k a ≤ 2 * (if IsRelevant k a then 1 else 0) := by
  by_cases hga : a.2.val = k + 1 ∧ a.1.val = k
  · rw [psiWeight_eq_of_gap hga]
    have hr : IsRelevant k a := Or.inr ⟨hga.2, by omega⟩
    simp [hr]
  · by_cases hr : IsRelevant k a
    · rw [psiWeight_eq_of_relevant_not_gap hr hga]
      simp [hr]
    · rw [psiWeight_eq_zero_of_not_relevant hr]
      simp [hr]

private theorem relevant_filter_card_le_one {n : ℕ} {k : ℕ} {P : ArcSet n}
    (hP : IsNoncrossingArcSet P) :
    (P.filter (IsRelevant k)).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  rw [Finset.mem_filter] at ha hb
  exact relevant_eq hP ha.1 hb.1 ha.2 hb.2

private theorem psi_eq_zero_iff {n : ℕ} {k : ℕ} {P : ArcSet n} :
    psi k P = 0 ↔ ∀ a ∈ P, ¬ IsRelevant k a := by
  unfold psi
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun a _ => Nat.zero_le _)]
  simp only [psiWeight_eq_zero_iff]

private theorem psi_le_two {n : ℕ} {k : ℕ} {P : ArcSet n} (hP : IsNoncrossingArcSet P) :
    psi k P ≤ 2 := by
  calc psi k P = ∑ a ∈ P, psiWeight k a := rfl
    _ ≤ ∑ a ∈ P, 2 * (if IsRelevant k a then 1 else 0) :=
        Finset.sum_le_sum fun a _ => psiWeight_le a
    _ = 2 * (P.filter (IsRelevant k)).card := by
        rw [← Finset.mul_sum, Finset.sum_boole, Nat.cast_id]
    _ ≤ 2 := by
        have hcard := relevant_filter_card_le_one (k := k) hP
        omega

private theorem psi_eq_two_iff {n : ℕ} {k : ℕ} (hk : k + 1 < n) {P : ArcSet n}
    (hP : IsNoncrossingArcSet P) : psi k P = 2 ↔ gapArc k hk ∈ P := by
  constructor
  · intro hpsi
    by_contra hgap
    have hle : psi k P ≤ 1 := by
      calc psi k P = ∑ a ∈ P, psiWeight k a := rfl
        _ ≤ ∑ a ∈ P, (if IsRelevant k a then 1 else 0) := by
            apply Finset.sum_le_sum
            intro a ha
            by_cases hga : a = gapArc k hk
            · exact absurd (hga ▸ ha) hgap
            · by_cases hr : IsRelevant k a
              · rw [psiWeight_eq_of_relevant_not_gap hr (by
                  rintro ⟨h2, h1⟩
                  exact hga (Prod.ext (Fin.ext h1) (Fin.ext h2)))]
                simp [hr]
              · rw [psiWeight_eq_zero_of_not_relevant hr]
                simp [hr]
        _ = (P.filter (IsRelevant k)).card := by rw [Finset.sum_boole, Nat.cast_id]
        _ ≤ 1 := relevant_filter_card_le_one (k := k) hP
    omega
  · intro hgap
    unfold psi
    rw [Finset.sum_eq_single (gapArc k hk)]
    · exact psiWeight_gapArc hk
    · intro b hb hne
      rw [psiWeight_eq_zero_iff]
      intro hrb
      exact hne (relevant_eq hP hgap hb (gapArc_relevant hk) hrb).symm
    · intro hcon
      exact (hcon hgap).elim

/-- The toggle composite, split at the gap arc: first the earlier toggles, then the gap
toggle, then the later toggles. -/
private theorem toggleComposite_eq {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    {L1 L2 : List (Fin n × Fin n)}
    (hsplit : toggleOrder n = L1 ++ gapArc k hk :: L2) :
    toggleComposite n Q =
      L2.foldl (fun Q c => toggle c Q)
        (toggle (gapArc k hk) (L1.foldl (fun Q c => toggle c Q) Q)) := by
  unfold toggleComposite
  rw [hsplit, List.foldl_append]
  simp only [List.foldl_cons]

/-- From a noncrossing arc set with no relevant arc, one toggle composite produces the gap
arc and no other relevant arc. -/
private theorem step_gapArc_of_no_relevant {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    (hQ : IsNoncrossingArcSet Q) (h : ∀ a ∈ Q, ¬ IsRelevant k a) :
    gapArc k hk ∈ toggleComposite n Q ∧
      ∀ b : Fin n × Fin n, IsRelevant k b → b ≠ gapArc k hk →
        b ∉ toggleComposite n Q := by
  obtain ⟨L1, L2, hsplit, hL1, hL2⟩ := toggleComposite_split hk
  have hQ1nc : IsNoncrossingArcSet (L1.foldl (fun Q c => toggle c Q) Q) :=
    foldl_toggle_noncrossing hQ
  have hQ1 : ∀ a ∈ L1.foldl (fun Q c => toggle c Q) Q, ¬ IsRelevant k a :=
    foldl_toggle_no_relevant hL1 h
  have hQ2 : gapArc k hk ∈ toggle (gapArc k hk) (L1.foldl (fun Q c => toggle c Q) Q) :=
    gapArc_mem_toggle hk hQ1nc hQ1
  have hQ2nc : IsNoncrossingArcSet
      (toggle (gapArc k hk) (L1.foldl (fun Q c => toggle c Q) Q)) :=
    toggle_noncrossing hQ1nc
  rw [toggleComposite_eq hk hsplit]
  refine ⟨(foldl_toggle_mem_of_ne hL2).mpr hQ2, fun b hb hne => ?_⟩
  exact (foldl_toggle_gapArc hk hQ2nc hL2 hQ2 hb hne
    (fun hmem => hQ1 b ((toggle_mem_of_ne (Ne.symm hne)).mp hmem) hb)).2

/-- From a noncrossing arc set containing a relevant arc, one toggle composite does not
produce the gap arc. -/
private theorem step_gapArc_not_mem_of_relevant {n : ℕ} {k : ℕ} (hk : k + 1 < n)
    {Q : ArcSet n} (hQ : IsNoncrossingArcSet Q) (h : ∃ a ∈ Q, IsRelevant k a) :
    gapArc k hk ∉ toggleComposite n Q := by
  obtain ⟨L1, L2, hsplit, hL1, hL2⟩ := toggleComposite_split hk
  obtain ⟨a, ha, hra⟩ := h
  have hQ1nc : IsNoncrossingArcSet (L1.foldl (fun Q c => toggle c Q) Q) :=
    foldl_toggle_noncrossing hQ
  have ha1 : a ∈ L1.foldl (fun Q c => toggle c Q) Q :=
    (foldl_toggle_mem_of_ne (fun c hc => hL1 c hc a hra)).mpr ha
  have hnot : gapArc k hk ∉ toggle (gapArc k hk) (L1.foldl (fun Q c => toggle c Q) Q) :=
    gapArc_not_mem_toggle hk hQ1nc ha1 hra
  rw [toggleComposite_eq hk hsplit]
  exact fun hmem => hnot ((foldl_toggle_mem_of_ne hL2).mp hmem)

/-- The gap statistic is `2` after one toggle composite applied to a noncrossing arc set
where it is `0`. -/
private theorem psi_step_zero {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    (hQ : IsNoncrossingArcSet Q) (h : psi k Q = 0) :
    psi k (toggleComposite n Q) = 2 := by
  rw [psi_eq_zero_iff] at h
  obtain ⟨hgap, -⟩ := step_gapArc_of_no_relevant hk hQ h
  exact (psi_eq_two_iff hk (toggleComposite_noncrossing hQ)).mpr hgap

/-- The gap statistic is not `2` after one toggle composite applied to a noncrossing arc
set where it is nonzero. -/
private theorem psi_step_ne_zero {n : ℕ} {k : ℕ} (hk : k + 1 < n) {Q : ArcSet n}
    (hQ : IsNoncrossingArcSet Q) (h : psi k Q ≠ 0) :
    psi k (toggleComposite n Q) ≠ 2 := by
  intro h2
  rw [psi_eq_two_iff hk (toggleComposite_noncrossing hQ)] at h2
  have hex : ∃ a ∈ Q, IsRelevant k a := by
    by_contra hcon
    have h0 : psi k Q = 0 := (psi_eq_zero_iff).mpr (by push Not at hcon; exact hcon)
    exact h h0
  exact (step_gapArc_not_mem_of_relevant hk hQ hex) h2

/-- A cyclic sequence of values in `{0, 1, 2}` in which `2` always follows `0` and only
`0` is followed by `2` sums to its length. -/
private theorem cycle_sum_eq_of_step {ψ : ℕ → ℕ} {L : ℕ}
    (hval : ∀ t, ψ t = 0 ∨ ψ t = 1 ∨ ψ t = 2)
    (hstep : ∀ t, ψ (t + 1) = 2 ↔ ψ t = 0) (hper : ψ L = ψ 0) :
    ∑ t ∈ Finset.range L, ψ t = L := by
  have hA : ∀ t, (if ψ (t + 1) = 2 then 1 else 0) = (if ψ t = 0 then 1 else 0) := by
    intro t
    by_cases h : ψ t = 0
    · simp [h, (hstep t).mpr h]
    · have h2 : ψ (t + 1) ≠ 2 := fun h2 => h ((hstep t).mp h2)
      simp [h, h2]
  have hshift : ∑ t ∈ Finset.range L, (if ψ (t + 1) = 2 then 1 else 0) =
      ∑ t ∈ Finset.range L, (if ψ t = 2 then 1 else 0) := by
    have h1 := Finset.sum_range_succ' (fun t => if ψ t = 2 then 1 else 0) L
    have h2 := Finset.sum_range_succ (fun t => if ψ t = 2 then 1 else 0) L
    rw [hper] at h2
    omega
  have hcount : ∑ t ∈ Finset.range L, (if ψ t = 2 then 1 else 0) =
      ∑ t ∈ Finset.range L, (if ψ t = 0 then 1 else 0) := by
    rw [← hshift]
    exact Finset.sum_congr rfl fun t _ => hA t
  have hsum : ∑ t ∈ Finset.range L, ψ t =
      ∑ t ∈ Finset.range L, (2 * (if ψ t = 2 then 1 else 0) +
        (if ψ t = 1 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro t _
    rcases hval t with h | h | h <;> simp [h]
  have hsplit : ∑ t ∈ Finset.range L, (2 * (if ψ t = 2 then 1 else 0) +
        (if ψ t = 1 then 1 else 0)) =
      2 * (∑ t ∈ Finset.range L, (if ψ t = 2 then 1 else 0)) +
        (∑ t ∈ Finset.range L, (if ψ t = 1 then 1 else 0)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have htotal : (∑ t ∈ Finset.range L, (if ψ t = 0 then 1 else 0)) +
      (∑ t ∈ Finset.range L, (if ψ t = 1 then 1 else 0)) +
      (∑ t ∈ Finset.range L, (if ψ t = 2 then 1 else 0)) = L := by
    have hone : ∀ t, (if ψ t = 0 then 1 else 0) + (if ψ t = 1 then 1 else 0) +
        (if ψ t = 2 then 1 else 0) = 1 := by
      intro t
      rcases hval t with h | h | h <;> simp [h]
    calc (∑ t ∈ Finset.range L, (if ψ t = 0 then 1 else 0)) +
          (∑ t ∈ Finset.range L, (if ψ t = 1 then 1 else 0)) +
          (∑ t ∈ Finset.range L, (if ψ t = 2 then 1 else 0))
        = ∑ t ∈ Finset.range L, ((if ψ t = 0 then 1 else 0) +
            (if ψ t = 1 then 1 else 0) + (if ψ t = 2 then 1 else 0)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      _ = ∑ t ∈ Finset.range L, 1 :=
          Finset.sum_congr rfl fun t _ => hone t
      _ = L := by simp
  omega

/-- The gap statistic is `1`-mesic along an orbit of the toggle composite: its values
over a period sum to the period length. -/
private theorem psi_orbit_sum {n : ℕ} {k : ℕ} (hk : k + 1 < n) {P : ArcSet n}
    (hP : IsNoncrossingArcSet P) {L : ℕ} (_hL : 1 ≤ L)
    (hper : (toggleComposite n)^[L] P = P) :
    ∑ t ∈ Finset.range L, psi k ((toggleComposite n)^[t] P) = L := by
  have hnc : ∀ t, IsNoncrossingArcSet ((toggleComposite n)^[t] P) := by
    intro t
    induction t with
    | zero => simpa using hP
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact toggleComposite_noncrossing ih
  have hval : ∀ t, psi k ((toggleComposite n)^[t] P) = 0 ∨
      psi k ((toggleComposite n)^[t] P) = 1 ∨ psi k ((toggleComposite n)^[t] P) = 2 := by
    intro t
    have hle := psi_le_two (k := k) (hnc t)
    omega
  have hstep : ∀ t, psi k ((toggleComposite n)^[t + 1] P) = 2 ↔
      psi k ((toggleComposite n)^[t] P) = 0 := by
    intro t
    rw [Function.iterate_succ_apply']
    constructor
    · intro h2
      by_contra h0
      exact psi_step_ne_zero hk (hnc t) h0 h2
    · intro h0
      exact psi_step_zero hk (hnc t) h0
  have hper' : psi k ((toggleComposite n)^[L] P) = psi k ((toggleComposite n)^[0] P) := by
    simp [hper]
  exact cycle_sum_eq_of_step hval hstep hper'

/-- Summing the gap statistics over all gaps counts every arc twice: an adjacent arc
contributes `2` at its own gap, and a longer arc contributes `1` at each of its two
endpoint gaps. -/
private theorem psi_sum_eq_two_card {n : ℕ} {P : ArcSet n} (hP : IsNoncrossingArcSet P) :
    ∑ k ∈ Finset.range (n - 1), psi k P = 2 * P.card := by
  have hper : ∀ a ∈ P, ∑ k ∈ Finset.range (n - 1), psiWeight k a = 2 := by
    intro a ha
    have ha12 : a.1.val < a.2.val := hP.1 a ha
    have ha2n : a.2.val < n := a.2.isLt
    have hmem1 : a.1.val ∈ Finset.range (n - 1) := by
      rw [Finset.mem_range]
      omega
    have hmem2 : a.2.val - 1 ∈ Finset.range (n - 1) := by
      rw [Finset.mem_range]
      omega
    by_cases hadj : a.2.val = a.1.val + 1
    · rw [Finset.sum_eq_single a.1.val]
      · exact psiWeight_eq_of_gap ⟨by omega, rfl⟩
      · intro k hk hne
        rw [psiWeight_eq_zero_iff]
        intro hr
        rcases hr with ⟨h2, -⟩ | ⟨h1, -⟩ <;> omega
      · intro hcon
        exact (hcon hmem1).elim
    · have hlong : a.1.val + 2 ≤ a.2.val := by omega
      have hne12 : a.1.val ≠ a.2.val - 1 := by omega
      have hsub : ∑ k ∈ Finset.range (n - 1), psiWeight k a =
          ∑ k ∈ ({a.1.val, a.2.val - 1} : Finset ℕ), psiWeight k a := by
        have hsubset : ({a.1.val, a.2.val - 1} : Finset ℕ) ⊆ Finset.range (n - 1) := by
          intro k hk
          rw [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact hmem1
          · exact hmem2
        have hf : ∀ k ∈ Finset.range (n - 1),
            k ∉ ({a.1.val, a.2.val - 1} : Finset ℕ) → psiWeight k a = 0 := by
          intro k hk hknot
          rw [psiWeight_eq_zero_iff]
          intro hr
          rw [Finset.mem_insert, Finset.mem_singleton] at hknot
          push Not at hknot
          rcases hr with ⟨h2, -⟩ | ⟨h1, -⟩ <;> omega
        exact (Finset.sum_subset hsubset hf).symm
      rw [hsub, Finset.sum_pair hne12]
      have hga1 : ¬ (a.2.val = a.1.val + 1 ∧ a.1.val = a.1.val) := by omega
      have hga2 : ¬ (a.2.val = a.2.val - 1 + 1 ∧ a.1.val = a.2.val - 1) := by omega
      have hr1 : IsRelevant a.1.val a := Or.inr ⟨rfl, by omega⟩
      have hr2 : IsRelevant (a.2.val - 1) a := Or.inl ⟨by omega, by omega⟩
      rw [psiWeight_eq_of_relevant_not_gap hr1 hga1,
        psiWeight_eq_of_relevant_not_gap hr2 hga2]
  calc ∑ k ∈ Finset.range (n - 1), psi k P
      = ∑ a ∈ P, ∑ k ∈ Finset.range (n - 1), psiWeight k a := by
        simp only [psi]
        exact Finset.sum_comm
    _ = ∑ a ∈ P, 2 := Finset.sum_congr rfl fun a ha => hper a ha
    _ = 2 * P.card := by
        rw [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

/-- A noncrossing arc set has at most `n - 1` arcs: distinct arcs have distinct left
endpoints, and every left endpoint is below `n - 1`. -/
private theorem card_le_sub_one {n : ℕ} {P : ArcSet n} (hP : IsNoncrossingArcSet P) :
    P.card ≤ n - 1 := by
  have hmaps : Set.MapsTo (fun a : Fin n × Fin n => a.1.val) (↑P : Set (Fin n × Fin n))
      (↑(Finset.range (n - 1)) : Set ℕ) := by
    intro a ha
    have h1 : a.1.val < a.2.val := hP.1 a ha
    have h2 : a.2.val < n := a.2.isLt
    exact Finset.mem_range.mpr
      (Nat.lt_of_succ_le (le_trans (Nat.succ_le_of_lt h1) (Nat.le_pred_of_lt h2)))
  have hinj : Set.InjOn (fun a : Fin n × Fin n => a.1.val) (↑P : Set (Fin n × Fin n)) := by
    intro a ha b hb hab
    by_contra hne
    exact (hP.2 a ha b hb hne).2.1 (Fin.ext hab)
  have h := Finset.card_le_card_of_injOn (fun a : Fin n × Fin n => a.1.val) hmaps hinj
  rwa [Finset.card_range] at h

/--
**Block-count homomesy for toggling noncrossing partitions.** The block-count homomesy claim
holds: with $\sigma_n$ the toggle composite on $n$ points and $\sigma_n^k$ its $k$-fold iterate,
for every $n \ge 1$, every noncrossing arc set $P$ on $n$ points and every $L \ge 1$ with
$\sigma_n^L(P) = P$, twice the sum of the block counts of
$P, \sigma_n(P), \dots, \sigma_n^{L-1}(P)$ equals $L(n + 1)$.

Source: AIM workshop Dynamical algebraic combinatorics, pre-workshop document,
http://aimath.org/pastworkshops/dac_preworkshop.pdf, §5.4, Conjecture 5.8; resolution: D. Einstein,
M. Farber, E. Gunawan, M. Joseph, M. Macauley, J. Propp and S. Rubinstein-Salzedo, Noncrossing
partitions, toggles, and homomesies, Electron. J. Combin. 23 (2016), no. 3, Paper 3.52,
arXiv:1510.06362, Theorem 4.5 and Corollary 4.7: for every partial Coxeter element w of the toggle
group (each toggle τ_{i,j} at most once) containing every τ_{i,i+1}, in particular every Coxeter
element, the block count β is (n + 1)/2-mesic on NC(n); σ toggles every arc exactly once,
https://doi.org/10.37236/5648.
-/
theorem noncrossingToggleBlockHomomesy_holds : noncrossingToggleBlockHomomesy := by
  intro n hn P hP L hL hper
  have hnc : ∀ t, IsNoncrossingArcSet ((toggleComposite n)^[t] P) := by
    intro t
    induction t with
    | zero => simpa using hP
    | succ t ih =>
      rw [show (toggleComposite n)^[t + 1] P =
        toggleComposite n ((toggleComposite n)^[t] P) from
        Function.iterate_succ_apply' _ _ _]
      exact toggleComposite_noncrossing ih
  have hcardbound : ∀ t, ((toggleComposite n)^[t] P).card ≤ n - 1 :=
    fun t => card_le_sub_one (hnc t)
  have hpsi : ∀ t, 2 * (((toggleComposite n)^[t] P).card) =
      ∑ k ∈ Finset.range (n - 1), psi k ((toggleComposite n)^[t] P) :=
    fun t => (psi_sum_eq_two_card (hnc t)).symm
  have horbit : ∀ k ∈ Finset.range (n - 1),
      ∑ t ∈ Finset.range L, psi k ((toggleComposite n)^[t] P) = L := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact psi_orbit_sum (by omega : k + 1 < n) hP hL hper
  have htotal : 2 * (∑ t ∈ Finset.range L, (((toggleComposite n)^[t] P).card)) =
      L * (n - 1) := by
    calc 2 * (∑ t ∈ Finset.range L, (((toggleComposite n)^[t] P).card))
        = ∑ t ∈ Finset.range L, 2 * (((toggleComposite n)^[t] P).card) := by
          rw [Finset.mul_sum]
      _ = ∑ t ∈ Finset.range L, ∑ k ∈ Finset.range (n - 1),
            psi k ((toggleComposite n)^[t] P) :=
          Finset.sum_congr rfl fun t _ => hpsi t
      _ = ∑ k ∈ Finset.range (n - 1), ∑ t ∈ Finset.range L,
            psi k ((toggleComposite n)^[t] P) := Finset.sum_comm
      _ = ∑ k ∈ Finset.range (n - 1), L :=
          Finset.sum_congr rfl fun k hk => horbit k hk
      _ = L * (n - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  have hblock : ∑ t ∈ Finset.range L, blockCount ((toggleComposite n)^[t] P) =
      L * n - ∑ t ∈ Finset.range L, (((toggleComposite n)^[t] P).card) := by
    have hsum := Finset.sum_tsub_distrib (Finset.range L) (f := fun _ => n)
      (g := fun t => (((toggleComposite n)^[t] P).card))
      (by intro t _
          exact le_trans (hcardbound t) (by omega))
    simp only [blockCount] at hsum ⊢
    rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]
  rw [hblock]
  have h2 : L * (n + 1) + L * (n - 1) = 2 * (L * n) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : m + 1 - 1 = m := Nat.add_sub_cancel m 1
    rw [hm, Nat.mul_succ, Nat.mul_succ]
    ring
  rw [Nat.mul_sub_left_distrib, ← h2, ← htotal, Nat.add_sub_cancel]

end MathlibExt.Combinatorics.NoncrossingToggleBlockHomomesyAIMOtherProblem36Wanted
