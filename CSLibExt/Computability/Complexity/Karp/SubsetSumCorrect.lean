/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSum
public import CSLibExt.Computability.Complexity.Karp.CliqueCorrect

/-!
# Correctness of Karp's reduction VERTEX-COVER ≤ SUBSET-SUM

`vertexCoverDec_eq_subsetSumDec_reduceSS`: the reduction `reduceSS` of
`CSLibExt.Computability.Complexity.Karp.SubsetSum` preserves membership.

* A sublist of `ssNums n bits` is a set `S` of vertices and a set `F` of pairs
  (`exists_sublist_ssNums_iff`). In base 4 its sum has `|S|` on top and, at pair `q`, the number of
  endpoints of `q` in `S` if `q` is an edge, plus `1` if `q ∈ F` is an edge
  (`sum_vtxNum_add_sum_edgeNum`, `sum_touches_eq`). Every digit is at most `3`, so there are no
  carries (`add_sum_digits_eq_iff`): the sum is `ssTarget k n bits` iff `|S| = k` and every edge
  digit is `2`.
* A digit `2` needs an endpoint in `S`, so `S` is a vertex cover (`isVertexCover_toGraph_iff`).
  Conversely a cover of `k` vertices hits the target with `F` the pairs with at most one endpoint
  in it (the number of a non-edge is `0`) (`exists_cover_iff_exists_sublist`).
* Invalid instances go to `noSS`, a no-instance (`subsetSumDec_noSS`, via `encodeSS_inj`).
-/

@[expose] public section

namespace Cslib.Complexity.Karp

open Cslib.CookLevin Computability MetaMathlibExt.BitstringEncoding

/-! ### The instance codec -/

/-- A delimited block and what follows it are read back from their concatenation. -/
private theorem delimit_append_inj {a a' r r' : List Bool}
    (h : delimit a ++ r = delimit a' ++ r') : a = a' ∧ r = r' := by
  simpa using congrArg undelimit h

theorem encodeSS_inj {as as' : List ℕ} {t t' : ℕ} (h : encodeSS as t = encodeSS as' t') :
    as = as' ∧ t = t' := by
  obtain ⟨ht, hr⟩ := delimit_append_inj h
  refine ⟨?_, by simpa [decode_encodeNat] using congrArg decodeNat ht⟩
  clear h ht
  induction as generalizing as' with
  | nil =>
    cases as' with
    | nil => rfl
    | cons a as' =>
      have := congrArg List.length hr
      simp at this
      omega
  | cons a as ih =>
    cases as' with
    | nil =>
      have := congrArg List.length hr
      simp at this
    | cons a' as' =>
      obtain ⟨h1, h2⟩ := delimit_append_inj hr
      rw [ih h2, show a = a' by simpa [decode_encodeNat] using congrArg decodeNat h1]

theorem subsetSumDec_encodeSS_eq_true {as : List ℕ} {t : ℕ} :
    subsetSumDec (encodeSS as t) = true ↔ ∃ l : List ℕ, l.Sublist as ∧ l.sum = t := by
  simp only [subsetSumDec, decide_eq_true_eq]
  constructor
  · rintro ⟨as', t', h, hl⟩
    obtain ⟨rfl, rfl⟩ := encodeSS_inj h
    exact hl
  · exact fun hl => ⟨as, t, rfl, hl⟩

/-- **The fixed no-instance of SUBSET-SUM.** The encoded SUBSET-SUM instance with no numbers and
target $1$ is a no-instance: the SUBSET-SUM decision problem returns false on it. -/
theorem subsetSumDec_noSS : subsetSumDec noSS = false := by
  rw [Bool.eq_false_iff, ne_eq, noSS, subsetSumDec_encodeSS_eq_true]
  rintro ⟨l, hl, hsum⟩
  rw [List.sublist_nil.1 hl] at hsum
  simp at hsum

/-! ### Base 4 without carries -/

/-- **Base-4 expansions with digits below $4$ are unique.** Let $m, A, B \in \mathbb{N}$ and let
$d, e : \mathbb{N} \to \mathbb{N}$ satisfy $d(q) < 4$ and $e(q) < 4$ for every $q < m$. Then
$A \cdot 4^m + \sum_{q < m} d(q) \, 4^q = B \cdot 4^m + \sum_{q < m} e(q) \, 4^q$ holds if and only
if $A = B$ and $d(q) = e(q)$ for every $q < m$. -/
theorem add_sum_digits_eq_iff {m A B : ℕ} {d e : ℕ → ℕ} (hd : ∀ q < m, d q < 4)
    (he : ∀ q < m, e q < 4) :
    A * 4 ^ m + ∑ q ∈ Finset.range m, d q * 4 ^ q =
        B * 4 ^ m + ∑ q ∈ Finset.range m, e q * 4 ^ q ↔
      A = B ∧ ∀ q < m, d q = e q := by
  induction m generalizing d e with
  | zero => simp
  | succ m ih =>
    have hpow : ∀ c q : ℕ, c * 4 ^ (q + 1) = 4 * (c * 4 ^ q) := fun c q => by
      rw [pow_succ, Nat.mul_comm 4, Nat.mul_assoc]
    have key : ∀ (C : ℕ) (f : ℕ → ℕ),
        C * 4 ^ (m + 1) + ∑ q ∈ Finset.range (m + 1), f q * 4 ^ q =
          f 0 + 4 * (C * 4 ^ m + ∑ q ∈ Finset.range m, f (q + 1) * 4 ^ q) := by
      intro C f
      rw [Finset.sum_range_succ', Finset.sum_congr rfl fun q _ => hpow (f (q + 1)) q,
        ← Finset.mul_sum, hpow, pow_zero, mul_one]
      omega
    have h0 := hd 0 (by omega)
    have h0' := he 0 (by omega)
    rw [key, key, show ∀ X Y : ℕ, d 0 + 4 * X = e 0 + 4 * Y ↔ d 0 = e 0 ∧ X = Y from
      fun X Y => by omega,
      ih (fun q hq => hd (q + 1) (by omega)) fun q hq => he (q + 1) (by omega)]
    constructor
    · rintro ⟨h0, hAB, hrest⟩
      refine ⟨hAB, fun q hq => ?_⟩
      cases q with
      | zero => exact h0
      | succ q => exact hrest q (by omega)
    · rintro ⟨hAB, h⟩
      exact ⟨h 0 (by omega), hAB, fun q hq => h (q + 1) (by omega)⟩

/-! ### Sublists as sets of numbers -/

/-- **Sublists of the reduction's numbers as vertex and pair sets.** Let $n, t \in \mathbb{N}$, let
$b$ be a list of booleans, and let $m$ be the length of the list of vertex pairs $(i, j)$,
$i < j < n$. Write $x_v$ for the vertex number of $v$ and $y_q$ for the pair number of $q$ defined
from $n$ and $b$. Some sublist (a subsequence, not necessarily contiguous) of the reduction's
numbers for $n$ and $b$ sums to $t$ if and only if there are finite sets $S$ of vertices $v < n$
and $F$ of pair indices $q < m$ with $\sum_{v \in S} x_v + \sum_{q \in F} y_q = t$. -/
theorem exists_sublist_ssNums_iff {n t : ℕ} {bits : List Bool} :
    (∃ l : List ℕ, l.Sublist (ssNums n bits) ∧ l.sum = t) ↔
      ∃ S ⊆ Finset.range n, ∃ F ⊆ Finset.range (pairs n).length,
        ∑ v ∈ S, vtxNum n bits v + ∑ q ∈ F, edgeNum bits q = t := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    obtain ⟨l1, l2, rfl, h1, h2⟩ := List.sublist_append_iff.1 hl
    obtain ⟨vs, hvs, rfl⟩ := List.sublist_map_iff.1 h1
    obtain ⟨qs, hqs, rfl⟩ := List.sublist_map_iff.1 h2
    refine ⟨vs.toFinset, fun v hv => ?_, qs.toFinset, fun q hq => ?_, ?_⟩
    · simpa using hvs.subset (List.mem_toFinset.1 hv)
    · simpa using hqs.subset (List.mem_toFinset.1 hq)
    · rw [List.sum_append, List.sum_toFinset _ (List.nodup_range.sublist hvs),
        List.sum_toFinset _ (List.nodup_range.sublist hqs)]
  · rintro ⟨S, hS, F, hF, rfl⟩
    have hset : ∀ (j : ℕ) (T : Finset ℕ), T ⊆ Finset.range j →
        ((List.range j).filter (· ∈ T)).toFinset = T := fun j T hT => by
      ext v
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq]
      exact ⟨And.right, fun h => ⟨Finset.mem_range.1 (hT h), h⟩⟩
    refine ⟨((List.range n).filter (· ∈ S)).map (vtxNum n bits) ++
      ((List.range (pairs n).length).filter (· ∈ F)).map (edgeNum bits),
      ((List.filter_sublist).map _).append ((List.filter_sublist).map _), ?_⟩
    rw [List.sum_append, ← List.sum_toFinset _ (List.nodup_range.filter _),
      ← List.sum_toFinset _ (List.nodup_range.filter _), hset n S hS, hset _ F hF]

/-! ### The numbers in base 4 -/

/-- **A vertex number in base 4.** Let $n, v \in \mathbb{N}$, let $b$ be a list of booleans, and let
$m$ be the length of the list of vertex pairs $(i, j)$, $i < j < n$. The vertex number of $v$
defined from $n$ and $b$ equals $4^m + \sum_{q < m} t_q 4^q$, where $t_q = 1$ if entry $q$ of $b$
(counting from $0$) is true and $v$ is an endpoint of the $q$-th pair, and $t_q = 0$ otherwise. -/
theorem vtxNum_eq (n : ℕ) (bits : List Bool) (v : ℕ) :
    vtxNum n bits v = 4 ^ (pairs n).length +
      ∑ q ∈ Finset.range (pairs n).length, (if touches n bits v q then 1 else 0) * 4 ^ q := by
  rw [vtxNum, ← List.sum_toFinset _ (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range, Finset.sum_filter]
  simp [pairDigit]

/-- **The target in base 4.** Let $k, n \in \mathbb{N}$, let $b$ be a list of booleans, and let $m$
be the length of the list of vertex pairs $(i, j)$, $i < j < n$. The reduction's target for $k$,
$n$ and $b$ equals $k \cdot 4^m + \sum_{q < m} c_q 4^q$, where $c_q = 2$ if entry $q$ of $b$
(counting from $0$) is true and $c_q = 0$ otherwise, in particular when $b$ has no entry $q$. -/
theorem ssTarget_eq (k n : ℕ) (bits : List Bool) :
    ssTarget k n bits = k * 4 ^ (pairs n).length +
      ∑ q ∈ Finset.range (pairs n).length, (if bits.getD q false then 2 else 0) * 4 ^ q := by
  rw [ssTarget, ← List.sum_toFinset _ (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range, Finset.sum_filter]
  simp [pairDigit]

/-- **A subset sum of the reduction's numbers in base 4.** Let $n \in \mathbb{N}$, let $b$ be a
list of booleans, let $m$ be the length of the list of vertex pairs $(i, j)$, $i < j < n$, and let
$S$ and $F$ be finite sets of natural numbers with every element of $F$ below $m$. Write $x_v$ for
the vertex number of $v$ and $y_q$ for the pair number of $q$ defined from $n$ and $b$. For $q < m$
let $t_{v,q} = 1$ if entry $q$ of $b$ (counting from $0$) is true and $v$ is an endpoint of the
$q$-th pair, and $t_{v,q} = 0$ otherwise; let $f_q = 1$ if $q \in F$ and entry $q$ of $b$ is true,
and $f_q = 0$ otherwise. An absent entry counts as false. Then
$\sum_{v \in S} x_v + \sum_{q \in F} y_q = |S| \cdot 4^m +
\sum_{q < m} \left(\sum_{v \in S} t_{v,q} + f_q\right) 4^q$. -/
theorem sum_vtxNum_add_sum_edgeNum {n : ℕ} {bits : List Bool} {S F : Finset ℕ}
    (hF : F ⊆ Finset.range (pairs n).length) :
    ∑ v ∈ S, vtxNum n bits v + ∑ q ∈ F, edgeNum bits q =
      S.card * 4 ^ (pairs n).length + ∑ q ∈ Finset.range (pairs n).length,
        ((∑ v ∈ S, if touches n bits v q then 1 else 0) +
          if q ∈ F ∧ bits.getD q false then 1 else 0) * 4 ^ q := by
  have hE : ∑ q ∈ F, edgeNum bits q = ∑ q ∈ Finset.range (pairs n).length,
      (if q ∈ F ∧ bits.getD q false then 1 else 0) * 4 ^ q := by
    rw [Finset.sum_congr rfl fun q _ => show
        (if q ∈ F ∧ bits.getD q false then 1 else 0) * 4 ^ q =
          if q ∈ F then edgeNum bits q else 0 by
        by_cases hq : q ∈ F <;> by_cases hb : bits.getD q false <;>
          simp only [hq, hb, edgeNum, pairDigit] <;> simp,
      ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hF]
  simp only [vtxNum_eq, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, add_mul,
    Finset.sum_mul, hE]
  rw [Finset.sum_comm, add_assoc]

/-- **Vertices of a set touching a vertex pair.** Let $n$ be a natural number, let
$p_0, \dots, p_{m-1}$ be the vertex pairs in encoding order for $n$, let $b$ be a list of pair
bits, let $q < m$ with $p_q = (i, j)$, and let $S$ be a finite set of natural numbers. Write $[P]$
for $1$ if $P$ holds and $0$ otherwise. Then the number of $v \in S$ for which the test whether
pair $q$ touches $v$ under $b$ is true equals $[i \in S] + [j \in S]$ if the bit $b_q$ is set, and
$0$ otherwise (an index past the end of $b$ counts as an unset bit). -/
theorem sum_touches_eq {n : ℕ} {bits : List Bool} {q : ℕ} (hq : q < (pairs n).length)
    (S : Finset ℕ) :
    (∑ v ∈ S, if touches n bits v q then 1 else 0) =
      if bits.getD q false then
        (if (pairs n)[q].1 ∈ S then 1 else 0) + if (pairs n)[q].2 ∈ S then 1 else 0
      else 0 := by
  have hne : (pairs n)[q].1 ≠ (pairs n)[q].2 := (mem_pairs.1 (List.getElem_mem hq)).1.ne
  have ht : ∀ v, touches n bits v q =
      (bits.getD q false && ((pairs n)[q].1 == v || (pairs n)[q].2 == v)) := fun v => by
    simp [touches, List.getElem?_eq_getElem hq]
  simp only [ht]
  cases bits.getD q false
  · simp
  · rw [Finset.sum_congr rfl fun v _ => show
        (if (true && ((pairs n)[q].1 == v || (pairs n)[q].2 == v)) = true then 1 else 0) =
          (if (pairs n)[q].1 = v then 1 else 0) + (if (pairs n)[q].2 = v then 1 else 0) by
        by_cases h1 : (pairs n)[q].1 = v <;> by_cases h2 : (pairs n)[q].2 = v <;>
          simp_all]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
    simp

/-! ### Vertex covers on valid instances -/

/-- **Vertex covers in terms of the pair bits.** Let $n \in \mathbb{N}$, let $b$ be a list of
booleans with one entry for each pair in the list of vertex pairs $(i, j)$, $i < j < n$, and let
$G$ be the graph on the vertices $0, \dots, n - 1$ encoded by the pair bits $b$. Let $s$ be a
finite set of vertices of $G$ and $S$ a finite set of natural numbers such that each vertex $i$
lies in $s$ exactly when $i \in S$. Then $s$ is a vertex cover of $G$ if and only if, for every
index $q$ (counting from $0$) of the pair list whose entry in $b$ is true, the $q$-th pair
$(i_q, j_q)$ satisfies $i_q \in S$ or $j_q \in S$. -/
theorem isVertexCover_toGraph_iff {n : ℕ} {bits : List Bool}
    (h : bits.length = (pairs n).length) {s : Finset (Fin n)} {S : Finset ℕ}
    (hsS : ∀ i : Fin n, i ∈ s ↔ i.val ∈ S) :
    (toGraph n bits).IsVertexCover (s : Set (Fin n)) ↔
      ∀ q (hq : q < (pairs n).length), bits.getD q false = true →
        (pairs n)[q].1 ∈ S ∨ (pairs n)[q].2 ∈ S := by
  constructor
  · intro hcov q hq hb
    obtain ⟨hab, hbn⟩ : (pairs n)[q].1 < (pairs n)[q].2 ∧ (pairs n)[q].2 < n :=
      mem_pairs.1 (List.getElem_mem hq)
    have hadj : (toGraph n bits).Adj ⟨_, hab.trans hbn⟩ ⟨_, hbn⟩ := by
      refine ⟨fun he => hab.ne (Fin.val_eq_of_eq he), ?_⟩
      rw [adjBits_eq_getElem h hab hbn]
      simp only [Prod.mk.eta, (pairs_nodup n).idxOf_getElem]
      rwa [List.getD_eq_getElem] at hb
    exact (hcov hadj).imp (hsS _).1 (hsS _).1
  · intro hS
    have key : ∀ i j : Fin n, i < j → (toGraph n bits).Adj i j → i ∈ s ∨ j ∈ s := by
      intro i j hij hadj
      have hmem : ((i : ℕ), (j : ℕ)) ∈ pairs n := mem_pairs.2 ⟨hij, j.2⟩
      have hq := List.idxOf_lt_length_of_mem hmem
      have hb := hadj.2
      rw [adjBits_eq_getElem h hij j.2] at hb
      have hcov := hS _ hq (by rwa [List.getD_eq_getElem])
      rw [List.getElem_idxOf] at hcov
      exact hcov.imp (hsS i).2 (hsS j).2
    intro i j hadj
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact key i j hij hadj
    · exact absurd rfl hadj.1
    · exact (key j i hij hadj.symm).symm

/-! ### Correctness -/

/-- **Vertex covers of size $k$ match subset sums hitting the target.** Let $k, n \in \mathbb{N}$
and let $b$ be a list of booleans with one entry for each pair in the list of vertex pairs
$(i, j)$, $i < j < n$. Let $G$ be the graph on the vertices $0, \dots, n - 1$ encoded by the pair
bits $b$. Then $G$ has a vertex cover with exactly $k$ vertices if and only if some sublist (a
subsequence, not necessarily contiguous) of the reduction's numbers for $n$ and $b$ sums to the
reduction's target for $k$, $n$ and $b$. -/
theorem exists_cover_iff_exists_sublist {k n : ℕ} {bits : List Bool}
    (h : bits.length = (pairs n).length) :
    (∃ s : Finset (Fin n), s.card = k ∧ (toGraph n bits).IsVertexCover (s : Set (Fin n))) ↔
      ∃ l : List ℕ, l.Sublist (ssNums n bits) ∧ l.sum = ssTarget k n bits := by
  rw [exists_sublist_ssNums_iff]
  -- Hitting the target: `k` vertices, and on each edge the chosen endpoints plus the chosen edge
  -- number make `2`.
  have hhit : ∀ S F, F ⊆ Finset.range (pairs n).length →
      (∑ v ∈ S, vtxNum n bits v + ∑ q ∈ F, edgeNum bits q = ssTarget k n bits ↔
        S.card = k ∧ ∀ q (hq : q < (pairs n).length), bits.getD q false = true →
          (if (pairs n)[q].1 ∈ S then 1 else 0) + (if (pairs n)[q].2 ∈ S then 1 else 0) +
            (if q ∈ F then 1 else 0) = 2) := by
    intro S F hF
    rw [sum_vtxNum_add_sum_edgeNum hF, ssTarget_eq, add_sum_digits_eq_iff]
    · refine and_congr_right fun _ => forall_congr' fun q => ?_
      constructor
      · intro hd hq hb
        have := hd hq
        rw [sum_touches_eq hq, hb] at this
        simpa using this
      · intro hd hq
        rw [sum_touches_eq hq]
        cases hb : bits.getD q false
        · simp
        · simpa using hd hq hb
    · intro q hq
      rw [sum_touches_eq hq]
      split_ifs <;> omega
    · intro q _
      split_ifs <;> omega
  constructor
  · rintro ⟨s, hk, hcov⟩
    set S := s.map Fin.valEmbedding
    have hsS : ∀ i : Fin n, i ∈ s ↔ i.val ∈ S := fun i => (Finset.mem_map' _).symm
    have hcovS := (isVertexCover_toGraph_iff h hsS).1 hcov
    -- Top up each edge with exactly one chosen endpoint by its edge number.
    set F := (Finset.range (pairs n).length).filter fun q =>
      ¬(((pairs n).getD q (0, 0)).1 ∈ S ∧ ((pairs n).getD q (0, 0)).2 ∈ S)
    refine ⟨S, fun v hv => ?_, F, Finset.filter_subset _ _,
      (hhit S F (Finset.filter_subset _ _)).2 ⟨by simp [S, hk], fun q hq hb => ?_⟩⟩
    · obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hv
      exact Finset.mem_range.2 i.2
    · have hF : q ∈ F ↔ ¬((pairs n)[q].1 ∈ S ∧ (pairs n)[q].2 ∈ S) := by
        simp [F, hq]
      have := hcovS q hq hb
      by_cases h1 : (pairs n)[q].1 ∈ S <;> by_cases h2 : (pairs n)[q].2 ∈ S <;>
        simp [h1, h2, hF] at this ⊢
  · rintro ⟨S, hS, F, hF, hsum⟩
    obtain ⟨hk, hd⟩ := (hhit S F hF).1 hsum
    set s := Finset.univ.filter fun i : Fin n => i.val ∈ S
    have hsS : ∀ i : Fin n, i ∈ s ↔ i.val ∈ S := fun i => by simp [s]
    refine ⟨s, ?_, (isVertexCover_toGraph_iff h hsS).2 fun q hq hb => ?_⟩
    · rw [← hk, ← Finset.card_map Fin.valEmbedding]
      congr 1
      ext v
      simp only [s, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply]
      exact ⟨fun ⟨a, ha, he⟩ => he ▸ ha, fun hv => ⟨⟨v, Finset.mem_range.1 (hS hv)⟩, hv, rfl⟩⟩
    · have := hd q hq hb
      by_contra hne
      simp only [not_or] at hne
      simp only [hne.1, hne.2, ite_false] at this
      split_ifs at this <;> omega

theorem vertexCoverDec_eq_subsetSumDec_reduceSS (x : List Bool) :
    vertexCoverDec x = subsetSumDec (reduceSS x) := by
  unfold reduceSS
  split
  next k n bits hx =>
    rw [decodeKG_eq_some_iff] at hx
    subst hx
    split_ifs with hlen
    · rw [Bool.eq_iff_iff, vertexCoverDec, kgDec_encodeKG_eq_true, subsetSumDec_encodeSS_eq_true,
        ← exists_cover_iff_exists_sublist hlen, and_iff_right hlen]
    · rw [subsetSumDec_noSS, vertexCoverDec, Bool.eq_false_iff, ne_eq, kgDec_encodeKG_eq_true]
      exact fun h' => hlen h'.1
  next hx => rw [vertexCoverDec, kgDec_of_decodeKG_eq_none hx, subsetSumDec_noSS]

end Cslib.Complexity.Karp
