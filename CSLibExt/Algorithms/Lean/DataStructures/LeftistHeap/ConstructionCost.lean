/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

/-!
# Bottom-up heap construction costs

Repeated adjacent merging is the construction pattern for leftist heaps in
Nipkow et al., *Functional Data Structures and Algorithms*, §15.4, (15.1–15.2).
The API abstracts over a carrier, its invariant, size, merge operation and
merge cost. It proves a one-pass bound for lists of any length and a multi-pass
bound for a power-of-two number of equally sized inputs. Neither statement
assumes its own conclusion: per-merge costs are bounded explicitly, and the
multi-pass theorem also requires preservation of size and the invariant.

Only merge costs are counted; list traversal, allocation and other auxiliary
operations are outside this cost model. The source uses the discrete bound
`2 * Nat.log2 (n + 1) + 1`. Fuel exhaustion gives zero cost, but the public
`mergeAllCost` supplies the original list length, proved sufficient by
`mergeAllCostAux_stable`.

Adapted from `auto-fdsa-15-01/solution/Solution.lean` and
`auto-fdsa-15-02/solution/Solution.lean` in `codimango/sw-verification-zhih`,
commit `16412d086eb5af2e74da78731bde50da0667bc79`.
The source declarations `fdsa_chap15_ex01` and `fdsa_chap15_ex02` remain
available in this namespace, with their hypotheses and conclusions preserved.
-/

set_option autoImplicit false

@[expose] public section

namespace Cslib.Algorithms.Lean.LeftistHeap.ConstructionCost

-- Concrete bound from source (15.1): mergeCostBound n = 2 * lg (n+1) + 1
def mergeCostBound : ℕ → ℕ
| n => 2 * Nat.log2 (n + 1) + 1

variable {α : Type*}

-- Functional mergeAdjacent: merges adjacent pairs
-- mergeAdjacent [] = [], [t] = [t], (t1 # t2 # ts) = merge t1 t2 # mergeAdjacent ts
-- Source gives length property |mergeAdjacent ts| = (|ts|+1) div 2
def mergeAdjacent {α : Type*} (merge : α → α → α) : List α → List α
| [] => []
| [t] => [t]
| t1 :: t2 :: ts => merge t1 t2 :: mergeAdjacent merge ts

-- Cost definitions from source appendix B.5
-- T_merge_adj [] = 0, [_]=0, (t1#t2#ts)= Tmerge t1 t2 + mergeAdjacentCost ts
def mergeAdjacentCost {α : Type*} (Tmerge : α → α → ℕ) : List α → ℕ
| [] => 0
| [_] => 0
| t1 :: t2 :: ts => Tmerge t1 t2 + mergeAdjacentCost Tmerge ts

-- T_merge_all with fuel recursion to avoid well-founded termination proof
-- Intended recurrence: T_merge_all []=0, [t]=0, mergeAllCost ts = mergeAdjacentCost ts +
-- mergeAllCost (mergeAdjacent ts)
-- Fuel = number of remaining passes; ts.length suffices because length at least halves each
-- step
def mergeAllCostAux {α : Type*} (merge : α → α → α) (Tmerge : α → α → ℕ) : Nat → List α → ℕ
| 0, _ => 0
| _ + 1, [] => 0
| _ + 1, [_] => 0
| fuel + 1, ts@(_ :: _ :: _) => mergeAdjacentCost Tmerge ts + mergeAllCostAux merge Tmerge fuel
    (mergeAdjacent merge ts)

-- Concrete mergeAllCost defined via sufficient fuel (original length)
def mergeAllCost {α : Type*} (merge : α → α → α) (Tmerge : α → α → ℕ) (ts : List α) : ℕ :=
  mergeAllCostAux merge Tmerge ts.length ts

-- Helper lemmas

lemma mergeAdjacent_length {α : Type*} (merge : α → α → α) (ts : List α) :
    (mergeAdjacent merge ts).length = (ts.length + 1) / 2 := by
  induction ts using mergeAdjacent.induct with
  | case1 => simp [mergeAdjacent]
  | case2 t => simp [mergeAdjacent]
  | case3 t1 t2 ts ih => simp [mergeAdjacent, ih]; omega

lemma mergeAdjacent_length_le {α : Type*} (merge : α → α → α) (ts : List α)
    (h : 2 ≤ ts.length) : (mergeAdjacent merge ts).length ≤ ts.length - 1 := by
  have hlen := mergeAdjacent_length merge ts
  omega

lemma mergeAdjacent_length_lt {α : Type*} (merge : α → α → α) (ts : List α)
    (h : 2 ≤ ts.length) : (mergeAdjacent merge ts).length < ts.length := by
  have hle := mergeAdjacent_length_le merge ts h
  omega

lemma mergeAdjacent_length_pow {α : Type*} (merge : α → α → α) (ts : List α) (k : ℕ)
    (hk : 1 ≤ k) (hlen : ts.length = 2 ^ k) :
    (mergeAdjacent merge ts).length = 2 ^ (k - 1) := by
  have h1 := mergeAdjacent_length merge ts
  rw [hlen] at h1
  have hpow : 2 * 2 ^ (k - 1) = 2 ^ k := by
    calc 2 * 2 ^ (k - 1) = 2 ^ (k - 1) * 2 := by rw [Nat.mul_comm]
      _ = 2 ^ ((k - 1) + 1) := by rw [← Nat.pow_succ]
      _ = 2 ^ k := by
        have hk1 : (k - 1) + 1 = k := by omega
        rw [hk1]
  have hpow' : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [hpow]
  rw [hpow'] at h1
  omega

lemma invariant_mergeAdjacent {α : Type*} (Itree : α → Prop) (merge : α → α → α)
    (hmerge_Itree : ∀ a b, Itree a → Itree b → Itree (merge a b))
    (ts : List α) (hItree : ∀ t ∈ ts, Itree t) :
    ∀ t ∈ mergeAdjacent merge ts, Itree t := by
  induction ts using mergeAdjacent.induct with
  | case1 => simp [mergeAdjacent]
  | case2 t =>
    simpa only [mergeAdjacent, List.mem_singleton, forall_eq] using hItree t (by simp)
  | case3 t1 t2 ts ih =>
    simp only [mergeAdjacent, List.mem_cons, forall_eq_or_imp]
    constructor
    · exact hmerge_Itree t1 t2 (hItree t1 (by simp)) (hItree t2 (by simp))
    · exact ih (fun u hu => hItree u (by simp [hu]))

lemma size_mergeAdjacent_even {α : Type*} (sz : α → ℕ) (merge : α → α → α)
    (hmerge_size : ∀ a b, sz (merge a b) = sz a + sz b)
    (ts : List α) (n : ℕ) :
    (∀ t ∈ ts, sz t = n) → ts.length % 2 = 0 → ∀ t ∈ mergeAdjacent merge ts, sz t = 2 * n := by
  induction ts using mergeAdjacent.induct with
  | case1 =>
    intro hsize heven
    simp [mergeAdjacent] at *
  | case2 t =>
    intro hsize heven
    simp at heven
  | case3 t1 t2 ts ih =>
    intro hsize heven
    simp only [mergeAdjacent, List.mem_cons, forall_eq_or_imp]
    constructor
    · rw [hmerge_size, hsize t1 (by simp), hsize t2 (by simp)]
      omega
    · apply ih
      · intro u hu; exact hsize u (by simp [hu])
      · simp at heven; omega

lemma size_mergeAdjacent_pow {α : Type*} (sz : α → ℕ) (merge : α → α → α)
    (hmerge_size : ∀ a b, sz (merge a b) = sz a + sz b)
    (ts : List α) (n k : ℕ) (hk : 1 ≤ k) (hlen : ts.length = 2 ^ k) :
    (∀ t ∈ ts, sz t = n) → ∀ t ∈ mergeAdjacent merge ts, sz t = 2 * n := by
  intro hsize
  have heven : ts.length % 2 = 0 := by
    rw [hlen]
    have : 2 ^ k % 2 = 0 := by
      have hk1 : k = (k - 1) + 1 := by omega
      rw [hk1, Nat.pow_succ]
      simp
    exact this
  exact size_mergeAdjacent_even sz merge hmerge_size ts n hsize heven

/-- One adjacent pass costs at most the number of pairs times the merge bound. -/
theorem fdsa_chap15_ex02
    (Itree : α → Prop) (sz : α → ℕ)
    (Tmerge : α → α → ℕ)
    (ts : List α) (n : ℕ)
    (hItree : ∀ t ∈ ts, Itree t)
    (hsize : ∀ t ∈ ts, sz t = n)
    (hTmerge_bound : ∀ t1 t2, Itree t1 → Itree t2 → sz t1 = n → sz t2 = n → Tmerge t1 t2 ≤
        mergeCostBound n) :
    mergeAdjacentCost Tmerge ts ≤ (ts.length / 2) * mergeCostBound n := by
  induction ts using mergeAdjacentCost.induct with
  | case1 => simp [mergeAdjacentCost]
  | case2 t => simp [mergeAdjacentCost]
  | case3 t1 t2 ts ih =>
    have hpair := hTmerge_bound t1 t2
      (hItree t1 (by simp)) (hItree t2 (by simp))
      (hsize t1 (by simp)) (hsize t2 (by simp))
    have htail := ih (fun t ht => hItree t (by simp [ht]))
      (fun t ht => hsize t (by simp [ht]))
    have hlength : (t1 :: t2 :: ts).length / 2 = ts.length / 2 + 1 := by
      simp
      omega
    simp only [mergeAdjacentCost]
    calc
      Tmerge t1 t2 + mergeAdjacentCost Tmerge ts
          ≤ mergeCostBound n + (ts.length / 2) * mergeCostBound n := Nat.add_le_add hpair htail
      _ = (ts.length / 2 + 1) * mergeCostBound n := by ring
      _ = ((t1 :: t2 :: ts).length / 2) * mergeCostBound n := by rw [hlength]

lemma mergeAdjacentCost_bound {α : Type*} (Itree : α → Prop) (sz : α → ℕ)
    (Tmerge : α → α → ℕ) (ts : List α) (n : ℕ)
    (hItree : ∀ t ∈ ts, Itree t) (hsize : ∀ t ∈ ts, sz t = n)
    (hTmerge_bound : ∀ a b m, Itree a → Itree b → sz a = m → sz b = m → Tmerge a b ≤
        mergeCostBound m) :
    mergeAdjacentCost Tmerge ts ≤ (ts.length / 2) * mergeCostBound n := by
  exact fdsa_chap15_ex02 Itree sz Tmerge ts n hItree hsize
    (fun a b ha hb hsa hsb => hTmerge_bound a b n ha hb hsa hsb)

lemma mergeAdjacentCost_bound_pow {α : Type*} (Itree : α → Prop) (sz : α → ℕ)
    (Tmerge : α → α → ℕ) (ts : List α) (n k : ℕ) (hk : 1 ≤ k)
    (hlen : ts.length = 2 ^ k)
    (hItree : ∀ t ∈ ts, Itree t) (hsize : ∀ t ∈ ts, sz t = n)
    (hTmerge_bound : ∀ a b m, Itree a → Itree b → sz a = m → sz b = m → Tmerge a b ≤
        mergeCostBound m) :
    mergeAdjacentCost Tmerge ts ≤ 2 ^ (k - 1) * mergeCostBound n := by
  have h := mergeAdjacentCost_bound Itree sz Tmerge ts n hItree hsize hTmerge_bound
  have hdiv : ts.length / 2 = 2 ^ (k - 1) := by
    rw [hlen]
    have hpow : 2 * 2 ^ (k - 1) = 2 ^ k := by
      calc 2 * 2 ^ (k - 1) = 2 ^ (k - 1) * 2 := by rw [Nat.mul_comm]
        _ = 2 ^ ((k - 1) + 1) := by rw [← Nat.pow_succ]
        _ = 2 ^ k := by
          have hk1 : (k - 1) + 1 = k := by omega
          rw [hk1]
    have hpow' : 2 ^ k = 2 * 2 ^ (k - 1) := by rw [hpow]
    rw [hpow', Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  rw [hdiv] at h
  exact h

lemma mergeAllCostAux_stable {α : Type*} (merge : α → α → α) (Tmerge : α → α → ℕ) :
    ∀ (ts : List α) (fuel : ℕ), fuel ≥ ts.length →
      mergeAllCostAux merge Tmerge fuel ts = mergeAllCostAux merge Tmerge ts.length ts := by
  intro ts
  have hP : ∀ (L : ℕ) (ts : List α), ts.length = L →
      ∀ fuel, fuel ≥ L → mergeAllCostAux merge Tmerge fuel ts = mergeAllCostAux merge Tmerge L
          ts := by
    intro L
    induction L using Nat.strongRecOn with
    | _ L ih =>
      intro ts hlen fuel hfuel
      match ts with
      | [] =>
        have hL0 : L = 0 := hlen.symm
        subst hL0
        cases fuel with
        | zero => rfl
        | succ f => simp [mergeAllCostAux]
      | [x] =>
        have hL1 : L = 1 := hlen.symm
        subst hL1
        cases fuel with
        | zero => omega
        | succ f =>
          simp [mergeAllCostAux]
      | x :: y :: ys =>
        have hM_lt : (mergeAdjacent merge (x :: y :: ys)).length < L := by
          have h1 := mergeAdjacent_length_lt merge (x :: y :: ys) (by simp)
          omega
        have hfuel_succ : ∃ f', fuel = f' + 1 := by
          have : 0 < fuel := by omega
          exact Nat.exists_eq_succ_of_ne_zero (by omega)
        rcases hfuel_succ with ⟨fuel', rfl⟩
        have hL_succ : ∃ L', L = L' + 1 := by
          exact ⟨L - 1, by omega⟩
        rcases hL_succ with ⟨L', rfl⟩
        have eq1 : mergeAllCostAux merge Tmerge (fuel' + 1) (x :: y :: ys) =
            mergeAdjacentCost Tmerge (x :: y :: ys) + mergeAllCostAux merge Tmerge fuel'
                (mergeAdjacent merge (x :: y :: ys)) := by
          simp [mergeAllCostAux]
        have eq2 : mergeAllCostAux merge Tmerge (L' + 1) (x :: y :: ys) =
            mergeAdjacentCost Tmerge (x :: y :: ys) + mergeAllCostAux merge Tmerge L'
                (mergeAdjacent merge (x :: y :: ys)) := by
          simp [mergeAllCostAux]
        rw [eq1, eq2]
        have hM_le_fuel' : (mergeAdjacent merge (x :: y :: ys)).length ≤ fuel' := by
          have hle := mergeAdjacent_length_le merge (x :: y :: ys) (by simp)
          omega
        have hM_le_L' : (mergeAdjacent merge (x :: y :: ys)).length ≤ L' := by
          have hle := mergeAdjacent_length_le merge (x :: y :: ys) (by simp)
          omega
        have ih_M := ih ((mergeAdjacent merge (x :: y :: ys)).length) hM_lt
        have eq_fuel' : mergeAllCostAux merge Tmerge fuel' (mergeAdjacent merge (x :: y :: ys))
            =
            mergeAllCostAux merge Tmerge (mergeAdjacent merge (x :: y :: ys)).length
                (mergeAdjacent merge (x :: y :: ys)) := by
          apply ih_M
          · rfl
          · exact hM_le_fuel'
        have eq_L' : mergeAllCostAux merge Tmerge L' (mergeAdjacent merge (x :: y :: ys)) =
            mergeAllCostAux merge Tmerge (mergeAdjacent merge (x :: y :: ys)).length
                (mergeAdjacent merge (x :: y :: ys)) := by
          apply ih_M
          · rfl
          · exact hM_le_L'
        rw [eq_fuel', eq_L']
  intro fuel hge
  exact hP ts.length ts rfl fuel hge

lemma mergeAllCost_unfold_pow {α : Type*} (merge : α → α → α) (Tmerge : α → α → ℕ)
    (ts : List α) (k : ℕ) (hk : 1 ≤ k) (hlen : ts.length = 2 ^ k) :
    mergeAllCost merge Tmerge ts = mergeAdjacentCost Tmerge ts + mergeAllCost merge Tmerge
        (mergeAdjacent merge ts) := by
  unfold mergeAllCost
  have hlen_ge2 : 2 ≤ ts.length := by
    rw [hlen]
    have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
    simp at this
    omega
  cases ts with
  | nil =>
    simp at hlen
    exfalso
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    omega
  | cons x xs =>
    cases xs with
    | nil =>
      simp at hlen
      exfalso
      have hge : 2 ≤ 2 ^ k := by
        have : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
        simp at this
        omega
      omega
    | cons y ys =>
      have h_eq1 : mergeAllCostAux merge Tmerge (x :: y :: ys).length (x :: y :: ys) =
          mergeAdjacentCost Tmerge (x :: y :: ys) + mergeAllCostAux merge Tmerge ((x :: y ::
              ys).length - 1) (mergeAdjacent merge (x :: y :: ys)) := by
        have h1 : (x :: y :: ys).length = ((x :: y :: ys).length - 1) + 1 := by omega
        conv_lhs => rw [h1]
        simp [mergeAllCostAux]
      rw [h_eq1]
      have hM_le : (mergeAdjacent merge (x :: y :: ys)).length ≤ (x :: y :: ys).length - 1 :=
          by
        apply mergeAdjacent_length_le
        simp
      have h_stable : mergeAllCostAux merge Tmerge ((x :: y :: ys).length - 1) (mergeAdjacent
          merge (x :: y :: ys)) =
          mergeAllCostAux merge Tmerge (mergeAdjacent merge (x :: y :: ys)).length
              (mergeAdjacent merge (x :: y :: ys)) := by
        apply mergeAllCostAux_stable
        exact hM_le
      rw [h_stable]

-- Sum lemmas
private lemma sum_Icc_succ_top (k n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (k + 1), (2 ^ ((k + 1) - i) * mergeCostBound (2 ^ (i - 1) * n)) =
    2 ^ k * mergeCostBound n + ∑ i ∈ Finset.Icc 2 (k + 1), (2 ^ ((k + 1) - i) * mergeCostBound
        (2 ^ (i - 1) * n)) := by
  have h_eq : Finset.Icc 1 (k + 1) = insert (1 : ℕ) (Finset.Icc 2 (k + 1)) := by
    ext x
    simp [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h_not_mem : (1 : ℕ) ∉ Finset.Icc 2 (k + 1) := by simp [Finset.mem_Icc]
  rw [h_eq, Finset.sum_insert h_not_mem]
  simp

private def successorEmbedding : ℕ ↪ ℕ :=
  ⟨Nat.succ, Nat.succ_injective⟩

private lemma Icc_two_eq_map_Icc_one (k : ℕ) :
    Finset.Icc 2 (k + 1) = (Finset.Icc 1 k).map successorEmbedding := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map]
  constructor
  · intro hx
    refine ⟨x - 1, ⟨by omega, by omega⟩, ?_⟩
    change Nat.succ (x - 1) = x
    omega
  · rintro ⟨y, hy, hxy⟩
    change Nat.succ y = x at hxy
    omega

private lemma sum_Icc_two_eq_sum_Icc_one (k n : ℕ) :
    ∑ i ∈ Finset.Icc 2 (k + 1), (2 ^ ((k + 1) - i) * mergeCostBound (2 ^ (i - 1) * n)) =
    ∑ j ∈ Finset.Icc 1 k, (2 ^ (k - j) * mergeCostBound (2 ^ j * n)) := by
  have h_eq := Icc_two_eq_map_Icc_one k
  rw [h_eq]
  rw [Finset.sum_map]
  simp only [successorEmbedding, Function.Embedding.coeFn_mk, Nat.succ_eq_add_one]
  apply Finset.sum_congr rfl
  intro j hj
  have h1 : (k + 1) - (j + 1) = k - j := by omega
  rw [h1]
  have h2 : (j + 1 - 1 : ℕ) = j := by omega
  rw [h2]

private lemma sum_S_succ (k n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (k + 1), (2 ^ ((k + 1) - i) * mergeCostBound (2 ^ (i - 1) * n)) =
    2 ^ k * mergeCostBound n + ∑ j ∈ Finset.Icc 1 k, (2 ^ (k - j) * mergeCostBound (2 ^ j * n))
        := by
  rw [sum_Icc_succ_top k n]
  rw [sum_Icc_two_eq_sum_Icc_one k n]

private lemma pow_mul_two (j n : ℕ) (hj : 1 ≤ j) : 2 ^ j * n = 2 ^ (j - 1) * (2 * n) := by
  have hj1 : j = (j - 1) + 1 := by omega
  have hpow : 2 ^ j = 2 * 2 ^ (j - 1) := by
    rw [hj1]
    simp [Nat.pow_succ, Nat.mul_comm]
  calc 2 ^ j * n = (2 * 2 ^ (j - 1)) * n := by rw [hpow]
    _ = 2 ^ (j - 1) * (2 * n) := by
      simp only [Nat.mul_assoc, Nat.mul_comm]

private lemma sum_transform_2n (k n : ℕ) :
    ∑ j ∈ Finset.Icc 1 k, (2 ^ (k - j) * mergeCostBound (2 ^ j * n)) =
    ∑ j ∈ Finset.Icc 1 k, (2 ^ (k - j) * mergeCostBound (2 ^ (j - 1) * (2 * n))) := by
  apply Finset.sum_congr rfl
  intro j hj
  have hj_ge : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hpow : 2 ^ j * n = 2 ^ (j - 1) * (2 * n) := pow_mul_two j n hj_ge
  rw [hpow]

-- (15.2) Bound for merge_all:
-- Under assumptions:
-- - all trees in ts satisfy Itree and have size n
-- - |ts| = 2^k
-- - merge preserves size: |merge t1 t2| = |t1| + |t2| and Itree
-- - Tmerge cost bounded: if |t1|=|t2|=m and Itree then Tmerge t1 t2 ≤ mergeCostBound m
-- Then mergeAllCost is bounded by Σ_{i=1}^k 2^{k-i} * mergeCostBound (2^{i-1} * n)
-- mergeCostBound is concrete (2*log2(n+1)+1), mergeAllCost is concrete defined via
-- recurrences,
-- so bound is not for arbitrary unconstrained cost functions.
/-- The multi-pass cost bound (15.2) for equally sized heaps. -/
theorem fdsa_chap15_ex01
    (Itree : α → Prop) (sz : α → ℕ)
    (merge : α → α → α) (Tmerge : α → α → ℕ)
    (ts : List α) (n k : ℕ)
    (hItree : ∀ t ∈ ts, Itree t)
    (hsize : ∀ t ∈ ts, sz t = n)
    (hlen : ts.length = 2 ^ k)
    (hmerge_size : ∀ a b, sz (merge a b) = sz a + sz b)
    (hmerge_Itree : ∀ a b, Itree a → Itree b → Itree (merge a b))
    (hTmerge_bound : ∀ a b m, Itree a → Itree b → sz a = m → sz b = m → Tmerge a b ≤
        mergeCostBound m) :
    mergeAllCost merge Tmerge ts ≤ ∑ i ∈ Finset.Icc 1 k, 2 ^ (k - i) * mergeCostBound (2 ^ (i -
        1) * n) := by
  induction k generalizing ts n with
  | zero =>
    have hlen1 : ts.length = 1 := by simpa using hlen
    have hT0 : mergeAllCost merge Tmerge ts = 0 := by
      cases ts with
      | nil => simp at hlen1
      | cons x xs =>
        cases xs with
        | nil =>
          unfold mergeAllCost
          simp [mergeAllCostAux]
        | cons y ys => simp at hlen1
    have hsum0 : ∑ i ∈ Finset.Icc 1 0, 2 ^ (0 - i) * mergeCostBound (2 ^ (i - 1) * n) = 0 := by
        simp
    rw [hT0, hsum0]
  | succ k ih =>
    have hk1 : 1 ≤ k + 1 := by omega
    have hunfold : mergeAllCost merge Tmerge ts = mergeAdjacentCost Tmerge ts + mergeAllCost
        merge Tmerge (mergeAdjacent merge ts) :=
      mergeAllCost_unfold_pow merge Tmerge ts (k + 1) hk1 hlen
    have hbound_adj : mergeAdjacentCost Tmerge ts ≤ 2 ^ k * mergeCostBound n := by
      have hk1' : 1 ≤ k + 1 := hk1
      have hlen' : ts.length = 2 ^ (k + 1) := hlen
      exact mergeAdjacentCost_bound_pow Itree sz Tmerge ts n (k + 1) hk1' hlen' hItree hsize
          hTmerge_bound
    have hlen_merge : (mergeAdjacent merge ts).length = 2 ^ k := by
      exact mergeAdjacent_length_pow merge ts (k + 1) hk1 hlen
    have hItree_merge : ∀ t ∈ mergeAdjacent merge ts, Itree t :=
      invariant_mergeAdjacent Itree merge hmerge_Itree ts hItree
    have hsize_merge : ∀ t ∈ mergeAdjacent merge ts, sz t = 2 * n :=
      size_mergeAdjacent_pow sz merge hmerge_size ts n (k + 1) hk1 hlen hsize
    have ih' : mergeAllCost merge Tmerge (mergeAdjacent merge ts) ≤
        ∑ i ∈ Finset.Icc 1 k, 2 ^ (k - i) * mergeCostBound (2 ^ (i - 1) * (2 * n)) := by
      apply ih (mergeAdjacent merge ts) (2 * n) hItree_merge hsize_merge hlen_merge
    have hsum_eq : ∑ i ∈ Finset.Icc 1 k, 2 ^ (k - i) * mergeCostBound (2 ^ (i - 1) * (2 * n)) =
        ∑ j ∈ Finset.Icc 1 k, 2 ^ (k - j) * mergeCostBound (2 ^ j * n) := by
      rw [← sum_transform_2n k n]
    rw [hsum_eq] at ih'
    have hsum_succ : ∑ i ∈ Finset.Icc 1 (k + 1), 2 ^ ((k + 1) - i) * mergeCostBound (2 ^ (i -
        1) * n) =
        2 ^ k * mergeCostBound n + ∑ j ∈ Finset.Icc 1 k, 2 ^ (k - j) * mergeCostBound (2 ^ j *
            n) := sum_S_succ k n
    calc mergeAllCost merge Tmerge ts
        = mergeAdjacentCost Tmerge ts + mergeAllCost merge Tmerge (mergeAdjacent merge ts) :=
            hunfold
      _ ≤ 2 ^ k * mergeCostBound n + (∑ j ∈ Finset.Icc 1 k, 2 ^ (k - j) * mergeCostBound (2 ^ j
          * n)) := Nat.add_le_add hbound_adj ih'
      _ = ∑ i ∈ Finset.Icc 1 (k + 1), 2 ^ ((k + 1) - i) * mergeCostBound (2 ^ (i - 1) * n) :=
          by rw [hsum_succ, Nat.add_comm]


end Cslib.Algorithms.Lean.LeftistHeap.ConstructionCost
