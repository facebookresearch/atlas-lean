/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# MAX-CUT: the random cut and local search

A graph on `Fin n` is an `EdgeSet n`: a finset of ordered pairs `(i, j)` with `i < j`, so each
undirected edge is stored exactly once. An assignment `x : Fin n → Bool` cuts the edge `(i, j)`
when `x i ≠ x j`, and `cutCount E x` counts the cut edges.

## Main results

* `sum_cutCount`: summed over all `2 ^ n` assignments, the cut size is `2 ^ (n - 1) * |E|`, so a
  uniformly random assignment cuts half the edges in expectation.
* `locally_optimal_cut_ge`: a locally optimal cut (no single-vertex flip increases it) cuts at
  least half the edges, so local search is a `1/2`-approximation.

## References

* J. Kleinberg and É. Tardos, *Algorithm Design*, Addison-Wesley, 2006, Section 12.4.
* M. Mitzenmacher and E. Upfal, *Probability and Computing*, Cambridge University Press, 2005,
  Chapter 6.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MaxCut

/-- A graph on `Fin n` given by its edges, each undirected edge stored once as an ordered pair
`(i, j)` with `i < j`. -/
structure EdgeSet (n : ℕ) where
  /-- The edges, as ordered pairs `(i, j)`. -/
  edges : Finset (Fin n × Fin n)
  /-- Each edge is stored smaller endpoint first, so each undirected edge occurs once. -/
  lt_of_mem : ∀ e ∈ edges, e.1 < e.2

/-- The number of edges of `E` cut by the assignment `x`
(an edge `(i, j)` is cut if `x i ≠ x j`). -/
noncomputable def cutCount {n : ℕ} (E : EdgeSet n) (x : Fin n → Bool) : ℝ :=
  ((E.edges.filter (fun e => x e.1 ≠ x e.2)).card : ℝ)

private lemma sum_single_indicator {n : ℕ} (_hn : 0 < n) (i : Fin n) :
    (∑ x : Fin n → Bool, (if x i then (1:ℝ) else 0)) = 2 ^ (n - 1) := by
  let f : Fin n → Bool → ℝ := fun j b => if j = i then (if b then 1 else 0) else 1
  have hterm : ∀ x : Fin n → Bool, (if x i then (1:ℝ) else 0) = ∏ j, f j (x j) := by
    intro x
    simp only [f]
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [← Fintype.prod_sum f]
  have hinner : ∀ j : Fin n, (∑ b : Bool, f j b) = (if j = i then 1 else 2) := by
    intro j
    simp only [f]
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]
  rw [Finset.prod_congr rfl (fun j _ => hinner j)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i (fun j => (if j = i then (1:ℝ) else 2)) (by simp)]
  simp only [ite_true, one_mul]
  have hall2 : ∀ j ∈ Finset.univ \ {i}, (if j = i then (1:ℝ) else 2) = 2 := by
    intro j hj
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hj
    simp [hj]
  rw [Finset.prod_congr rfl hall2]
  rw [Finset.prod_const]
  have hcard : (Finset.univ \ {i}).card = n - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem]
    · rw [Finset.card_univ, Fintype.card_fin]
    · simp
  rw [hcard]

private lemma sum_pair_indicator {n : ℕ} (i j : Fin n) (hij : i ≠ j) (_hn2 : 2 ≤ n) :
    (∑ x : Fin n → Bool, (if x i then (1:ℝ) else 0) * (if x j then (1:ℝ) else 0))
      = 2 ^ (n - 2) := by
  let f : Fin n → Bool → ℝ := fun k b =>
    if k = i then (if b then 1 else 0) else if k = j then (if b then 1 else 0) else 1
  have hji : j ≠ i := fun h => hij h.symm
  have hjmem : j ∈ (Finset.univ : Finset (Fin n)) \ {i} := by simp [hji]
  have hterm : ∀ x : Fin n → Bool,
      (if x i then (1:ℝ) else 0) * (if x j then (1:ℝ) else 0) = ∏ k, f k (x k) := by
    intro x
    simp only [f]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton i _ (by simp)]
    simp only [ite_true]
    rw [Finset.prod_eq_mul_prod_sdiff_singleton j _ (by intro h; exact absurd hjmem h)]
    have h1 : (if j = i then (if x j then (1:ℝ) else 0)
        else if j = j then (if x j then (1:ℝ) else 0) else 1) =
        (if x j then (1:ℝ) else 0) := by
      simp [hji]
    rw [h1]
    have hall1 : ∀ k ∈ (Finset.univ \ {i}) \ {j}, (if k = i then (if x k then (1:ℝ) else 0)
        else if k = j then (if x k then (1:ℝ) else 0) else 1) = 1 := by
      intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hk
      simp [hk.1, hk.2]
    rw [Finset.prod_congr rfl hall1]
    simp
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [← Fintype.prod_sum f]
  have hinner : ∀ k : Fin n,
      (∑ b : Bool, f k b) = (if k = i then 1 else if k = j then 1 else 2) := by
    intro k
    simp only [f]
    by_cases hki : k = i
    · simp [hki]
    · by_cases hkj : k = j
      · simp [hkj]
      · simp [hki, hkj]
  rw [Finset.prod_congr rfl (fun k _ => hinner k)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton i _ (by simp)]
  simp only [ite_true, one_mul]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton j _ (by intro h; exact absurd hjmem h)]
  have h2 : (if j = i then (1:ℝ) else if j = j then 1 else 2) = 1 := by simp [hji]
  rw [h2, one_mul]
  have hall2 : ∀ k ∈ (Finset.univ \ {i}) \ {j},
      (if k = i then (1:ℝ) else if k = j then 1 else 2) = 2 := by
    intro k hk
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at hk
    simp [hk.1, hk.2]
  rw [Finset.prod_congr rfl hall2]
  rw [Finset.prod_const]
  have hcard : ((Finset.univ \ {i}) \ {j}).card = n - 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase]
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem]
      · rw [Finset.card_univ, Fintype.card_fin]
        omega
      · simp
    · simp [hji]
  rw [hcard]

private lemma cut_indicator_eq {n : ℕ} (x : Fin n → Bool) (a b : Fin n) :
    (if x a ≠ x b then (1:ℝ) else 0)
      = (if x a then (1:ℝ) else 0) + (if x b then (1:ℝ) else 0)
        - 2 * ((if x a then (1:ℝ) else 0) * (if x b then (1:ℝ) else 0)) := by
  cases ha : x a <;> cases hb : x b
  all_goals simp_all
  all_goals norm_num

private lemma sum_cut_indicator {n : ℕ} (hn : 0 < n) (hn2 : 2 ≤ n) (a b : Fin n)
    (hab : a ≠ b) :
    (∑ x : Fin n → Bool, (if x a ≠ x b then (1:ℝ) else 0)) = 2 ^ (n - 1) := by
  have hrewrite : ∀ x : Fin n → Bool, (if x a ≠ x b then (1:ℝ) else 0)
      = (if x a then (1:ℝ) else 0) + (if x b then (1:ℝ) else 0)
        - 2 * ((if x a then (1:ℝ) else 0) * (if x b then (1:ℝ) else 0)) :=
    fun x => cut_indicator_eq x a b
  rw [Finset.sum_congr rfl (fun x _ => hrewrite x)]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib]
  rw [sum_single_indicator hn a, sum_single_indicator hn b]
  have hmul : (∑ x : Fin n → Bool, 2 * ((if x a then (1:ℝ) else 0) * (if x b then (1:ℝ) else 0)))
      = 2 * (∑ x : Fin n → Bool, (if x a then (1:ℝ) else 0) * (if x b then (1:ℝ) else 0)) := by
    rw [Finset.mul_sum]
  rw [hmul, sum_pair_indicator a b hab hn2]
  have hpow : (2:ℝ) * 2 ^ (n - 2) = 2 ^ (n - 1) := by
    have h1 : n - 2 + 1 = n - 1 := by omega
    conv_rhs => rw [← h1]
    rw [pow_succ, mul_comm]
  linarith

private lemma cutCount_eq_sum {n : ℕ} (E : EdgeSet n) (x : Fin n → Bool) :
    cutCount E x = ∑ e ∈ E.edges, (if x e.1 ≠ x e.2 then (1:ℝ) else 0) := by
  unfold cutCount
  rw [Finset.card_filter]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with h
  · simp
  · simp

private lemma flip_edge_indicator {n : ℕ} (x : Fin n → Bool) (e : Fin n × Fin n)
    (hne : e.1 ≠ e.2) (v : Fin n) :
    (if (Function.update x v (!x v)) e.1 ≠ (Function.update x v (!x v)) e.2 then (1:ℝ) else 0)
      = (if v = e.1 ∨ v = e.2 then 1 - (if x e.1 ≠ x e.2 then (1:ℝ) else 0)
          else (if x e.1 ≠ x e.2 then (1:ℝ) else 0)) := by
  by_cases hv1 : v = e.1
  · by_cases hv2 : v = e.2
    · exfalso
      exact hne (hv1.symm.trans hv2)
    · subst hv1
      simp only [hv2, true_or, ite_true]
      have h1 : (Function.update x e.1 (!x e.1)) e.1 = (!x e.1) :=
        Function.update_self e.1 (!x e.1) x
      have h2 : (Function.update x e.1 (!x e.1)) e.2 = x e.2 :=
        Function.update_of_ne (fun h => hv2 h.symm) _ _
      rw [h1, h2]
      cases ha : x e.1 <;> cases hb : x e.2
      all_goals simp_all
  · by_cases hv2 : v = e.2
    · subst hv2
      simp only [hv1, or_true, ite_true]
      have h1 : (Function.update x e.2 (!x e.2)) e.1 = x e.1 :=
        Function.update_of_ne (fun h => hv1 h.symm) _ _
      have h2 : (Function.update x e.2 (!x e.2)) e.2 = (!x e.2) :=
        Function.update_self e.2 (!x e.2) x
      rw [h1, h2]
      cases ha : x e.1 <;> cases hb : x e.2
      all_goals simp_all
    · simp only [hv1, hv2, false_or, ite_false]
      have h1 : (Function.update x v (!x v)) e.1 = x e.1 :=
        Function.update_of_ne (fun h => hv1 h.symm) _ _
      have h2 : (Function.update x v (!x v)) e.2 = x e.2 :=
        Function.update_of_ne (fun h => hv2 h.symm) _ _
      rw [h1, h2]

private lemma sum_flip_indicator {n : ℕ} (x : Fin n → Bool) (e : Fin n × Fin n)
    (hne : e.1 ≠ e.2) :
    (∑ v : Fin n, (if (Function.update x v (!x v)) e.1 ≠ (Function.update x v (!x v)) e.2
        then (1:ℝ) else 0))
      = (n : ℝ) * (if x e.1 ≠ x e.2 then (1:ℝ) else 0)
        + 2 * (1 - 2 * (if x e.1 ≠ x e.2 then (1:ℝ) else 0)) := by
  set c : ℝ := (if x e.1 ≠ x e.2 then (1:ℝ) else 0) with hc
  set K : ℝ := 1 - 2 * c with hK
  have hdiff : ∀ v : Fin n,
      (if (Function.update x v (!x v)) e.1 ≠ (Function.update x v (!x v)) e.2 then (1:ℝ) else 0)
        = c + (if v = e.1 ∨ v = e.2 then K else 0) := by
    intro v
    rw [flip_edge_indicator x e hne v]
    by_cases hv : v = e.1 ∨ v = e.2
    · simp only [hv, ite_true]
      rw [hK]
      ring
    · simp only [hv, ite_false, add_zero]
      rw [hc]
  rw [Finset.sum_congr rfl (fun v _ => hdiff v)]
  rw [Finset.sum_add_distrib]
  have hsumc : (∑ _v : Fin n, c) = (n : ℝ) * c := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hsumc]
  have hsumK : (∑ v : Fin n, (if v = e.1 ∨ v = e.2 then K else 0)) = 2 * K := by
    let s : Finset (Fin n) := {e.1, e.2}
    have hcard : s.card = 2 := Finset.card_pair hne
    have hmem : ∀ v : Fin n, v ∈ s ↔ (v = e.1 ∨ v = e.2) := by
      intro v
      simp [s]
    have hsub : (∑ v : Fin n, (if v = e.1 ∨ v = e.2 then K else 0))
        = ∑ v ∈ s, (if v = e.1 ∨ v = e.2 then K else 0) := by
      apply (Finset.sum_subset (Finset.subset_univ s) _).symm
      intro v _ hvs
      have hnot : ¬ (v = e.1 ∨ v = e.2) := by
        intro hcon
        exact hvs ((hmem v).mpr hcon)
      simp [hnot]
    rw [hsub]
    have hall : ∀ v ∈ s, (if v = e.1 ∨ v = e.2 then K else 0) = K := by
      intro v hvs
      have hcon : v = e.1 ∨ v = e.2 := (hmem v).mp hvs
      simp [hcon]
    rw [Finset.sum_congr rfl hall]
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    norm_num
  rw [hsumK]

/-- Expected cut size of a uniform random assignment is half the
edges: the total over all assignments is `2 ^ (n - 1) * |E|`
(for `n ≥ 1`). -/
theorem sum_cutCount {n : ℕ} (hn : 0 < n) (E : EdgeSet n) :
    (∑ x : Fin n → Bool, cutCount E x) = 2 ^ (n - 1) * E.edges.card := by
  by_cases hn2 : 2 ≤ n
  · have hswap : (∑ x : Fin n → Bool, cutCount E x)
        = ∑ e ∈ E.edges, ∑ x : Fin n → Bool, (if x e.1 ≠ x e.2 then (1:ℝ) else 0) := by
      rw [Finset.sum_congr rfl (fun x _ => cutCount_eq_sum E x)]
      rw [Finset.sum_comm]
    rw [hswap]
    have hper : ∀ e ∈ E.edges,
        (∑ x : Fin n → Bool, (if x e.1 ≠ x e.2 then (1:ℝ) else 0)) = 2 ^ (n - 1) := by
      intro e he
      have hlt := E.lt_of_mem e he
      have hne : e.1 ≠ e.2 := ne_of_lt hlt
      exact sum_cut_indicator hn hn2 e.1 e.2 hne
    rw [Finset.sum_congr rfl hper]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [mul_comm]
  · have hn1 : n = 1 := by omega
    have hEmpty : E.edges = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro e he
      have hlt := E.lt_of_mem e he
      subst hn1
      have h1 : e.1 = 0 := Fin.eq_zero e.1
      have h2 : e.2 = 0 := Fin.eq_zero e.2
      rw [h1, h2] at hlt
      exact lt_irrefl 0 hlt
    simp [cutCount, hEmpty]

/-- Local-search optimality gives a `1 / 2`-approximation: if no
single-vertex flip increases the cut, then the cut has at least
half the edges. -/
theorem locally_optimal_cut_ge {n : ℕ} (E : EdgeSet n) (x : Fin n → Bool)
    (hlocal : ∀ v : Fin n, cutCount E x ≥
      cutCount E (Function.update x v (!x v))) :
    (E.edges.card : ℝ) ≤ 2 * cutCount E x := by
  have hswap : (∑ v : Fin n, cutCount E (Function.update x v (!x v)))
      = ∑ e ∈ E.edges, ∑ v : Fin n, (if (Function.update x v (!x v)) e.1 ≠
          (Function.update x v (!x v)) e.2 then (1:ℝ) else 0) := by
    rw [Finset.sum_congr rfl (fun v _ => cutCount_eq_sum E (Function.update x v (!x v)))]
    rw [Finset.sum_comm]
  have hper : ∀ e ∈ E.edges, (∑ v : Fin n, (if (Function.update x v (!x v)) e.1 ≠
      (Function.update x v (!x v)) e.2 then (1:ℝ) else 0))
      = (n : ℝ) * (if x e.1 ≠ x e.2 then (1:ℝ) else 0)
        + 2 * (1 - 2 * (if x e.1 ≠ x e.2 then (1:ℝ) else 0)) := by
    intro e he
    have hlt := E.lt_of_mem e he
    exact sum_flip_indicator x e (ne_of_lt hlt)
  have hexpand : (∑ e ∈ E.edges, ((n : ℝ) * (if x e.1 ≠ x e.2 then (1:ℝ) else 0)
      + 2 * (1 - 2 * (if x e.1 ≠ x e.2 then (1:ℝ) else 0))))
      = (n : ℝ) * cutCount E x + 2 * (E.edges.card : ℝ) - 4 * cutCount E x := by
    rw [Finset.sum_add_distrib]
    have h1 : (∑ e ∈ E.edges, (n : ℝ) * (if x e.1 ≠ x e.2 then (1:ℝ) else 0))
        = (n : ℝ) * cutCount E x := by
      rw [← Finset.mul_sum]
      rw [cutCount_eq_sum]
    rw [h1]
    have h2 : ∀ e ∈ E.edges, (2 : ℝ) * (1 - 2 * (if x e.1 ≠ x e.2 then (1:ℝ) else 0))
        = 2 - 4 * (if x e.1 ≠ x e.2 then (1:ℝ) else 0) := by
      intro e _
      ring
    rw [Finset.sum_congr rfl h2]
    rw [Finset.sum_sub_distrib]
    have h3 : (∑ _e ∈ E.edges, (2:ℝ)) = 2 * (E.edges.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    rw [h3]
    have h4 : (∑ e ∈ E.edges, (4:ℝ) * (if x e.1 ≠ x e.2 then (1:ℝ) else 0))
        = 4 * cutCount E x := by
      rw [← Finset.mul_sum]
      rw [cutCount_eq_sum]
    rw [h4]
    ring
  have hS : (∑ v : Fin n, cutCount E (Function.update x v (!x v)))
      = (n : ℝ) * cutCount E x + 2 * (E.edges.card : ℝ) - 4 * cutCount E x := by
    rw [hswap, Finset.sum_congr rfl hper, hexpand]
  have hlocal_sum : (∑ v : Fin n, cutCount E (Function.update x v (!x v)))
      ≤ (n : ℝ) * cutCount E x := by
    have hle : (∑ v : Fin n, cutCount E (Function.update x v (!x v)))
        ≤ ∑ _v : Fin n, cutCount E x := by
      apply Finset.sum_le_sum
      intro v _
      exact hlocal v
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at hle
    exact hle
  linarith

end Cslib.Algorithms.Lean.MaxCut
