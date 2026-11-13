/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# MAX-CUT: the random cut and local search

For a finite simple graph `G : SimpleGraph V`, an assignment `x : V → Bool` cuts the edge
`s(a, b)` when `x a ≠ x b` (`cutsEdge`), and `cutCount G x` counts the cut edges of
`G.edgeFinset`.

## Main results

* `sum_cutCount`: summed over all `2 ^ |V|` assignments, the cut size is `2 ^ (|V| - 1) * |E|`,
  so a uniformly random assignment cuts half the edges in expectation.
* `locally_optimal_cut_ge`: a locally optimal cut (no single-vertex flip increases it) cuts at
  least half the edges, so local search is a `1/2`-approximation.

## References

* J. Kleinberg and É. Tardos, *Algorithm Design*, Addison-Wesley, 2006, Section 12.4.
* M. Mitzenmacher and E. Upfal, *Probability and Computing*, Cambridge University Press, 2005,
  Chapter 6.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MaxCut

variable {V : Type*}

/-- Whether the assignment `x` cuts the edge `e`, that is, gives its endpoints different
values. -/
def cutsEdge (x : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun a b => decide (x a ≠ x b), fun a b => by simp only [ne_comm]⟩

@[simp]
theorem cutsEdge_mk (x : V → Bool) (a b : V) : cutsEdge x s(a, b) = decide (x a ≠ x b) := rfl

private lemma ite_cutsEdge_mk (x : V → Bool) (a b : V) :
    (if cutsEdge x s(a, b) then (1:ℝ) else 0) = if x a ≠ x b then 1 else 0 := by
  simp

private lemma cut_indicator_eq (x : V → Bool) (a b : V) :
    (if x a ≠ x b then (1:ℝ) else 0)
      = (if x a then (1:ℝ) else 0) + (if x b then (1:ℝ) else 0)
        - 2 * ((if x a then (1:ℝ) else 0) * (if x b then (1:ℝ) else 0)) := by
  cases ha : x a <;> cases hb : x b
  all_goals simp_all
  all_goals norm_num

variable [Fintype V]

/-- The number of edges of `G` cut by the assignment `x`. -/
def cutCount (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Bool) : ℕ :=
  (G.edgeFinset.filter fun e => cutsEdge x e).card

private lemma ne_of_mem_edgeFinset (G : SimpleGraph V) [DecidableRel G.Adj] {a b : V}
    (he : s(a, b) ∈ G.edgeFinset) : a ≠ b :=
  G.ne_of_adj ((SimpleGraph.mem_edgeSet G).1 (SimpleGraph.mem_edgeFinset.1 he))

private lemma cutCount_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Bool) :
    (cutCount G x : ℝ) = ∑ e ∈ G.edgeFinset, (if cutsEdge x e then (1:ℝ) else 0) := by
  unfold cutCount
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp

variable [DecidableEq V]

private lemma sum_single_indicator (i : V) :
    (∑ x : V → Bool, (if x i then (1:ℝ) else 0)) = 2 ^ (Fintype.card V - 1) := by
  let f : V → Bool → ℝ := fun j b => if j = i then (if b then 1 else 0) else 1
  have hterm : ∀ x : V → Bool, (if x i then (1:ℝ) else 0) = ∏ j, f j (x j) := by
    intro x
    simp only [f]
    rw [Finset.prod_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [← Fintype.prod_sum f]
  have hinner : ∀ j : V, (∑ b : Bool, f j b) = (if j = i then 1 else 2) := by
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
  have hcard : (Finset.univ \ {i}).card = Fintype.card V - 1 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem]
    · rw [Finset.card_univ]
    · simp
  rw [hcard]

private lemma sum_pair_indicator (i j : V) (hij : i ≠ j) :
    (∑ x : V → Bool, (if x i then (1:ℝ) else 0) * (if x j then (1:ℝ) else 0))
      = 2 ^ (Fintype.card V - 2) := by
  let f : V → Bool → ℝ := fun k b =>
    if k = i then (if b then 1 else 0) else if k = j then (if b then 1 else 0) else 1
  have hji : j ≠ i := fun h => hij h.symm
  have hjmem : j ∈ (Finset.univ : Finset V) \ {i} := by simp [hji]
  have hterm : ∀ x : V → Bool,
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
  have hinner : ∀ k : V,
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
  have hcard : ((Finset.univ \ {i}) \ {j}).card = Fintype.card V - 2 := by
    rw [Finset.sdiff_singleton_eq_erase, Finset.sdiff_singleton_eq_erase]
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem]
      · rw [Finset.card_univ]
        omega
      · simp
    · simp [hji]
  rw [hcard]

private lemma sum_cut_indicator (a b : V) (hab : a ≠ b) :
    (∑ x : V → Bool, (if x a ≠ x b then (1:ℝ) else 0)) = 2 ^ (Fintype.card V - 1) := by
  have hn2 : 2 ≤ Fintype.card V := Fintype.one_lt_card_iff.2 ⟨a, b, hab⟩
  have hrewrite : ∀ x : V → Bool, (if x a ≠ x b then (1:ℝ) else 0)
      = (if x a then (1:ℝ) else 0) + (if x b then (1:ℝ) else 0)
        - 2 * ((if x a then (1:ℝ) else 0) * (if x b then (1:ℝ) else 0)) :=
    fun x => cut_indicator_eq x a b
  rw [Finset.sum_congr rfl (fun x _ => hrewrite x)]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib]
  rw [sum_single_indicator a, sum_single_indicator b]
  have hmul : (∑ x : V → Bool, 2 * ((if x a then (1:ℝ) else 0) * (if x b then (1:ℝ) else 0)))
      = 2 * (∑ x : V → Bool, (if x a then (1:ℝ) else 0) * (if x b then (1:ℝ) else 0)) := by
    rw [Finset.mul_sum]
  rw [hmul, sum_pair_indicator a b hab]
  have hpow : (2:ℝ) * 2 ^ (Fintype.card V - 2) = 2 ^ (Fintype.card V - 1) := by
    have h1 : Fintype.card V - 2 + 1 = Fintype.card V - 1 := by omega
    conv_rhs => rw [← h1]
    rw [pow_succ, mul_comm]
  linarith

omit [Fintype V] in
private lemma flip_edge_indicator (x : V → Bool) (e : V × V)
    (hne : e.1 ≠ e.2) (v : V) :
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

private lemma sum_flip_indicator (x : V → Bool) (e : V × V)
    (hne : e.1 ≠ e.2) :
    (∑ v : V, (if (Function.update x v (!x v)) e.1 ≠ (Function.update x v (!x v)) e.2
        then (1:ℝ) else 0))
      = (Fintype.card V : ℝ) * (if x e.1 ≠ x e.2 then (1:ℝ) else 0)
        + 2 * (1 - 2 * (if x e.1 ≠ x e.2 then (1:ℝ) else 0)) := by
  set c : ℝ := (if x e.1 ≠ x e.2 then (1:ℝ) else 0) with hc
  set K : ℝ := 1 - 2 * c with hK
  have hdiff : ∀ v : V,
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
  have hsumc : (∑ _v : V, c) = (Fintype.card V : ℝ) * c := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ]
  rw [hsumc]
  have hsumK : (∑ v : V, (if v = e.1 ∨ v = e.2 then K else 0)) = 2 * K := by
    let s : Finset V := {e.1, e.2}
    have hcard : s.card = 2 := Finset.card_pair hne
    have hmem : ∀ v : V, v ∈ s ↔ (v = e.1 ∨ v = e.2) := by
      intro v
      simp [s]
    have hsub : (∑ v : V, (if v = e.1 ∨ v = e.2 then K else 0))
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

/-- Each edge is cut by exactly half of the assignments. -/
private lemma sum_cutsEdge (G : SimpleGraph V) [DecidableRel G.Adj] {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    (∑ x : V → Bool, (if cutsEdge x e then (1:ℝ) else 0)) = 2 ^ (Fintype.card V - 1) := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [ite_cutsEdge_mk]
    exact sum_cut_indicator a b (ne_of_mem_edgeFinset G he)

private lemma sum_flip_cutsEdge (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Bool)
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (∑ v : V, (if cutsEdge (Function.update x v (!x v)) e then (1:ℝ) else 0))
      = (Fintype.card V : ℝ) * (if cutsEdge x e then (1:ℝ) else 0)
        + 2 * (1 - 2 * (if cutsEdge x e then (1:ℝ) else 0)) := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [ite_cutsEdge_mk]
    exact sum_flip_indicator x (a, b) (ne_of_mem_edgeFinset G he)

/-- Expected cut size of a uniform random assignment is half the
edges: the total over all assignments is `2 ^ (|V| - 1) * |E|`. -/
theorem sum_cutCount (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∑ x : V → Bool, cutCount G x = 2 ^ (Fintype.card V - 1) * G.edgeFinset.card := by
  have h : (∑ x : V → Bool, (cutCount G x : ℝ)) =
      2 ^ (Fintype.card V - 1) * (G.edgeFinset.card : ℝ) := by
    rw [Finset.sum_congr rfl (fun x _ => cutCount_eq_sum G x), Finset.sum_comm,
      Finset.sum_congr rfl (fun e he => sum_cutsEdge G he), Finset.sum_const, nsmul_eq_mul,
      mul_comm]
  exact_mod_cast h

/-- Local-search optimality gives a `1 / 2`-approximation: if no
single-vertex flip increases the cut, then the cut has at least
half the edges. -/
theorem locally_optimal_cut_ge (G : SimpleGraph V) [DecidableRel G.Adj] (x : V → Bool)
    (hlocal : ∀ v : V, cutCount G x ≥ cutCount G (Function.update x v (!x v))) :
    G.edgeFinset.card ≤ 2 * cutCount G x := by
  have hswap : (∑ v : V, (cutCount G (Function.update x v (!x v)) : ℝ))
      = ∑ e ∈ G.edgeFinset, ∑ v : V,
          (if cutsEdge (Function.update x v (!x v)) e then (1:ℝ) else 0) := by
    rw [Finset.sum_congr rfl (fun v _ => cutCount_eq_sum G (Function.update x v (!x v)))]
    rw [Finset.sum_comm]
  have hexpand : (∑ e ∈ G.edgeFinset, ((Fintype.card V : ℝ) * (if cutsEdge x e then (1:ℝ) else 0)
      + 2 * (1 - 2 * (if cutsEdge x e then (1:ℝ) else 0))))
      = (Fintype.card V : ℝ) * cutCount G x + 2 * (G.edgeFinset.card : ℝ)
        - 4 * cutCount G x := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← cutCount_eq_sum]
    have h2 : ∀ e ∈ G.edgeFinset, (2 : ℝ) * (1 - 2 * (if cutsEdge x e then (1:ℝ) else 0))
        = 2 - 4 * (if cutsEdge x e then (1:ℝ) else 0) := by
      intro e _
      ring
    rw [Finset.sum_congr rfl h2, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum, ← cutCount_eq_sum]
    ring
  have hS : (∑ v : V, (cutCount G (Function.update x v (!x v)) : ℝ))
      = (Fintype.card V : ℝ) * cutCount G x + 2 * (G.edgeFinset.card : ℝ)
        - 4 * cutCount G x := by
    rw [hswap, Finset.sum_congr rfl (fun e he => sum_flip_cutsEdge G x he), hexpand]
  have hlocal_sum : (∑ v : V, (cutCount G (Function.update x v (!x v)) : ℝ))
      ≤ (Fintype.card V : ℝ) * cutCount G x := by
    have hle : (∑ v : V, (cutCount G (Function.update x v (!x v)) : ℝ))
        ≤ ∑ _v : V, (cutCount G x : ℝ) :=
      Finset.sum_le_sum fun v _ => by exact_mod_cast hlocal v
    rwa [Finset.sum_const, nsmul_eq_mul, Finset.card_univ] at hle
  have hreal : (G.edgeFinset.card : ℝ) ≤ 2 * cutCount G x := by linarith
  exact_mod_cast hreal

end Cslib.Algorithms.Lean.MaxCut
