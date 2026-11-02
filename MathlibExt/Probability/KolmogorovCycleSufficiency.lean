/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.KolmogorovCycleNecessity
public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Field

import Mathlib.Tactic.Ring

/-!
# Kolmogorov's cycle theorem, sufficiency half

For a finite irreducible Markov chain, Kolmogorov's cycle condition
implies the existence of a reversible measure: if every positive
transition has a positive reverse transition, and the product of
transition probabilities around every loop equals the product along the
reversed loop, then there is a distribution satisfying the detailed
balance equations (hence stationary).

## Source

This formalizes the sufficiency half (`<-` direction) of
"Kolmogorov's cycle theorem" / `kolmogorov_cycle_theorem` (Lecture 32,
Cycle theorem) of `v1/Atlas/TheoryOfProbability/targets.yaml`:
"Suppose `p` is irreducible. Then there exists a reversible measure if
and only if (1) `p(x, y) > 0` implies `p(y, x) > 0`, and (2) for any loop
`x_0, x_1, ..., x_n` with `prod P(x_i, x_{i-1}) > 0`, we have
`prod (P(x_{i-1}, x_i) / P(x_i, x_{i-1})) = 1`."
Its v1 formalization is `v1/Atlas/TheoryOfProbability/code/KolmogorovCycle.lean`
(`StochasticMatrix.kolmogorov_cycle_theorem`), proved in full there.
The necessity half is a separate import
(`MathlibExt.Probability.KolmogorovCycleNecessity`, batch 17).

The proof follows v1's cycle-weight construction: for a fixed reference
state `i_0`, the weight of a state `j` is the product of the ratios
`P(x, y) / P(y, x)` along any positive-probability path from `i_0` to
`j`. The cycle condition makes this weight independent of the chosen
path, the weights satisfy detailed balance, and normalizing them gives
the reversible distribution.

## Main results

* `StochasticMatrix.kolmogorov_cycle_sufficiency`: the cycle condition
  implies reversibility for an irreducible finite chain.

## Shared API

The matrix, distribution, irreducibility, detailed balance, stationarity,
and cycle condition are the canonical declarations imported from
`KolmogorovCycleNecessity`. The new path and weight helpers and sufficiency
theorem use those declarations directly. The positive-sum argument for
path extraction does not require another matrix-power nonnegativity lemma.
-/

@[expose] public section

open Finset BigOperators

namespace StochasticMatrix

variable {M : ℕ}

/-- **Forward path product.** For a stochastic matrix $P$ and a path of states
$x_0, x_1, \dots, x_k$, the path product is the real number
$\prod_{i=0}^{k-1} P(x_i, x_{i+1})$, the product of the forward transition probabilities along
the path. For the empty path and for a path consisting of a single state it is $1$. -/
def listPathProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: rest => P.prob a b * listPathProduct P (b :: rest)

/-- **Path products are nonnegative.** Let $P$ be a stochastic matrix on the states
$\{0, \dots, M\}$. For every path (finite list of states), the product of the forward transition
probabilities $P(x, y)$ over consecutive states $x, y$ along the path is nonnegative. -/
lemma listPathProduct_nonneg (P : StochasticMatrix M) (path : List (Fin (M + 1))) :
    0 ≤ listPathProduct P path := by
  induction path with
  | nil => exact zero_le_one
  | cons a tail ih =>
    cases tail with
    | nil => exact zero_le_one
    | cons b rest =>
      show 0 ≤ P.prob a b * listPathProduct P (b :: rest)
      exact mul_nonneg (P.nonneg a b) ih
/-- **Ratio product along a path.** For a stochastic matrix $P$ and a path of states
$x_0, x_1, \dots, x_k$, the ratio product is the real number
$\prod_{i=0}^{k-1} \frac{P(x_i, x_{i+1})}{P(x_{i+1}, x_i)}$, where a quotient with
denominator $0$ is taken to be $0$. For the empty path and for a path consisting of a single
state it is $1$.

This is the quantity that defines the "cycle weight" used to construct a reversible measure
from Kolmogorov's cycle condition. -/
noncomputable def listRatioProduct (P : StochasticMatrix M) : List (Fin (M + 1)) → ℝ
  | [] => 1
  | [_] => 1
  | a :: b :: rest => (P.prob a b / P.prob b a) * listRatioProduct P (b :: rest)

/-- **The ratio product is nonnegative.** For a stochastic matrix $P$, the ratio product along
every path of states is nonnegative. -/
lemma listRatioProduct_nonneg (P : StochasticMatrix M) (path : List (Fin (M + 1))) :
    0 ≤ listRatioProduct P path := by
  induction path with
  | nil => exact zero_le_one
  | cons a tail ih =>
    cases tail with
    | nil => exact zero_le_one
    | cons b rest =>
      show 0 ≤ (P.prob a b / P.prob b a) * listRatioProduct P (b :: rest)
      exact mul_nonneg (div_nonneg (P.nonneg a b) (P.nonneg b a)) ih
/-- **Positive paths have positive ratio product.** Let $P$ be a stochastic matrix such that
$P(x, y) > 0$ implies $P(y, x) > 0$ for all states $x$ and $y$. If the forward path product
along a path of states is positive, then the ratio product along that path is positive. -/
lemma listRatioProduct_pos_of_listPathProduct_pos (P : StochasticMatrix M)
    (hsymm : ∀ x y : Fin (M + 1), P.prob x y > 0 → P.prob y x > 0)
    (path : List (Fin (M + 1))) (h : 0 < listPathProduct P path) :
    0 < listRatioProduct P path := by
  induction path with
  | nil => exact zero_lt_one
  | cons a tail ih =>
    cases tail with
    | nil => exact zero_lt_one
    | cons b rest =>
      show 0 < (P.prob a b / P.prob b a) * listRatioProduct P (b :: rest)
      have hP : 0 < P.prob a b * listPathProduct P (b :: rest) := h
      have hPab : 0 < P.prob a b := pos_of_mul_pos_left hP (listPathProduct_nonneg P _)
      have hPba : 0 < P.prob b a := hsymm a b hPab
      have h_tail : 0 < listPathProduct P (b :: rest) :=
        pos_of_mul_pos_right hP (P.nonneg a b)
      exact mul_pos (div_pos hPab hPba) (ih h_tail)
/-- **Paths from positive matrix powers.** Let $P$ be a stochastic matrix on the states
$\{0, \dots, M\}$. If $n > 0$ and the $(i, j)$ entry of the $n$-th matrix power $P^n$ is positive,
then there is a path from $i$ to $j$ (a finite list of states starting at $i$ and ending at $j$)
along which the product of the transition probabilities $P(x, y)$ over consecutive states $x, y$
is positive. -/
lemma exists_path_of_matPow_pos (P : StochasticMatrix M) :
    ∀ (n : ℕ) (i j : Fin (M + 1)), 0 < n → 0 < P.matPow n i j →
    ∃ path : List (Fin (M + 1)),
      path.head? = some i ∧ path.getLast? = some j ∧ 0 < listPathProduct P path := by
  intro n
  induction n with
  | zero => intro i j hn; omega
  | succ k ih =>
    intro i j _ hpos
    simp only [matPow] at hpos
    have hsum_pos : (∑ m : Fin (M + 1), (0 : ℝ)) <
        ∑ m, P.prob i m * P.matPow k m j := by simpa using hpos
    obtain ⟨m, _, hm⟩ := Finset.exists_lt_of_sum_lt hsum_pos
    have hPkj : 0 < P.matPow k m j := pos_of_mul_pos_right hm (P.nonneg i m)
    have hPim : 0 < P.prob i m := pos_of_mul_pos_left hm hPkj.le
    by_cases hk : k = 0
    · subst hk
      simp only [matPow] at hPkj
      split_ifs at hPkj with heq
      · subst heq
        refine ⟨[i, m], by simp, by simp, ?_⟩
        simpa [listPathProduct] using hPim
      · linarith
    · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
      obtain ⟨path, hhead, hlast, hprod⟩ := ih m j hk_pos hPkj
      cases path with
      | nil => simp at hhead
      | cons a tail =>
        simp at hhead
        subst hhead
        refine ⟨i :: a :: tail, by simp, ?_, ?_⟩
        · simp only [List.getLast?]
          simp only [List.getLast?] at hlast
          exact hlast
        · simp only [listPathProduct]
          exact mul_pos (hPim) hprod

/-- **Irreducible chains have positive paths.** Let $P$ be an irreducible stochastic matrix on the
states $\{0, \dots, M\}$. For any two states $i, j$ there is a path from $i$ to $j$ (a finite list
of states starting at $i$ and ending at $j$) along which the product of the transition
probabilities $P(x, y)$ over consecutive states $x, y$ is strictly positive. -/
theorem IsIrreducible.exists_path {P : StochasticMatrix M} (hirr : P.IsIrreducible)
    (i j : Fin (M + 1)) :
    ∃ path : List (Fin (M + 1)),
      path.head? = some i ∧ path.getLast? = some j ∧ 0 < listPathProduct P path := by
  obtain ⟨n, hn_pos, hn⟩ := hirr i j
  exact exists_path_of_matPow_pos P n i j hn_pos hn

/-- **First step of the ratio product.** Let $P$ be a stochastic matrix, $n$ a natural number
and $c_0, c_1, \dots, c_{n+1}$ states. Then the ratio product along $c_0, c_1, \dots, c_{n+1}$
equals $\frac{P(c_0, c_1)}{P(c_1, c_0)}$ times the ratio product along $c_1, \dots, c_{n+1}$,
where a quotient with denominator $0$ is taken to be $0$. -/
lemma listRatioProduct_cons_ofFn (P : StochasticMatrix M) (n : ℕ)
    (c : Fin (n + 2) → Fin (M + 1)) :
    listRatioProduct P (c 0 :: List.ofFn (fun i : Fin (n + 1) => c i.succ)) =
    (P.prob (c 0) (c 1) / P.prob (c 1) (c 0)) *
    listRatioProduct P (List.ofFn (fun i : Fin (n + 1) => c i.succ)) := by
  rw [show List.ofFn (fun i : Fin (n + 1) => c i.succ) =
         c (Fin.succ 0) :: List.ofFn (fun i : Fin n => c i.succ.succ) from List.ofFn_succ,
      show (1 : Fin (n + 2)) = Fin.succ (0 : Fin (n + 1)) from rfl]; rfl

/-- **The ratio product as a finite product.** Let $P$ be a stochastic matrix, $n$ a natural
number and $c_0, c_1, \dots, c_n$ states. Then the ratio product along $c_0, c_1, \dots, c_n$
equals $\prod_{i=0}^{n-1} \frac{P(c_i, c_{i+1})}{P(c_{i+1}, c_i)}$, where a quotient with
denominator $0$ is taken to be $0$. -/
lemma listRatioProduct_ofFn (P : StochasticMatrix M) :
    ∀ (n : ℕ) (c : Fin (n + 1) → Fin (M + 1)),
    listRatioProduct P (List.ofFn c) =
    ∏ i : Fin n, (P.prob (c i.castSucc) (c i.succ) /
                   P.prob (c i.succ) (c i.castSucc) : ℝ) := by
  intro n; induction n with
  | zero => intro c; simp [List.ofFn_succ, List.ofFn_zero, listRatioProduct]
  | succ k ih =>
    intro c
    rw [show List.ofFn c = c 0 :: List.ofFn (fun i : Fin (k + 1) => c i.succ) from List.ofFn_succ,
        listRatioProduct_cons_ofFn, ih (fun i => c i.succ), Fin.prod_univ_succ]; rfl

/-- **The ratio product around a loop is one.** Let $P$ be a stochastic matrix satisfying
Kolmogorov's cycle condition, and let $x_0, x_1, \dots, x_n$ be a path of states with
$n \ge 1$ and $x_0 = x_n$ such that $P(x_{i+1}, x_i) > 0$ for every $i < n$. Then the ratio
product along $x_0, x_1, \dots, x_n$ equals $1$. -/
lemma listRatioProduct_cycle_eq_one (P : StochasticMatrix M)
    (hcycle : P.KolmogorovCycleCondition)
    (path : List (Fin (M + 1))) (hlen : 2 ≤ path.length) (hne : path ≠ [])
    (hloop : path.head hne = path.getLast hne)
    (hpos : ∀ i : Fin (path.length - 1),
      0 < P.prob (path.get ⟨i + 1, by omega⟩) (path.get ⟨i, by omega⟩)) :
    listRatioProduct P path = 1 := by
  set n := path.length - 1
  have hlen_eq : path.length = n + 1 := by omega
  set c : Fin (n + 1) → Fin (M + 1) := fun i => path.get (i.cast hlen_eq.symm)
  have path_eq : path = List.ofFn c := by
    conv_lhs => rw [← List.ofFn_get (l := path)]
    rw [List.ofFn_congr hlen_eq]
  have hc0 : c 0 = path.head hne := by
    simp only [c]; cases path with | nil => contradiction | cons a t => rfl
  have hclast : c (Fin.last n) = path.getLast hne := by
    simp only [c]
    have hcast : (Fin.last n).cast hlen_eq.symm = ⟨path.length - 1, by omega⟩ := by
      ext; simp [Fin.last, Fin.cast]; omega
    rw [hcast]; exact List.get_length_sub_one _
  have hloop_fin : c 0 = c (Fin.last n) := by rw [hc0, hclast, hloop]
  have hbwd_pos : 0 < ∏ i : Fin n, P.prob (c i.succ) (c i.castSucc) := by
    apply Finset.prod_pos; intro i _
    have hi := i.isLt
    have e1 : c i.succ = path.get ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext; simp only [c, Fin.succ, Fin.cast]
    have e2 : c i.castSucc = path.get ⟨i.val, by omega⟩ := by
      apply Fin.ext; simp only [c, Fin.castSucc, Fin.cast, Fin.castAdd, Fin.castLE]
    rw [e1, e2]
    exact hpos ⟨i.val, by omega⟩
  have hfwd_eq := hcycle.cycle_prod n c hloop_fin hbwd_pos
  rw [path_eq, listRatioProduct_ofFn, Finset.prod_div_distrib, hfwd_eq]
  exact div_self (ne_of_gt hbwd_pos)
/-- **Cycle weight.** Let $P$ be an irreducible stochastic matrix on the states
$\{0, \dots, M\}$ and fix a reference state $i_0$. The cycle weight of a state $j$ relative to
$i_0$ is the product of the ratios $P(x, y) / P(y, x)$ over consecutive states $x, y$ along a
path (a finite list of states) from $i_0$ to $j$ whose product of transition probabilities
$P(x, y)$ over consecutive states is positive, where a ratio with $P(y, x) = 0$ counts as $0$;
such a path exists by irreducibility, and one is fixed by choice.

For chains satisfying Kolmogorov's cycle condition this value does not depend on the chosen path,
and the weights give a reversible measure. -/
noncomputable def cycleWeight (P : StochasticMatrix M) (hirr : P.IsIrreducible)
    (i₀ : Fin (M + 1)) (j : Fin (M + 1)) : ℝ :=
  listRatioProduct P (Classical.choose (hirr.exists_path i₀ j))
/-- **Ratio product of joined paths.** Let $P$ be a stochastic matrix and let $x_0, \dots, x_k$
and $y_0, \dots, y_l$ be paths of states with $x_k = y_0$. Then the ratio product along the
joined path $x_0, \dots, x_k, y_1, \dots, y_l$ equals the ratio product along
$x_0, \dots, x_k$ times the ratio product along $y_0, \dots, y_l$. -/
lemma listRatioProduct_append (P : StochasticMatrix M) :
    ∀ (l1 l2 : List (Fin (M + 1))) (hne1 : l1 ≠ []) (hne2 : l2 ≠ []),
    l1.getLast hne1 = l2.head hne2 →
    listRatioProduct P (l1 ++ l2.tail) =
      listRatioProduct P l1 * listRatioProduct P l2 := by
  intro l1
  induction l1 with
  | nil => intro _ hne1; exact absurd rfl hne1
  | cons a t ih =>
    intro l2 _ hne2 hjoin
    cases t with
    | nil =>
      simp only [listRatioProduct, List.singleton_append, one_mul,
                 List.getLast_singleton] at *
      cases l2 with
      | nil => exact absurd rfl hne2
      | cons b rest =>
        simp only [List.head] at hjoin
        subst hjoin
        simp only [List.tail]
    | cons b rest =>
      have htne : (b :: rest) ≠ [] := List.cons_ne_nil _ _
      have hjoin' : (b :: rest).getLast htne = l2.head hne2 := by
        simp only [List.getLast_cons htne] at hjoin; exact hjoin
      have ih_eq := ih l2 htne hne2 hjoin'
      show (P.prob a b / P.prob b a) *
            listRatioProduct P ((b :: rest) ++ l2.tail) =
          (P.prob a b / P.prob b a) *
            listRatioProduct P (b :: rest) * listRatioProduct P l2
      rw [ih_eq, mul_assoc]

/-- **Positive path products have positive steps.** Let $P$ be a stochastic matrix on the states
$\{0, \dots, M\}$, and let $l$ be a path (a finite list of states) whose $i$-th state, counting
from $0$, is $l_i$. If the product of the transition probabilities $P(x, y)$ over consecutive
states $x, y$ along $l$ is positive, then $P(l_i, l_{i+1}) > 0$ for every $i$ such that $i + 1$
is less than the length of $l$. -/
lemma listPathProduct_pos_implies_transitions (P : StochasticMatrix M)
    (l : List (Fin (M + 1))) (hpos : 0 < listPathProduct P l)
    (i : ℕ) (hi : i + 1 < l.length) :
    0 < P.prob (l.get ⟨i, by omega⟩) (l.get ⟨i + 1, hi⟩) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases t with
    | nil => simp at hi
    | cons b rest =>
      simp only [listPathProduct] at hpos
      have hPab : (0 : ℝ) < P.prob a b :=
        pos_of_mul_pos_left hpos (listPathProduct_nonneg P (b :: rest))
      have h_tail : 0 < listPathProduct P (b :: rest) :=
        pos_of_mul_pos_right hpos (P.nonneg a b)
      cases i with
      | zero => exact hPab
      | succ i => exact ih h_tail i (by simp only [List.length] at hi ⊢; omega)

/-- **Joining positive paths.** Let $P$ be a stochastic matrix on the states $\{0, \dots, M\}$,
and let $l_1, l_2$ be nonempty paths (finite lists of states) such that the last state of $l_1$
is the first state of $l_2$. If the products of the transition probabilities $P(x, y)$ over
consecutive states $x, y$ along $l_1$ and along $l_2$ are both positive, then so is the product
along the path that follows $l_1$ and then $l_2$ with its first state removed. -/
lemma listPathProduct_append_pos (P : StochasticMatrix M)
    (l1 l2 : List (Fin (M + 1))) (hne1 : l1 ≠ []) (hne2 : l2 ≠ [])
    (hjoin : l1.getLast hne1 = l2.head hne2)
    (h1 : 0 < listPathProduct P l1) (h2 : 0 < listPathProduct P l2) :
    0 < listPathProduct P (l1 ++ l2.tail) := by
  induction l1 with
  | nil => exact absurd rfl hne1
  | cons a t ih =>
    match t with
    | [] =>
      simp only [List.singleton_append, List.getLast_singleton] at hjoin ⊢
      cases l2 with
      | nil => exact absurd rfl hne2
      | cons b rest =>
        simp only [List.head] at hjoin
        subst hjoin
        simp only [List.tail]
        cases rest with
        | nil => simp [listPathProduct]
        | cons c rest' => simp only [listPathProduct] at h2 ⊢; exact h2
    | b :: rest =>
      have htne : (b :: rest) ≠ [] := List.cons_ne_nil _ _
      have hjoin' : (b :: rest).getLast htne = l2.head hne2 := by
        simp only [List.getLast_cons htne] at hjoin; exact hjoin
      simp only [listPathProduct] at h1 ⊢
      have hPab : (0 : ℝ) < P.prob a b :=
        pos_of_mul_pos_left h1 (listPathProduct_nonneg P (b :: rest))
      have h_tail : 0 < listPathProduct P (b :: rest) :=
        pos_of_mul_pos_right h1 (P.nonneg a b)
      exact mul_pos hPab (ih htne hjoin' h_tail)

/-- **Path independence of cycle weight.** Let $P$ be an irreducible stochastic matrix on the
states $\{0, \dots, M\}$ satisfying Kolmogorov's cycle condition, and let $i_0, j$ be states. If
two paths (finite lists of states) both start at $i_0$, end at $j$, and have positive product of
the transition probabilities $P(x, y)$ over consecutive states $x, y$, then the products of the
ratios $P(x, y) / P(y, x)$ over consecutive states $x, y$ along the two paths are equal.

This is the key step that makes the cycle weight well-defined and ultimately produces a
reversible measure. -/
theorem cycleWeight_path_independent (P : StochasticMatrix M)
    (hcycle : P.KolmogorovCycleCondition) (hirr : P.IsIrreducible) (i₀ j : Fin (M + 1))
    (path1 path2 : List (Fin (M + 1)))
    (h1 : path1.head? = some i₀) (h1' : path1.getLast? = some j)
    (h2 : path2.head? = some i₀) (h2' : path2.getLast? = some j)
    (hp1 : 0 < listPathProduct P path1) (hp2 : 0 < listPathProduct P path2) :
    listRatioProduct P path1 = listRatioProduct P path2 := by

  obtain ⟨p3, hp3_head, hp3_last, hp3_pos⟩ := hirr.exists_path j i₀

  have hne3 : p3 ≠ [] := by intro h; simp [h] at hp3_head

  have hlast3 : p3.getLast hne3 = i₀ := by
    have := List.getLast?_eq_some_getLast hne3; rw [this] at hp3_last; exact Option.some_injective _ hp3_last
  have hhead3 : p3.head hne3 = j := by
    have := List.head?_eq_some_head hne3; rw [this] at hp3_head; exact Option.some_injective _ hp3_head

  have hp3_rpos := listRatioProduct_pos_of_listPathProduct_pos P hcycle.symm_support p3 hp3_pos

  have hji_of_ptail_nil : p3.tail = [] → j = i₀ := by
    intro htnil
    cases p3 with | nil => contradiction | cons x t =>
      simp only [List.tail] at htnil; subst htnil

      simp [List.getLast_singleton] at hlast3
      simp at hhead3
      rw [← hhead3, hlast3]

  suffices h_suffices : ∀ (p : List (Fin (M + 1))),
      p.head? = some i₀ → p.getLast? = some j → 0 < listPathProduct P p →
      listRatioProduct P p * listRatioProduct P p3 = 1 by
    have h1eq := h_suffices path1 h1 h1' hp1
    have h2eq := h_suffices path2 h2 h2' hp2
    exact mul_right_cancel₀ (ne_of_gt hp3_rpos) (h1eq.trans h2eq.symm)
  intro p hp_head hp_last hp_pos
  have hne_p : p ≠ [] := by intro h; simp [h] at hp_head
  have hlast_p : p.getLast hne_p = j := by
    have := List.getLast?_eq_some_getLast hne_p; rw [this] at hp_last
    exact Option.some_injective _ hp_last
  have hhead_p : p.head hne_p = i₀ := by
    have := List.head?_eq_some_head hne_p; rw [this] at hp_head
    exact Option.some_injective _ hp_head
  have hjoin_p : p.getLast hne_p = p3.head hne3 := by rw [hlast_p, hhead3]
  have happ_p := listRatioProduct_append P p p3 hne_p hne3 hjoin_p

  set cp := p ++ p3.tail
  have hne_cp : cp ≠ [] := List.append_ne_nil_of_left_ne_nil hne_p _
  have hcp_pos := listPathProduct_append_pos P p p3 hne_p hne3 hjoin_p hp_pos hp3_pos

  by_cases hcp_len : 2 ≤ cp.length
  ·
    have hcp_head : cp.head hne_cp = i₀ := by
      show (p ++ p3.tail).head _ = i₀
      rw [List.head_append_of_ne_nil hne_p]; exact hhead_p
    have hcp_last : cp.getLast hne_cp = i₀ := by
      show (p ++ p3.tail).getLast _ = i₀
      by_cases htail_ne : p3.tail = []
      · simp only [htail_ne, List.append_nil]
        exact hlast_p.trans (hji_of_ptail_nil htail_ne)
      · rw [List.getLast_append_of_ne_nil _ htail_ne, List.getLast_tail htail_ne, hlast3]
    have hcp_loop : cp.head hne_cp = cp.getLast hne_cp := by rw [hcp_head, hcp_last]
    have hcp_bwd : ∀ i : Fin (cp.length - 1),
        0 < P.prob (cp.get ⟨i + 1, by omega⟩) (cp.get ⟨i, by omega⟩) := by
      intro ⟨i, hi⟩
      exact hcycle.symm_support _ _
        (listPathProduct_pos_implies_transitions P cp hcp_pos i (by omega))
    have heq_cp : listRatioProduct P cp = 1 :=
      listRatioProduct_cycle_eq_one P hcycle cp hcp_len hne_cp hcp_loop hcp_bwd
    rw [happ_p] at heq_cp; exact heq_cp
  ·
    push Not at hcp_len
    have hcp_len1 : cp.length = 1 := by
      have : 1 ≤ cp.length := List.length_pos_of_ne_nil hne_cp; omega

    have hptail : p3.tail = [] := by
      have hlen : p.length + p3.tail.length = 1 := by
        have : (p ++ p3.tail).length = 1 := hcp_len1
        rwa [List.length_append] at this
      have : 1 ≤ p.length := List.length_pos_of_ne_nil hne_p
      have : p3.tail.length = 0 := by omega
      exact List.eq_nil_of_length_eq_zero this




    have hp_single : p.length = 1 := by
      have hlen : p.length + p3.tail.length = 1 := by
        have : (p ++ p3.tail).length = 1 := hcp_len1
        rwa [List.length_append] at this
      simp [hptail] at hlen; exact hlen

    have hp_ratio : listRatioProduct P p = 1 := by
      cases p with
      | nil => contradiction
      | cons a t =>
        cases t with
        | nil => simp [listRatioProduct]
        | cons b rest => simp at hp_single

    have hp3_ratio : listRatioProduct P p3 = 1 := by
      cases p3 with
      | nil => contradiction
      | cons a t =>
        simp only [List.tail] at hptail; subst hptail
        simp [listRatioProduct]
    rw [hp_ratio, hp3_ratio, mul_one]

/-- **Ratio product after appending a state.** Let $P$ be a stochastic matrix,
$x_0, \dots, x_k$ a path of states and $j$ a state. Then the ratio product along
$x_0, \dots, x_k, j$ equals the ratio product along $x_0, \dots, x_k$ times
$\frac{P(x_k, j)}{P(j, x_k)}$, where a quotient with denominator $0$ is taken to be $0$. -/
lemma listRatioProduct_snoc (P : StochasticMatrix M) :
    ∀ (path : List (Fin (M + 1))) (j : Fin (M + 1)) (hne : path ≠ []),
    listRatioProduct P (path ++ [j]) =
      listRatioProduct P path *
        (P.prob (path.getLast hne) j /
          P.prob j (path.getLast hne)) := by
  intro path
  induction path with
  | nil => intro j hne; contradiction
  | cons a tail ih =>
    intro j hne
    cases tail with
    | nil =>
      simp only [listRatioProduct, List.singleton_append, List.getLast_singleton]
      ring
    | cons b rest =>


      have htail_ne : b :: rest ≠ [] := List.cons_ne_nil b rest
      have ih_eq := ih j htail_ne

      have lhs_eq : listRatioProduct P ((a :: b :: rest) ++ [j]) =
          (P.prob a b / P.prob b a) *
            listRatioProduct P ((b :: rest) ++ [j]) := by
        show listRatioProduct P (a :: (b :: rest) ++ [j]) = _
        rfl

      have rhs_eq : listRatioProduct P (a :: b :: rest) =
          (P.prob a b / P.prob b a) *
            listRatioProduct P (b :: rest) := rfl
      rw [lhs_eq, ih_eq, rhs_eq]
      simp only [List.getLast_cons htail_ne]
      ring

/-- **Cycle weights along a positive transition.** Let $P$ be an irreducible stochastic matrix on
the states $\{0, \dots, M\}$ satisfying Kolmogorov's cycle condition, fix a reference state
$i_0$, and write $w(j)$ for the cycle weight of a state $j$ relative to $i_0$. If $i, j$ are
states with $P(i, j) > 0$, then $w(i) \cdot P(i, j) / P(j, i) = w(j)$. -/
lemma cycleWeight_extend (P : StochasticMatrix M)
    (hcycle : P.KolmogorovCycleCondition) (hirr : P.IsIrreducible)
    (i₀ i j : Fin (M + 1)) (hPij : 0 < P.prob i j) :
    cycleWeight P hirr i₀ i *
      (P.prob i j / P.prob j i) =
      cycleWeight P hirr i₀ j := by

  let path_i := Classical.choose (hirr.exists_path i₀ i)
  have hspec_i := Classical.choose_spec (hirr.exists_path i₀ i)
  have hhead_i : path_i.head? = some i₀ := hspec_i.1
  have hlast_i : path_i.getLast? = some i := hspec_i.2.1

  have hne_i : path_i ≠ [] := by intro heq; simp [heq] at hhead_i

  have hlast_eq : path_i.getLast hne_i = i := by
    rw [List.getLast?_eq_some_getLast hne_i] at hlast_i
    exact Option.some_injective _ hlast_i

  have hw_i : cycleWeight P hirr i₀ i = listRatioProduct P path_i := rfl

  let ext_path := path_i ++ [j]

  have hsnoc : listRatioProduct P ext_path =
      listRatioProduct P path_i *
        (P.prob (path_i.getLast hne_i) j /
          P.prob j (path_i.getLast hne_i)) :=
    listRatioProduct_snoc P path_i j hne_i

  rw [hlast_eq] at hsnoc

  rw [hw_i]
  rw [← hsnoc]


  let path_j := Classical.choose (hirr.exists_path i₀ j)
  have hspec_j := Classical.choose_spec (hirr.exists_path i₀ j)
  have hhead_j : path_j.head? = some i₀ := hspec_j.1
  have hlast_j : path_j.getLast? = some j := hspec_j.2.1

  show listRatioProduct P ext_path = listRatioProduct P path_j

  have hhead_ext : ext_path.head? = some i₀ := by
    show (path_i ++ [j]).head? = some i₀
    rw [List.head?_append_of_ne_nil _ hne_i, hhead_i]
  have hlast_ext : ext_path.getLast? = some j := by
    show (path_i ++ [j]).getLast? = some j
    simp

  have hprod_j : 0 < listPathProduct P path_j := hspec_j.2.2
  have hprod_ext : 0 < listPathProduct P ext_path := by


    have hne_ij : ([i, j] : List _) ≠ [] := List.cons_ne_nil _ _
    have hlast_eq_i : path_i.getLast hne_i = i := hlast_eq
    have hhead_ij : ([i, j] : List _).head hne_ij = i := rfl
    have hjoin_ij : path_i.getLast hne_i = ([i, j] : List _).head hne_ij := by
      rw [hlast_eq_i, hhead_ij]
    have hprod_ij : 0 < listPathProduct P [i, j] := by
      simpa [listPathProduct] using hPij
    have hprod_i := hspec_i.2.2
    have := listPathProduct_append_pos P path_i [i, j] hne_i hne_ij hjoin_ij hprod_i hprod_ij

    simp only [List.tail] at this; exact this
  exact cycleWeight_path_independent P hcycle hirr i₀ j ext_path path_j
    hhead_ext hlast_ext hhead_j hlast_j hprod_ext hprod_j

/-- **Detailed balance for cycle weights.** Let $P$ be an irreducible stochastic matrix on the
states $\{0, \dots, M\}$ satisfying Kolmogorov's cycle condition, fix a reference state $i_0$,
and write $w(j)$ for the cycle weight of a state $j$ relative to $i_0$. Then for all states
$i, j$ we have $w(i) \cdot P(i, j) = w(j) \cdot P(j, i)$. -/
theorem cycleWeight_detailed_balance (P : StochasticMatrix M)
    (hcycle : P.KolmogorovCycleCondition) (hirr : P.IsIrreducible)
    (i₀ i j : Fin (M + 1)) :
    cycleWeight P hirr i₀ i * P.prob i j =
    cycleWeight P hirr i₀ j * P.prob j i := by
  by_cases hPij0 : P.prob i j = 0
  ·
    have hPji0 : P.prob j i = 0 := by
      by_contra h; push Not at h
      exact absurd (hcycle.symm_support j i (lt_of_le_of_ne (P.nonneg j i) (Ne.symm h))) (by linarith)
    rw [hPij0, hPji0, mul_zero, mul_zero]
  ·
    have hPij_pos : 0 < P.prob i j := lt_of_le_of_ne (P.nonneg i j) (Ne.symm hPij0)
    have hPji_pos : 0 < P.prob j i := hcycle.symm_support i j hPij_pos
    have hPji_ne : P.prob j i ≠ 0 := ne_of_gt hPji_pos
    have h_ij := cycleWeight_extend P hcycle hirr i₀ i j hPij_pos
    calc cycleWeight P hirr i₀ i * P.prob i j
        = (cycleWeight P hirr i₀ i * (P.prob i j / P.prob j i)) * P.prob j i := by
          rw [mul_div_assoc', div_mul_cancel₀ _ hPji_ne]
      _ = cycleWeight P hirr i₀ j * P.prob j i := by rw [h_ij]

/-- **Kolmogorov's cycle theorem, sufficiency.** For an irreducible finite
Markov chain satisfying the cycle condition, there exists a reversible
measure: a distribution satisfying the detailed balance equations (and
hence stationary). -/
theorem kolmogorov_cycle_sufficiency {M : ℕ} (P : StochasticMatrix M)
    (hirr : P.IsIrreducible) (hcycle : P.KolmogorovCycleCondition) :
    P.IsReversible := by
  let i₀ : Fin (M + 1) := ⟨0, Nat.zero_lt_succ M⟩
  let w : Fin (M + 1) → ℝ := fun j => cycleWeight P hirr i₀ j
  have hw_pos : ∀ j, 0 ≤ w j := fun j => listRatioProduct_nonneg P _
  have hw_i₀_pos : 0 < w i₀ := by
    simp only [w, cycleWeight]
    have hspec := (Classical.choose_spec (hirr.exists_path i₀ i₀))
    have hprod_pos := hspec.2.2
    exact listRatioProduct_pos_of_listPathProduct_pos P hcycle.symm_support _ hprod_pos
  let S : ℝ := ∑ j, w j
  have hS_pos : 0 < S := by
    apply Finset.sum_pos'
    · intro j _; exact hw_pos j
    · exact ⟨i₀, Finset.mem_univ _, hw_i₀_pos⟩
  have hS_ne : S ≠ 0 := ne_of_gt hS_pos
  let π : Distribution M :=
    { val := fun j => w j / S
      nonneg := fun j => div_nonneg (hw_pos j) (le_of_lt hS_pos)
      sum_one := by
        rw [← Finset.sum_div]
        exact div_self hS_ne }
  have hdb : P.DetailedBalance π := by
    intro i j
    show w i / S * P.prob i j = w j / S * P.prob j i
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    congr 1
    exact cycleWeight_detailed_balance P hcycle hirr i₀ i j
  have hstat : P.IsStationary π := detailedBalance_isStationary P π hdb
  exact ⟨π, hstat, hdb⟩



end StochasticMatrix
