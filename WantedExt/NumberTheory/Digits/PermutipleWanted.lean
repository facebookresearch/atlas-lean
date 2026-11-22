/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Permutiples with a fixed set of digits (Holt)

Statements from B. V. Holt, *A Method for Finding All Permutiples with a Fixed
Set of Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88
(arXiv:2312.02056).

A `(k+1)`-digit base-`b` numeral `(d_k, …, d_0)_b` is a digit function
`d : Fin (k + 1) → ℕ` (digit `d j` has weight `b ^ j`); for a permutation `π`,
the numeral `(d_{π(k)}, …, d_{π(0)})_b` is `d ∘ π`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Permutiples with a given digit permutation.** Let $n$, $b$ and $d_0, \dots, d_k$ be
natural numbers and let $\sigma$ be a permutation of $\{0, \dots, k\}$. The numeral
$(d_k, \dots, d_0)_b$ is an $(n, b, \sigma)$-permutiple when $d_j < b$ for every $j$ and
$$\sum_{j=0}^k d_j b^j = n \sum_{j=0}^k d_{\sigma(j)} b^j,$$
that is, $(d_k, \dots, d_0)_b = n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88,
Definition 1 (from Holt, *Some general results and open questions on
palintiple numbers*). -/
public def IsPermutiple (n b : ℕ) {k : ℕ} (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    Prop :=
  (∀ j, d j < b) ∧ ∑ j, d j * b ^ (j : ℕ) = n * ∑ j, d (σ j) * b ^ (j : ℕ)

/-- **Carries of a permutiple multiplication.** Let $n$, $b$ and $d_0, \dots, d_k$ be
natural numbers and let $\sigma$ be a permutation of $\{0, \dots, k\}$. The carries of the
single-digit multiplication $n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$, where
$(e_k, \dots, e_0)_b$ denotes the base-$b$ numeral $\sum_{j=0}^{k} e_j b^j$, are the
natural numbers $c_0, c_1, c_2, \dots$ defined by $c_0 = 0$,
$c_{j+1} = \lfloor (n d_{\sigma(j)} + c_j) / b \rfloor$ for $0 \le j \le k$, and
$c_{j+1} = 0$ for $j > k$. Division by $b = 0$ is taken to give $0$.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Section 2. -/
public def permutipleCarry (n b : ℕ) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if h : j < k + 1 then (n * d (σ ⟨j, h⟩) + permutipleCarry n b d σ j) / b else 0

/-- **First two carries of a permutiple multiplication.** Let $n$, $b$ and $d_0, \dots, d_k$
be natural numbers, let $\sigma$ be a permutation of $\{0, \dots, k\}$, and write
$(e_k, \dots, e_0)_b$ for the base-$b$ numeral $\sum_{j=0}^{k} e_j b^j$. The carries
$c_0, c_1, \dots$ of the single-digit multiplication
$n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$, defined by $c_0 = 0$ and
$c_{j+1} = \lfloor (n d_{\sigma(j)} + c_j) / b \rfloor$ for $0 \le j \le k$, satisfy
$c_0 = 0$ and $c_1 = \lfloor n d_{\sigma(0)} / b \rfloor$, where division by $b = 0$ is
taken to give $0$.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Section 2. -/
public theorem permutipleCarry_zero_one (n b : ℕ) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) :
    permutipleCarry n b d σ 0 = 0 ∧ permutipleCarry n b d σ 1 = n * d (σ 0) / b := by
  refine ⟨rfl, ?_⟩
  simp [permutipleCarry]

/-- **$87912$ is a $(4, 10)$-permutiple by digit reversal.** The numeral
$(d_4, d_3, d_2, d_1, d_0)_{10} = 87912$ is a $(4, 10, \sigma)$-permutiple, where $\sigma$ is the
reversal $j \mapsto 4 - j$ of $\{0, \dots, 4\}$; that is, $87912 = 4 \cdot 21978$, and $21978$ has
the digits of $87912$ in reverse order.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88,
Introduction. -/
public theorem isPermutiple_87912 :
    IsPermutiple 4 10 (k := 4) ![2, 1, 9, 7, 8] Fin.revPerm := by
  unfold IsPermutiple
  decide

/-- **Carry relation for permutiples.** Let $n$ and $b \ge 2$ be natural numbers, let
$\sigma$ be a permutation of $\{0, \dots, k\}$, and let $(d_k, \dots, d_0)_b$ be an
$(n, b, \sigma)$-permutiple, where $(e_k, \dots, e_0)_b$ denotes the base-$b$ numeral
$\sum_{j=0}^{k} e_j b^j$. Let $c_0, c_1, \dots$ be the carries of the multiplication
$n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$. Then for every $0 \le j \le k$,
$$b\, c_{j+1} - c_j = n\, d_{\sigma(j)} - d_j,$$
with both sides computed in the integers.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 1
(`integers-2024-A88-thm-1`), quoting Holt's earlier paper; restated as Theorem 1
of Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025),
Article A13 (`integers-2025-A13-thm-1`). -/
public theorem_wanted permutipleCarry_relation (n b : ℕ) (hb : 2 ≤ b) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    (b : ℤ) * permutipleCarry n b d σ (j + 1) - permutipleCarry n b d σ j =
      (n : ℤ) * d (σ j) - d j

/-- **Carry bound for permutiples.** Let $n$ and $b \ge 2$ be natural numbers, let $\sigma$
be a permutation of $\{0, \dots, k\}$, and let $(d_k, \dots, d_0)_b$ be an
$(n, b, \sigma)$-permutiple, where $(e_k, \dots, e_0)_b$ denotes the base-$b$ numeral
$\sum_{j=0}^{k} e_j b^j$. Let $c_0, c_1, \dots$ be the carries of the multiplication
$n \cdot (d_{\sigma(k)}, \dots, d_{\sigma(0)})_b$. Then for every $0 \le j \le k$ we have
$c_j \le n - 1$ if $n \ge 1$, and $c_j = 0$ if $n = 0$.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 2
(`integers-2024-A88-thm-2`), quoting Holt's earlier paper; restated as Theorem 2
of Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25 (2025),
Article A13 (`integers-2025-A13-thm-2`). -/
public theorem_wanted permutipleCarry_le (n b : ℕ) (hb : 2 ≤ b) {k : ℕ} (d : Fin (k + 1) → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) (j : Fin (k + 1)) :
    permutipleCarry n b d σ j ≤ n - 1

/-- **Holt's residue condition for rearranged permutiples.** Let $n \ge 1$ and $b \ge 2$ be
natural numbers, let $d_0, \dots, d_k$ be natural numbers, and write $(e_k, \dots, e_0)_b$
for the base-$b$ numeral $\sum_{j=0}^{k} e_j b^j$. Let $\sigma$, $\pi$ and $\tau$ be
permutations of $\{0, \dots, k\}$. If $(d_k, \dots, d_0)_b$ is an $(n, b, \sigma)$-permutiple
and $(d_{\pi(k)}, \dots, d_{\pi(0)})_b$ is an $(n, b, \tau)$-permutiple, then for every
$0 \le j \le k$
$$\lambda\bigl(d_j + (b - n)\, d_{\pi(\tau(\pi^{-1}(j)))}\bigr) \le n - 1,$$
where $\lambda(x)$ is the least non-negative residue of the integer $x$ modulo $b$ (the
difference $b - n$ is taken in the integers and may be negative).

The hypothesis $n \ge 1$ is needed: for $n = 0$ the only permutiples have all digits zero
and the bound would read $0 \le -1$.

Source: B. V. Holt, *A Method for Finding All Permutiples with a Fixed Set of
Digits from a Single Known Example*, INTEGERS 24 (2024), Article A88, Theorem 3
(`integers-2024-A88-thm-3`). -/
public theorem_wanted permutiple_basePerm_residue_le (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d : Fin (k + 1) → ℕ) (σ π τ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (hq : IsPermutiple n b (d ∘ π) τ) (j : Fin (k + 1)) :
    ((d j : ℤ) + ((b : ℤ) - n) * d ((π * τ * π⁻¹) j)) % b ≤ n - 1

/-- **Edge set of the graph of a numeral.** Let $b$ be a base, let $d_0, \dots, d_k$ be
natural numbers, the digits of the base-$b$ numeral
$(d_k, \dots, d_0)_b = \sum_{j=0}^{k} d_j b^j$, and let $\sigma$ be a permutation of
$\{0, \dots, k\}$. The graph $G$ of these digits with digit permutation $\sigma$ has edge set
$$E = \{(d_j, d_{\sigma(j)}) : 0 \le j \le k\},$$
a finite set of ordered pairs of natural numbers; it does not depend on $b$.

The vertices of $G$ are all base-$b$ digits, so $G$ is determined by its edge set.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Definition 3 (the graph of a permutiple). -/
public def permutipleGraphEdges {k : ℕ} (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) :
    Finset (ℕ × ℕ) :=
  Finset.univ.image fun j => (d j, d (σ j))

/-- **Graph of the permutiple 87912.** Let $(d_0, d_1, d_2, d_3, d_4) = (2, 1, 9, 7, 8)$ be
the decimal digits of $87912$, from the units digit up, and let $\sigma$ be the reversal
$\sigma(j) = 4 - j$ of $\{0, \dots, 4\}$. The edge set
$\{(d_j, d_{\sigma(j)}) : 0 \le j \le 4\}$ of the graph of these digits with digit
permutation $\sigma$ is exactly $\{(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)\}$: the edges
$8 \rightleftarrows 2$ and $7 \rightleftarrows 1$ and a loop at $9$.

Here $87912 = 4 \cdot 21978$, and $21978$ is $87912$ with its digits reversed.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Figure 1. -/
public theorem permutipleGraphEdges_87912 :
    permutipleGraphEdges (k := 4) ![2, 1, 9, 7, 8] Fin.revPerm =
      {(2, 8), (1, 7), (9, 9), (7, 1), (8, 2)} := by
  decide

/-- **Edges of the mother graph.** Let $n$ and $b$ be natural numbers. For natural numbers $x$
and $y$, the pair $(x, y)$ is an edge of the $(n, b)$-mother graph $M$ when $x < b$, $y < b$ and
$$\lambda(x + (b - n) y) \le n - 1,$$
where $\lambda(z)$ is the least non-negative residue of the integer $z$ modulo $b$, and $b - n$
and $n - 1$ are computed in the integers.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Definition 4 (the mother graph). -/
public def IsMotherGraphEdge (n b x y : ℕ) : Prop :=
  x < b ∧ y < b ∧ ((x : ℤ) + ((b : ℤ) - n) * y) % b ≤ (n : ℤ) - 1

/-- **An edge and a non-edge of the $(2, 4)$-mother graph.** In the $(2, 4)$-mother graph, the
pair $(0, 2)$ is an edge, since $\lambda(0 + (4 - 2) \cdot 2) = \lambda(4) = 0 \le 1$, and the
pair $(0, 1)$ is not an edge, since $\lambda(0 + (4 - 2) \cdot 1) = \lambda(2) = 2 > 1$, where
$\lambda$ is the least non-negative residue modulo $4$.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Definition 4 and Example 1. -/
public theorem isMotherGraphEdge_two_four :
    IsMotherGraphEdge 2 4 0 2 ∧ ¬ IsMotherGraphEdge 2 4 0 1 := by
  unfold IsMotherGraphEdge
  decide

/-- **Carries of the Hoey–Sloane machine.** Let $n$ and $b$ be natural numbers and let
$(d_0, \hat d_0)(d_1, \hat d_1) \cdots (d_k, \hat d_k)$ be an input string of pairs of natural
numbers. The carries $c_0, c_1, c_2, \dots$ of the $(n, b)$-Hoey–Sloane machine on this string
are the integers given by $c_0 = 0$,
$$c_{j+1} = \left\lfloor \frac{n \hat d_j - d_j + c_j}{b} \right\rfloor \quad (0 \le j \le k)$$
and $c_{j+1} = 0$ for $j > k$, where division by $b = 0$ gives $0$.

The machine has a transition from the state $c_j$ on the input $(d_j, \hat d_j)$ when this
division is exact.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Section 4, Equation (2) (the Hoey-Sloane machine). -/
public def hoeySloaneCarry (n b : ℕ) {k : ℕ} (d dh : Fin (k + 1) → ℕ) : ℕ → ℤ
  | 0 => 0
  | j + 1 =>
    if h : j < k + 1 then
      ((n : ℤ) * dh ⟨j, h⟩ - d ⟨j, h⟩ + hoeySloaneCarry n b d dh j) / b
    else 0

/-- **Carries of the $(2, 4)$-Hoey–Sloane machine on $(0,0)(2,3)(1,2)(3,1)$.** On the input
string $(d_0, \hat d_0)(d_1, \hat d_1)(d_2, \hat d_2)(d_3, \hat d_3) = (0,0)(2,3)(1,2)(3,1)$,
the carries $c_0, c_1, c_2, c_3, c_4$ of the $(2, 4)$-Hoey–Sloane machine are $0, 0, 1, 1, 0$.

This is the $(2, 4)$-permutiple string of $(3, 1, 2, 0)_4 = 216 = 2 \cdot 108 =
2 \cdot (1, 2, 3, 0)_4$.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Example 1. -/
public theorem hoeySloaneCarry_two_four_example :
    (List.range 5).map (hoeySloaneCarry 2 4 (k := 3) ![0, 2, 1, 3] ![0, 3, 2, 1]) =
      [0, 0, 1, 1, 0] := by
  decide

/-- **Hoey–Sloane words.** Let $n$ and $b$ be natural numbers. An input string
$(d_0, \hat d_0) \cdots (d_k, \hat d_k)$ of pairs of natural numbers belongs to the language $L$
of the $(n, b)$-Hoey–Sloane machine when, with $c_0, \dots, c_{k+1}$ the carries of the machine
on this string, every input $(d_j, \hat d_j)$ is an edge of the $(n, b)$-mother graph, $b$
divides $n \hat d_j - d_j + c_j$ for every $0 \le j \le k$, and $c_{k+1} = 0$.

So the walk starts in the state $c_0 = 0$, every transition is an exact division, and the walk
ends in the state $0$.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Section 4 (the language `L` and `L`-walks). -/
public def IsHoeySloaneWord (n b : ℕ) {k : ℕ} (d dh : Fin (k + 1) → ℕ) : Prop :=
  (∀ j, IsMotherGraphEdge n b (d j) (dh j)) ∧
    (∀ j : Fin (k + 1), (b : ℤ) ∣ (n : ℤ) * dh j - d j + hoeySloaneCarry n b d dh j) ∧
      hoeySloaneCarry n b d dh (k + 1) = 0

/-- **The string $(0,0)(2,3)(1,2)(3,1)$ lies in the $(2, 4)$-Hoey–Sloane language.** The input
string $(d_0, \hat d_0) \cdots (d_3, \hat d_3) = (0,0)(2,3)(1,2)(3,1)$ belongs to the language
$L$ of the $(2, 4)$-Hoey–Sloane machine.

This is the $(2, 4)$-permutiple string of $(3, 1, 2, 0)_4 = 216 = 2 \cdot 108 =
2 \cdot (1, 2, 3, 0)_4$.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Example 1. -/
public theorem isHoeySloaneWord_two_four_example :
    IsHoeySloaneWord 2 4 (k := 3) ![0, 2, 1, 3] ![0, 3, 2, 1] := by
  unfold IsHoeySloaneWord IsMotherGraphEdge
  decide

/-- **Conjugate rearrangements have the same graph.** Let $d_0, \dots, d_k$ be natural numbers
and let $\pi_1, \pi_2, \tau_1, \tau_2$ be permutations of $\{0, \dots, k\}$ with
$\pi_1 \tau_1 \pi_1^{-1} = \pi_2 \tau_2 \pi_2^{-1}$. Then the graph of the digits
$d_{\pi_1(0)}, \dots, d_{\pi_1(k)}$ with digit permutation $\tau_1$ and the graph of the digits
$d_{\pi_2(0)}, \dots, d_{\pi_2(k)}$ with digit permutation $\tau_2$ have the same edge set:
$$\{(d_{\pi_1(j)}, d_{\pi_1(\tau_1(j))}) : 0 \le j \le k\} =
\{(d_{\pi_2(j)}, d_{\pi_2(\tau_2(j))}) : 0 \le j \le k\}.$$

The source assumes, for a base $b$ and a multiplier $n$ with $1 < n < b$, that
$(d_{\pi_1(k)}, \dots, d_{\pi_1(0)})_b$ is an $(n, b, \tau_1)$-permutiple and that
$(d_{\pi_2(k)}, \dots, d_{\pi_2(0)})_b$ is an $(n, b, \tau_2)$-permutiple, together with a base
permutiple $(d_k, \dots, d_0)_b$; these hypotheses are not needed.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 4 (`integers-2025-A13-thm-4`). -/
public theorem_wanted permutipleGraphEdges_eq_of_conj {k : ℕ} (d : Fin (k + 1) → ℕ)
    (π₁ π₂ τ₁ τ₂ : Equiv.Perm (Fin (k + 1))) (hconj : π₁ * τ₁ * π₁⁻¹ = π₂ * τ₂ * π₂⁻¹) :
    permutipleGraphEdges (d ∘ π₁) τ₁ = permutipleGraphEdges (d ∘ π₂) τ₂

/-- **Every permutiple has a cycle-preserving digit permutation.** Let $n$, $b$ and
$d_0, \dots, d_k$ be natural numbers and let $\sigma$ be a permutation of $\{0, \dots, k\}$ such
that $(d_k, \dots, d_0)_b$ is an $(n, b, \sigma)$-permutiple. Then there is a permutation
$\hat\sigma$ of $\{0, \dots, k\}$ such that $(d_k, \dots, d_0)_b$ is also an
$(n, b, \hat\sigma)$-permutiple and the digits along each cycle of $\hat\sigma$ are distinct:
for all $j \in \{0, \dots, k\}$ and all $i \ge 0$, if $d_{\hat\sigma^i(j)} = d_j$ then
$\hat\sigma^i(j) = j$.

Unlike the paper, no assumption $1 < n < b$ is made.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 5 (`integers-2025-A13-thm-5`), with Definition 5
(cycle-preserving permutations). -/
public theorem_wanted exists_cyclePreserving_permutiple (n b : ℕ) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) :
    ∃ σ' : Equiv.Perm (Fin (k + 1)), IsPermutiple n b d σ' ∧
      ∀ (j : Fin (k + 1)) (i : ℕ), d ((σ' ^ i) j) = d j → (σ' ^ i) j = j

/-- **Permutiple graphs are unions of simple cycles of the mother graph.** Let $n \ge 1$
and $b \ge 2$ be natural numbers, let $\sigma$ be a permutation of $\{0, \dots, k\}$, and
let $(d_k, \dots, d_0)_b$ be an $(n, b, \sigma)$-permutiple, where $(e_k, \dots, e_0)_b$
denotes the base-$b$ numeral $\sum_{j=0}^{k} e_j b^j$. Let
$E = \{(d_j, d_{\sigma(j)}) : 0 \le j \le k\}$ be the edge set of its graph. Then every
pair in $E$ is an edge of the $(n, b)$-mother graph, and every $e \in E$ lies on a directed
cycle with distinct vertices all of whose edges are in $E$: there are $m \ge 0$ and pairwise
distinct natural numbers $v_0, \dots, v_m$ such that, with indices taken modulo $m + 1$,
$(v_i, v_{i+1}) \in E$ for every $0 \le i \le m$ and $e = (v_i, v_{i+1})$ for some $i$.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Theorem 6 (`integers-2025-A13-thm-6`), with Definition 6
(permutiple classes and their graphs). -/
public theorem_wanted permutipleGraphEdges_union_cycles (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ) :
    (∀ e ∈ permutipleGraphEdges d σ, IsMotherGraphEdge n b e.1 e.2) ∧
      ∀ e ∈ permutipleGraphEdges d σ, ∃ (m : ℕ) (v : Fin (m + 1) → ℕ), Function.Injective v ∧
        (∀ i, (v i, v (finRotate (m + 1) i)) ∈ permutipleGraphEdges d σ) ∧
          ∃ i, e = (v i, v (finRotate (m + 1) i))

/-- **Hoey–Sloane words with permuted digits are unions of cycles.** Let $n \ge 1$ and $b \ge 2$
be natural numbers, and let $s = (d_0, \hat d_0) \cdots (d_k, \hat d_k)$ be an input string in
the language $L$ of the $(n, b)$-Hoey–Sloane machine such that $\hat d_j = d_{\sigma(j)}$ for all
$j$, for some permutation $\sigma$ of $\{0, \dots, k\}$. Let
$E = \{(d_j, \hat d_j) : 0 \le j \le k\}$ be the set of inputs of $s$. Then every $e \in E$ lies
on a directed cycle with edges in $E$: there are $m \ge 0$ and pairwise distinct natural numbers
$v_0, \dots, v_m$ such that $(v_i, v_{i+1}) \in E$ for all $0 \le i \le m$, with indices taken
modulo $m + 1$, and $e = (v_i, v_{i+1})$ for some $i$.

Source: B. V. Holt, *Finding Permutiples of a Known Base and Multiplier*, INTEGERS 25
(2025), Article A13, Corollary 1 (`integers-2025-A13-cor-1`). -/
public theorem_wanted hoeySloaneWord_inputs_union_cycles (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d dh : Fin (k + 1) → ℕ) (hs : IsHoeySloaneWord n b d dh)
    (σ : Equiv.Perm (Fin (k + 1))) (hσ : dh = d ∘ σ) :
    ∀ e ∈ Finset.univ.image (fun j => (d j, dh j)), ∃ (m : ℕ) (v : Fin (m + 1) → ℕ),
      Function.Injective v ∧
        (∀ i, (v i, v (finRotate (m + 1) i)) ∈ Finset.univ.image (fun j => (d j, dh j))) ∧
          ∃ i, e = (v i, v (finRotate (m + 1) i))

end

end MetaMathlibExt
