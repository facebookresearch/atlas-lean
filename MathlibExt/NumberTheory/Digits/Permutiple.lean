/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

/-!
# Permutiples with a fixed set of digits (Holt)

Holt's residue condition bounds a digit expression modulo the base by the incoming
carry in a rearranged multiplication. The definitions below also describe the digit
graph and the carries of the Hoey–Sloane machine.

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

namespace permutipleCarry_relation

/-- Extract a digit from a numeral by dividing by its place value and reducing modulo the base. -/
private theorem digit_mod {m b : ℕ} (d : Fin m → ℕ) (hd : ∀ i, d i < b) (j : Fin m) :
    (∑ i, d i * b ^ (i : ℕ)) / b ^ (j : ℕ) % b = d j := by
  let f (i : Fin m) : Fin b := ⟨d i, hd i⟩
  exact congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply f) j)

end permutipleCarry_relation

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
public theorem permutipleCarry_relation (n b : ℕ) (hb : 2 ≤ b) {k : ℕ}
    (d : Fin (k + 1) → ℕ) (σ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (j : Fin (k + 1)) :
    (b : ℤ) * permutipleCarry n b d σ (j + 1) - permutipleCarry n b d σ j =
      (n : ℤ) * d (σ j) - d j := by
  let a := ∑ i, d (σ i) * b ^ (i : ℕ)
  let c := permutipleCarry n b d σ
  have input (i : Fin (k + 1)) : a / b ^ (i : ℕ) % b = d (σ i) :=
    permutipleCarry_relation.digit_mod (fun l ↦ d (σ l)) (fun l ↦ hp.1 _) i
  have carry_succ (i : Fin (k + 1)) : c ((i : ℕ) + 1) = (n * d (σ i) + c i) / b := by
    simp [c, permutipleCarry]
  -- Split the remaining input into its current column and its higher columns.
  have split (i : Fin (k + 1)) :
      n * (a / b ^ (i : ℕ)) + c i =
        n * d (σ i) + c i + b * (n * (a / b ^ ((i : ℕ) + 1))) := by
    rw [← input i, pow_succ, ← Nat.div_div_eq_div_mul]
    conv_lhs => rw [← Nat.mod_add_div (a / b ^ (i : ℕ)) b]
    ring
  -- After dropping t columns, the incoming carry accounts for the discarded digits.
  have quotient (t : ℕ) (ht : t ≤ k + 1) :
      n * a / b ^ t = n * (a / b ^ t) + c t := by
    induction t with
    | zero => simp [c, permutipleCarry]
    | succ t ih =>
      have h : t < k + 1 := ht
      rw [pow_succ, ← Nat.div_div_eq_div_mul, ih (by omega), split ⟨t, h⟩,
        Nat.add_mul_div_left _ _ (by omega)]
      rw [← carry_succ ⟨t, h⟩, pow_succ, add_comm]
  have digit := permutipleCarry_relation.digit_mod d hp.1 j
  rw [hp.2, quotient _ j.isLt.le, split j, Nat.add_mul_mod_self_left] at digit
  have col := Nat.mod_add_div (n * d (σ j) + c j) b
  rw [digit, ← carry_succ j, add_comm (d j)] at col
  exact sub_eq_sub_iff_add_eq_add.mpr (by exact_mod_cast col)

namespace permutiple_basePerm_residue_le

/-- Dividing a numeral by its place value gives its digit modulo the base. -/
private theorem digit_modEq {m b : ℕ} (d : Fin m → ℕ) (hd : ∀ i, d i < b) (j : Fin m) :
    (d j : ℤ) ≡ (((∑ i, d i * b ^ (i : ℕ)) / b ^ (j : ℕ) : ℕ) : ℤ) [ZMOD b] := by
  rw [Int.natCast_modEq_iff, Nat.ModEq, Nat.mod_eq_of_lt (hd j),
    permutipleCarry_relation.digit_mod d hd j]

end permutiple_basePerm_residue_le

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
public theorem permutiple_basePerm_residue_le (n b : ℕ) (hn : 1 ≤ n) (hb : 2 ≤ b)
    {k : ℕ} (d : Fin (k + 1) → ℕ) (σ π τ : Equiv.Perm (Fin (k + 1))) (hp : IsPermutiple n b d σ)
    (hq : IsPermutiple n b (d ∘ π) τ) (j : Fin (k + 1)) :
    ((d j : ℤ) + ((b : ℤ) - n) * d ((π * τ * π⁻¹) j)) % b ≤ n - 1 := by
  let i := π.symm j
  let p := b ^ (i : ℕ)
  let a := ∑ l : Fin (k + 1), d (π (τ l)) * b ^ (l : ℕ)
  have hprod : (d j : ℤ) ≡ (↑(n * a / p) : ℤ) [ZMOD b] := by
    have h := permutiple_basePerm_residue_le.digit_modEq (d ∘ π) hq.1 i
    rw [hq.2] at h
    simpa only [Function.comp_apply, i, Equiv.apply_symm_apply] using h
  have hin : (d ((π * τ * π⁻¹) j) : ℤ) ≡ (↑(a / p) : ℤ) [ZMOD b] :=
    permutiple_basePerm_residue_le.digit_modEq (fun l ↦ d (π (τ l))) (fun l ↦ hp.1 _) i
  -- The digits below position i contribute this carry to the quotient of the product.
  let carry := n * (a % p) / p
  have hp_pos : 0 < p := pow_pos (by omega : 0 < b) _
  have hcarry : carry < n := (Nat.div_lt_iff_lt_mul hp_pos).2
    (Nat.mul_lt_mul_of_pos_left (Nat.mod_lt a hp_pos) hn)
  have hquot : n * a / p = carry + n * (a / p) := by
    calc
      n * a / p = n * (a % p + p * (a / p)) / p :=
        congrArg (fun x ↦ n * x / p) (Nat.mod_add_div a p).symm
      _ = carry + n * (a / p) := by
        rw [mul_add, mul_left_comm n p, Nat.add_mul_div_left _ _ hp_pos]
  calc
    _ = ((↑(n * a / p) : ℤ) + ((b : ℤ) - n) * ↑(a / p)) % b :=
      (hprod.add (hin.mul_left _)).eq
    _ = ((carry : ℤ) + b * ↑(a / p)) % b := by
      rw [hquot, Nat.cast_add, Nat.cast_mul]
      congr 1
      ring
    _ = (carry : ℤ) % b := Int.add_mul_emod_self_left _ _ _
    _ ≤ n - 1 := by
      rw [← Int.natCast_emod]
      have := Nat.mod_le carry b
      omega

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
public theorem permutipleGraphEdges_eq_of_conj {k : ℕ} (d : Fin (k + 1) → ℕ)
    (π₁ π₂ τ₁ τ₂ : Equiv.Perm (Fin (k + 1))) (hconj : π₁ * τ₁ * π₁⁻¹ = π₂ * τ₂ * π₂⁻¹) :
    permutipleGraphEdges (d ∘ π₁) τ₁ = permutipleGraphEdges (d ∘ π₂) τ₂ := by
  have reindex (π τ : Equiv.Perm (Fin (k + 1))) :
      permutipleGraphEdges (d ∘ π) τ = permutipleGraphEdges d (π * τ * π⁻¹) := by
    unfold permutipleGraphEdges
    conv_rhs => rw [← Finset.image_univ_equiv π, Finset.image_image]
    simp [Function.comp_def, Equiv.Perm.mul_apply]
  rw [reindex π₁ τ₁, reindex π₂ τ₂, hconj]

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

end

end MetaMathlibExt
