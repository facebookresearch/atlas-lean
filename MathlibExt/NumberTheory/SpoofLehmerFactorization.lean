/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Spoof Lehmer factorizations

Statements from Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26
(2026), Article A33. A spoof factorization `x_1^{a_1} ⋯ x_r^{a_r}` is a multiset of pairs
`(x_i, a_i)` of positive integers; `x_1 ⋯ x_r` denotes the factorization with all exponents `1`,
encoded as `Multiset.map (fun a => (a, 1)) x`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Spoof factorizations.** A finite multiset $F = \{(x_1, a_1), \dots, (x_r, a_r)\}$ of pairs of
natural numbers, read as the formal product $x_1^{a_1} \cdots x_r^{a_r}$, is a spoof factorization
if every base $x_i$ and every exponent $a_i$ is positive.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 1. -/
def IsSpoofFactorization (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, 0 < p.1 ∧ 0 < p.2

/-- **Spoof evaluation.** Let $F = x_1^{a_1} \cdots x_r^{a_r}$ be a finite multiset of pairs
$(x_i, a_i)$ of natural numbers, each a base $x_i$ with an exponent $a_i$. The spoof evaluation of
$F$ is the integer $\tilde e(F) = x_1^{a_1} \cdots x_r^{a_r} = \prod_{i=1}^{r} x_i^{a_i}$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 2. -/
def spoofEval (F : Multiset (ℕ × ℕ)) : ℤ :=
  (F.map fun p => (p.1 : ℤ) ^ p.2).prod

/-- **Spoof totient.** Let $F$ be a finite multiset of pairs $(x_i, a_i)$ of natural numbers,
$i = 1, \dots, r$, viewed as the formal product $x_1^{a_1} \cdots x_r^{a_r}$. The spoof totient
of $F$ is the integer $\tilde\varphi(F) = \prod_{i=1}^{r} (x_i^{a_i} - x_i^{a_i - 1})$, where
the exponent $a_i - 1$ is truncated at $0$, so a pair with $a_i = 0$ contributes the factor $0$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 3. -/
def spoofTotient (F : Multiset (ℕ × ℕ)) : ℤ :=
  (F.map fun p => (p.1 : ℤ) ^ p.2 - (p.1 : ℤ) ^ (p.2 - 1)).prod

/-- **Spoof evaluation and spoof totient of $3 \cdot 3$.** Let $3 \cdot 3$ denote the spoof
factorization $3^1 \cdot 3^1$, with two factors of base $3$ and exponent $1$. Its spoof evaluation
is $\tilde e(3 \cdot 3) = 9$ and its spoof totient is $\tilde\varphi(3 \cdot 3) = 4$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definitions 2 and 3. -/
theorem spoofEval_spoofTotient_three_three :
    spoofEval {(3, 1), (3, 1)} = 9 ∧ spoofTotient {(3, 1), (3, 1)} = 4 := by
  norm_num [spoofEval, spoofTotient]

/-- **Spoof Lehmer factorizations.** Let $k$ be an integer and $F$ a finite multiset of pairs
$(x, a)$ of natural numbers. Write $\tilde e(F) = \prod x^a$ for the spoof evaluation and
$\tilde\varphi(F) = \prod (x^a - x^{a-1})$ for the spoof totient of $F$, the products running
over the pairs of $F$ with multiplicity. Then $F$ is a (spoof) $k$-Lehmer factorization if $F$ is
a spoof factorization (every base and exponent is positive), $k \cdot \tilde\varphi(F) =
\tilde e(F) - 1$, and $F$ has at least two factors counted with multiplicity or some factor
whose exponent is greater than $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 4. -/
def IsSpoofLehmer (k : ℤ) (F : Multiset (ℕ × ℕ)) : Prop :=
  IsSpoofFactorization F ∧ k * spoofTotient F = spoofEval F - 1 ∧
    (2 ≤ Multiset.card F ∨ ∃ p ∈ F, 1 < p.2)

/-- **$3 \cdot 3$ is a $2$-Lehmer factorization.** The spoof factorization $3^1 \cdot 3^1$ is a
$2$-Lehmer factorization; indeed $2 \cdot (3 - 1)(3 - 1) = 3 \cdot 3 - 1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Table 1. -/
theorem isSpoofLehmer_three_three : IsSpoofLehmer 2 {(3, 1), (3, 1)} :=
  ⟨by simp [IsSpoofFactorization], by norm_num [spoofEval, spoofTotient], Or.inl (by simp)⟩

/-- **The factorizations $1^a \cdot 1^b$ are Lehmer for every $k$.** For all positive integers
$a$ and $b$ and every integer $k$, the spoof factorization $1^a \cdot 1^b$ is a $k$-Lehmer
factorization.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Example 1. -/
theorem isSpoofLehmer_one_one (k : ℤ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    IsSpoofLehmer k {(1, a), (1, b)} :=
  ⟨by simp [IsSpoofFactorization, ha, hb], by simp [spoofEval, spoofTotient], Or.inl (by simp)⟩

/-- **Trivial spoof factorizations.** A finite multiset $F$ of pairs $(x, a)$ of natural numbers,
read as a spoof factorization with bases $x$ and exponents $a$, is trivial if every base $x$
occurring in $F$ equals $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 6. -/
def IsTrivialSpoof (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, p.1 = 1

/-- **Spoof Lehmer factorizations with a base $1$ are trivial.** If a finite multiset $F$ of pairs
$(x, a)$ of natural numbers is a $k$-Lehmer factorization for some integer $k$, and some pair in
$F$ has base $x = 1$, then every base of $F$ equals $1$, that is, $F$ is trivial.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Proposition 1 (`integers-2026-A33-prop-1`). -/
theorem isTrivialSpoof_of_isSpoofLehmer_of_one_mem (F : Multiset (ℕ × ℕ))
    (hL : ∃ k : ℤ, IsSpoofLehmer k F) (h1 : ∃ p ∈ F, p.1 = 1) :
    IsTrivialSpoof F := by
  obtain ⟨k, hpos, heq, _⟩ := hL
  obtain ⟨p, hp, hbase⟩ := h1
  have hzero : spoofTotient F = 0 := by
    apply Multiset.prod_eq_zero
    exact Multiset.mem_map.mpr ⟨p, hp, by simp [hbase]⟩
  have heval : spoofEval F = 1 := by
    simpa [hzero, sub_eq_zero] using heq.symm
  intro q hq
  have hdvd : (q.1 : ℤ) ∣ spoofEval F :=
    (dvd_pow_self _ (hpos q hq).2.ne').trans
      (Multiset.dvd_prod (Multiset.mem_map_of_mem _ hq))
  rw [heval] at hdvd
  exact Nat.dvd_one.mp (Int.ofNat_dvd.mp hdvd)

/-- **Odd spoof factorizations.** A finite multiset $F$ of pairs $(x, a)$ of natural numbers, read
as a spoof factorization with bases $x$ and exponents $a$, is odd if every base $x$ occurring in
$F$ is odd.

A spoof factorization that is not odd is called even.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 7. -/
def IsOddSpoof (F : Multiset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, Odd p.1

/-- **Factorization with all exponents one.** For a finite multiset $x$ of natural numbers
$x_1, \dots, x_r$, this is the formal product $x_1 \cdots x_r = x_1^1 \cdots x_r^1$, that is,
the multiset of pairs $(x_1, 1), \dots, (x_r, 1)$, each consisting of a base $x_i$ and the
exponent $1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Remark 3. -/
def spoofOfBases (x : Multiset ℕ) : Multiset (ℕ × ℕ) :=
  x.map fun a => (a, 1)

/-- **The exponent-one factorization on the bases 3 and 3.** The factorization with all exponents
one on the multiset of bases consisting of two copies of $3$ is the multiset consisting of two
copies of the pair $(3, 1)$, that is, $3 \cdot 3 = 3^1 \cdot 3^1$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Remark 3. -/
theorem spoofOfBases_three_three : spoofOfBases {3, 3} = {(3, 1), (3, 1)} := by
  simp [spoofOfBases]

/-- **Solutions of the Lehmer equation.** A finite multiset $x$ of natural numbers solves
Equation (1) if every element $x_j$ of $x$ satisfies $x_j \ge 2$ and there is a positive integer
$k$ with $k \prod_j (x_j - 1) = \prod_j x_j - 1$, where the products run over the elements of $x$
with multiplicity and are computed in $\mathbb{Z}$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Equation (1). -/
def IsLehmerEquationSolution (x : Multiset ℕ) : Prop :=
  (∀ a ∈ x, 2 ≤ a) ∧ ∃ k : ℤ, 0 < k ∧
    k * (x.map fun a : ℕ => (a : ℤ) - 1).prod = (x.map fun a : ℕ => (a : ℤ)).prod - 1

/-- **The multiset $\{3, 3\}$ solves the Lehmer equation.** Every element of the multiset
$\{3, 3\}$ is at least $2$, and there is a positive integer $k$ with
$k \cdot (3 - 1)(3 - 1) = 3 \cdot 3 - 1$ (namely $k = 2$). So $\{3, 3\}$ solves Equation (1), the
equation $k \prod_j (x_j - 1) = \prod_j x_j - 1$ in the elements $x_j$ of a multiset, counted
with multiplicity.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Table 1. -/
theorem isLehmerEquationSolution_three_three : IsLehmerEquationSolution {3, 3} :=
  ⟨by simp, 2, by norm_num, by norm_num⟩

/-- **The Lehmer function $\kappa_r$.** For a list $t = (t_1, \dots, t_r)$ of real numbers,
$$\kappa_r(t_1, \dots, t_r) = \frac{t_1 \cdots t_r - 1}{(t_1 - 1) \cdots (t_r - 1)},$$
with division by zero giving $0$ (so $\kappa_r(t) = 0$ when some $t_i = 1$).

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 8. -/
noncomputable def lehmerKappa (t : List ℝ) : ℝ :=
  (t.prod - 1) / (t.map (· - 1)).prod

/-- **The Lehmer function at $(2, 2)$.** The Lehmer function
$\kappa_2(t_1, t_2) = (t_1 t_2 - 1) / ((t_1 - 1)(t_2 - 1))$ takes the value $\kappa_2(2, 2) = 3$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 8 and proof of Theorem 5. -/
theorem lehmerKappa_two_two : lehmerKappa [2, 2] = 3 := by
  simp only [lehmerKappa, List.prod_cons, List.prod_nil, List.map_cons, List.map_nil]
  norm_num

/-- **Admissible completions for the Lehmer bounds.** Let $t = (t_1, \dots, t_s)$ be a list of
real numbers and let $r$ be a natural number. The admissible completions of $t$ to length $r$
are the lists $u = (u_1, \dots, u_m)$ of real numbers with $s + m = r$ such that
$t_1, \dots, t_s, u_1, \dots, u_m$ is nondecreasing and $u_j \ge 2$ for every $j$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
def lehmerCompletions (t : List ℝ) (r : ℕ) : Set (List ℝ) :=
  {u | t.length + u.length = r ∧ (t ++ u).Pairwise (· ≤ ·) ∧ ∀ x ∈ u, 2 ≤ x}

/-- **The lower Lehmer bound.** Let $t = (t_1, \dots, t_s)$ be a list of real numbers and let $r$
be a natural number. An admissible completion of $t$ to length $r$ is a list
$u = (u_1, \dots, u_m)$ of real numbers with $s + m = r$ such that
$t_1, \dots, t_s, u_1, \dots, u_m$ is nondecreasing and $u_j \ge 2$ for every $j$. The lower
Lehmer bound $L(t; r)$ is the infimum of $\kappa_r(t_1, \dots, t_s, u_1, \dots, u_m)$ over all
admissible completions $u$ of $t$ to length $r$, where $\kappa_r$ is the Lehmer function. The
infimum is taken to be $0$ when there is no admissible completion or the values are unbounded
below.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
noncomputable def lehmerLower (t : List ℝ) (r : ℕ) : ℝ :=
  sInf ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r)

/-- **Upper Lehmer bound $U(t; r)$.** For real numbers $y_1, \dots, y_r$ let
$\kappa_r(y_1, \dots, y_r) = (y_1 \cdots y_r - 1) / ((y_1 - 1) \cdots (y_r - 1))$, where division
by $0$ gives $0$. For a list $t = (t_1, \dots, t_s)$ of real numbers and a natural number $r$, an
admissible completion of $t$ is a list $u = (u_{s+1}, \dots, u_r)$ of $r - s$ real numbers (there
is none if $s > r$) such that $t_1, \dots, t_s, u_{s+1}, \dots, u_r$ is nondecreasing and
$u_j \ge 2$ for every $j$. Then $U(t; r)$ is the supremum in $\mathbb{R}$ of
$\kappa_r(t_1, \dots, t_s, u_{s+1}, \dots, u_r)$ over all admissible completions $u$ of $t$; by
convention it is $0$ when $t$ has no admissible completion or these values are not bounded above.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
noncomputable def lehmerUpper (t : List ℝ) (r : ℕ) : ℝ :=
  sSup ((fun u => lehmerKappa (t ++ u)) '' lehmerCompletions t r)

/-- **A full-length nondecreasing list has only the empty completion.** Let
$t = (t_1, \dots, t_r)$ be a nondecreasing list of $r$ real numbers. Then the empty list is the
only admissible completion of $t$ to length $r$, that is, the only list $u$ of real numbers such
that $r + |u| = r$, the concatenation of $t$ and $u$ is nondecreasing, and every entry of $u$ is
at least $2$.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9. -/
theorem lehmerCompletions_length {t : List ℝ} (ht : t.Pairwise (· ≤ ·)) :
    lehmerCompletions t t.length = {[]} := by
  ext u
  simp only [lehmerCompletions, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, -, -⟩
    exact List.eq_nil_of_length_eq_zero (by omega)
  · rintro rfl
    simpa using ht

/-- **The Lehmer bounds of a full-length list.** Let $L(t; r)$ and $U(t; r)$ be the lower and
upper Lehmer bounds and $\kappa_r$ the Lehmer function. For every nondecreasing list
$t = (t_1, \dots, t_r)$ of real numbers, $L(t; r) = U(t; r) = \kappa_r(t_1, \dots, t_r)$.

The only admissible completion of such a list to its own length $r$ is the empty list.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Definition 9 and proof of Lemma 3. -/
theorem lehmerLower_upper_length {t : List ℝ} (ht : t.Pairwise (· ≤ ·)) :
    lehmerLower t t.length = lehmerKappa t ∧ lehmerUpper t t.length = lehmerKappa t := by
  simp [lehmerLower, lehmerUpper, lehmerCompletions_length ht]

end

namespace lehmerKappa_antitone_bounds

private theorem one_le_denominator {t : List ℝ} (ht : ∀ x ∈ t, 2 ≤ x) :
    1 ≤ (t.map (· - 1)).prod := by
  apply List.one_le_prod
  intro a ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  linarith [ht x hx]

private theorem denominator_lt_prod {t : List ℝ} (ht : ∀ x ∈ t, 2 ≤ x) (hne : t ≠ []) :
    (t.map (· - 1)).prod < t.prod := by
  simpa using List.prod_map_lt_prod_map hne (· - 1) id
    (fun x hx => by linarith [ht x hx]) (fun x _ => by simp)

/-- The upper bound after clearing its positive denominator. -/
private theorem numerator_le {t : List ℝ} (ht : ∀ x ∈ t, 2 ≤ x) :
    t.prod - 1 ≤ (2 ^ t.length - 1) * (t.map (· - 1)).prod := by
  induction t with
  | nil => simp
  | cons x s ih =>
    obtain ⟨hx, hs⟩ := List.forall_mem_cons.mp ht
    have hden := one_le_denominator hs
    have hpow : 1 ≤ (2 : ℝ) ^ s.length := one_le_pow₀ (by norm_num)
    simp only [List.length_cons, List.prod_cons, List.map_cons, pow_succ]
    calc
      x * s.prod - 1 = x * (s.prod - 1) + (x - 1) := by ring
      _ ≤ x * ((2 ^ s.length - 1) * (s.map (· - 1)).prod) + (x - 1) * (s.map (· - 1)).prod :=
        add_le_add (mul_le_mul_of_nonneg_left (ih hs) (by linarith))
          (le_mul_of_one_le_right (by linarith) hden)
      _ ≤ (2 * (x - 1)) * ((2 ^ s.length - 1) * (s.map (· - 1)).prod) +
          (x - 1) * (s.map (· - 1)).prod := by
        gcongr
        linarith
      _ = _ := by ring

private theorem perm_invariant {s t : List ℝ} (h : s.Perm t) :
    lehmerKappa s = lehmerKappa t := by
  rw [lehmerKappa, lehmerKappa, h.prod_eq, (h.map (· - 1)).prod_eq]

end lehmerKappa_antitone_bounds

open lehmerKappa_antitone_bounds in
/-- **Bounds and monotonicity of the Lehmer function.** For real numbers $t_1, \dots, t_r$ let
$\kappa_r(t_1, \dots, t_r) = (t_1 \cdots t_r - 1) / ((t_1 - 1) \cdots (t_r - 1))$. Let $r \ge 2$
and let $t_1, \dots, t_r \ge 2$ be real numbers. Then
$1 < \kappa_r(t_1, \dots, t_r) \le 2^r - 1$. Moreover, for every index $j$ and every real
$y > t_j$, replacing $t_j$ by $y$ strictly decreases $\kappa_r$, that is,
$\kappa_r(t_1, \dots, t_{j-1}, y, t_{j+1}, \dots, t_r) < \kappa_r(t_1, \dots, t_r)$.

The hypothesis $r \ge 2$ is needed: $\kappa_1(t) = 1$ for every $t \ge 2$, so for $r = 1$ the
lower bound fails and $\kappa_1$ is not strictly decreasing.

Source: Grant Molnar and Guntas Singh, *Spoof Lehmer Factorizations*, INTEGERS 26 (2026),
Article A33, Theorem 5 (`integers-2026-A33-thm-5`). -/
public theorem lehmerKappa_antitone_bounds (r : ℕ) (hr : 2 ≤ r) (t : List ℝ)
    (hlen : t.length = r)
    (ht : ∀ x ∈ t, 2 ≤ x) :
    (1 < lehmerKappa t ∧ lehmerKappa t ≤ 2 ^ r - 1) ∧
      ∀ (j : ℕ) (hj : j < t.length) (y : ℝ), t[j] < y →
        lehmerKappa (t.set j y) < lehmerKappa t := by
  subst r
  have hd := lt_of_lt_of_le zero_lt_one (one_le_denominator ht)
  refine ⟨⟨?_, (div_le_iff₀ hd).2 (numerator_le ht)⟩, ?_⟩
  · cases t with
    | nil => simp at hr
    | cons x s =>
      obtain ⟨hx, hs⟩ := List.forall_mem_cons.mp ht
      have hlt := denominator_lt_prod hs (by rintro rfl; simp at hr)
      have hp := lt_of_le_of_lt (one_le_denominator hs) hlt
      apply (lt_div_iff₀ hd).2
      simp only [one_mul, List.map_cons, List.prod_cons]
      calc
        (x - 1) * (s.map (· - 1)).prod < (x - 1) * s.prod :=
          mul_lt_mul_of_pos_left hlt (by linarith)
        _ < x * s.prod - 1 := by linarith
  · intro j hj y hy
    let s := t.eraseIdx j
    have hs : ∀ x ∈ s, 2 ≤ x := fun x hx => ht x (List.eraseIdx_subset hx)
    have hne : s ≠ [] := by
      apply List.ne_nil_of_length_pos
      rw [List.length_eraseIdx_of_lt hj]
      omega
    have hp := lt_of_le_of_lt (one_le_denominator hs) (denominator_lt_prod hs hne)
    have hx := ht t[j] (List.getElem_mem hj)
    rw [perm_invariant (List.set_perm_cons_eraseIdx hj y),
      ← perm_invariant (List.getElem_cons_eraseIdx_perm hj)]
    change (y * s.prod - 1) / ((y - 1) * (s.map (· - 1)).prod) <
      (t[j] * s.prod - 1) / ((t[j] - 1) * (s.map (· - 1)).prod)
    rw [← div_div, ← div_div]
    apply div_lt_div_of_pos_right _ (lt_of_lt_of_le zero_lt_one (one_le_denominator hs))
    apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
    nlinarith only [mul_pos (sub_pos.mpr hy) (sub_pos.mpr hp)]

end MetaMathlibExt
