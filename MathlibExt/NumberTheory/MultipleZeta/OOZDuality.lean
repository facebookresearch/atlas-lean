/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Duality for Ohno–Okuda–Zudilin q-multiple zeta values

OOZ evaluation is invariant under the duality transported from Schlesinger–Zudilin words
by the binomial change of basis.

To check the coefficient of degree `N`, we work modulo `X ^ (N + 1)`. In an SZ word,
a letter `p` multiplies by a geometric series and a letter `y` sums over smaller indices.
These operations are adjoint for the symmetric pairing with kernel `X ^ (m * n)`.
Moving the letters across the pairing reverses the word and exchanges `p` and `y`.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Partial sums of Schlesinger–Zudilin qMZVs.** For an index $(k_1, \dots, k_r)$ of natural
numbers and a natural number $M$, the partial sum is the formal power series in $q$ over
$\mathbb{Q}$
$$\sum_{M > m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{q^{m_j k_j}}{(1 - q^{m_j})^{k_j}},$$
where the sum runs over integers $m_1, \dots, m_r$ and $1/(1 - q^m)$ is the inverse in
$\mathbb{Q}[[q]]$. For the empty index it equals $1$ for every $M$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs (defining sum truncated at
`m₁ < M`). -/
public noncomputable def szQMZVPartial : List ℕ → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | k :: ks, M => ∑ m ∈ Finset.Ioo 0 M, (X ^ m * (1 - X ^ m)⁻¹) ^ k * szQMZVPartial ks m

/-- **Schlesinger–Zudilin qMZVs.** For an index $k = (k_1, \dots, k_r)$ of natural numbers, the
Schlesinger–Zudilin qMZV $\zeta_q^{SZ}(k)$ is the formal power series in $q$ over $\mathbb{Q}$
whose coefficient of $q^N$, for each $N \ge 0$, is the coefficient of $q^N$ in the partial sum
$$\sum_{N \ge m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{q^{m_j k_j}}{(1 - q^{m_j})^{k_j}}$$
over integers $m_1, \dots, m_r$. In particular $\zeta_q^{SZ}(\emptyset) = 1$.

When the index is empty or $k_1 \ge 1$, the summands with $m_1 > N$ have no term of degree at
most $N$, so $\zeta_q^{SZ}(k)$ is the full series
$\sum_{m_1 > \dots > m_r > 0} \prod_{j} q^{m_j k_j} / (1 - q^{m_j})^{k_j}$. The paper does not
define the value when $k_1 = 0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs (extended version of
Ebrahimi-Fard, Manchon and Singer, allowing `kⱼ = 0` for `j ≥ 2`). -/
public noncomputable def szQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N => coeff N (szQMZVPartial k (N + 1))

/-- **The empty Schlesinger–Zudilin qMZV.** The Schlesinger–Zudilin qMZV of the empty index is
$1$: $\zeta_q^{SZ}(\emptyset) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem szQMZV_nil : szQMZV [] = 1 := by
  ext N
  simp [szQMZV, szQMZVPartial]

/-- **Recursion for partial sums of Schlesinger–Zudilin qMZVs.** For natural numbers $k_1$ and
$M$ and an index $\kappa = (k_2, \dots, k_r)$ (possibly empty), write $Z_M(k_1, \kappa)$ and
$Z_m(\kappa)$ for the partial sums of Schlesinger–Zudilin qMZVs with bounds $M$ and $m$. Then
$$Z_M(k_1, \kappa) = \sum_{0 < m < M} \left(\frac{q^m}{1 - q^m}\right)^{k_1} Z_m(\kappa).$$

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem szQMZVPartial_cons (k : ℕ) (ks : List ℕ) (M : ℕ) :
    szQMZVPartial (k :: ks) M =
      ∑ m ∈ Finset.Ioo 0 M, (X ^ m * (1 - X ^ m)⁻¹) ^ k * szQMZVPartial ks m :=
  rfl

/-- **Nonempty Schlesinger–Zudilin qMZVs have no constant term.** For every nonempty index
$(k_1, \dots, k_r)$ of natural numbers, the constant term of the Schlesinger–Zudilin qMZV
$\zeta_q^{\mathrm{SZ}}(k_1, \dots, k_r)$ is $0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem coeff_zero_szQMZV_cons (k : ℕ) (ks : List ℕ) :
    coeff 0 (szQMZV (k :: ks)) = 0 := by
  have h : Finset.Ioo 0 1 = ∅ := by decide
  simp [szQMZV, szQMZVPartial, h]

/-- **The coefficient of $q$ in $\zeta_q^{\mathrm{SZ}}(1)$.** The coefficient of $q$ in the
Schlesinger–Zudilin qMZV $\zeta_q^{\mathrm{SZ}}(1) = \sum_{m > 0} q^m / (1 - q^m)$ is $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem coeff_one_szQMZV_singleton_one : coeff 1 (szQMZV [1]) = 1 := by
  have h : Finset.Ioo 0 2 = {1} := by decide
  simp [szQMZV, szQMZVPartial, h, coeff_succ_X_mul, constantCoeff_inv]

/-- **Partial Ohno–Okuda–Zudilin sums.** For an index $(k_1, \dots, k_r)$ of natural numbers and a
natural number $M$, the partial OOZ sum is the formal power series in $q$ over $\mathbb{Q}$
$$\sum_{M > m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{1}{(1 - q^{m_j})^{k_j}},$$
the defining sum of $\zeta_q^{\mathrm{OOZ}}(k_1, \dots, k_r)$ with the factor $q^{m_1}$ removed and
truncated to $m_1 < M$. For the empty index it is $1$, for every $M$ (including $M = 0$).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs (inner sums of the defining series). -/
public noncomputable def oozQMZVPartial : List ℕ → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | k :: ks, M => ∑ m ∈ Finset.Ioo 0 M, ((1 - X ^ m)⁻¹) ^ k * oozQMZVPartial ks m

/-- **Ohno–Okuda–Zudilin q-multiple zeta values.** For an index $(k_1, \dots, k_r)$ of natural
numbers with $r \ge 1$, the (extended) Ohno–Okuda–Zudilin qMZV is the formal power series in $q$
over $\mathbb{Q}$
$$\zeta_q^{\mathrm{OOZ}}(k_1, \dots, k_r) = \sum_{m_1 > \dots > m_r > 0}
\frac{q^{m_1}}{(1 - q^{m_1})^{k_1} \cdots (1 - q^{m_r})^{k_r}},$$
and $\zeta_q^{\mathrm{OOZ}}(\varnothing) = 1$ for the empty index. The summands with $m_1 > N$
have $q$-adic order greater than $N$, so the coefficient of $q^N$ is computed from the finitely
many summands with $m_1 \le N$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs (extended version, `k₁ ≥ 1`, `kᵢ ≥ 0`). -/
public noncomputable def oozQMZV : List ℕ → ℚ⟦X⟧
  | [] => 1
  | k :: ks => PowerSeries.mk fun N =>
      coeff N (∑ m ∈ Finset.Ioo 0 (N + 1), X ^ m * ((1 - X ^ m)⁻¹) ^ k * oozQMZVPartial ks m)

/-- **The OOZ-qMZV of the empty index.** The Ohno–Okuda–Zudilin qMZV of the empty index is $1$:
$\zeta_q^{\mathrm{OOZ}}(\varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs. -/
public theorem oozQMZV_nil : oozQMZV [] = 1 := rfl

/-- **Nonempty Ohno–Okuda–Zudilin qMZVs have no constant term.** For every nonempty index
$(k_1, \dots, k_r)$ of natural numbers, the constant term of the Ohno–Okuda–Zudilin qMZV
$\zeta_q^{\mathrm{OOZ}}(k_1, \dots, k_r)$ is $0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs. -/
public theorem coeff_zero_oozQMZV_cons (k : ℕ) (ks : List ℕ) :
    coeff 0 (oozQMZV (k :: ks)) = 0 := by
  have h : Finset.Ioo 0 1 = ∅ := by decide
  simp [oozQMZV, h]

/-- **Word of an index.** The word of an index $(k_1, \dots, k_r)$ of natural numbers is the word
$p^{k_1} y \cdots p^{k_r} y$ in the letters $p$ and $y$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public def szWord (k : List ℕ) : List Bool :=
  (k.map fun n => List.replicate n true ++ [false]).flatten

/-- **Word of the empty index.** The word of the empty index is the empty word.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public theorem szWord_nil : szWord [] = [] := rfl

/-- **Reading an index off a word in $p$ and $y$.** For $c \in \mathbb{N}$ and a word $w$ in the
letters $p$ and $y$, the index $R_c(w)$, a finite sequence of natural numbers, is defined
recursively by $R_c(\mathbf{1}) = ()$ for the empty word $\mathbf{1}$, $R_c(p w) = R_{c+1}(w)$,
and $R_c(y w) = (c, R_0(w))$, the index with first entry $c$ followed by the entries of
$R_0(w)$. Thus $R_c(p^{k_1} y\, p^{k_2} y \cdots p^{k_r} y\, p^j) = (c + k_1, k_2, \dots, k_r)$
for $r \ge 1$ and $R_c(p^j) = ()$: the entries are the lengths of the blocks of $p$s before
each $y$, with $c$ added to the first, and trailing $p$s are dropped.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public def szIndexOfWordAux : ℕ → List Bool → List ℕ
  | _, [] => []
  | c, true :: w => szIndexOfWordAux (c + 1) w
  | c, false :: w => c :: szIndexOfWordAux 0 w

/-- **Reading off a leading block of $p$s.** Write $R_c(w)$ for the index read off a word $w$ in
the letters $p$ and $y$ when $c$ letters $p$ have already been read. For all $c, n \in \mathbb{N}$
and every word $w$, $R_c(p^n y w)$ is the index whose first entry is $c + n$ and whose remaining
entries are those of $R_0(w)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public theorem szIndexOfWordAux_replicate_append (c n : ℕ) (w : List Bool) :
    szIndexOfWordAux c (List.replicate n true ++ false :: w) = (c + n) :: szIndexOfWordAux 0 w := by
  induction n generalizing c with
  | zero => simp [szIndexOfWordAux]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, szIndexOfWordAux, ih]
    congr 1
    omega

/-- **The SZ dual index.** Identify an index $k = (k_1, \dots, k_r)$ of natural numbers with the
word $p^{k_1} y \cdots p^{k_r} y$ in the letters $p$ and $y$, and let $\tilde\tau$ be the
anti-automorphism of words with $\tilde\tau(p) = y$ and $\tilde\tau(y) = p$ (reverse the word and
swap the letters). Write $\tilde\tau(p^{k_1} y \cdots p^{k_r} y)$ as $p^{a_1} y \cdots p^{a_s} y$
followed by a possibly empty run of letters $p$ (nonempty only when $k_1 = 0$); that run is
dropped, and the SZ dual index is $k^\dagger = (a_1, \dots, a_s)$.

For $k = (k_1, \{0\}^{d_1 - 1}, \dots, k_r, \{0\}^{d_r - 1})$ with all $k_i, d_i \ge 1$, where
$\{0\}^m$ stands for $m$ zeros, this gives
$k^\dagger = (d_r, \{0\}^{k_r - 1}, \dots, d_1, \{0\}^{k_1 - 1})$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 5 (SZ duality, the map `τ̃` and the SZ dual index). -/
public def szDualIndex (k : List ℕ) : List ℕ :=
  szIndexOfWordAux 0 ((szWord k).reverse.map not)

/-- **The SZ dual of $(2)$.** The SZ dual index of the one-entry index $(2)$ is $(1, 0)$, that
is, $(2)^\dagger = (1, 0)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 5 (SZ dual index). -/
public theorem szDualIndex_two : szDualIndex [2] = [1, 0] := by decide

/-- **The tail part of the map $V$.** Identify an index $(k_1, \dots, k_s)$ of natural numbers
with the word $p^{k_1} y \cdots p^{k_s} y$ in the letters $p$ and $y$. This map sends the empty
word to itself and, for $s \ge 1$, sends $p^{k_1} y \cdots p^{k_s} y$ to the formal
$\mathbb{Q}$-linear combination of words
$$\sum \binom{k_1}{n_1} \cdots \binom{k_s}{n_s} \, p^{n_1} y \cdots p^{n_s} y$$
over $0 \le n_j \le k_j$ for $1 \le j \le s$. The map $V$ from OOZ to SZ words applies it to the
blocks $p^{k_j} y$ after the first.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (after Ebrahimi-Fard, Manchon and Singer, the map `V`). -/
public noncomputable def oozToSZTail : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | b :: k => ∑ n ∈ Finset.range (b + 1),
      ((b.choose n : ℕ) : ℚ) • (oozToSZTail k).mapDomain (List.cons n)

/-- **The map $V$ from OOZ to SZ words.** Identify an index $(k_1, \dots, k_r)$ of natural
numbers with the word $p^{k_1} y \cdots p^{k_r} y$ in the letters $p$ and $y$. The map $V$ sends
each such word to a formal $\mathbb{Q}$-linear combination of words: $V(\mathbf{1}) = \mathbf{1}$
for the empty word $\mathbf{1}$, and for $r \ge 1$
$$V(p^{k_1} y \cdots p^{k_r} y) = \sum \binom{k_1 - 1}{n_1 - 1} \binom{k_2}{n_2} \cdots
\binom{k_r}{n_r} \, p^{n_1} y \cdots p^{n_r} y$$
where the sum runs over $1 \le n_1 \le k_1$ and $0 \le n_j \le k_j$ for $2 \le j \le r$ (an empty
sum is $0$).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (after Ebrahimi-Fard, Manchon and Singer, the map `V`). -/
public noncomputable def oozToSZ : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | a :: k => ∑ n ∈ Finset.Icc 1 a,
      (((a - 1).choose (n - 1) : ℕ) : ℚ) • (oozToSZTail k).mapDomain (List.cons n)

/-- **The map $V$ fixes $py$.** The map $V$ from OOZ to SZ words sends the word $py$ (the index
$(1)$) to itself with coefficient $1$: $V(py) = py$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii). -/
public theorem oozToSZ_one : oozToSZ [1] = Finsupp.single [1] 1 := by
  simp [oozToSZ, oozToSZTail]

end

namespace sum_oozQMZV_eq_of_oozToSZ_eq_szDual

open Finset
noncomputable section

private abbrev Truncation (N : ℕ) := ℚ⟦X⟧ ⧸ Ideal.span {(X : ℚ⟦X⟧) ^ (N + 1)}

private abbrev residue (N : ℕ) : ℚ⟦X⟧ →+* Truncation N := Ideal.Quotient.mk _

private abbrev geom (m : ℕ) : ℚ⟦X⟧ := X ^ m * (1 - X ^ m)⁻¹

private lemma unit_factor {m : ℕ} (hm : 0 < m) :
    (1 - X ^ m : ℚ⟦X⟧) * (1 - X ^ m)⁻¹ = 1 := by
  apply PowerSeries.mul_inv_cancel
  simp [hm.ne']

-- Modulo X^(N+1), the tail of the geometric series is a finite sum.
private lemma kernel_tail (N m n : ℕ) (hm : 0 < m) (hn : n ≤ N) :
    (∑ j ∈ Ico (n + 1) (N + 1), residue N (X ^ (m * j))) =
      residue N (X ^ (m * n) * geom m) := by
  let x := residue N (X ^ m)
  have hnil : x ^ (N + 1) = 0 := by
    rw [← map_pow, ← pow_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    apply pow_dvd_pow
    exact Nat.le_mul_of_pos_left _ hm
  have hunit := congrArg (residue N) (unit_factor hm)
  simp only [map_mul, map_sub, map_one] at hunit
  simp only [pow_mul, map_mul, map_pow, geom]
  change (∑ j ∈ Ico (n + 1) (N + 1), x ^ j) = x ^ n * (x * _)
  calc
    _ = (∑ j ∈ Ico (n + 1) (N + 1), x ^ j) *
          ((1 - x) * residue N ((1 - X ^ m)⁻¹)) := by rw [hunit, mul_one]
    _ = _ := by
      rw [← mul_assoc, geom_sum_Ico_mul_neg _ (by omega), hnil, sub_zero, pow_succ x n, mul_assoc]

private def letter (N : ℕ) : Bool → (ℕ → Truncation N) → ℕ → Truncation N
  | true, f, m => residue N (geom m) * f m
  | false, f, m => ∑ j ∈ Ico 1 m, f j

private def act (N : ℕ) (w : List Bool) (f : ℕ → Truncation N) : ℕ → Truncation N :=
  w.foldr (letter N) f

private def pairing (N : ℕ) (f g : ℕ → Truncation N) : Truncation N :=
  ∑ m ∈ Ico 1 (N + 1), ∑ n ∈ Ico 1 (N + 1), residue N (X ^ (m * n)) * f m * g n

private lemma pairing_comm (N : ℕ) (f g : ℕ → Truncation N) :
    pairing N f g = pairing N g f := by
  unfold pairing
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  apply sum_congr rfl
  intro m _
  rw [Nat.mul_comm m n]
  ring

private lemma pairing_true (N : ℕ) (f g : ℕ → Truncation N) :
    pairing N (letter N true f) g = pairing N f (letter N false g) := by
  apply sum_congr rfl
  intro m hm
  change (∑ n ∈ _, residue N (X ^ (m * n)) * (residue N (geom m) * f m) * g n) =
    ∑ j ∈ _, residue N (X ^ (m * j)) * f m * ∑ n ∈ Ico 1 j, g n
  simp_rw [mul_sum]
  rw [← sum_Ico_Ico_comm']
  apply sum_congr rfl
  intro n hn
  rw [← sum_mul, ← sum_mul, kernel_tail N m n (mem_Ico.mp hm).1 (by
    have := (mem_Ico.mp hn).2
    omega)]
  simp only [map_mul]
  ac_rfl

private lemma pairing_letter (N : ℕ) (b : Bool) (f g : ℕ → Truncation N) :
    pairing N (letter N b f) g = pairing N f (letter N (!b) g) := by
  cases b
  · exact (pairing_comm N _ _).trans ((pairing_true N g f).symm.trans (pairing_comm N _ _))
  · exact pairing_true N f g

private lemma pairing_act (N : ℕ) (w : List Bool) (f g : ℕ → Truncation N) :
    pairing N (act N w f) g = pairing N f (act N (w.reverse.map (!·)) g) := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih =>
    simpa [act, List.foldr_append] using (pairing_letter N b (act N w f) g).trans (ih _)

private lemma word_cons (a : ℕ) (ks : List ℕ) :
    szWord (a :: ks) = List.replicate a true ++ false :: szWord ks := by
  simp [szWord]

private lemma decode_word (k : List ℕ) : szIndexOfWordAux 0 (szWord k) = k := by
  induction k with
  | nil => rfl
  | cons a ks ih => simp [word_cons, szIndexOfWordAux_replicate_append, ih]

private lemma word_ends (ks : List ℕ) : ∃ u, false :: szWord ks = u ++ [false] := by
  induction ks with
  | nil => exact ⟨[], rfl⟩
  | cons a ks ih =>
    obtain ⟨u, hu⟩ := ih
    exact ⟨false :: (List.replicate a true ++ u), by simp [word_cons, hu, List.append_assoc]⟩

private lemma partial_decode (N c : ℕ) (u : List Bool) (M : ℕ) :
    residue N (szQMZVPartial (szIndexOfWordAux c (u ++ [false])) M) =
      ∑ m ∈ Ico 1 M, residue N (geom m) ^ c * act N u (fun _ => 1) m := by
  have hI (b : ℕ) : Ioo 0 b = Ico 1 b := by ext; simp; omega
  induction u generalizing c M with
  | nil => simp [szIndexOfWordAux, szQMZVPartial, hI, act]
  | cons b u ih =>
    cases b
    · simp only [List.cons_append, szIndexOfWordAux, szQMZVPartial, hI, map_sum, map_mul,
        map_pow, ih, pow_zero, one_mul]
      rfl
    · simpa [szIndexOfWordAux, act, letter, pow_succ, mul_assoc] using ih (c + 1) M

-- The outer letters in p u y supply the two boundary vectors of the pairing.
private lemma partial_word (N : ℕ) (u : List Bool) :
    residue N (szQMZVPartial (szIndexOfWordAux 0 (true :: (u ++ [false]))) (N + 1)) =
      pairing N (act N u (fun _ => 1)) (fun _ => 1) := by
  rw [szIndexOfWordAux, partial_decode]
  apply sum_congr rfl
  intro m hm
  simp only [Nat.zero_add, pow_one, mul_one, ← sum_mul]
  congr 1
  simpa using (kernel_tail N m 0 (mem_Ico.mp hm).1 (Nat.zero_le N)).symm

private lemma dual_value (k : List ℕ) (hk : ∀ a ∈ k.head?, 1 ≤ a) :
    szQMZV (szDualIndex k) = szQMZV k := by
  cases k with
  | nil => rfl
  | cons a ks =>
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := by
      have := hk a (by simp)
      exact ⟨a - 1, by omega⟩
    obtain ⟨u, hu⟩ := word_ends ks
    let v := List.replicate b true ++ u
    have hv : szWord ((b + 1) :: ks) = true :: (v ++ [false]) := by
      simp [word_cons, List.replicate_succ, hu, v, List.append_assoc]
    have hr : szDualIndex ((b + 1) :: ks) =
        szIndexOfWordAux 0 (true :: (v.reverse.map (!·) ++ [false])) := by
      simp [szDualIndex, hv]
    have hv_decode := decode_word ((b + 1) :: ks)
    rw [hv] at hv_decode
    ext N
    simp only [szQMZV, coeff_mk]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (X_pow_dvd_iff.mp _ N (Nat.lt_succ_self N))
    apply Ideal.mem_span_singleton.mp
    apply (Ideal.Quotient.eq_zero_iff_mem (I := Ideal.span {(X : ℚ⟦X⟧) ^ (N + 1)})).mp
    change residue N (_ - _) = 0
    rw [map_sub, sub_eq_zero, hr, partial_word, ← hv_decode, partial_word]
    exact (pairing_comm N _ _).trans (pairing_act N v _ _).symm

-- The inverse denominator is 1 + geom m. The first block has an extra factor of geom m.
private lemma binomial_tail (b m : ℕ) (hm : 0 < m) :
    ∑ n ∈ range (b + 1), (b.choose n : ℚ) • geom m ^ n = ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) ^ b := by
  have h : geom m + 1 = (1 - X ^ m : ℚ⟦X⟧)⁻¹ := by
    linear_combination -(unit_factor hm)
  rw [← h, add_pow]
  apply sum_congr rfl
  intro n _
  simp [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]

private lemma binomial_head (b m : ℕ) (hm : 0 < m) :
    ∑ n ∈ Icc 1 (b + 1), (b.choose (n - 1) : ℚ) • geom m ^ n =
      X ^ m * ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) ^ (b + 1) := by
  have hs : Icc 1 (b + 1) = Ico 1 (b + 2) := by ext; simp; omega
  rw [hs, sum_Ico_eq_sum_range]
  simp only [Nat.reduceSubDiff, Nat.add_comm 1, Nat.add_sub_cancel,
    pow_succ (geom m), ← smul_mul_assoc, ← sum_mul]
  rw [binomial_tail b m hm, pow_succ]
  unfold geom
  ring

private lemma eval_cons (n M : ℕ) (t : List ℕ →₀ ℚ) :
    Finsupp.linearCombination ℚ ((fun w => szQMZVPartial w M) ∘ List.cons n) t =
      ∑ m ∈ Ioo 0 M, geom m ^ n *
        Finsupp.linearCombination ℚ (fun w => szQMZVPartial w m) t := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Function.comp_apply, szQMZVPartial,
    smul_sum, mul_sum, mul_smul_comm, geom]
  rw [sum_comm]

private lemma eval_blocks (s : Finset ℕ) (c : ℕ → ℚ) (t : List ℕ →₀ ℚ) (M : ℕ) :
    Finsupp.linearCombination ℚ (fun w => szQMZVPartial w M)
        (∑ n ∈ s, c n • t.mapDomain (List.cons n)) =
      ∑ m ∈ Ioo 0 M, (∑ n ∈ s, c n • geom m ^ n) *
        Finsupp.linearCombination ℚ (fun w => szQMZVPartial w m) t := by
  simp only [map_sum, map_smul, Finsupp.linearCombination_mapDomain, eval_cons,
    smul_sum, sum_mul, smul_mul_assoc]
  rw [sum_comm]

private lemma eval_tail (ks : List ℕ) (M : ℕ) :
    Finsupp.linearCombination ℚ (fun w => szQMZVPartial w M) (oozToSZTail ks) =
      oozQMZVPartial ks M := by
  induction ks generalizing M with
  | nil => simp [oozToSZTail, szQMZVPartial, oozQMZVPartial]
  | cons b ks ih =>
    rw [oozToSZTail, eval_blocks, oozQMZVPartial]
    apply sum_congr rfl
    intro m hm
    rw [binomial_tail b m (mem_Ioo.mp hm).1, ih]

private lemma conversion (k : List ℕ) (hk : ∀ a ∈ k.head?, 1 ≤ a) :
    Finsupp.linearCombination ℚ szQMZV (oozToSZ k) = oozQMZV k := by
  cases k with
  | nil => simp [oozToSZ, szQMZV_nil, oozQMZV_nil]
  | cons a ks =>
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := by
      have := hk a (by simp)
      exact ⟨a - 1, by omega⟩
    ext N
    have h (z : List ℕ →₀ ℚ) :
        coeff N (Finsupp.linearCombination ℚ szQMZV z) =
          coeff N (Finsupp.linearCombination ℚ (fun w => szQMZVPartial w (N + 1)) z) := by
      simp [Finsupp.linearCombination_apply, Finsupp.sum, szQMZV]
    rw [h, oozQMZV, coeff_mk, oozToSZ, eval_blocks]
    congr 1
    apply sum_congr rfl
    intro m hm
    simp only [Nat.add_sub_cancel, binomial_head b m (mem_Ioo.mp hm).1, eval_tail]

private lemma eval_dual_image (w : List ℕ) :
    Finsupp.linearCombination ℚ szQMZV ((oozToSZ w).mapDomain szDualIndex) =
      Finsupp.linearCombination ℚ szQMZV (oozToSZ w) := by
  rw [Finsupp.linearCombination_mapDomain]
  cases w with
  | nil => simp [oozToSZ, szDualIndex, szWord, szIndexOfWordAux]
  | cons a ks =>
    simp only [oozToSZ, map_sum, map_smul, Finsupp.linearCombination_mapDomain]
    apply sum_congr rfl
    intro n hn
    congr 3
    funext v
    exact dual_value (n :: v) (by simpa using (mem_Icc.mp hn).1)

end

end sum_oozQMZV_eq_of_oozToSZ_eq_szDual

open sum_oozQMZV_eq_of_oozToSZ_eq_szDual

/-- **Duality for OOZ-qMZVs.** Call an index $(k_1, \dots, k_r)$ of natural numbers SZ-admissible
if it is empty or $k_1 \ge 1$. Extend $\zeta_q^{\mathrm{OOZ}}$ and the map $V$ linearly to formal
$\mathbb{Q}$-linear combinations of indices, and let $\tilde\tau$ act on such a combination by
replacing each index with its SZ dual index. Let $w$ be an SZ-admissible index and let $x$ be a
$\mathbb{Q}$-linear combination of SZ-admissible indices with $V(x) = \tilde\tau(V(w))$. Then
$\zeta_q^{\mathrm{OOZ}}(x) = \zeta_q^{\mathrm{OOZ}}(w)$.

Since $V$ is a bijection on combinations of SZ-admissible indices (Proposition 12 (ii) of the
source), this is the identity
$\zeta_q^{\mathrm{OOZ}} = \zeta_q^{\mathrm{OOZ}} \circ V^{-1} \circ \tilde\tau \circ V$ on
SZ-admissible indices.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (ii) (after Ebrahimi-Fard, Manchon and Singer) (`integers-2024-A6-thm-17`). -/
public theorem sum_oozQMZV_eq_of_oozToSZ_eq_szDual (w : List ℕ)
    (hw₁ : ∀ a ∈ w.head?, 1 ≤ a) (x : List ℕ →₀ ℚ)
    (hx : x ∈ Finsupp.supported ℚ ℚ {v : List ℕ | ∀ a ∈ v.head?, 1 ≤ a})
    (hVx : Finsupp.linearCombination ℚ oozToSZ x = (oozToSZ w).mapDomain szDualIndex) :
    (x.sum fun v c => c • oozQMZV v) = oozQMZV w := by
  let Z := Finsupp.linearCombination ℚ szQMZV
  calc
    _ = Finsupp.linearCombination ℚ (Z ∘ oozToSZ) x := by
      apply Finset.sum_congr rfl
      intro v hv
      change x v • oozQMZV v = x v • Finsupp.linearCombination ℚ szQMZV (oozToSZ v)
      rw [conversion v ((Finsupp.mem_supported ℚ x).mp hx hv)]
    _ = Z (Finsupp.linearCombination ℚ oozToSZ x) :=
      (Finsupp.apply_linearCombination ℚ Z oozToSZ x).symm
    _ = _ := by
      rw [hVx]
      exact (eval_dual_image w).trans (conversion w hw₁)

section Partitions

open Finset

-- At positive depth there are not enough possible sizes if the depth exceeds the bound.
private lemma partial_replicate_one_eq_zero {r M : ℕ} (h : M < r) :
    szQMZVPartial (List.replicate r 1) (M + 1) = 0 := by
  induction r generalizing M with
  | zero => omega
  | succ r ih =>
    rw [List.replicate_succ, szQMZVPartial_cons]
    apply sum_eq_zero
    intro m hm
    obtain ⟨hm₀, hmM⟩ := mem_Ioo.mp hm
    obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm₀.ne'
    rw [ih (by omega), mul_zero]

-- A new largest size `M + 1` can be skipped, or used with positive multiplicity.
private lemma partial_replicate_one_succ_bound (r M : ℕ) :
    szQMZVPartial (List.replicate (r + 1) 1) (M + 2) =
      szQMZVPartial (List.replicate (r + 1) 1) (M + 1) +
        geom (M + 1) * szQMZVPartial (List.replicate r 1) (M + 1) := by
  have hI : Ioo 0 (M + 2) = insert (M + 1) (Ioo 0 (M + 1)) := by
    ext m
    simp only [mem_Ioo, mem_insert]
    omega
  simp only [List.replicate_succ, szQMZVPartial_cons, hI, pow_one]
  rw [sum_insert (by simp), add_comm]

private lemma sum_partial_replicate_one (M : ℕ) :
    (∑ r ∈ range (M + 1), szQMZVPartial (List.replicate r 1) (M + 1)) =
      ∏ m ∈ Icc 1 M, (1 + geom m) := by
  induction M with
  | zero => simp [szQMZVPartial]
  | succ M ih =>
    have hI : Icc 1 (M + 1) = insert (M + 1) (Icc 1 M) := by
      ext m
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, prod_insert (by simp), add_mul, one_mul, ← ih]
    rw [sum_range_succ' (fun r => szQMZVPartial (List.replicate r 1) (M + 2)) (M + 1)]
    simp_rw [partial_replicate_one_succ_bound, sum_add_distrib, ← mul_sum]
    have hnil : szQMZVPartial (List.replicate 0 1) (M + 2) =
        szQMZVPartial (List.replicate 0 1) (M + 1) := rfl
    rw [add_right_comm, hnil,
      ← sum_range_succ' (fun r => szQMZVPartial (List.replicate r 1) (M + 1)) (M + 1),
      sum_range_succ (fun r => szQMZVPartial (List.replicate r 1) (M + 1)) (M + 1),
      partial_replicate_one_eq_zero (Nat.lt_succ_self M), add_zero]

-- The coefficient is one precisely when a nonnegative multiplicity of size `m` gives degree `d`.
private lemma coeff_one_add_geom {m : ℕ} (hm : 0 < m) (d : ℕ) :
    coeff d (1 + geom m) = if m ∣ d then 1 else 0 := by
  let g : ℚ⟦X⟧ := PowerSeries.mk fun n => if m ∣ n then 1 else 0
  have hg : (1 - X ^ m) * g = 1 := by
    ext n
    rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_one]
    by_cases hn : m ≤ n
    · have hd : m ∣ n - m ↔ m ∣ n := by
        constructor
        · intro h
          simpa [Nat.sub_add_cancel hn] using Nat.dvd_add h (dvd_refl m)
        · exact fun h => Nat.dvd_sub h (dvd_refl m)
      simp [hn, hd, g, show n ≠ 0 by omega]
    · obtain rfl | hn₀ := Nat.eq_zero_or_pos n
      · simp [g, hm.ne']
      · have hd : ¬ m ∣ n := fun h => hn (Nat.le_of_dvd hn₀ h)
        simp [hn, hd, g, hn₀.ne']
  have hgeom : (1 - X ^ m) * (1 + geom m) = 1 := by
    unfold geom
    linear_combination (X ^ m : ℚ⟦X⟧) * unit_factor hm
  have hunit : IsUnit (1 - X ^ m : ℚ⟦X⟧) := IsUnit.of_mul_eq_one _ (unit_factor hm)
  rw [hunit.mul_left_cancel (hgeom.trans hg.symm)]
  exact coeff_mk _ _

-- Divide the degree allocated to each size by that size to recover its multiplicity.
private lemma exists_partition_of_weights {N : ℕ} {w : ℕ →₀ ℕ}
    (hw : w ∈ (Icc 1 N).finsuppAntidiag N) (hd : ∀ i ∈ Icc 1 N, i ∣ w i) :
    ∃ p : N.Partition, p.toFinsuppAntidiag = w := by
  obtain ⟨hsum, hsupport⟩ := mem_finsuppAntidiag.mp hw
  let c : ℕ →₀ ℕ := Finsupp.onFinset (Icc 1 N) (fun i => w i / i) (by
    intro i hi
    apply hsupport
    exact Finsupp.mem_support_iff.mpr (fun h => hi (by simp [h])))
  have hc (i : ℕ) : c i * i = w i := by
    change w i / i * i = w i
    by_cases hi : i ∈ Icc 1 N
    · exact Nat.div_mul_cancel (hd i hi)
    · rw [Finsupp.notMem_support_iff.mp (fun h => hi (hsupport h)), Nat.zero_div, zero_mul]
  have hc_support : c.support ⊆ Icc 1 N := Finsupp.support_onFinset_subset
  have hsum_c : c.toMultiset.sum = N := by
    rw [Finsupp.sum_toMultiset, Finsupp.sum, ← hsum]
    refine (sum_subset hc_support (fun i _ hi => ?_)).trans ?_
    · rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
    · exact sum_congr rfl (fun i _ => by simpa only [nsmul_eq_mul, Nat.cast_id] using hc i)
  let p : N.Partition := ⟨c.toMultiset, fun {i} hi =>
    (mem_Icc.mp (hc_support ((Finsupp.mem_toMultiset c i).mp hi))).1, hsum_c⟩
  refine ⟨p, Finsupp.ext fun i => ?_⟩
  change c.toMultiset.count i * i = w i
  rw [Finsupp.count_toMultiset, hc]

private lemma coeff_prod_one_add_geom (N : ℕ) :
    coeff N (∏ m ∈ Icc 1 N, (1 + geom m)) = (Fintype.card N.Partition : ℚ) := by
  classical
  have hcard : (∑ _p : N.Partition, (1 : ℚ)) = (Fintype.card N.Partition : ℚ) := by simp
  rw [coeff_prod, ← hcard]
  refine (sum_of_injOn Nat.Partition.toFinsuppAntidiag
    (Nat.Partition.toFinsuppAntidiag_injective N).injOn ?_ ?_ ?_).symm
  · exact fun p _ => p.toFinsuppAntidiag_mem_finsuppAntidiag
  · intro w hw hnot
    have h : ¬ ∀ m ∈ Icc 1 N, m ∣ w m := by
      intro hd
      obtain ⟨p, hp⟩ := exists_partition_of_weights hw hd
      exact hnot ⟨p, mem_univ _, hp⟩
    push Not at h
    obtain ⟨m, hm, hd⟩ := h
    exact prod_eq_zero hm (by rw [coeff_one_add_geom (mem_Icc.mp hm).1, ite_eq_right hd])
  · intro p _
    symm
    apply prod_eq_one
    intro m hm
    rw [coeff_one_add_geom (mem_Icc.mp hm).1, ite_eq_left]
    exact ⟨p.parts.count m, Nat.mul_comm _ _⟩

/-- **Partitions from Schlesinger–Zudilin qMZVs.** Let $\zeta_q^{SZ}$ denote the
Schlesinger–Zudilin qMZV, $\{1\}^r$ the index of $r$ ones and $p(N)$ the number of
partitions of $N$. For all natural numbers $N \ge 1$ and $R \ge N$, the coefficient of $q^N$ in
$\sum_{r=1}^{R} \zeta_q^{SZ}(\{1\}^r)$ equals $p(N)$.

Since the summands with $r > N$ have no $q^N$ term, this is the coefficientwise form of
$\sum_{r \ge 1} \zeta_q^{SZ}(\{1\}^r) = \sum_{N \ge 1} p(N) q^N$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 3 (`integers-2024-A6-lem-3`). -/
public theorem sum_coeff_szQMZV_replicate_one_eq_card_partition (N R : ℕ)
    (hN : 1 ≤ N) (hR : N ≤ R) :
    ∑ r ∈ Finset.Icc 1 R, coeff N (szQMZV (List.replicate r 1)) =
      Fintype.card N.Partition := by
  simp only [szQMZV, coeff_mk]
  calc
    _ = ∑ r ∈ Icc 1 N, coeff N (szQMZVPartial (List.replicate r 1) (N + 1)) := by
      symm
      refine sum_subset (fun r hr => mem_Icc.mpr ⟨(mem_Icc.mp hr).1, (mem_Icc.mp hr).2.trans hR⟩) ?_
      intro r hr hrN
      have hNr : N < r := by
        simp only [mem_Icc] at hr hrN
        omega
      rw [partial_replicate_one_eq_zero hNr, map_zero]
    _ = ∑ r ∈ range (N + 1), coeff N (szQMZVPartial (List.replicate r 1) (N + 1)) := by
      have hI : Icc 1 N = (range (N + 1)).erase 0 := by
        ext r
        simp only [mem_Icc, mem_erase, mem_range]
        omega
      rw [hI]
      apply sum_erase
      simp [szQMZVPartial, coeff_one, show N ≠ 0 by omega]
    _ = _ := by rw [← map_sum, sum_partial_replicate_one, coeff_prod_one_add_geom]

end Partitions

end MetaMathlibExt
