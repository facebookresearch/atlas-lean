/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Topology.Instances.Real.Lemmas
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Arithmetic density of ℓ-regular overpartitions (statements)

Statement-only targets from Murugan P and Fathima S. N, *Arithmetic Density of Certain
ℓ-Regular Overpartitions*. `A_ℓ(n)` is `regularOverpartitionCount ℓ n`, counted with the
existing `Nat.Overpartition` structure.
-/

namespace MetaMathlibExt

open scoped Topology

@[expose] public section


/--
**Number of $\ell$-regular overpartitions.** For natural numbers $\ell$ and $n$, $A_\ell(n)$ is
the number of overpartitions of $n$ in which no part is divisible by $\ell$.

No positivity restriction is placed on $\ell$; for $\ell = 0$ every overpartition of $n$ is
counted, since parts are positive.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public noncomputable def regularOverpartitionCount (ℓ n : ℕ) : ℕ :=
  Nat.card {O : Nat.Overpartition n // ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a}

/--
**One $\ell$-regular overpartition of zero.** For every natural number $\ell$, the number
$A_\ell(0)$ of overpartitions of $0$ with no part divisible by $\ell$ equals $1$: the only one is
the empty overpartition.

The statement also covers $\ell = 0$, a harmless extension of the paper's positive regularity
parameter.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public theorem regularOverpartitionCount_zero (ℓ : ℕ) :
    regularOverpartitionCount ℓ 0 = 1 := by
  let O : {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} :=
    ⟨Nat.Overpartition.ofPartition default, by
      intro a ha
      simp [_root_.Nat.Partition.partition_zero_parts] at ha⟩
  let _ : Nonempty {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} := ⟨O⟩
  let _ : Subsingleton {O : Nat.Overpartition 0 //
      ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} :=
    ⟨fun O₁ O₂ => Subtype.ext (Nat.Overpartition.eq_of_zero O₁.1 O₂.1)⟩
  exact Nat.card_unique

/--
**Two $\ell$-regular overpartitions of one.** For every natural number $\ell \ge 2$, the number
$A_\ell(1)$ of overpartitions of $1$ with no part divisible by $\ell$ equals $2$: they are the
single part $1$, without and with an overline.

Among positive $\ell$, the hypothesis $\ell \ge 2$ says exactly that $\ell$ does not divide the
sole part $1$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public theorem regularOverpartitionCount_one (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    regularOverpartitionCount ℓ 1 = 2 := by
  let e :
      {O : Nat.Overpartition 1 //
        ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} ≃ Bool := {
    toFun O := decide (1 ∈ O.1.overlines)
    invFun b :=
      ⟨{
        toPartition := default
        overlines := if b = true then {1} else ∅
        overlines_subset := by
          intro a ha
          rw [_root_.Nat.Partition.partition_one_parts]
          cases b <;> simp_all
      }, by
        intro a ha hdiv
        rw [_root_.Nat.Partition.partition_one_parts] at ha
        have haone : a = 1 := by simpa using ha
        subst a
        have hle : ℓ ≤ 1 := Nat.le_of_dvd (by decide) hdiv
        omega⟩
    left_inv O := by
      apply Subtype.ext
      apply Nat.Overpartition.ext
      · exact Subsingleton.elim _ _
      · have hsub : O.1.overlines ⊆ {1} := by
          intro a ha
          have h := O.1.overlines_subset ha
          rw [_root_.Nat.Partition.partition_one_parts] at h
          simpa using h
        by_cases hmem : 1 ∈ O.1.overlines
        · have hover : O.1.overlines = {1} := by
            apply Finset.Subset.antisymm hsub
            simpa using hmem
          simp [hover]
        · have hover : O.1.overlines = ∅ := by
            apply Finset.Subset.antisymm
            · intro a ha
              have haone : a = 1 := by simpa using hsub ha
              subst a
              exact (hmem ha).elim
            · exact Finset.empty_subset _
          simp [hover]
    right_inv b := by
      cases b <;> simp
  }
  unfold regularOverpartitionCount
  calc
    Nat.card {O : Nat.Overpartition 1 //
        ∀ a ∈ O.toPartition.parts, ¬ ℓ ∣ a} =
        Nat.card Bool := Nat.card_congr e
    _ = 2 := by simp

/--
**Truncated generating function for $\ell$-regular overpartitions.** Let $\ell \ge 1$, $N$ and
$n \le N$ be natural numbers, and let $A_\ell(n)$ be the number of overpartitions of $n$ with no
part divisible by $\ell$. Then the coefficient of $X^n$ in the polynomial
$$\prod_{1 \le k \le N,\ \ell \nmid k} \Big((1 + X^k) \sum_{i=0}^{N} X^{ki}\Big) \in \mathbb{N}[X]$$
equals $A_\ell(n)$.

This is a finite-polynomial form of the generating function
$\sum_{n \ge 0} A_\ell(n) q^n = \prod_{k \ge 1,\ \ell \nmid k} (1 + q^k)/(1 - q^k)$: each
geometric series is cut off at $i = N$, and only coefficients up to degree $N$ are compared.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Identity (1).
-/
public theorem_wanted regularOverpartitionCount_eq_coeff_truncatedProduct
    (ℓ N n : ℕ) (hℓ : 1 ≤ ℓ) (hn : n ≤ N) :
    (∏ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ ℓ ∣ k),
      (((1 : Polynomial ℕ) + Polynomial.X ^ k) *
        ∑ i ∈ Finset.range (N + 1), Polynomial.X ^ (k * i))).coeff n =
      regularOverpartitionCount ℓ n

/--
**$p$-regular overpartitions are almost always divisible by $2^j$.** Let $p$ be an odd prime,
let $j \ge 1$, and let $A_p(n)$ be the number of overpartitions of $n$ with no part divisible by
$p$. Then
$$\lim_{X \to \infty} \frac{\#\{n : 0 \le n \le X,\ 2^j \mid A_p(n)\}}{X} = 1,$$
where $X$ runs over the natural numbers.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 1.
-/
public theorem_wanted regularOverpartition_prime_power_two_density
    (p j : ℕ) (hp : p.Prime) (hpodd : Odd p) (hj : 1 ≤ j) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.range (X + 1)).filter
          (fun n => 2 ^ j ∣ regularOverpartitionCount p n)).card : ℝ) /
          (X : ℝ))
      Filter.atTop (𝓝 1)

/--
**Almost all $3p$-regular overpartition counts are divisible by $2^j$.** Write $A_\ell(m)$ for
the number of overpartitions of $m$ none of whose parts is divisible by $\ell$. Let $p$ be an
odd prime and let $j \ge 1$. Then the number of natural numbers $n$ with $0 \le n \le X$ and
$2^j \mid A_{3p}(n)$, divided by $X$, tends to $1$ as the natural number $X$ tends to infinity.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 2.
-/
public theorem_wanted regularOverpartition_three_mul_prime_power_two_density
    (p j : ℕ) (hp : p.Prime) (hpodd : Odd p) (hj : 1 ≤ j) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.range (X + 1)).filter
          (fun n => 2 ^ j ∣ regularOverpartitionCount (3 * p) n)).card : ℝ) /
          (X : ℝ))
      Filter.atTop (𝓝 1)

/--
**Almost all $3 \cdot 2^\alpha$-regular overpartition counts are divisible by $2^j$.** Write
$A_\ell(m)$ for the number of overpartitions of $m$ none of whose parts is divisible by $\ell$.
Let $\alpha \ge 1$ and $j \ge \alpha + 1$ be natural numbers. Then the number of natural numbers
$n$ with $0 \le n \le X$ and $2^j \mid A_{3 \cdot 2^\alpha}(n)$, divided by $X$, tends to $1$ as
the natural number $X$ tends to infinity.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 3.
-/
public theorem_wanted regularOverpartition_three_mul_two_power_density
    (j α : ℕ) (hα : 1 ≤ α) (hja : α + 1 ≤ j) :
    Filter.Tendsto
      (fun X : ℕ =>
        (((Finset.range (X + 1)).filter
          (fun n =>
            2 ^ j ∣ regularOverpartitionCount (3 * 2 ^ α) n)).card : ℝ) /
          (X : ℝ))
      Filter.atTop (𝓝 1)

/--
**Congruences modulo powers of two for $3 \cdot 2^\alpha$-regular overpartitions.** Write
$A_\ell(m)$ for the number of overpartitions of $m$ none of whose parts is divisible by $\ell$.
For every natural number $\alpha \ge 1$ there is a natural number $c$ with the following
property. Let $d \ge 1$ be a natural number, let $p_1, \dots, p_{c+d}$ be distinct primes, each
coprime to $6$, and let $n$ be a natural number that is divisible by $24$ and coprime to every
$p_i$. Then $A_{3 \cdot 2^\alpha}(p_1 p_2 \cdots p_{c+d} \, n / 24) \equiv 0 \pmod{2^d}$.

The hypothesis that $24$ divides $n$ makes the argument an integer; the paper reads this value
off a series in $q^{24}$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 4.
-/
public theorem_wanted regularOverpartition_three_mul_two_power_many_primes
    (α : ℕ) (hα : 0 < α) :
    ∃ c : ℕ, ∀ (d : ℕ), 1 ≤ d →
      ∀ (ps : Fin (c + d) → ℕ), Function.Injective ps →
        (∀ i, (ps i).Prime) →
        (∀ i, Nat.Coprime (ps i) 6) →
        ∀ n : ℕ, (∀ i, Nat.Coprime n (ps i)) → 24 ∣ n →
          Nat.ModEq (2 ^ d)
            (regularOverpartitionCount (3 * 2 ^ α)
              ((∏ i, ps i) * n / 24))
            0

/--
**$\ell$-regular overpartitions vanish modulo $4$ along families of primes.** For a natural
number $\ell$, let $A_\ell(m)$ be the number of overpartitions of $m$ with no part divisible by
$\ell$. Let $\ell \equiv 3 \pmod 4$, let $k$, $n$ and $j$ be natural numbers, and let
$p_1, \dots, p_{k+1}$ be primes, not necessarily distinct, each greater than $2$ and congruent
to $3$ modulo $4$. If $j \not\equiv 0 \pmod{p_{k+1}}$, then
$$A_\ell\big(p_1^2 \cdots p_k^2 \, p_{k+1} \, (p_{k+1}(4n + 1) + 4j)\big) \equiv 0 \pmod 4.$$

The paper takes $j$ to be an integer; here $j$ is a natural number.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 5.
-/
public theorem_wanted regularOverpartition_mod_four_prime_family
    (ℓ n k j : ℕ) (hℓ : Nat.ModEq 4 ℓ 3)
    (ps : Fin (k + 1) → ℕ)
    (hps : ∀ i, (ps i).Prime ∧ 2 < ps i ∧ Nat.ModEq 4 (ps i) 3)
    (hj : ¬ Nat.ModEq (ps (Fin.last k)) j 0) :
    Nat.ModEq 4
      (regularOverpartitionCount ℓ
        ((∏ i : Fin k, (ps i.castSucc) ^ 2) *
          ps (Fin.last k) *
          (ps (Fin.last k) * (4 * n + 1) + 4 * j)))
      0

/--
**$\ell$-regular overpartitions vanish modulo $4$ along powers of one prime.** For a natural
number $\ell$, let $A_\ell(m)$ be the number of overpartitions of $m$ with no part divisible by
$\ell$. Let $\ell \equiv 3 \pmod 4$, and let $p > 2$ be a prime with $p \not\equiv 1 \pmod 6$.
Then for all natural numbers $k$, $n$ and $j$ with $j \not\equiv 0 \pmod p$,
$$A_\ell\big(p^{2k+2}(4n + 1) + 4j \, p^{2k+1}\big) \equiv 0 \pmod 4.$$

The condition modulo $6$ is the one printed in the paper; it is not replaced by the condition
$p \equiv 3 \pmod 4$ of Theorem 5.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Corollary 1.
-/
public theorem_wanted regularOverpartition_mod_four_single_prime
    (ℓ p k n j : ℕ) (hℓ : Nat.ModEq 4 ℓ 3)
    (hp : p.Prime) (hp2 : 2 < p) (hp6 : ¬ Nat.ModEq 6 p 1)
    (hj : ¬ Nat.ModEq p j 0) :
    Nat.ModEq 4
      (regularOverpartitionCount ℓ
        (p ^ (2 * k + 2) * (4 * n + 1) +
          p ^ (2 * k + 1) * (4 * j)))
      0

/--
**$\ell$-regular overpartitions vanish modulo $4$ on progressions modulo $4\ell$.** For a
natural number $\ell$, let $A_\ell(m)$ be the number of overpartitions of $m$ with no part
divisible by $\ell$. Let $\ell \equiv 3 \pmod 4$, and let $n$ and $j$ be natural numbers with
$j \not\equiv (\ell - 3)/4 \pmod{\ell}$. Then $A_\ell(4\ell n + 4j + 3) \equiv 0 \pmod 4$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 6.
-/
public theorem_wanted regularOverpartition_mod_four_progression
    (ℓ n j : ℕ) (hℓ : Nat.ModEq 4 ℓ 3)
    (hj : ¬ Nat.ModEq ℓ j ((ℓ - 3) / 4)) :
    Nat.ModEq 4
      (regularOverpartitionCount ℓ (4 * ℓ * n + 4 * j + 3))
      0

/--
**Self-similarity modulo 7 of 7-regular overpartition counts.** Write $A_7(m)$ for the number
of overpartitions of $m$ none of whose parts is divisible by $7$. For all natural numbers $n$
and $k$, $A_7(7^{2k}(4n+3)) \equiv A_7(4n+3) \pmod 7$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 7.
-/
public theorem_wanted regularOverpartition_seven_self_similarity
    (n k : ℕ) :
    Nat.ModEq 7
      (regularOverpartitionCount 7 (7 ^ (2 * k) * (4 * n + 3)))
      (regularOverpartitionCount 7 (4 * n + 3))

/--
**Ramanujan-type congruences modulo 7 for 7-regular overpartitions.** Write $A_7(m)$ for the
number of overpartitions of $m$ none of whose parts is divisible by $7$. For every natural number
$n$, we have $A_7(16n+4) \equiv 0 \pmod 7$; $A_7(64n+i) \equiv 0 \pmod 7$ for every natural
number $i < 64$ with $i \equiv 4 \pmod{32}$; $A_7(256n+i) \equiv 0 \pmod 7$ for every natural
number $i < 256$ with $i \equiv 4 \pmod{32}$; and $A_7(1024n+i) \equiv 0 \pmod 7$ for every
natural number $i < 1024$ with $i \equiv 4 \pmod{32}$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Theorem 8.
-/
public theorem_wanted regularOverpartition_seven_ramanujan_congruences
    (n : ℕ) :
    Nat.ModEq 7 (regularOverpartitionCount 7 (16 * n + 4)) 0 ∧
    (∀ i : ℕ, i % 32 = 4 → i < 64 →
      Nat.ModEq 7 (regularOverpartitionCount 7 (64 * n + i)) 0) ∧
    (∀ j : ℕ, j % 32 = 4 → j < 256 →
      Nat.ModEq 7 (regularOverpartitionCount 7 (256 * n + j)) 0) ∧
    (∀ k : ℕ, k % 32 = 4 → k < 1024 →
      Nat.ModEq 7 (regularOverpartitionCount 7 (1024 * n + k)) 0)

/--
**Prime-power congruence for truncated Euler products.** Let $s$ and $t$ be positive integers,
let $p$ be a prime and let $N$ be a natural number. Then every coefficient of the polynomial
$$\Big(\prod_{m=1}^{N} (1 - X^{sm})\Big)^{p^t} - \Big(\prod_{m=1}^{N} (1 - X^{spm})\Big)^{p^{t-1}}$$
in $\mathbb{Z}[X]$ is divisible by $p^t$.

Since the truncated products agree with the infinite products in all degrees up to $N$, letting
$N$ grow gives the congruence of formal power series
$\prod_{m \ge 1} (1 - q^{sm})^{p^t} \equiv \prod_{m \ge 1} (1 - q^{spm})^{p^{t-1}} \pmod{p^t}$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Lemma 1.
-/
public theorem_wanted finiteEulerProduct_primePower_congruence
    (s t p N : ℕ) (hs : 0 < s) (ht : 0 < t) (hp : p.Prime) :
    ∀ r : ℕ, (p : ℤ) ^ t ∣
      ((∏ m ∈ Finset.Icc 1 N,
          ((1 : Polynomial ℤ) - Polynomial.X ^ (s * m))) ^ (p ^ t) -
        (∏ m ∈ Finset.Icc 1 N,
          ((1 : Polynomial ℤ) - Polynomial.X ^ (s * p * m))) ^
            (p ^ (t - 1))).coeff r

/-- **Double coset representatives for $\Gamma_0(N)$.** Let $N$ be a natural number such that
either $N$ is squarefree, or $N$ is even and $N/2$ is squarefree. Write $\Gamma_0(N)$ for the
group of matrices in $\mathrm{SL}_2(\mathbb{Z})$ whose lower left entry is divisible by $N$, and
$T = \begin{pmatrix} 1 & 1 \\ 0 & 1 \end{pmatrix}$. Then for every
$\gamma \in \mathrm{SL}_2(\mathbb{Z})$ there is exactly one natural number $\delta$ dividing $N$
for which there exist $A \in \Gamma_0(N)$ and an integer $h$ with
$$\gamma = A \begin{pmatrix} 1 & 0 \\ \delta & 1 \end{pmatrix} T^h.$$

Equivalently, the matrices $\begin{pmatrix} 1 & 0 \\ \delta & 1 \end{pmatrix}$ with
$\delta \mid N$ form a complete set of representatives, without repetition, of the double cosets
$\Gamma_0(N) \backslash \mathrm{SL}_2(\mathbb{Z}) / \Gamma_\infty$, where $\Gamma_\infty$ is
generated by $T$; adding $-I$ to $\Gamma_\infty$ changes nothing, as $-I \in \Gamma_0(N)$.

Source: Murugan P and Fathima S. N, *Arithmetic Density of Certain ℓ-Regular Overpartitions*,
INTEGERS 25 (2025), Article A3, Lemma 3 (`integers-2025-A3-lem-3`), quoting Wang, Lemma 4.3.
"`N / 2` is squarefree" is read with `2 ∣ N`. -/
public theorem_wanted exists_gamma0_lowerUnipotent_T_zpow_decomposition (N : ℕ)
    (hsq : Squarefree N ∨ (2 ∣ N ∧ Squarefree (N / 2)))
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    ∃! δ : ℕ, δ ∣ N ∧ ∃ A ∈ CongruenceSubgroup.Gamma0 N, ∃ h : ℤ,
      γ = A * ⟨!![1, 0; (δ : ℤ), 1], by simp [Matrix.det_fin_two]⟩ * ModularGroup.T ^ h

end

end MetaMathlibExt
