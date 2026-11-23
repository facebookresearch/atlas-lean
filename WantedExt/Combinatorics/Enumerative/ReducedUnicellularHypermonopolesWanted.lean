/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Reduced unicellular hypermonopoles

Statements from Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*,
Journal of Integer Sequences 28 (2025), Article 25.3.3 (arXiv:2403.19569). Labels follow the
journal numbering (Lemma 2, Theorem 4, ...); the arXiv version numbers them by section.

A hypermap on `n` points is a pair `(σ, α)` of permutations of `Fin n`; its vertices,
hyperedges and faces are the cycles of `σ`, `α` and `α⁻¹ * σ`, and its genus `g` is given by
Jacques' formula `n + 2 - 2g = z(σ) + z(α) + z(α⁻¹σ)`, where `z` counts cycles including
fixed points (`MetaMathlibExt.cycleQuotientCount`). It is a hypermonopole when `z(σ) = 1`
and unicellular when `z(α⁻¹σ) = 1`; a bud is a fixed point of `α`, and the hypermap is
reduced when it has no bud (Definition 1). The paper's circular permutation
`(1, …, n)` is `finRotate n`, which maps `i` to `i + 1` modulo `n`.

Transitivity of `⟨σ, α⟩` is not stated separately: it holds whenever `z(σ) = 1`
(Remark 7). Zagier's Theorem 4 is already proved as
`MetaMathlibExt.zagier_probability_product_two_cyclic_permutations`. Theorem 5 (the count
of circular `ψ` with `z((1, …, n) ψ) = k`) follows from it by conjugation, so it is not
restated here.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import MathlibExt.Combinatorics.Enumerative.Stirling

namespace MetaMathlibExt

@[expose] public section

open Polynomial

/-- **Cyclic product numbers.** For natural numbers $n$ and $k$, write $c(m, j)$ for the unsigned
Stirling numbers of the first kind. The cyclic product number $H(n, k)$ is the quotient
$c(n + 1, k) / \binom{n + 1}{2}$, rounded down to a natural number, when $n + k$ is even
(equivalently, $n - k$ is even), and $0$ when $n + k$ is odd. Division by zero gives $0$, so
$H(0, k) = 0$ for every $k$.

These are the numbers displayed in Theorem 5 of the source. The numbers $H(n + 1, k)$ are the
Hultman numbers (OEIS A164652).

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public def cyclicProductNumber (n k : ℕ) : ℕ :=
  if Even (n + k) then Nat.stirlingFirst (n + 1) k / (n + 1).choose 2 else 0

/-- **Vanishing of the cyclic product numbers for odd $n - k$.** For natural numbers $n$ and $k$
such that $n + k$ is odd (equivalently, $n - k$ is odd), the cyclic product number $H(n, k)$ is
$0$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public theorem cyclicProductNumber_of_odd {n k : ℕ} (h : ¬ Even (n + k)) :
    cyclicProductNumber n k = 0 := by
  simp [cyclicProductNumber, h]

/-- **Cyclic product numbers with second argument zero.** For every natural number $n$, the
cyclic product number $H(n, 0)$ is $0$, since the unsigned Stirling number of the first kind
$c(n + 1, 0)$ is $0$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public theorem cyclicProductNumber_zero_right (n : ℕ) : cyclicProductNumber n 0 = 0 := by
  simp [cyclicProductNumber, Nat.stirlingFirst_succ_zero]

/-- **Small cyclic product numbers.** The cyclic product numbers satisfy $H(3, 1) = 1$,
$H(4, 2) = 5$, $H(5, 1) = 8$ and $H(7, 1) = 180$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Table 1 (values of `H(n, k)`). -/
public theorem cyclicProductNumber_small_values :
    cyclicProductNumber 3 1 = 1 ∧ cyclicProductNumber 4 2 = 5 ∧
      cyclicProductNumber 5 1 = 8 ∧ cyclicProductNumber 7 1 = 180 := by
  decide

/-- **Genus bounds for reduced unicellular hypermonopoles.** Let $\sigma$ and $\alpha$ be
permutations of $\{0, 1, \dots, n - 1\}$, and write $z(\pi)$ for the number of cycles of a
permutation $\pi$, fixed points included. Suppose that $z(\sigma) = 1$, that
$z(\alpha^{-1} \circ \sigma) = 1$, that $\alpha$ has no fixed point, and that the natural
number $g$ satisfies $n + 2 = z(\sigma) + z(\alpha) + z(\alpha^{-1} \circ \sigma) + 2g$. Then
$2g + 1 \le n \le 4g$.

In the terms of the source, $(\sigma, \alpha)$ is a reduced unicellular hypermonopole on $n$
points and $g$ is its genus, given by Jacques' formula.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 2 (`jis-2025-25.3.3-lem-2`). -/
public theorem_wanted genus_bounds_of_reduced_unicellular_hypermonopole {n g : ℕ}
    (σ α : Equiv.Perm (Fin n)) (hσ : cycleQuotientCount σ = 1)
    (hface : cycleQuotientCount (α⁻¹ * σ) = 1) (hred : ∀ i, α i ≠ i)
    (hgenus : n + 2 = cycleQuotientCount σ + cycleQuotientCount α +
      cycleQuotientCount (α⁻¹ * σ) + 2 * g) :
    2 * g + 1 ≤ n ∧ n ≤ 4 * g

/-- **Generating polynomial of the cyclic product numbers.** For every natural number $n$, let
$H(n, k)$ be the cyclic product numbers, viewed as rational numbers. Then in the polynomial
ring $\mathbb{Q}[x]$
$$\sum_{k=0}^{n} H(n, k) x^k = c_n (x (x + 1) \cdots (x + n) - x (x - 1) \cdots (x - n)),$$
where $c_n = \frac{1}{(n + 1) n}$ for $n \ge 1$ and $c_0 = 0$; for $n = 0$ both sides are $0$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 6 (`jis-2025-25.3.3-lem-6`), quoting
S. Grusea and A. Labarre. -/
public theorem_wanted sum_cyclicProductNumber_mul_X_pow (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), C (cyclicProductNumber n k : ℚ) * X ^ k =
      C (((n + 1 : ℚ) * n)⁻¹) * (ascPochhammer ℚ (n + 1) - descPochhammer ℚ (n + 1))

/-- **Unicellular hypermonopoles with a cyclic vertex permutation.** Let $n$ and $k$ be natural
numbers, let $\sigma$ be the cyclic permutation $i \mapsto i + 1$ (modulo $n$) of
$\{0, 1, \dots, n - 1\}$, and write $z(\pi)$ for the number of cycles of a permutation $\pi$,
fixed points included. Then the number of permutations $\alpha$ of $\{0, 1, \dots, n - 1\}$ with
$z(\alpha^{-1} \circ \sigma) = 1$ and $z(\alpha) = k$ is the cyclic product number $H(n, k)$.

In the terms of the source, these $\alpha$ are the unicellular hypermonopoles $(\sigma, \alpha)$
with $\sigma = (1, \dots, n)$ and $z(\alpha) = k$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Corollary 8 (`jis-2025-25.3.3-cor-8`). -/
public theorem_wanted card_unicellular_hypermonopoles_finRotate (n k : ℕ) :
    Fintype.card {α : Equiv.Perm (Fin n) //
      cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ cycleQuotientCount α = k} =
      cyclicProductNumber n k

/-- **Criterion for a hypermap with a cyclic vertex permutation to have no bud.** Let $\sigma$ be
the cyclic permutation $i \mapsto i + 1$ (modulo $n$) of $\{0, 1, \dots, n - 1\}$. A permutation
$\alpha$ of $\{0, 1, \dots, n - 1\}$ has no fixed point if and only if
$\pi = \alpha^{-1} \circ \sigma$ satisfies $\pi(i) \ne i + 1$ (modulo $n$) for every $i$.

In the terms of the source, a bud of the hypermap $(\sigma, \alpha)$ is a fixed point of $\alpha$.
The source assumes the hypermap is a unicellular hypermonopole; the equivalence does not use that
assumption, so it is stated for every $\alpha$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 10 (`jis-2025-25.3.3-lem-10`). -/
public theorem_wanted reduced_iff_forall_face_ne_finRotate {n : ℕ}
    (α : Equiv.Perm (Fin n)) :
    (∀ i, α i ≠ i) ↔ ∀ i, (α⁻¹ * finRotate n) i ≠ finRotate n i

/-- **Cycle count of a fixed-point-free permutation.** Let $n \ge 1$ and let $\alpha$ be a
permutation of $\{0, 1, \dots, n - 1\}$ with no fixed point. Then the number $z(\alpha)$ of
cycles of $\alpha$ satisfies $1 \le z(\alpha)$ and $2 z(\alpha) \le n$.

This is the source's bound $1 \le z(\alpha) \le n / 2$ for a reduced unicellular
hypermonopole $(\sigma, \alpha)$ on $n$ points: only $n \ge 1$ (forced by $z(\sigma) = 1$) and
the absence of buds (fixed points of $\alpha$) are used.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Corollary 11 (`jis-2025-25.3.3-cor-11`). -/
public theorem_wanted cycleCount_bounds_of_reduced {n : ℕ} (hn : 1 ≤ n)
    (α : Equiv.Perm (Fin n)) (hred : ∀ i, α i ≠ i) :
    1 ≤ cycleQuotientCount α ∧ 2 * cycleQuotientCount α ≤ n

/-- **Counting reduced unicellular hypermonopoles with a cyclic vertex permutation.** Let
$n \ge 2$ and $k \ge 1$ be natural numbers with $2k \le n$, let $\sigma$ be the cyclic
permutation $i \mapsto i + 1$ (modulo $n$) of $\{0, 1, \dots, n - 1\}$, and write $z(\pi)$ for
the number of cycles of a permutation $\pi$, fixed points included. Let $r(n, k)$ be the number
of permutations $\alpha$ of $\{0, 1, \dots, n - 1\}$ with no fixed point such that
$z(\alpha^{-1} \circ \sigma) = 1$ and $z(\alpha) = k$. Then, in terms of the cyclic product
numbers $H$,

$$r(n, k) = \sum_{i=0}^{k-1} (-1)^i \binom{n}{i} H(n - i, k - i).$$

In the terms of the source, $r(n, k)$ counts the reduced unicellular hypermonopoles
$(\sigma, \alpha)$ with $\sigma = (1, \dots, n)$ and $z(\alpha) = k$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Proposition 12 (`jis-2025-25.3.3-prop-12`). -/
public theorem_wanted card_reduced_unicellular_hypermonopoles_finRotate {n k : ℕ}
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (Fintype.card {α : Equiv.Perm (Fin n) //
      cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
        cycleQuotientCount α = k} : ℤ) =
      ∑ i ∈ Finset.range k,
        (-1) ^ i * (n.choose i : ℤ) * cyclicProductNumber (n - i) (k - i)

/-- **Vanishing of the reduced unicellular hypermonopole counts.** Let $\sigma_n$ be the cyclic
permutation $i \mapsto i + 1$ (modulo $n$) of $\{0, 1, \dots, n - 1\}$, write $z(\pi)$ for the
number of cycles of a permutation $\pi$, fixed points included, and let $r(n, k)$ be the number
of permutations $\alpha$ of $\{0, 1, \dots, n - 1\}$ with no fixed point such that
$z(\alpha^{-1} \circ \sigma_n) = 1$ and $z(\alpha) = k$. Then $r(n, k) = 0$ for all natural
numbers $n$ and $k$ with $n - k$ odd; $r(3, k) > 0$ for some natural number $k$ with $2k \le 3$;
and $r(n, k) = 0$ whenever $n < 3$ and $2k \le n$.

So the least $n$ with $r(n, k) > 0$ for some $k \le n / 2$ is $n = 3$. In the terms of the
source, $r(n, k)$ counts the reduced unicellular hypermonopoles $(\sigma_n, \alpha)$ with
$\sigma_n = (1, \dots, n)$ and $z(\alpha) = k$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Corollary 13 (`jis-2025-25.3.3-cor-13`). -/
public theorem_wanted reduced_unicellular_hypermonopoles_finRotate_vanishing :
    (∀ n k : ℕ, Odd ((n : ℤ) - k) →
      Fintype.card {α : Equiv.Perm (Fin n) //
        cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
          cycleQuotientCount α = k} = 0) ∧
    (∃ k : ℕ, 2 * k ≤ 3 ∧
      0 < Fintype.card {α : Equiv.Perm (Fin 3) //
        cycleQuotientCount (α⁻¹ * finRotate 3) = 1 ∧ (∀ i, α i ≠ i) ∧
          cycleQuotientCount α = k}) ∧
    ∀ n < 3, ∀ k : ℕ, 2 * k ≤ n →
      Fintype.card {α : Equiv.Perm (Fin n) //
        cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
          cycleQuotientCount α = k} = 0

/-- **Counting reduced unicellular hypermonopoles by genus.** Fix $g \in \mathbb{N}$. For
each $n \in \mathbb{N}$ let $\zeta_n$ be the cyclic permutation of $\{0, \ldots, n - 1\}$
sending $i$ to $i + 1$ modulo $n$, and let $z(\pi)$ be the number of cycles of a permutation
$\pi$, fixed points included. Let $U_g$ be the set of pairs $(n, \alpha)$, with
$n \in \mathbb{N}$ and $\alpha$ a permutation of $\{0, \ldots, n - 1\}$, such that
$z(\zeta_n) = 1$, $z(\alpha^{-1} \zeta_n) = 1$ (the product applies $\zeta_n$ first), $\alpha$
has no fixed point, and $n + 2 = z(\zeta_n) + z(\alpha) + z(\alpha^{-1} \zeta_n) + 2g$. Then
$U_g$ is finite and its number of elements is $\sum_{n = 2g + 1}^{4g} r(n, n - 2g)$, where
$r(n, k)$ is the number of permutations $\alpha$ of $\{0, \ldots, n - 1\}$ without fixed
points such that $z(\alpha^{-1} \zeta_n) = 1$ and $z(\alpha) = k$.

The pairs in $U_g$ are the reduced unicellular hypermonopoles $(\zeta_n, \alpha)$ of genus
$g$, with the genus given by Jacques' formula and the vertex permutation normalized to
$\zeta_n$. The paper writes $u(g)$ for the number of elements of $U_g$; its first value is
$u(1) = 2$.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Proposition 15 (`jis-2025-25.3.3-prop-15`). -/
public theorem_wanted reduced_unicellular_hypermonopoles_of_genus_count (g : ℕ) :
    let U : Set (Σ n : ℕ, Equiv.Perm (Fin n)) :=
      {p | cycleQuotientCount (finRotate p.1) = 1 ∧
        cycleQuotientCount (p.2⁻¹ * finRotate p.1) = 1 ∧ (∀ i, p.2 i ≠ i) ∧
        p.1 + 2 = cycleQuotientCount (finRotate p.1) + cycleQuotientCount p.2 +
          cycleQuotientCount (p.2⁻¹ * finRotate p.1) + 2 * g}
    U.Finite ∧
      U.ncard = ∑ n ∈ Finset.Icc (2 * g + 1) (4 * g),
        Fintype.card {α : Equiv.Perm (Fin n) //
          cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
            cycleQuotientCount α = n - 2 * g}

end

end MetaMathlibExt
