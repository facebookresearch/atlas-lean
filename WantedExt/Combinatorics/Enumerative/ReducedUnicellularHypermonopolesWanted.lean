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
public import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopolesGenusBounds
public import MathlibExt.Combinatorics.Enumerative.ReducedUnicellularHypermonopolesVanishing
public import MathlibExt.Combinatorics.Enumerative.Stirling
public import MathlibExt.Combinatorics.Enumerative.UnicellularHypermonopolesFinRotate

namespace MetaMathlibExt

@[expose] public section

open Polynomial

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
