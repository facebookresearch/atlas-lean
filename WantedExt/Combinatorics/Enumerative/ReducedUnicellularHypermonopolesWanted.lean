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

/-- The number `H(n, k)` displayed in Theorem 5: `c(n + 1, k) / binom(n + 1, 2)` when `n - k` is
even, and `0` when `n - k` is odd, where `c` is the unsigned Stirling number of the first
kind. The parity of `n - k` is tested as the parity of `n + k`, so that `k > n` is
handled as in the paper. The numbers `H(n + 1, k)` are the Hultman numbers (OEIS A164652).

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public def cyclicProductNumber (n k : ℕ) : ℕ :=
  if Even (n + k) then Nat.stirlingFirst (n + 1) k / (n + 1).choose 2 else 0

/-- `H(n, k) = 0` when `n - k` is odd.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public theorem cyclicProductNumber_of_odd {n k : ℕ} (h : ¬ Even (n + k)) :
    cyclicProductNumber n k = 0 := by
  simp [cyclicProductNumber, h]

/-- `H(n, 0) = 0`, since `c(n + 1, 0) = 0`.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Theorem 5. -/
public theorem cyclicProductNumber_zero_right (n : ℕ) : cyclicProductNumber n 0 = 0 := by
  simp [cyclicProductNumber, Nat.stirlingFirst_succ_zero]

/-- Small values from the table of `H(n, k)` values: `H(3, 1) = 1`, `H(4, 2) = 5`, `H(5, 1) = 8`,
`H(7, 1) = 180`.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Table 1 (values of `H(n, k)`). -/
public theorem cyclicProductNumber_small_values :
    cyclicProductNumber 3 1 = 1 ∧ cyclicProductNumber 4 2 = 5 ∧
      cyclicProductNumber 5 1 = 8 ∧ cyclicProductNumber 7 1 = 180 := by
  decide

/-- Lemma 2: if `(σ, α)` is a reduced unicellular hypermonopole of genus `g` on `n`
points, then `2g + 1 ≤ n ≤ 4g`. The genus is given by Jacques' formula.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 2 (`jis-2025-25.3.3-lem-2`). -/
public theorem_wanted genus_bounds_of_reduced_unicellular_hypermonopole {n g : ℕ}
    (σ α : Equiv.Perm (Fin n)) (hσ : cycleQuotientCount σ = 1)
    (hface : cycleQuotientCount (α⁻¹ * σ) = 1) (hred : ∀ i, α i ≠ i)
    (hgenus : n + 2 = cycleQuotientCount σ + cycleQuotientCount α +
      cycleQuotientCount (α⁻¹ * σ) + 2 * g) :
    2 * g + 1 ≤ n ∧ n ≤ 4 * g

/-- Lemma 6 (Grusea–Labarre): `∑_{k=0}^{n} H(n, k) x^k` equals
`((x)^{(n+1)} - (x)_{n+1}) / ((n + 1) n)`, with the rising factorial
`x (x + 1) ⋯ (x + n)` and the falling factorial `x (x - 1) ⋯ (x - n)`.
For `n = 0` both sides are `0`.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 6 (`jis-2025-25.3.3-lem-6`), quoting
S. Grusea and A. Labarre. -/
public theorem_wanted sum_cyclicProductNumber_mul_X_pow (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), C (cyclicProductNumber n k : ℚ) * X ^ k =
      C (((n + 1 : ℚ) * n)⁻¹) * (ascPochhammer ℚ (n + 1) - descPochhammer ℚ (n + 1))

/-- Corollary 8: the number of unicellular hypermonopoles `(σ, α)` with
`σ = (1, …, n)` and `z(α) = k` is `H(n, k)`.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Corollary 8 (`jis-2025-25.3.3-cor-8`). -/
public theorem_wanted card_unicellular_hypermonopoles_finRotate (n k : ℕ) :
    Fintype.card {α : Equiv.Perm (Fin n) //
      cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ cycleQuotientCount α = k} =
      cyclicProductNumber n k

/-- Lemma 10: `(σ, α)` with `σ = (1, …, n)` has no bud if and only if
`π = α⁻¹σ` satisfies `π(i) ≠ i + 1` (modulo `n`) for every `i`. The paper assumes the
hypermap is a unicellular hypermonopole; the equivalence does not use that assumption,
so it is stated for every `α`.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Lemma 10 (`jis-2025-25.3.3-lem-10`). -/
public theorem_wanted reduced_iff_forall_face_ne_finRotate {n : ℕ}
    (α : Equiv.Perm (Fin n)) :
    (∀ i, α i ≠ i) ↔ ∀ i, (α⁻¹ * finRotate n) i ≠ finRotate n i

/-- Corollary 11: if `(σ, α)` is a reduced unicellular hypermonopole on `n` points,
then `1 ≤ z(α) ≤ n / 2`. Only `n ≥ 1` (forced by `z(σ) = 1`) and the absence of buds
are used, so the vertex and face hypotheses are replaced by `1 ≤ n`.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Corollary 11 (`jis-2025-25.3.3-cor-11`). -/
public theorem_wanted cycleCount_bounds_of_reduced {n : ℕ} (hn : 1 ≤ n)
    (α : Equiv.Perm (Fin n)) (hred : ∀ i, α i ≠ i) :
    1 ≤ cycleQuotientCount α ∧ 2 * cycleQuotientCount α ≤ n

/-- Proposition 12: for `n ≥ 2` and `1 ≤ k ≤ n / 2`, the number `r(n, k)` of reduced
unicellular hypermonopoles `(σ, α)` with `σ = (1, …, n)` and `z(α) = k` is
`∑_{i=0}^{k-1} (-1)^i binom(n, i) H(n - i, k - i)`.

Source: Robert Cori and Gábor Hetyei, *On Reduced Unicellular Hypermonopoles*, Journal of
Integer Sequences 28 (2025), Article 25.3.3, Proposition 12 (`jis-2025-25.3.3-prop-12`). -/
public theorem_wanted card_reduced_unicellular_hypermonopoles_finRotate {n k : ℕ}
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hkn : 2 * k ≤ n) :
    (Fintype.card {α : Equiv.Perm (Fin n) //
      cycleQuotientCount (α⁻¹ * finRotate n) = 1 ∧ (∀ i, α i ≠ i) ∧
        cycleQuotientCount α = k} : ℤ) =
      ∑ i ∈ Finset.range k,
        (-1) ^ i * (n.choose i : ℤ) * cyclicProductNumber (n - i) (k - i)

/-- Corollary 13: `r(n, k) = 0` when `n - k` is odd, and the least `n` with
`r(n, k) > 0` for some `k ≤ n / 2` is `n = 3`.

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

/-- Proposition 15: the number `u(g)` of reduced unicellular hypermonopoles of genus `g`
is finite and equals `∑_{n=2g+1}^{4g} r(n, n - 2g)`. As in the paper's count (whose first
value is `u(1) = 2`), hypermonopoles are counted with the vertex normalized to
`σ = (1, …, n)`, over all numbers of points `n`.

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
