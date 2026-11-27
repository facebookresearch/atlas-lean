/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Asymptotics of RNA secondary structure statistics

Hofacker, Schuster and Stadler (1998): a secondary structure on `n` points with minimum hairpin
size `m` is a non-crossing set of base pairs `(i, j)` with at least `m` unpaired points strictly
inside each pair, every point in at most one pair (Definition 2.1 and equation (1)). Their number
`S_n` satisfies Waterman's recursion; with minimum stack length `l = 1` its generating function
`s(x)` solves `F(x, s(x)) = 0` with `F(x, y) = 1 + (2x - ∑_{k=0}^{m+1} x^k) y + x² y²`
(Corollary 4.10). Let `α` be the smallest positive root of `∑_{k=0}^{m+1} x^k - 4x = 0` and
`β = 1 / α` (Corollary 4.12; `α = 0.3820` for `m = 1`). Then (Corollary 4.11 with equations (30)
and (31))

  `S_n ~ √(α F_x(α, β) / (2π F_yy(α, β))) · n^{-3/2} · α^{-n}`,

and over all structures on `n` points (sums over structures, so `X_n / S_n` is the average):

* components (base pairs enclosed by no other pair), Theorem 4.14: `I_n / S_n → 2/α - 3`;
* external points (unpaired points enclosed by no pair), Theorem 4.16: `E_n / S_n → 2`;
* unpaired points, Theorem 4.17:
  `U_n / S_n ~ (2α + m(1 - 2α)) / (2 + m(1 - 2α)) · n`;
* base pairs, Remark 4.18: the finite identity `U_n + 2 P_n = n S_n`. With Theorem 4.17 it gives
  `P_n / S_n ~ (1 - c_U) / 2 · n`, with `c_U` the constant of Theorem 4.17, a limit the source does
  not display;
* stacks (maximal runs of stacked pairs `(p, q), (p + 1, q - 1), …`), Theorem 4.19:
  `N_n / S_n ~ (1 - α)²(1 + α) / (2 + m - 2mα) · n`.

The structures are the native ones of `Cslib.Bioinformatics.RNA.PartitionFunction.structures` on
`n` identical points with every pair allowed (0-based positions; `i + m < j` for each pair), whose
number is `watermanNumber m n` by `card_structures_eq_watermanNumber`. Here `F_x` and `F_yy` are
written out: `F_x(x, y) = (2 - ∑_{k=1}^{m+1} k x^{k-1}) y + 2 x y²` and `F_yy(x, y) = 2 x²`. Not
recorded here: minimum stack length `l > 1` (Corollary 4.9, equations (45), (48), (49)), and the
counts with given numbers of pairs, stacks, hairpins or components and the loop and stack-length
distributions (Theorems 4.20–4.30).

Sources: I. L. Hofacker, P. Schuster and P. F. Stadler, "Combinatorics of RNA secondary
structures", Discrete Applied Mathematics 88 (1998) 207–237, doi:10.1016/S0166-218X(98)00073-0,
Section 2, equation (1), Theorem 4.3, Corollaries 4.10–4.12, Theorems 4.14, 4.16, 4.17 and 4.19,
Remark 4.18; M. S. Waterman, "Secondary structure of single-stranded nucleic acids", Studies in
Foundations and Combinatorics, Advances in Mathematics Supplementary Studies 1 (1978) 167–212.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.RNA.PartitionFunction
public import CSLibExt.Bioinformatics.RNA.Zuker
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.RNASecondaryStructureAsymptoticsWanted

open Cslib.Bioinformatics.RNA.PartitionFunction Filter Topology Asymptotics

/-- The secondary structures on `n` points with minimum hairpin `m` (every pair allowed). -/
noncomputable def structs (m n : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  structures (fun _ _ : Unit => True) m (List.replicate n ())

/-- `S_n`: the number of secondary structures on `n` points with minimum hairpin `m`. -/
noncomputable def S (m n : ℕ) : ℝ :=
  (structs m n).card

/-- The **sum over structures** of a statistic `f`: `∑_{P} f(P)`. -/
noncomputable def total (m n : ℕ) (f : Finset (ℕ × ℕ) → ℕ) : ℝ :=
  ∑ P ∈ structs m n, (f P : ℝ)

/-- **Components.** The number of base pairs of `P` enclosed by no other pair of `P`, the exterior
branches `Cslib.Bioinformatics.RNA.Zuker.exteriorBranches P`. -/
def components (P : Finset (ℕ × ℕ)) : ℕ :=
  (Cslib.Bioinformatics.RNA.Zuker.exteriorBranches P).card

open Classical in
/-- The number of **external points** of `P` on `n` points: unpaired points enclosed by no pair. -/
noncomputable def externals (n : ℕ) (P : Finset (ℕ × ℕ)) : ℕ :=
  ((Finset.range n).filter fun i =>
    (∀ p ∈ P, p.1 ≠ i ∧ p.2 ≠ i) ∧ ¬ ∃ p ∈ P, p.1 < i ∧ i < p.2).card

/-- `n - 2 |P|`: the number of **unpaired points** of `P` when `P` is a structure on `n` points,
in which every point lies in at most one pair. -/
def unpaired (n : ℕ) (P : Finset (ℕ × ℕ)) : ℕ :=
  n - 2 * P.card

open Classical in
/-- The number of **stacks** of `P`: base pairs `(p, q)` such that `(p - 1, q + 1)` is not a pair
of `P` (the outermost pair of each maximal run of stacked pairs). -/
noncomputable def stackCount (P : Finset (ℕ × ℕ)) : ℕ :=
  (P.filter fun p => ¬ (1 ≤ p.1 ∧ (p.1 - 1, p.2 + 1) ∈ P)).card

/-- `α`: the smallest positive root of `∑_{k=0}^{m+1} x^k - 4x = 0` (Corollary 4.12). -/
noncomputable def alpha (m : ℕ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ ∑ k ∈ Finset.range (m + 2), x ^ k - 4 * x = 0}

/-- `F_x(x, y) = (2 - ∑_{k=1}^{m+1} k x^{k-1}) y + 2 x y²` for
`F(x, y) = 1 + (2x - ∑_{k=0}^{m+1} x^k) y + x² y²`. -/
noncomputable def Fx (m : ℕ) (x y : ℝ) : ℝ :=
  (2 - ∑ k ∈ Finset.range (m + 2), (k : ℝ) * x ^ (k - 1)) * y + 2 * x * y ^ 2

/-- `F_yy(x, y) = 2 x²`. -/
def Fyy (x : ℝ) : ℝ :=
  2 * x ^ 2

/-- **Asymptotic number of secondary structures** (Hofacker, Schuster and Stadler 1998,
Corollaries 4.11 and 4.12 with equations (30)–(31), `l = 1`): for every minimum hairpin size
`m`, with `α` the smallest positive root of `∑_{k=0}^{m+1} x^k - 4x = 0` and `β = 1 / α`,
`S_n ~ √(α F_x(α, β) / (2π F_yy(α, β))) · n^{-3/2} · α^{-n}` as `n → ∞`.

Source: Hofacker, Schuster and Stadler (1998), Corollaries 4.11 and 4.12. -/
public theorem_wanted S_isEquivalent (m : ℕ) :
    (fun n : ℕ => S m n) ~[atTop] fun n : ℕ =>
      Real.sqrt (alpha m * Fx m (alpha m) (alpha m)⁻¹ / (2 * Real.pi * Fyy (alpha m))) *
        (n : ℝ) ^ (-(3 / 2 : ℝ)) * (alpha m)⁻¹ ^ n

/-- **Average number of components** (Hofacker, Schuster and Stadler 1998, Theorem 4.14): for every
minimum hairpin size `m`, `I_n / S_n → 2/α - 3`.

Source: Hofacker, Schuster and Stadler (1998), Theorem 4.14. -/
public theorem_wanted tendsto_components (m : ℕ) :
    Tendsto (fun n => total m n components / S m n) atTop (𝓝 (2 / alpha m - 3))

/-- **Average number of external points** (Hofacker, Schuster and Stadler 1998, Theorem 4.16): for
every minimum hairpin size `m`, `E_n / S_n → 2`.

Source: Hofacker, Schuster and Stadler (1998), Theorem 4.16. -/
public theorem_wanted tendsto_externals (m : ℕ) :
    Tendsto (fun n => total m n (externals n) / S m n) atTop (𝓝 2)

/-- **Average number of unpaired points** (Hofacker, Schuster and Stadler 1998, Theorem 4.17): for
every minimum hairpin size `m`,
`(U_n / S_n) / n → (2α + m(1 - 2α)) / (2 + m(1 - 2α))`.

Source: Hofacker, Schuster and Stadler (1998), Theorem 4.17. -/
public theorem_wanted tendsto_unpaired (m : ℕ) :
    Tendsto (fun n : ℕ => total m n (unpaired n) / S m n / n) atTop
      (𝓝 ((2 * alpha m + m * (1 - 2 * alpha m)) / (2 + m * (1 - 2 * alpha m))))

/-- **Unpaired points and base pairs** (Hofacker, Schuster and Stadler 1998, Remark 4.18): for
every minimum hairpin size `m` and every `n`, `U_n + 2 P_n = n S_n`, where `U_n` and `P_n` are the
numbers of unpaired points and of base pairs summed over all structures on `n` points. With
Theorem 4.17 it gives `(P_n / S_n) / n → (1 - c_U) / 2` with
`c_U = (2α + m(1 - 2α)) / (2 + m(1 - 2α))`, a limit the source does not display.

Source: Hofacker, Schuster and Stadler (1998), Remark 4.18. -/
public theorem_wanted total_unpaired_add_two_mul_total_card (m n : ℕ) :
    total m n (unpaired n) + 2 * total m n Finset.card = n * S m n

/-- **Average number of stacks** (Hofacker, Schuster and Stadler 1998, Theorem 4.19): for every
minimum hairpin size `m`, `(N_n / S_n) / n → (1 - α)²(1 + α) / (2 + m - 2mα)`.

Source: Hofacker, Schuster and Stadler (1998), Theorem 4.19. -/
public theorem_wanted tendsto_stacks (m : ℕ) :
    Tendsto (fun n : ℕ => total m n stackCount / S m n / n) atTop
      (𝓝 ((1 - alpha m) ^ 2 * (1 + alpha m) / (2 + m - 2 * m * alpha m)))

end WantedExt.Biology.ComputationalBiology.RNASecondaryStructureAsymptoticsWanted
