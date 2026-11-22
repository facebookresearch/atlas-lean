/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Razborov: monotone circuits for clique need superpolynomial size

Source:
A. A. Razborov, "Lower bounds on the monotone complexity of some Boolean functions", Soviet
Mathematics Doklady 31 (1985), 354-357.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.RazborovMonotoneClique

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Razborov: monotone circuits for clique need superpolynomial size

Monotone circuits (AND/OR only, no NOT, no MOD) computing the `n / 3`-clique function on `n`
vertices need superpolynomial size: for every polynomial `p` there is a vertex count `n` such
that every well-formed monotone circuit computing clique on `n^2` adjacency-matrix bits has
more than `p (n^2)` gates. Adjacency is read row-major from the input bitstring via `getD`.

Razborov's theorem itself concerns `CLIQUE(m, s)`, cliques of size `s` in graphs on `m`
vertices: monotone circuits (fan-in two) need size `m ^ Ω(log m)` for `s` about `(log m) / 4`,
and size `Ω(m ^ s / (log m) ^ (2 s))` for fixed `s`; Alon and Boppana sharpened the method to
`exp (Ω ((m / log m) ^ (1/3)))` for `s` about `(m / (8 log m)) ^ (2/3)` (as summarised in
N. Alon and R. B. Boppana, *The monotone circuit complexity of Boolean functions*,
Combinatorica 7 (1987), 1-22, Section 1). The statement here, for cliques of size `⌊n/3⌋`,
follows by padding: setting to `1` every input bit that involves `⌊n/3⌋ - s` chosen vertices
turns a monotone circuit for the `⌊n/3⌋`-clique function on `n` vertices into one, no larger
after constant propagation, for `s`-cliques on the remaining `m ≥ 2n/3` vertices. Gates here
have unbounded fan-in. Inputs are themselves `var` gates of the list, so a gate can reference
only earlier gates, at most `g` distinct ones; a circuit with `g` gates therefore has a
fan-in-two equivalent with at most `g ^ 2` gates, and superpolynomial bounds transfer.
-/


/-- The `n / 3`-clique predicate on adjacency-matrix bits read row-major. -/
def cliqueHolds (n : ℕ) (x : List Bool) : Prop :=
  ∃ S : Finset ℕ, S.card = n / 3 ∧ (∀ v ∈ S, v < n) ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → x.getD (a * n + b) false = true

/-- **Razborov: monotone circuits for clique need superpolynomial size.** For every polynomial
`p` there is `n` such that every well-formed monotone circuit (input, and, or gates of
unbounded fan-in) that decides, on `n ^ 2` adjacency bits read row-major, whether the graph has
a clique of size `⌊n/3⌋` has more than `p (n ^ 2)` gates. This is a consequence of Razborov's
bound `m ^ Ω(log m)` for cliques of size about `(log m) / 4` on `m` vertices, by padding with
universal vertices (A. A. Razborov, "Lower bounds on the monotone complexity of some Boolean
functions", Soviet Mathematics Doklady 31 (1985), 354-357; the bound is restated in N. Alon and
R. B. Boppana, Combinatorica 7 (1987), 1-22, Section 1, which also gives the exponential
bound). -/
public theorem_wanted razborov_monotone_clique :
    ∀ p : Polynomial ℕ, ∃ n : ℕ, ∀ C : List (ACGate (n * n)),
      WellFormedCircuit C → IsMonotoneCircuit C →
        (∀ x : List Bool, x.length = n * n →
          ((circuitEval C (fun i => x.getD (i : ℕ) false)).getLast? = some true ↔
            cliqueHolds n x)) →
          C.length > p.eval (n * n)

/-- **The clique function `CLIQUE(n, s)` on adjacency-matrix bits.** For a bitstring `x` read
as an `n × n` adjacency matrix in row-major order (positions beyond the end read as false),
the graph has a clique of size `s`: a set of `s` vertices among `0, …, n - 1` whose entries
`(a, b)` are true for all distinct `a, b` in it. `cliqueHolds n` is `cliqueOfSize n (n / 3)`. -/
def cliqueOfSize (n s : ℕ) (x : List Bool) : Prop :=
  ∃ S : Finset ℕ, S.card = s ∧ (∀ v ∈ S, v < n) ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → x.getD (a * n + b) false = true

/-- **Alon–Boppana: monotone circuits for clique need exponential size.** There are `c > 0` and
`n₀` such that for every `n ≥ n₀`, with `s = ⌊(n / (8 log₂ n)) ^ (2/3)⌋`, every well-formed
monotone circuit (input, and, or gates) on `n ^ 2` adjacency bits that computes `CLIQUE(n, s)`
has at least `exp (c (n / log₂ n) ^ (1/3))` gates (N. Alon and R. B. Boppana, *The monotone
circuit complexity of Boolean functions*, Combinatorica 7 (1987), 1-22, Section 1, refining
Razborov's approximation method; logarithms base `2`). Their bound counts gates of fan-in two.
Inputs here are `var` gates of the list, so each gate references at most `g` distinct earlier
gates, and a circuit with `g` gates of any fan-in has a fan-in-two equivalent with at most
`g ^ 2` gates, which only changes `c`. -/
public theorem_wanted alon_boppana_monotone_clique :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ C : List (ACGate (n * n)), WellFormedCircuit C → IsMonotoneCircuit C →
        (∀ x : List Bool, x.length = n * n →
          ((circuitEval C (fun i => x.getD (i : ℕ) false)).getLast? = some true ↔
            cliqueOfSize n ⌊((n : ℝ) / (8 * Real.logb 2 n)) ^ ((2 : ℝ) / 3)⌋₊ x)) →
          Real.exp (c * ((n : ℝ) / Real.logb 2 n) ^ ((1 : ℝ) / 3)) ≤ C.length

end MetaMathlibExt.Complexity.KeyTheorems.RazborovMonotoneClique
