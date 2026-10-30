/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Karp-Luby: FPRAS for DNF counting

Source:
R. M. Karp and M. Luby, "Monte-Carlo algorithms for enumeration and reliability problems",
Proceedings of the Twenty-Fourth Annual Symposium on Foundations of Computer Science (FOCS
1983), 56-64.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.KarpLuby

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Karp-Luby: FPRAS for DNF counting

Counting the satisfying assignments of a DNF formula admits a fully polynomial randomized
approximation scheme (FPRAS): a single polynomial-time estimator `Est` takes the instance,
a random string, and the precision parameter in unary (a bitstring `prec` of length `n`,
so `|prec| = n`), and outputs an estimate within a multiplicative `(1 ± 1/n)` factor of
the true count with probability at least `2/3`. The number of random bits and the
estimator's running time are polynomial in `|x| + n` (the precision is unary, so
polynomial time in the input length is polynomial in `|x| + n`); a separate hard-coded
estimator per precision would be nonuniform and would not be an FPRAS. The DNF formula is
a list of terms, each a list of literals `(variable, polarity)`; inputs decode to
`(unary variable count, formula)` with all variables below the count. The count is
unary (a bitstring of length `n`): with a binary-encoded count, the formula `[[]]`
has input length `O(log n)` but `2 ^ n` satisfying assignments, so every successful
estimate has binary output length `Ω(n)`, which no polynomial-time estimator
receiving only polynomially many random bits in `|x|` could emit.
-/

/-- A DNF formula, given by an assignment, is satisfied if some term's literals all hold. -/
def dnfSat (assign : ℕ → Bool) (φ : List (List (ℕ × Bool))) : Prop :=
  ∃ term ∈ φ, ∀ p ∈ term, assign p.1 = p.2

/-- The number of satisfying assignments of the DNF formula decoded from `x`
(`0` on malformed inputs). -/
noncomputable def dnfCountOf (x : List Bool) : ℕ :=
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List Bool × List (List (ℕ × Bool))) x with
  | some (u, φ) =>
    if ∀ clause ∈ φ, ∀ l ∈ clause, l.1 < u.length then
      Set.ncard {a : Fin u.length → Bool |
        dnfSat (fun v => if h : v < u.length then a ⟨v, h⟩ else false) φ}
    else 0
  | none => 0

/-- **Karp-Luby: FPRAS for DNF counting.** Source: R. M. Karp and M. Luby, "Monte-Carlo
algorithms for enumeration and reliability problems", Proceedings of the Twenty-Fourth
Annual Symposium on Foundations of Computer Science (FOCS 1983), 56-64. -/
public theorem_wanted karp_luby_dnf_counting :
    ∃ p : Polynomial ℕ, ∃ Est : List Bool × List Bool × List Bool → ℕ,
      IsPolyTime Est ∧ ∀ (x : List Bool) (prec : List Bool), 1 ≤ prec.length →
        3 * Set.ncard {r : Fin (p.eval (x.length + prec.length)) → Bool |
          |(Est (x, List.ofFn r, prec) : ℚ) - (dnfCountOf x : ℚ)| ≤
            (dnfCountOf x : ℚ) / (prec.length : ℚ)} ≥
          2 * 2 ^ (p.eval (x.length + prec.length))

end MetaMathlibExt.Complexity.KeyTheorems.KarpLuby
