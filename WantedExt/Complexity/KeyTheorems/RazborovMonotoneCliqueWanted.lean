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
-/


/-- The `n / 3`-clique predicate on adjacency-matrix bits read row-major. -/
def cliqueHolds (n : ℕ) (x : List Bool) : Prop :=
  ∃ S : Finset ℕ, S.card = n / 3 ∧ (∀ v ∈ S, v < n) ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → x.getD (a * n + b) false = true

/-- **Razborov: monotone circuits for clique need superpolynomial size.** Source: A. A.
Razborov, "Lower bounds on the monotone complexity of some Boolean functions", Soviet
Mathematics Doklady 31 (1985), 354-357. -/
public theorem_wanted razborov_monotone_clique :
    ∀ p : Polynomial ℕ, ∃ n : ℕ, ∀ C : List (ACGate (n * n)),
      WellFormedCircuit C → IsMonotoneCircuit C →
        (∀ x : List Bool, x.length = n * n →
          ((circuitEval C (fun i => x.getD (i : ℕ) false)).getLast? = some true ↔
            cliqueHolds n x)) →
          C.length > p.eval (n * n)

end MetaMathlibExt.Complexity.KeyTheorems.RazborovMonotoneClique
