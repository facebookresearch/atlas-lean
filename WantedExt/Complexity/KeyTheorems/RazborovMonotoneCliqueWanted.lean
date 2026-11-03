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


/-- **The clique function on adjacency-matrix bits.** For a natural number $n$ and a bitstring
$x$, read $x$ as an $n \times n$ adjacency matrix in row-major order: the entry for a pair
$(a, b)$ is the bit of $x$ at position $an + b$, where a position beyond the end of $x$ reads as
false. The clique predicate holds for $n$ and $x$ when there is a set $S$ of exactly
$\lfloor n/3 \rfloor$ vertices among $0, \dots, n - 1$ such that the entry for $(a, b)$ is true
for all distinct $a, b \in S$. -/
def cliqueHolds (n : ℕ) (x : List Bool) : Prop :=
  ∃ S : Finset ℕ, S.card = n / 3 ∧ (∀ v ∈ S, v < n) ∧
    ∀ a ∈ S, ∀ b ∈ S, a ≠ b → x.getD (a * n + b) false = true

/-- **Razborov: monotone circuits for clique need superpolynomial size.** For every polynomial
$p$ with natural-number coefficients there is a natural number $n$ with the following property.
Let $C$ be a well-formed monotone flat circuit on $n^2$ inputs, that is, every gate of $C$ is an
input variable, an and gate or an or gate, and refers only to earlier gates. Suppose that for
every bitstring $x$ of length $n^2$, when input variable $i$ is given the $i$-th bit of $x$, $C$
has a last gate with value true if and only if the $n \times n$ matrix read from $x$ in
row-major order has a clique of size $\lfloor n/3 \rfloor$, that is, a set
$S \subseteq \{0, \dots, n - 1\}$ of $\lfloor n/3 \rfloor$ vertices whose entries $(a, b)$ are
true for all distinct $a, b \in S$. Then $C$ has more than $p(n^2)$ gates.

Source: A. A.
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
