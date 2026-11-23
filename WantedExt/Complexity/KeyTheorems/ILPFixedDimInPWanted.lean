/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Integer linear programming in fixed dimension is in P (Lenstra)

Source:
H. W. Lenstra Jr., "Integer programming with a fixed number of variables", Mathematics of
Operations Research 8 (1983), 538-548.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.ILPFixedDimInP

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Integer linear programming in fixed dimension is in P (Lenstra)

For every fixed dimension `d`, integer linear-program feasibility in dimension `d` is in `P`,
by Lenstra's algorithm (geometry of numbers). The instance is a constraint matrix `A` and
right-hand side `b` with integer entries encoded as `(magnitude, sign)` pairs, and the question
is whether some integer vector `x` of length `d` satisfies `A x ≤ b`.
-/


/-- **Integer from magnitude and sign.** A pair $(n, s)$ of a natural number $n$ and a Boolean
sign $s$ decodes to the integer $n$ if $s$ is true and to $-n$ if $s$ is false. -/
def decodeIntILP (p : ℕ × Bool) : ℤ :=
  if p.2 then (p.1 : ℤ) else -(p.1 : ℤ)

open Classical in
/-- **Integer linear-programming feasibility in fixed dimension.** For a natural number $d$, this
decision problem accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring
decoding, to a pair $(A, b)$ such that $A$ is a list of rows, each a list of exactly $d$ integers,
$b$ is a list of integers with as many entries as $A$ has rows, and there is an integer vector
$y \in \mathbb{Z}^d$ with $\sum_{j < d} A_{rj} y_j \le b_r$ for every row index $r$. Each integer
entry is given as a pair $(n, s)$ of a natural number and a sign, standing for $n$ if $s$ is true
and $-n$ otherwise. Every other bitstring is rejected. -/
noncomputable def ilpFixedDec (d : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List (List (ℕ × Bool)) × List (ℕ × Bool)) x with
  | some i => decide (
      (∀ row ∈ i.1, row.length = d) ∧ i.2.length = i.1.length ∧
      ∃ x : List ℤ, x.length = d ∧
        ∀ r < i.1.length,
          (Finset.range d).sum (fun j =>
            decodeIntILP ((i.1.getD r []).getD j (0, true)) * x.getD j 0) ≤
              decodeIntILP (i.2.getD r (0, true)))
  | none => false

/-- **Integer linear programming in fixed dimension is in P (Lenstra).** For every natural number
$d$, integer linear-programming feasibility in dimension $d$ is in the complexity class P.

Source: H. W. Lenstra
Jr., "Integer programming with a fixed number of variables", Mathematics of Operations
Research 8 (1983), 538-548. -/
public theorem_wanted ilp_fixed_dim_in_p :
    ∀ d : ℕ, ilpFixedDec d ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.ILPFixedDimInP
