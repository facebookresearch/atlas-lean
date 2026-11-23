/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Linear programming is in P (Khachiyan)

Source:
L. G. Khachiyan, "A polynomial algorithm in linear programming", Soviet Mathematics Doklady 20
(1979), 191-194.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.LPInPWanted

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Linear programming is in P (Khachiyan)

Feasibility of rational linear programs is in `P`, by the ellipsoid method. Integers are
encoded as `(magnitude, sign)` pairs, decoded to `ℤ` and then to `ℚ`; the instance is a
constraint matrix `A` and a right-hand side `b`, and the question is whether some rational `x`
satisfies `A x ≤ b` row by row. Malformed instances (rows of differing lengths) are no-
instances.
-/


/-- **Signed integer from a magnitude–sign pair.** The integer decoded from a pair $(k, s)$ of a
natural number $k$ and a boolean $s$ is $k$ if $s$ is true and $-k$ if $s$ is false. -/
def decodeInt (p : ℕ × Bool) : ℤ :=
  if p.2 then (p.1 : ℤ) else -(p.1 : ℤ)

open Classical in
/-- **Rational linear-program feasibility.** The decision problem of rational linear-program
feasibility accepts a bitstring $w$ exactly when $w$ decodes, under the canonical bitstring
encoding, to a pair $(A, b)$ of a list $A$ of $m$ rows, each a list of magnitude–sign pairs, and
a list $b$ of $m'$ magnitude–sign pairs, such that every row of $A$ has the length $n$ of the
first row ($n = 0$ when $m = 0$), $m' = m$, and some $x \in \mathbb{Q}^n$ satisfies
$\sum_{j<n} A_{rj} x_j \le b_r$ for every $r < m$. Here a magnitude–sign pair $(k, s)$ of a
natural number $k$ and a boolean $s$ stands for the integer $k$ if $s$ is true and $-k$ if $s$ is
false, $A_{rj}$ is the integer given by the $j$-th entry of the $r$-th row and $b_r$ is the
integer given by the $r$-th entry of $b$. Bitstrings that do not decode are rejected. -/
noncomputable def lpDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List (List (ℕ × Bool)) × List (ℕ × Bool)) x with
  | some i => decide (
      (∀ row ∈ i.1, row.length = (i.1.getD 0 []).length) ∧
      i.2.length = i.1.length ∧
      ∃ x : List ℚ, x.length = (i.1.getD 0 []).length ∧
        ∀ r < i.1.length,
          (Finset.range (i.1.getD 0 []).length).sum (fun j =>
            (decodeInt ((i.1.getD r []).getD j (0, true)) : ℚ) * x.getD j 0) ≤
              (decodeInt (i.2.getD r (0, true)) : ℚ))
  | none => false

/-- **Linear programming is in P (Khachiyan).** The decision problem of rational linear-program
feasibility is in the complexity class P. This problem accepts exactly the bitstrings that decode,
under the canonical bitstring encoding, to a list $A$ of $m$ rows of integers, all of the same
length $n$, and a list $b$ of $m$ integers, for which some $x \in \mathbb{Q}^n$ satisfies
$\sum_{j<n} A_{rj} x_j \le b_r$ for every $r < m$, where $A_{rj}$ is the $j$-th entry of the
$r$-th row of $A$ and $b_r$ is the $r$-th entry of $b$. Each integer is given as a magnitude–sign
pair $(k, s)$ of a natural number $k$ and a boolean $s$, standing for $k$ if $s$ is true and $-k$
if $s$ is false.

Source: L. G. Khachiyan, "A polynomial
algorithm in linear programming", Soviet Mathematics Doklady 20 (1979), 191-194. -/
public theorem_wanted lp_in_p :
    lpDec ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.LPInPWanted
