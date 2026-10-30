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


/-- Decode an `(magnitude, sign)` pair to an integer. -/
def decodeInt (p : ℕ × Bool) : ℤ :=
  if p.2 then (p.1 : ℤ) else -(p.1 : ℤ)

open Classical in
/-- Rational linear-program feasibility as a decision problem over bitstrings. -/
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

/-- **Linear programming is in P (Khachiyan).** Source: L. G. Khachiyan, "A polynomial
algorithm in linear programming", Soviet Mathematics Doklady 20 (1979), 191-194. -/
public theorem_wanted lp_in_p :
    lpDec ∈ MetaMathlibExt.ComplexityTheory.P

end MetaMathlibExt.Complexity.KeyTheorems.LPInPWanted
