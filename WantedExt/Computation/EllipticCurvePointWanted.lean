/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finding point on elliptic curve (O24)
-/
module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Logic.Encodable.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Computation.EllipticCurvePointWanted

/-! Source record `AMR-083-0028__8400028`. -/

/-!
# O24 — Finding a point on an elliptic curve

Source: Adleman & McCurley, Open Problems in Number Theory Complexity II (1994),
item O24, p17 / LNCS p307. URL: https://mccurley.org/papers/open.ps.gz.
Stable identifiers: [AMR-083-0028], O24. Posed as an open question in the source;
resolved affirmatively by Shallue and van de Woestijne (see `conjecture_holds` below).

Clause list from the source; each appears in the formal text:
1. Inputs `a b : Nat` (curve coefficients).
2. Input `p : Nat` with `p.Prime`.
3. Curve equation `y^2 = x^3 + a*x + b` modulo `p`.
4. Nonsingularity via Jacobian: no mod-`p` point with `2*y = 0` and `3*x^2 + a = 0`.
5. Point `(x, y)` with `x < p`, `y < p` satisfying the equation mod `p`.
6. Determinism: a Lean function, hence single-valued.
7. Polynomial time: Mathlib's bundled two-tape Turing computability in
   polynomial time (`Turing.TM2ComputableInPolyTime`) over standard
   `Encodable`-based bit encodings of the input triple and output pair.
8. Conditional success: if an affine mod-`p` point exists, the output is one;
   vacuous at inputs such as `(2,2,3)` with zero affine points.
9. Question: one shared function always finds a point whenever one exists on
   all prime nonsingular inputs.
-/

/-- `(x, y)` lies on `y^2 = x^3 + a*x + b` modulo `p`. Curve equation for [AMR-083-0028] O24 (Adleman & McCurley 1994, O24 p17/LNCS p307). -/
def O24IsCurvePoint (a b p x y : Nat) : Prop :=
  x < p ∧ y < p ∧ (y ^ 2) % p = (x ^ 3 + a * x + b) % p

/-- Jacobian nonsingularity: no mod-`p` curve point is singular. Side condition for [AMR-083-0028] O24 (Adleman & McCurley 1994, O24 p17/LNCS p307). -/
def O24IsNonsingular (a b p : Nat) : Prop :=
  ∀ x y : Nat, x < p → y < p → (y ^ 2) % p = (x ^ 3 + a * x + b) % p →
    ¬ ((2 * y) % p = 0 ∧ (3 * x ^ 2 + a) % p = 0)

/-- O24 (resolved, see `conjecture_holds`): one deterministic polynomial-time function, computed in
polynomial time by a bundled Mathlib Turing machine over standard bit encodings,
outputs a mod-`p` point on prime nonsingular `y^2 = x^3 + a*x + b` inputs
whenever one exists. Source [AMR-083-0028] O24 (Adleman & McCurley 1994, O24 p17/LNCS p307). -/
def conjecture : Prop :=
  ∃ alg : (ℕ × ℕ × ℕ) → (ℕ × ℕ),
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun x : ℕ × ℕ × ℕ => Computability.encodeNat (Encodable.encode x))
      (fun o : ℕ × ℕ => Computability.encodeNat (Encodable.encode o)) alg) ∧
    ∀ a b p : ℕ, p.Prime → O24IsNonsingular a b p →
      ((∃ x y : ℕ, O24IsCurvePoint a b p x y) →
        O24IsCurvePoint a b p (alg (a, b, p)).1 (alg (a, b, p)).2)

/--
Resolved true: Resolved affirmatively: Shallue and van de Woestijne (Construction of rational
points on elliptic curves over finite fields, ANTS VII, LNCS 4076 (2006) 510-524) give a
deterministic polynomial-time algorithm that computes a nontrivial rational point on an elliptic
curve over a finite field from a Weierstrass equation, by reduction to finding a point on a
genus-zero curve. Source: A. Shallue, C. E. van de Woestijne, Construction of rational points on
elliptic curves over finite fields, ANTS VII, Lecture Notes in Comput. Sci. 4076 (2006) 510-524,
https://doi.org/10.1007/11792086_36. Moved from
`OpenConjectures/Computation/EllipticCurvePoint`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Computation.EllipticCurvePointWanted
