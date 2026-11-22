/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Algorithmic enumeration of integer points on elliptic curves (AimPL definedecide 3.1(2))

AimPL: Definability and decidability problems in number theory, Section 3 (Decidability), Problem
3.1 (C. Hall, A. Shlapentokh): Given an elliptic curve `E` given by `y² = x³ + Ax + B`: (1) is there
an algorithm that decides if `E(ℤ) ∖ {∞}` is empty? (2) Is there an algorithm for enumerating
`E(ℤ)`? (3) Can these questions be answered if `E` is replaced with an arbitrary curve?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.Partrec

@[expose] public section

namespace MathlibExt.NumberTheory.EllipticCurveIntegerPointsAlgorithmAIMLogicProblem9Wanted

/-!
Source: AimPL: Definability and decidability problems in number theory, Section 3 (Decidability),
Problem 3.1 (proposed by Chris Hall and Alexandra Shlapentokh), American Institute of Mathematics
problem lists, https://aimpl.org/definedecide/3/. UnsolvedMath record UM-20002233
(`AIM-LOGIC-0009`), dataset ulamai/UnsolvedMath v1.8.0.

Reading: question (2) is stated. The curve has integer coefficients `A, B` and is an elliptic curve,
i.e. `4A³ + 27B² ≠ 0` (the hypothesis is needed: for `A = B = 0` the cuspidal cubic `y² = x³` has
the infinitely many integer points `(t², t³)`). `E(ℤ)` is read as the set of integer solutions `(x,
y)` of the equation, the point at infinity omitted; it is finite by Siegel's theorem. 'An algorithm
for enumerating `E(ℤ)`' is read as a computable function (Mathlib's `Computable`) sending `(A, B)`
to a finite list that contains exactly these points. Question (1), whether `E(ℤ) ∖ {∞}` is empty, is
the emptiness test of this list and is not stated separately; question (3), for arbitrary plane
curves, is the OpenConjectures entry `AIMLogicProblem9`.
-/

/-- AimPL definedecide Problem 3.1, second question, with a positive answer: there is an algorithm
that enumerates the integer points of an elliptic curve `y² = x³ + Ax + B` (`A, B ∈ ℤ`,
`4A³ + 27B² ≠ 0`), i.e. a computable function of `(A, B)` whose value is a finite list containing
exactly the integer solutions `(x, y)` of the equation. -/
def ellipticCurveIntegerPointsEnumerable : Prop :=
  ∃ f : ℤ × ℤ → List (ℤ × ℤ), Computable f ∧
    ∀ A B : ℤ, 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 →
      ∀ x y : ℤ, (x, y) ∈ f (A, B) ↔ y ^ 2 = x ^ 3 + A * x + B

/--
Resolved true: Baker and Coates establish an algorithm that determines all the integer points on a
curve of genus 1; the elliptic curve `y² = x³ + Ax + B` with `4A³ + 27B² ≠ 0` is a curve of genus 1,
so its integer points are listed by an algorithm taking `(A, B)` as input. Source: AimPL:
Definability and decidability problems in number theory, Section 3 (Decidability), Problem 3.1
(proposed by Chris Hall and Alexandra Shlapentokh), American Institute of Mathematics problem lists,
https://aimpl.org/definedecide/3/; resolution: A. Baker and J. Coates, Integer points on curves of
genus 1, Math. Proc. Cambridge Philos. Soc. 67 (1970), 595-602, doi:10.1017/S0305004100045904,
Section 1 (Introduction, shown on Cambridge Core): Siegel's theorem gives only finitely many integer
points on any curve of genus at least 1, but 'Siegel's argument cannot provide an algorithm for
determining all the integer points on the curve. The purpose of the present paper is to establish
such an algorithm in the case of curves of genus 1.' (The first effective bound for y² = ax³ + bx² +
cx + d is A. Baker, The Diophantine equation y² = ax³ + bx² + cx + d, J. London Math. Soc. 43
(1968), 1-9, https://doi.org/10.1112/jlms/s1-43.1.1.) An elliptic curve y² = x³ + Ax + B with 4A³ +
27B² ≠ 0 is a curve of genus 1, https://doi.org/10.1017/S0305004100045904.
-/
public theorem_wanted ellipticCurveIntegerPointsEnumerable_holds :
    ellipticCurveIntegerPointsEnumerable

end MathlibExt.NumberTheory.EllipticCurveIntegerPointsAlgorithmAIMLogicProblem9Wanted
