/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An odd-degree point on Skorobogatov's bielliptic surface (AIM rational points, Problem 20)

AIM workshop Rational and integral points on higher dimensional varieties, Problem 20
(Colliot-Thélène): with `p(t) = 3(t⁴ - 54t² - 117t - 243)`, the system `y² = p(t)(x² + 1)`, `z² =
p(t)(x² + 2)` has no rational point although its Brauer-Manin set is nonempty (Skorobogatov). Is
`X(k) ≠ ∅` for some number field `k` of odd degree?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.OddDegreePointBiellipticAIMAlgebraicNumberTheoryProblem105Wanted

/-!
Source: AIM workshop Rational and integral points on higher dimensional varieties (2002), problem
list, https://aimath.org/WWN/qptsurface2/qptsurface2.pdf, Problem 20 (J.-L. Colliot-Thélène).
UnsolvedMath record UM-20000453 (`AIM-ALGEBRAIC_NUMBER_THEORY-0105`), dataset ulamai/UnsolvedMath
v1.8.0.

The statement asks for a point of the displayed affine system over a number field of odd degree. The
quartic `t⁴ - 54t² - 117t - 243` has no rational root and no factorization into integral quadratics,
so it is irreducible over `ℚ` and has no root in a field of odd degree; the quadratics `x² + 1` and
`x² + 2` have no root there either. Hence every such point has `y z ≠ 0`, and degenerate solutions
cannot witness the statement. Creutz writes the surface as `(x² + 1) ỹ² = (x² + 2) z̃² = p(t)`,
which becomes this system under `y = (x² + 1) ỹ`, `z = (x² + 2) z̃`.
-/

/-- Colliot-Thélène's question (AIM workshop Rational and integral points on higher dimensional
varieties, Problem 20): with `p(t) = 3 (t⁴ - 54 t² - 117 t - 243)`, Skorobogatov's surface
`y² = p(t) (x² + 1)`, `z² = p(t) (x² + 2)` has a point over some number field `k` of odd degree
`[k : ℚ]`. -/
def skorobogatovSurfaceOddDegreePoint : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : NumberField k), Odd (Module.finrank ℚ k) ∧
    ∃ x y z t : k,
      y ^ 2 = 3 * (t ^ 4 - 54 * t ^ 2 - 117 * t - 243) * (x ^ 2 + 1) ∧
      z ^ 2 = 3 * (t ^ 4 - 54 * t ^ 2 - 117 * t - 243) * (x ^ 2 + 2)

/--
Resolved true: Creutz exhibited a closed point of Skorobogatov's surface with residue field the
cubic field `ℚ(θ)`, `θ³ + θ + 1 = 0`, so the surface has a point over a number field of odd degree
`3` (and a 0-cycle of degree 1, as Colliot-Thélène predicted). Source: AIM workshop Rational and
integral points on higher dimensional varieties (2002), problem list,
https://aimath.org/WWN/qptsurface2/qptsurface2.pdf, Problem 20 (J.-L. Colliot-Thélène); resolution:
B. Creutz, Zero-cycles of degree one on Skorobogatov's bielliptic surface, J. Number Theory 178
(2017), 1-4, arXiv:1702.02629, page 1: explicit coordinates (x0, y0, z0, t0) of a closed point of S
whose residue field is the cubic field L = Q[θ], θ^3 + θ + 1 = 0, giving a 0-cycle of degree 1 on S,
https://doi.org/10.1016/j.jnt.2017.02.007.
-/
public theorem_wanted skorobogatovSurfaceOddDegreePoint_holds : skorobogatovSurfaceOddDegreePoint

end MathlibExt.NumberTheory.OddDegreePointBiellipticAIMAlgebraicNumberTheoryProblem105Wanted
