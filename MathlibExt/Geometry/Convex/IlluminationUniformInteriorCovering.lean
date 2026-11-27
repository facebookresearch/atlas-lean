/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.Illumination
import all MathlibExt.Geometry.Convex.IlluminationInteriorCovering

/-!
# Uniform directional illumination and interior-translate covering

The pointwise conversions between illuminating directions and interior translates preserve the
size of the family. They therefore preserve any bound required to hold for all convex bodies.

## References

* Andrii Arman, Jaskaran Singh Kaire, and Andriy Prymak, *Hadwiger's conjecture for cap bodies*,
  arXiv:2510.25968v3 (2026), Section 1 (Introduction).
* Hugo Hadwiger, *Ungelöste Probleme Nr. 20*, Elemente der Mathematik 12 (1957), p. 121,
  poses the uniform covering problem.
* Vladimir Boltyanski, *The problem of illuminating the boundary of a convex body*,
  Izvestiya Moldavskogo Filiala Akademii Nauk SSSR 76 (1960), no. 10, pp. 77–84,
  gives the equivalent formulation by illumination, as credited in Section 1.
-/

namespace ConvexCovering

/-- **Uniform covering by interior translates and uniform directional illumination.** For
integers $n \ge 1$ and $q \ge 0$, every convex body in $\mathbb{R}^n$ (a compact convex set with
nonempty interior) can be covered by $q$ translates of its interior if and only if every convex
body $K$ in $\mathbb{R}^n$ is illuminated by $q$ directions: there are unit vectors
$v_1, \dots, v_q$ such that each boundary point $x$ of $K$ has some $i$ and some $t > 0$ with
$x + t v_i$ in the interior of $K$.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction; follows from the
finite-count equivalence, whose Lean proof is also requested here. -/
public theorem uniformDirectionalIlluminationInterpretation (n : ℕ) (hn : 0 < n) (q : ℕ) :
    UniformInteriorTranslateBound n q ↔
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K → IlluminatedByDirections K q := by
  unfold UniformInteriorTranslateBound
  constructor
  · intro h K hK
    exact illuminatedByDirections_of_coveredByTranslates hn hK (h K hK)
  · intro h K hK
    exact coveredByTranslates_of_illuminatedByDirections hn hK (h K hK)

end ConvexCovering
