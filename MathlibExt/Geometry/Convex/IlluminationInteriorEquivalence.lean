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
# Directional illumination and interior-translate covering

## References

* Andrii Arman, Jaskaran Singh Kaire, and Andriy Prymak, *Hadwiger's conjecture for cap bodies*,
  arXiv:2510.25968v3 (2026), pp. 1–14, §1 (p. 1), where the equivalence is recalled.
* Hugo Hadwiger, *Ungelöste Probleme Nr. 20*, Elemente der Mathematik **12** (1957), p. 121,
  for the interior-translate covering problem.
* Vladimir Boltyanski, *The problem of illuminating the boundary of a convex body*,
  Izvestiya Moldavskogo Filiala Akademii Nauk SSSR, no. 10 (76) (1960), pp. 77–84,
  for the equivalent directional illumination formulation credited in §1.
-/

namespace ConvexCovering

/-- **Directional illumination is equivalent to covering by interior translates.** Let $n \ge 1$,
let $K \subseteq \mathbb{R}^n$ be a convex body and let $q$ be a natural number. Then some $q$ unit
vectors illuminate $K$ if and only if $K$ is covered by $q$ translates
$v_1 + \operatorname{int} K, \dots, v_q + \operatorname{int} K$ of its interior, repetitions
allowed.

Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction. -/
public theorem directionalInteriorFormulationsEquivalent :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∀ q : ℕ, IlluminatedByDirections K q ↔ CoveredByInteriorTranslates K q := by
  intro n hn K hK q
  change IlluminatedByDirections K q ↔ CoveredByTranslates K (interior K) q
  exact ⟨coveredByTranslates_of_illuminatedByDirections hn hK,
    illuminatedByDirections_of_coveredByTranslates hn hK⟩

end ConvexCovering
