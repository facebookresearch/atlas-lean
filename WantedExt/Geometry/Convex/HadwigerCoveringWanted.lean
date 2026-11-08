/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.Illumination
import Batteries.Util.ProofWanted

/-!
# Known Hadwiger covering and illumination statements with unproved Lean payloads

These twelve private `ProofWanted` records supply no proof of their payloads.
They import only canonical geometry, not an open conjecture or its Results.
-/

@[expose] public section

namespace ConvexCovering

/-- The at-most homothet formulation and fixed-count interior formulation agree.
Source: Bezdek and Khan, arXiv:1602.06040v2, introduction; Arman, Kaire and Prymak,
arXiv:2510.25968v3, introduction. The left side is the explicit closed formulation,
not an assumed OpenConjectures declaration. -/
theorem_wanted homothetInteriorTranslateFormulationsEquivalent :
    (∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∃ q : ℕ, q ≤ 2 ^ n ∧ CoveredBySmallerPositiveHomothets K q) ↔
      ∀ n : ℕ, 0 < n → UniformInteriorTranslateBound n (2 ^ n)

/-- The historical `H_3 <= 16` covering construction.
Source: Papadoperakis (1999), reported in Arman, Bondarenko and Prymak,
arXiv:2404.00547v1, introduction. -/
theorem_wanted papadoperakis1999UpperBound : UniformInteriorTranslateBound 3 16

/-- The `H_3 <= 14` covering construction.
Source: Prymak (2023), arXiv:2112.10698; reported in Arman, Bondarenko and Prymak,
arXiv:2404.00547v1, introduction. -/
theorem_wanted prymak2023UpperBound : UniformInteriorTranslateBound 3 14

/-- Eight is the least uniform count over all centrally symmetric three-dimensional bodies.
Source: Lassak (1984), reported in Arman, Bondarenko and Prymak,
arXiv:2404.00547v1, introduction. -/
theorem_wanted lassak1984SymmetricExactValue :
  IsLeast {q : ℕ | UniformSymmetricInteriorTranslateBound 3 q} 8

/-- Finite directional and actual exterior-point illumination counts agree.
Source: Bezdek and Khan, arXiv:1602.06040v2, introduction. -/
theorem_wanted directionalExternalFormulationsEquivalent :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∀ q : ℕ, IlluminatedByDirections K q ↔ IlluminatedByExternalPoints K q

/-- Finite illumination and smaller positive homothet covering counts agree.
Source: Bezdek and Khan, arXiv:1602.06040v2, introduction. -/
theorem_wanted directionalHomothetFormulationsEquivalent :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∀ q : ℕ, IlluminatedByDirections K q ↔ CoveredBySmallerPositiveHomothets K q

/-- Finite illumination and actual interior-translate covering counts agree.
Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction. -/
theorem_wanted directionalInteriorFormulationsEquivalent :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∀ q : ℕ, IlluminatedByDirections K q ↔ CoveredByInteriorTranslates K q

/-- The two illumination numbers have the same minimum over actual finite families.
Source: Bezdek and Khan, arXiv:1602.06040v2, introduction; follows from its finite-count
equivalence, whose Lean proof is also requested here. -/
theorem_wanted directionalExternalIlluminationNumbersEqual (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K) :
    directionalIlluminationNumber K = externalPointIlluminationNumber K

/-- Directional illumination equals covering by actual translates of the interior.
Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction; follows from the
finite-count equivalence, whose Lean proof is also requested here. -/
theorem_wanted directionalInteriorCoveringNumbersEqual (n : ℕ) (hn : 0 < n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K) :
    directionalIlluminationNumber K = translateCoveringNumber K (interior K)

/-- A finite least illuminating family exists for every positive-dimensional convex body.
Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction's illumination-number
definition; finite existence is the standard compact-convex-body qualification. -/
theorem_wanted illuminationFiniteMinimum :
    ∀ n : ℕ, 0 < n → ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K →
      ∃ q : ℕ, IsLeast {q : ℕ | IlluminatedByDirections K q} q

/-- The universal covering predicate has the directional illumination interpretation.
Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction; follows from the
finite-count equivalence, whose Lean proof is also requested here. -/
theorem_wanted uniformDirectionalIlluminationInterpretation (n : ℕ) (hn : 0 < n) (q : ℕ) :
    UniformInteriorTranslateBound n q ↔
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K → IlluminatedByDirections K q

/-- The symmetric universal covering predicate has the exterior-point illumination interpretation.
Source: Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction, and Bezdek and Khan,
arXiv:1602.06040v2, introduction; follows from the two finite-count equivalences. -/
theorem_wanted uniformSymmetricExternalIlluminationInterpretation (n : ℕ) (hn : 0 < n) (q : ℕ) :
    UniformSymmetricInteriorTranslateBound n q ↔
      ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsConvexBody K → IsCentrallySymmetric K →
        IlluminatedByExternalPoints K q

end ConvexCovering
