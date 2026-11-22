/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.InnerProductSpace.OrthogonalPolynomialHilbertBasisWanted

/-- Classical Hilbert basis of orthogonal polynomials: `L²([-1, 1])` admits a
Hilbert basis whose `n`-th element is represented almost everywhere by a real
polynomial of exact degree `n` (the normalized Legendre basis).

Sources:
- Mathlib `docs/undergrad.yaml`, section "Topology / Hilbert spaces", entry
  "example, classical Hilbert bases of orthogonal polynomials" (currently
  missing: empty entry, no Mathlib declaration).
- NIST Digital Library of Mathematical Functions, §18.3, Table 18.3.1 (Legendre polynomials:
  weight `1` on `(-1, 1)`, `∫ P_n ^ 2 = 2 / (2n + 1)`).
- E. Kreyszig, *Introductory Functional Analysis with Applications*, Wiley, 1978, §3.6
  ("Total Orthonormal Sets and Sequences") and §3.7 ("Legendre, Hermite and Laguerre
  Polynomials": the normalized Legendre polynomials are a total orthonormal sequence in
  `L²[-1, 1]`).
- https://en.wikipedia.org/wiki/Legendre_polynomials#Orthogonality_and_completeness
-/
public theorem_wanted orthogonalPolynomial_hilbertBasis :
    ∃ B : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume.restrict (Set.Icc (-1 : ℝ) 1))),
      ∀ n : ℕ, ∃ q : Polynomial ℝ, q.natDegree = n ∧
        ∀ᵐ x ∂(volume.restrict (Set.Icc (-1 : ℝ) 1)),
          (B n) x = Polynomial.aeval x q

end MathlibExt.Analysis.InnerProductSpace.OrthogonalPolynomialHilbertBasisWanted
