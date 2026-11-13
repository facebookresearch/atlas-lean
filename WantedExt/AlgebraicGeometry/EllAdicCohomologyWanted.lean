/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.EllAdicCohomology

@[expose] public noncomputable section

/-!
# Integral and rational ℓ-adic cohomology obligations

The completed imported module defines coefficient-induced scalar maps,
the characterized module interface, and rational scalar extension.
The module-law constructor and the finiteness and vanishing theorems
remain construction or proof requests.

References: Bhatt–Scholze, *The pro-étale topology for schemes* (2015),
§6.8; Stacks Tag 0F0W, https://stacks.math.columbia.edu/tag/0F0W;
and SGA 4, Exposé X, Corollary 4.3. Finiteness allows integral torsion;
the degree bounds require the displayed proper smooth hypotheses.
-/

namespace WantedExt.AlgebraicGeometry.EllAdicCohomologyWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open _root_.MathlibExt.AlgebraicGeometry.EllAdicCohomology

universe u

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Integral cohomology is finitely generated over integral coefficients in the
proper smooth algebraically closed setting. Torsion is permitted. -/
public theorem_wanted integralFinite
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) :
    Module.Finite ℤ_[ℓ] (X.left.EllAdicCohomology ℓ n)

/-- The actual rational scalar extension is finite-dimensional. -/
public theorem_wanted rationalFinite
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) :
    FiniteDimensional ℚ_[ℓ] (RationalCohomology ℓ X.left n)

/-- Integral cohomology vanishes above twice the pure relative dimension.
Source: the finite-type torsion cohomological-dimension bound and
Bhatt–Scholze (2015), §6.8. -/
public theorem_wanted integralVanish
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) (hn : 2 * d < n) :
    Subsingleton (X.left.EllAdicCohomology ℓ n)

/-- Rational cohomology vanishes above twice the pure relative dimension. -/
public theorem_wanted rationalVanish
    (k : Type u) [Field k] [IsAlgClosed k]
    (X : Over (Spec (.of k))) (d n : ℕ)
    [IsProper X.hom] [SmoothOfRelativeDimension d X.hom]
    (hℓ : ℓ ≠ ringChar k) (hn : 2 * d < n) :
    Subsingleton (RationalCohomology ℓ X.left n)

end WantedExt.AlgebraicGeometry.EllAdicCohomologyWanted
