/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CenteredValuationSections

/-!
# Normalized multiplication on actual section spaces

Degrees are literal H0 of the native tensor powers of the same line.
Multiplication is characterized by product of the actual rational section
values; the injective germ maps make this characterization unique.
This is an explicit tensor/frame comparison dependency, not a freely
chosen graded ring or filtration. The native tensor/power constructions
are already completed and are not requested again.

Sources: Blum--Jonsson arXiv1706.04548v2, §§1 and 3--5;
Stacks Project Tags 01CY/01CR. The remaining asymptotic comparison uses
the actual subspaces and finite-basis formulas.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NormalizedSectionAlgebras

open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.CenteredValuationSections
open MathlibExt.AlgebraicGeometry.BirationalSectionCoordinates
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

variable {k : Type} [Field k] {n : ℕ}
  {V : NormalVariety k n} {v : CenteredValuation V}

/-- Comparison with native section multiplication on the fixed tensor powers.
Normalization determines every output through an injective actual germ map. -/
structure SectionMultiplication (S : SectionSeries V v) where
  multiply : ∀ a b : ℕ,
    SectionSpace V (power S.line a) →ₗ[k]
      SectionSpace V (power S.line b) →ₗ[k] SectionSpace V (power S.line (a+b))
  normalized : ∀ a b s t,
    (S.evaluation (a+b)).map (multiply a b s t) =
      (S.evaluation a).map s * (S.evaluation b).map t

/-- Degreewise multiplication has no ambiguity once its rational normalization is fixed. -/
theorem multiply_unique (S : SectionSeries V v)
    (A B : SectionMultiplication S) (a b : ℕ)
    (s : SectionSpace V (power S.line a)) (t : SectionSpace V (power S.line b)) :
    A.multiply a b s t = B.multiply a b s t := by
  apply (S.evaluation (a+b)).injective
  rw [A.normalized, B.normalized]

/-- Supremum of the actual finite-basis vanishing averages in degree m. -/
def maximalBasisOrder (S : SectionSeries V v) (m : ℕ) : EReal :=
  sSup {t | ∃ N : ℕ, ∃ b : Module.Basis (Fin N) k (SectionSpace V (power S.line m)),
    t = (basisExpectedOrder S m N b : EReal)}

end MathlibExt.AlgebraicGeometry.NormalizedSectionAlgebras
