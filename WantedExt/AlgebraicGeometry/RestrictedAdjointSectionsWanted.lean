/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RestrictedAdjointSections
public import Batteries.Util.ProofWanted

/-!
# Restricted section multiplication and model moving-part comparison

Hacon--Xu arXiv1302.0298v2, §2 (restricted algebras and mobile b-divisors);
BCHM arXivmath/0610203v2, §3.6. All spaces are actual complete section
spaces of the same tensor powers. Product and pullback comparisons are
fixed on every local generator, and the restriction is the actual native
unit/pullback map. Fixed/mobile coefficients use actual section orders.
Generic section/tensor/Cartier primitives remain completed source inputs.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RestrictedAdjointSections

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

theorem_wanted model_fixed_part_monotone
    {k : Type} [Field k] {n : ℕ} (P : LogPair k n)
    (m : ℕ) (hm : 0 < m) (A : AdjointPower P m)
    (M₁ M₂ : BirationalModel P) (R : ModelRefinement M₁ M₂)
    (S₁ : ModelSections A M₁) (S₂ : ModelSections A M₂)
    [Module.Finite k (GenericSectionMaps.Sections P.variety.X A.cartier.line.val)]
    (F : FixedCartierPart S₁) (p : PrimePoint M₂.variety) :
    pulledFixedCoefficient R F p ≤ fixedCoefficient S₂ p

end MathlibExt.AlgebraicGeometry.RestrictedAdjointSections
