/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.CharacterModulation
public import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.FullCovariantSeminorm
public import MathlibExt.Analysis.CStarAlgebra.SeminormPullback

/-!
# Original full crossed-product gauge under actual character modulation

Composition with the computed raw character star automorphism preserves
admissibility by the original L1 isometry. The original maximal gauge is
itself admissible, so its character pullback is bounded by that same maximum.
The inverse character gives the reverse inequality. This is the original
all-covariant full norm, through its already proved intrinsic identification.
No covariant model, isometry certificate or desired completed action is input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HaarTwistedCore

universe uG uA

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable (mu : Measure G) [mu.IsHaarMeasure] [mu.Regular] (alpha : PointNormCStarAction G A)

omit [mu.Regular] in
/-- Actual character pullback preserves the original L1-admissible C-star seminorm family. -/
theorem admissible_character_pullback
    (chi : PontryaginDual G) {p : CStarSeminorm (Carrier mu alpha)}
    (hp : p ∈ admissibleCStarSeminorms mu alpha) :
    p.comp (characterModulationEquiv mu alpha chi).toNonUnitalStarAlgHom ∈
      admissibleCStarSeminorms mu alpha := by
  intro f
  change p (characterModulation mu alpha chi f) ≤ l1Gauge mu alpha f
  exact (hp (characterModulation mu alpha chi f)).trans
    (l1Gauge_characterModulation mu alpha chi f).le

omit [mu.Regular] in
/-- The actual modulated original full gauge is bounded by the same original full gauge. -/
theorem maximal_character_le (chi : PontryaginDual G) (f : Carrier mu alpha) :
    maximalCStarSeminorm mu alpha (characterModulation mu alpha chi f) ≤
      maximalCStarSeminorm mu alpha f :=
  le_maximalCStarSeminorm mu alpha
    (admissible_character_pullback mu alpha chi (maximalCStarSeminorm_mem_admissible mu alpha)) f

omit [mu.Regular] in
/-- The actual original full covariant norm is exactly unchanged by the dual character. -/
theorem maximal_character_eq (chi : PontryaginDual G) (f : Carrier mu alpha) :
    maximalCStarSeminorm mu alpha (characterModulation mu alpha chi f) =
      maximalCStarSeminorm mu alpha f := by
  apply le_antisymm (maximal_character_le mu alpha chi f)
  have h := maximal_character_le mu alpha chi⁻¹ (characterModulation mu alpha chi f)
  simpa only [← characterModulation_mul_character, inv_mul_cancel, characterModulation_one] using h

end HaarTwistedCore
