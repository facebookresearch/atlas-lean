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
# Character invariance of the maximal covariant C-star seminorm

For a point-norm action α of a locally compact group G on a nonunital C-star algebra A and
regular Haar measure μ, write Mχf(s)=χ(s)•f(s). A C-star seminorm p dominated by the L¹ gauge
remains dominated after pullback along Mχ. Consequently the maximal such seminorm pmax
satisfies pmax(Mχf)=pmax(f) for every continuous unitary character χ and compactly supported
coefficient f.
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
/-- **Character pullback preserves L¹-admissibility.**

Let p be a C-star seminorm on the Haar twisted-convolution core satisfying p(f)≤∫ s, ‖f(s)‖ ∂μ
for every compactly supported f. For a continuous unitary character χ, its pullback f↦p(Mχf),
where Mχf(s)=χ(s)•f(s), satisfies the same bound.
-/
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
/-- **Maximal covariant seminorm bound after modulation.**

For a continuous unitary character χ of G and Haar-core coefficient f, pmax(Mχf)≤pmax(f),
where Mχf(s)=χ(s)•f(s) and pmax is the supremum of the C-star seminorms dominated by the L¹
gauge.
-/
theorem maximal_character_le (chi : PontryaginDual G) (f : Carrier mu alpha) :
    maximalCStarSeminorm mu alpha (characterModulation mu alpha chi f) ≤
      maximalCStarSeminorm mu alpha f :=
  le_maximalCStarSeminorm mu alpha
    (admissible_character_pullback mu alpha chi (maximalCStarSeminorm_mem_admissible mu alpha)) f

omit [mu.Regular] in
/-- **Maximal covariant seminorm is character invariant.**

For every unitary character χ of G and compactly supported coefficient f, pmax(Mχf)=pmax(f),
with Mχf(s)=χ(s)•f(s) and pmax the maximal L¹-dominated C-star seminorm of the Haar
convolution core.
-/
theorem maximal_character_eq (chi : PontryaginDual G) (f : Carrier mu alpha) :
    maximalCStarSeminorm mu alpha (characterModulation mu alpha chi f) =
      maximalCStarSeminorm mu alpha f := by
  apply le_antisymm (maximal_character_le mu alpha chi f)
  have h := maximal_character_le mu alpha chi⁻¹ (characterModulation mu alpha chi f)
  simpa only [← characterModulation_mul_character, inv_mul_cancel, characterModulation_one] using h

end HaarTwistedCore
