/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.BaseFilteredPeriodAssociation

/-!
# Source-normalized associated coefficient augmentation

The source coefficient is the actual positive period scalar extension,
restricted to the native inverse image of the BASE absolute period ring.
Its source complex is the native degree-zero cochain. The augmentation
into the actual relative period de Rham complex is fixed on EVERY
positive coefficient section by the GIVEN BASE association and the
native degree-zero tensor/exterior unit.

No higher comparison map is a field. Native derived adjunction and
scalar projection construct the final comparison from this original
source cochain unit in `NativeRelativePeriodComparisonMaps`.

Reference: Scholze, arXiv:1205.3463v2, Definition 7.5, Proposition 8.5
and Theorem 8.8. Native Mathlib, Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.AssociatedPeriodAugmentationSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open RingedDerivedCoefficientOperations NativeRingInverseImages RingSheafModuleTensors
open StructuralPeriodConnectionSources NativeFilteredDeRhamOutputs

attribute [local instance] HasDerivedCategory.standard

universe v u

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [UnivLE.{max u v, 1}] [HasSheafify J CommRingCat.{1}] [HasSheafify T CommRingCat.{1}]
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]
  [(G.sheafPushforwardContinuous CommRingCat.{1} J T).IsRightAdjoint]
  (AY PY : Sheaf J CommRingCat.{1}) (AX PX : Sheaf T CommRingCat.{1}) (sy : AY ⟶ PY)
  (a : AY ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj AX)
  (b : AX ⟶ PX) (L : Modules AX) (M Ω : Modules PX)

def baseAbsolute : Sheaf T CommRingCat.{1} := inverseRing (J := J) (T := T) G AY
def basePeriod : Sheaf T CommRingCat.{1} := inverseRing (J := J) (T := T) G PY
def absoluteScalar : baseAbsolute (J := J) (T := T) G AY ⟶ AX := inverseScalar G AY AX a
def scalar : baseAbsolute (J := J) (T := T) G AY ⟶ basePeriod (J := J) (T := T) G PY :=
  (G.sheafPullback CommRingCat.{1} J T).map sy

variable [(pushforward (𝟭 D) AX PX b).IsRightAdjoint]

def fullCoefficient : Modules PX := (pullback (𝟭 D) AX PX b).obj L

def coefficientComplex : CochainComplex.Plus (Modules (baseAbsolute (J := J) (T := T) G AY)) :=
  ⟨(CochainComplex.singleFunctor (Modules (baseAbsolute (J := J) (T := T) G AY)) 0).obj
    ((restrict (baseAbsolute (J := J) (T := T) G AY) AX (absoluteScalar (J := J) (T := T) G AY AX a)).obj L), ⟨0, by infer_instance⟩⟩

variable (association : fullCoefficient AX PX b L ≅ M)
  (period : CochainComplex.Plus (Modules (basePeriod (J := J) (T := T) G PY)))
  (r : basePeriod (J := J) (T := T) G PY ⟶ PX)
  (terms : ∀ n : ℕ, period.obj.X (n : ℤ) ≅
    (restrict (basePeriod (J := J) (T := T) G PY) PX r).obj (tensor PX M (exterior PX Ω n)))
  [(pushforward (𝟭 D) (baseAbsolute (J := J) (T := T) G AY) (basePeriod (J := J) (T := T) G PY) (scalar (J := J) (T := T) G AY PY sy)).IsRightAdjoint]

/-- Native coefficient augmentation is a source construction, pinned in degree zero by the
BASE association. A freely chosen higher comparison cannot satisfy this unit normalization. -/
structure Source where
  unit : coefficientComplex (J := J) (T := T) G AY AX a L ⟶
    (pushforward (𝟭 D) (baseAbsolute (J := J) (T := T) G AY) (basePeriod (J := J) (T := T) G PY) (scalar (J := J) (T := T) G AY PY sy)).mapCochainComplexPlus.obj period
  original_source : ∀ (U : Dᵒᵖ) (l : L.val.obj U),
    ((terms 0).hom.val.app U).hom (((unit.hom.f 0).val.app U).hom
      (show ((coefficientComplex (J := J) (T := T) G AY AX a L).obj.X 0).val.obj U from l)) =
    (show ((restrict (basePeriod (J := J) (T := T) G PY) PX r).obj (tensor PX M (exterior PX Ω 0))).val.obj U from
      generator PX M (exterior PX Ω 0) U
        ((association.hom.val.app U).hom
          ((((adjunction (𝟭 D) AX PX b).unit.app L).val.app U).hom l))
        (exteriorUnit PX Ω 0 U (_root_.exteriorPower.ιMulti (PX.obj.obj U) 0 (fun i => i.elim0))))

variable (S : Source G AY PY AX PX sy a b L M Ω association period r terms)
  [HasSheafify J AddCommGrpCat.{1}] [J.WEqualsLocallyBijective AddCommGrpCat.{1}]
  [(pushforward G AY (baseAbsolute (J := J) (T := T) G AY)
    (inverseUnit (J := J) (T := T) G AY)).IsRightAdjoint]
  [(pushforward G PY (basePeriod (J := J) (T := T) G PY)
    (inverseUnit (J := J) (T := T) G PY)).IsRightAdjoint]
  [(pushforward (𝟭 C) AY PY sy).IsRightAdjoint]
  [EnoughInjectives (Modules AY)] [EnoughInjectives (Modules PY)]
  [EnoughInjectives (Modules (baseAbsolute (J := J) (T := T) G AY))]
  [EnoughInjectives (Modules (basePeriod (J := J) (T := T) G PY))]
  [PullbackSourceUnit G AY (baseAbsolute (J := J) (T := T) G AY) (inverseUnit (J := J) (T := T) G AY)]
  [PullbackSourceUnit G PY (basePeriod (J := J) (T := T) G PY) (inverseUnit (J := J) (T := T) G PY)]
  [PullbackSourceUnit (𝟭 D) (baseAbsolute (J := J) (T := T) G AY)
    (basePeriod (J := J) (T := T) G PY) (scalar (J := J) (T := T) G AY PY sy)]
  (Q : NativeScalarProjectionMaps.SourceSquare G AY PY (baseAbsolute (J := J) (T := T) G AY)
    (basePeriod (J := J) (T := T) G PY) sy (scalar (J := J) (T := T) G AY PY sy)
    (inverseUnit (J := J) (T := T) G AY) (inverseUnit (J := J) (T := T) G PY))
  (AO : DerivedAdjunctionSource G AY (baseAbsolute (J := J) (T := T) G AY) (inverseUnit (J := J) (T := T) G AY))
  (AP : DerivedAdjunctionSource G PY (basePeriod (J := J) (T := T) G PY) (inverseUnit (J := J) (T := T) G PY))
  (AS : DerivedAdjunctionSource (𝟭 D) (baseAbsolute (J := J) (T := T) G AY)
    (basePeriod (J := J) (T := T) G PY) (scalar (J := J) (T := T) G AY PY sy))
  [PreservesFiniteLimits (NativeScalarProjectionMaps.scalarY AY PY sy)]
  [PreservesFiniteColimits (NativeScalarProjectionMaps.scalarY AY PY sy)]

/-- The associated lisse-to-period comparison is built from the ORIGINAL cochain augmentation
and native derived adjunction/scalar projection. Its IsIso remains an OUTPUT conclusion. -/
def comparison (i : ℤ) := NativeRelativePeriodComparisonMaps.degreeComparison G AY PY
  (baseAbsolute (J := J) (T := T) G AY) (basePeriod (J := J) (T := T) G PY)
  sy (scalar (J := J) (T := T) G AY PY sy) (inverseUnit (J := J) (T := T) G AY) (inverseUnit (J := J) (T := T) G PY)
  Q AO AP AS (coefficientComplex (J := J) (T := T) G AY AX a L) period S.unit i

end MathlibExt.CategoryTheory.AssociatedPeriodAugmentationSources
