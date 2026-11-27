/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeRelativePeriodComparisonMaps
public import MathlibExt.CategoryTheory.StructuralPeriodConnectionSources
public import MathlibExt.RingTheory.ContinuousDeRhamQuotients

/-!
# Actual coefficient period cochains with total relative connection

Each degree is the native O_X scalar extension of the original
coefficient and form sheaves, followed by native tensor/exterior powers.
The positive differential is fixed on all exact-form generators by the
total coefficient connection and the actual exterior wedge. Sheaf-local
generation is explicit; arbitrary global Gamma is not identified with
raw Kaehler differentials.

Full cochains are fixed on EVERY local absolute-generator fraction of
the positive cochains. Full O_BdR is not assumed complete. Both complexes
are linear over the native inverse image of the BASE structural period
ring. The original cochain unit is fixed on the original native module,
tensor and exterior units. Final comparison maps are built separately
from this unit by the native derived adjunction.

References: Scholze, arXiv:1205.3463v2, Definition 6.8, Proposition 8.5
and Theorem 8.8; completed Stacks 07I0 native connection source.
Native Mathlib: Apache 2.0, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.PeriodCoefficientComplexSources

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields
open RingedDerivedCoefficientOperations RingSheafModuleTensors NativeRingInverseImages NativeFilteredDeRhamOutputs
open StructuralDeRhamPeriodSources UntiltingSheafSources StructuralPeriodConnectionSources

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {T : GrothendieckTopology D}
  [HasSheafify J CommRingCat.{1}] [HasSheafify T CommRingCat.{1}]
  [UnivLE.{max u₂ v₂, 1}]
  [HasSheafify T AddCommGrpCat.{1}] [T.WEqualsLocallyBijective AddCommGrpCat.{1}]
  (G : C ⥤ D) [G.IsContinuous J T]
  [(G.sheafPushforwardContinuous CommRingCat.{1} J T).IsRightAdjoint]
  (YP YF : Sheaf J CommRingCat.{1})
  (p : ℕ) [Fact p.Prime] (K : BaseField p)
  (O Rplus : Sheaf T CommRingCat.{1}) (A : UntiltingData p Rplus)
  (W : WittScalarSource p K O Rplus A)
  (φP : YP ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj W.naiveStructuralPositive)
  (φF : YF ⟶ (G.sheafPushforwardContinuous CommRingCat.{1} J T).obj W.naiveStructuralFull)
  (M Ω : Modules O)
  [(pushforward (𝟭 D) O W.naiveStructuralPositive W.originalToPositive).IsRightAdjoint]
  [(pushforward (𝟭 D) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).IsRightAdjoint]

def basePositive := inverseRing (J := J) (T := T) G YP
def baseFull := inverseRing (J := J) (T := T) G YF
def positiveBaseMap := inverseScalar (J := J) (T := T) G YP W.naiveStructuralPositive φP
def fullBaseMap := inverseScalar (J := J) (T := T) G YF W.naiveStructuralFull φF

def positiveTerm (n : ℕ) : Modules W.naiveStructuralPositive :=
  tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M)
    (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n)

def fullTerm (n : ℕ) : Modules W.naiveStructuralFull :=
  tensor W.naiveStructuralFull (fullForms p K O Rplus A W M)
    (exterior W.naiveStructuralFull (fullForms p K O Rplus A W Ω) n)

variable (d : ∀ U : Dᵒᵖ, O.obj.obj U →+ Ω.val.obj U)
  (nabla : ∀ U : Dᵒᵖ, M.val.obj U →+ (tensor O M Ω).val.obj U)
  (P : PositiveConnectionSource p K O Rplus A W Ω d)
  (F : FullConnectionSource p K O Rplus A W Ω d P)
  (R : Sheaf T CommRingCat.{1}) (η : R ⟶ O)
  (sx : R ⟶ baseFull (J := J) (T := T) G YF)
  [(pushforward (𝟭 D) R (baseFull (J := J) (T := T) G YF) sx).IsRightAdjoint]
  (original : CochainComplex.Plus (Modules R))
  (originalTerms : ∀ n : ℕ, original.obj.X (n : ℤ) ≅
    (restrict R O η).obj (tensor O M (exterior O Ω n)))

/-- All fields are source cochains/maps on FIXED native period terms. No higher bundle is an input. -/
structure Source where
  base_square : η ≫ W.originalToFull = sx ≫ fullBaseMap (J := J) (T := T) G YF p K O Rplus A W φF
  basePositiveHorizontal : ∀ U a,
    P.connection U ((positiveBaseMap (J := J) (T := T) G YP p K O Rplus A W φP).hom.app U a) = 0
  baseFullHorizontal : ∀ U a,
    F.connection U ((fullBaseMap (J := J) (T := T) G YF p K O Rplus A W φF).hom.app U a) = 0
  originalTensor : tensor O M Ω ⟶
    (pushforward (𝟭 D) O W.naiveStructuralPositive W.originalToPositive).obj
      (tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω))
  originalTensor_source : ∀ U m w,
    (originalTensor.val.app U).hom (generator O M Ω U m w) =
      (show ((pushforward (𝟭 D) O W.naiveStructuralPositive W.originalToPositive).obj
        (tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω))).val.obj U from
      generator W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω) U
        (originalFormUnit p K O Rplus A W M U m) (originalFormUnit p K O Rplus A W Ω U w))
  coefficientConnection : ∀ U : Dᵒᵖ, (positiveForms p K O Rplus A W M).val.obj U →+
    (tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω)).val.obj U
  coefficient_natural : ∀ {U V : Dᵒᵖ} (a : U ⟶ V) m,
    coefficientConnection V ((positiveForms p K O Rplus A W M).val.map a m) =
      (tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω)).val.map a
        (coefficientConnection U m)
  coefficient_source : ∀ (U : Dᵒᵖ) (r : W.naiveStructuralPositive.obj.obj U) (m : M.val.obj U),
    coefficientConnection U (r • originalFormUnit p K O Rplus A W M U m) =
      r • (show (tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M)
        (positiveForms p K O Rplus A W Ω)).val.obj U from (originalTensor.val.app U).hom (nabla U m)) +
        generator W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω) U
          (originalFormUnit p K O Rplus A W M U m) (P.connection U r)
  exactFormGeneration : sInf {N : (positiveForms p K O Rplus A W Ω).Submodule |
    ∀ U r, P.connection U r ∈ N.toSubmodule.obj U} = ⊤
  wedge : ∀ n : ℕ,
    tensor W.naiveStructuralPositive
      (tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω))
      (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n) ⟶ positiveTerm p K O Rplus A W M Ω (n + 1)
  wedge_source : ∀ (n : ℕ) (U : Dᵒᵖ) (m : (positiveForms p K O Rplus A W M).val.obj U)
    (w : (positiveForms p K O Rplus A W Ω).val.obj U)
    (a : ⋀[W.naiveStructuralPositive.obj.obj U]^n ((positiveForms p K O Rplus A W Ω).val.obj U)),
    ((wedge n).val.app U).hom
      (generator W.naiveStructuralPositive
        (tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω))
        (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n) U
          (generator W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω) U m w)
          (exteriorUnit W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n U a)) =
      generator W.naiveStructuralPositive (positiveForms p K O Rplus A W M)
        (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) (n + 1)) U m
          (exteriorUnit W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) (n + 1) U
            (MathlibExt.DeRhamSource.Crystalline.leftWedge n w a))
  positive : CochainComplex.Plus (Modules (basePositive (J := J) (T := T) G YP))
  positiveTerms : ∀ n : ℕ, positive.obj.X (n : ℤ) ≅
    (restrict (basePositive (J := J) (T := T) G YP) W.naiveStructuralPositive (positiveBaseMap (J := J) (T := T) G YP p K O Rplus A W φP)).obj
      (positiveTerm p K O Rplus A W M Ω n)
  positive_negative : ∀ i : ℤ, i < 0 → IsZero (positive.obj.X i)
  positive_source : ∀ (n : ℕ) (U : Dᵒᵖ) (m : (positiveForms p K O Rplus A W M).val.obj U)
    (a : Fin n → W.naiveStructuralPositive.obj.obj U),
    ((positiveTerms (n + 1)).hom.val.app U).hom
      (((positive.obj.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).val.app U).hom
        (((positiveTerms n).inv.val.app U).hom
          (show ((restrict (basePositive (J := J) (T := T) G YP) W.naiveStructuralPositive (positiveBaseMap (J := J) (T := T) G YP p K O Rplus A W φP)).obj
            (positiveTerm p K O Rplus A W M Ω n)).val.obj U from
          generator W.naiveStructuralPositive (positiveForms p K O Rplus A W M)
            (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n) U m
              (exteriorUnit W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n U
                (_root_.exteriorPower.ιMulti (W.naiveStructuralPositive.obj.obj U) n (fun i => P.connection U (a i))))))) =
    (show ((restrict (basePositive (J := J) (T := T) G YP) W.naiveStructuralPositive (positiveBaseMap (J := J) (T := T) G YP p K O Rplus A W φP)).obj
      (positiveTerm p K O Rplus A W M Ω (n + 1))).val.obj U from
      ((wedge n).val.app U).hom
        (generator W.naiveStructuralPositive
          (tensor W.naiveStructuralPositive (positiveForms p K O Rplus A W M) (positiveForms p K O Rplus A W Ω))
          (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n) U
            (coefficientConnection U m)
            (exteriorUnit W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n U
              (_root_.exteriorPower.ιMulti (W.naiveStructuralPositive.obj.obj U) n (fun i => P.connection U (a i))))))
  positiveTermUnit : ∀ n : ℕ, positiveTerm p K O Rplus A W M Ω n ⟶
    (pushforward (𝟭 D) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj (fullTerm p K O Rplus A W M Ω n)
  positiveTermUnit_source : ∀ (n : ℕ) (U : Dᵒᵖ) (m : (positiveForms p K O Rplus A W M).val.obj U)
    (a : ⋀[W.naiveStructuralPositive.obj.obj U]^n ((positiveForms p K O Rplus A W Ω).val.obj U)),
    ((positiveTermUnit n).val.app U).hom
      (generator W.naiveStructuralPositive (positiveForms p K O Rplus A W M)
        (exterior W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n) U m
          (exteriorUnit W.naiveStructuralPositive (positiveForms p K O Rplus A W Ω) n U a)) =
    (show ((pushforward (𝟭 D) W.naiveStructuralPositive W.naiveStructuralFull W.positiveToFull).obj
      (fullTerm p K O Rplus A W M Ω n)).val.obj U from
      generator W.naiveStructuralFull (fullForms p K O Rplus A W M)
        (exterior W.naiveStructuralFull (fullForms p K O Rplus A W Ω) n) U
          (positiveFormUnit p K O Rplus A W M U m)
          (exteriorUnit W.naiveStructuralFull (fullForms p K O Rplus A W Ω) n U
            (ExteriorAlgebra.powMapₛₗ n (W.positiveToFull.hom.app U).hom
              (formSemilinearUnit p K O Rplus A W Ω U) a)))
  full : CochainComplex.Plus (Modules (baseFull (J := J) (T := T) G YF))
  fullTerms : ∀ n : ℕ, full.obj.X (n : ℤ) ≅
    (restrict (baseFull (J := J) (T := T) G YF) W.naiveStructuralFull (fullBaseMap (J := J) (T := T) G YF p K O Rplus A W φF)).obj
      (fullTerm p K O Rplus A W M Ω n)
  full_negative : ∀ i : ℤ, i < 0 → IsZero (full.obj.X i)
  fraction_source : ∀ (n : ℕ) (U : Dᵒᵖ) (t : A.deRhamPositive.obj.obj U)
    (ht : SheafLocalGeneratorLocalization.IsLocalGenerator A.deRhamPositive
      (completedRegular p Rplus) A.completedTheta U t) (j : ℤ)
    (m : (positiveTerm p K O Rplus A W M Ω n).val.obj U),
    ((fullTerms (n + 1)).hom.val.app U).hom
      (((full.obj.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).val.app U).hom
        (((fullTerms n).inv.val.app U).hom
          (show ((restrict (baseFull (J := J) (T := T) G YF) W.naiveStructuralFull (fullBaseMap (J := J) (T := T) G YF p K O Rplus A W φF)).obj
            (fullTerm p K O Rplus A W M Ω n)).val.obj U from
            localGeneratorPower p K O Rplus A W U t ht (-j) •
              (show (fullTerm p K O Rplus A W M Ω n).val.obj U from ((positiveTermUnit n).val.app U).hom m)))) =
    (show ((restrict (baseFull (J := J) (T := T) G YF) W.naiveStructuralFull (fullBaseMap (J := J) (T := T) G YF p K O Rplus A W φF)).obj
      (fullTerm p K O Rplus A W M Ω (n + 1))).val.obj U from
      localGeneratorPower p K O Rplus A W U t ht (-j) •
        (show (fullTerm p K O Rplus A W M Ω (n + 1)).val.obj U from ((positiveTermUnit (n + 1)).val.app U).hom
          (show (positiveTerm p K O Rplus A W M Ω (n + 1)).val.obj U from
            ((positiveTerms (n + 1)).hom.val.app U).hom
              (((positive.obj.d (n : ℤ) ((n + 1 : ℕ) : ℤ)).val.app U).hom
                (((positiveTerms n).inv.val.app U).hom
                  (show ((restrict (basePositive (J := J) (T := T) G YP) W.naiveStructuralPositive (positiveBaseMap (J := J) (T := T) G YP p K O Rplus A W φP)).obj
                    (positiveTerm p K O Rplus A W M Ω n)).val.obj U from m))))))
  unit : original ⟶ (pushforward (𝟭 D) R (baseFull (J := J) (T := T) G YF) sx).mapCochainComplexPlus.obj full
  unit_source : ∀ (n : ℕ) (U : Dᵒᵖ) (m : M.val.obj U) (a : ⋀[O.obj.obj U]^n (Ω.val.obj U)),
    ((fullTerms n).hom.val.app U).hom
      (((unit.hom.f (n : ℤ)).val.app U).hom
        (((originalTerms n).inv.val.app U).hom
          (show ((restrict R O η).obj (tensor O M (exterior O Ω n))).val.obj U from
            generator O M (exterior O Ω n) U m (exteriorUnit O Ω n U a)))) =
    (show ((restrict (baseFull (J := J) (T := T) G YF) W.naiveStructuralFull (fullBaseMap (J := J) (T := T) G YF p K O Rplus A W φF)).obj
      (fullTerm p K O Rplus A W M Ω n)).val.obj U from
      generator W.naiveStructuralFull (fullForms p K O Rplus A W M)
        (exterior W.naiveStructuralFull (fullForms p K O Rplus A W Ω) n) U
          (originalFullFormSemilinearUnit p K O Rplus A W M U m)
          (exteriorUnit W.naiveStructuralFull (fullForms p K O Rplus A W Ω) n U
            (ExteriorAlgebra.powMapₛₗ n (W.originalToFull.hom.app U).hom
              (originalFullFormSemilinearUnit p K O Rplus A W Ω U) a)))

end MathlibExt.CategoryTheory.PeriodCoefficientComplexSources
