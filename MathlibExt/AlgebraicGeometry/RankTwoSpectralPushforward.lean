/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoSpectralFamilies
public import MathlibExt.AlgebraicGeometry.NumericalCompactifiedJacobians
public import Mathlib.CategoryTheory.Core
public import MathlibExt.AlgebraicGeometry.CurveCohomologyCalculus

/-!
# Singular integral spectral sheaves and their tautological pushforward

Objects are actual coherent rank-one torsion-free module sheaves on the
integral spectral equation scheme. Their degree is one plus deg K, which
is 2g-1 for the degree-one Higgs problem. The underlying Higgs sheaf is
literally the native finite pushforward. Its field is pushforward of
multiplication by the actual tautological y, followed by the inverse of
the projection-formula map defined by the native module adjunction.
Arrows are the actual pushed sheaf isomorphisms.

Source: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2,
Section 1.3.2 and Theorem 1.3.4; Beauville--Narasimhan--Ramanan,
Proposition 3.6. Degree-one Picard normalization requires a twist and is
not used as the degree of the directly pushed sheaf.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RankTwoSpectralPushforward

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoHitchinModels
open RankTwoSpectralFamilies GeometricHiggsFamilies CoherentCurveLinearSeries
open AlgebraicLineBundleFamilies LineBundleTaskContracts RelativeLambdaReindexing
open NumericalCompactifiedJacobians DeligneFaltingsCategories

/-- The genuine projection-formula mate, with no separately supplied comparison map. -/
def projectionFormulaMap {X Y : Scheme.{0}} (pi : X ⟶ Y)
    (P : TensorPullbackComparison pi) (F : X.Modules) (L : Y.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward pi).obj F) L ⟶
      (Scheme.Modules.pushforward pi).obj
        (moduleTensor X F ((Scheme.Modules.pullback pi).obj L)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction pi).homEquiv _ _
    ((P.iso ((Scheme.Modules.pushforward pi).obj F) L).hom ≫
      tensorMap ((Scheme.Modules.pullbackPushforwardAdjunction pi).counit.app F)
        (𝟙 ((Scheme.Modules.pullback pi).obj L)))

/-- Multiplication by the actual tautological line section on a spectral module. -/
def tautologicalMultiplication {X Y : Scheme.{0}} (pi : X ⟶ Y)
    (F : X.Modules) (L : Y.Modules)
    (y : Section ((Scheme.Modules.pullback pi).obj L)) :
    F ⟶ moduleTensor X F ((Scheme.Modules.pullback pi).obj L) :=
  (tensorRightUnit X F).inv ≫ tensorMap (𝟙 F) y

def nativeTwistedImage {X Y : Scheme.{0}} (pi : X ⟶ Y)
    (F : X.Modules) (L : Y.Modules)
    (y : Section ((Scheme.Modules.pullback pi).obj L))
    (P : TensorPullbackComparison pi) (hL : IsLineBundle L)
    (hF : CurveVectorBundles.IsVectorBundle ((Scheme.Modules.pushforward pi).obj F) 2)
    (hP : IsIso (projectionFormulaMap pi P F L)) : TwistedBundle Y L 2 := by
  letI := hP
  exact {
    module := (Scheme.Modules.pushforward pi).obj F
    twistLine := hL
    bundle := hF
    field := (Scheme.Modules.pushforward pi).map (tautologicalMultiplication pi F L y) ≫
      inv (projectionFormulaMap pi P F L) }

def baseChangedTotalMap {C T : ComplexScheme} [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] {S : SectionBases C}
    (F : SpectralFamily C S) (s : T ⟶ base C) : baseChangedSpectral F s ⟶
      totalWithBase C F.totalLine :=
  pullback.fst (spectralProjection F.ideal) (prod.map (𝟙 C) s) ≫ spectralInclusion F.ideal

theorem baseChangedTotalMap_curve {C T : ComplexScheme} [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] {S : SectionBases C}
    (F : SpectralFamily C S) (s : T ⟶ base C) :
    baseChangedTotalMap F s ≫ toCurve C F.totalLine =
      baseChangedProjection F s ≫ (prod.fst : prod C T ⟶ C) := by
  calc
    _ = pullback.fst (spectralProjection F.ideal) (prod.map (𝟙 C) s) ≫
        spectralProjection F.ideal ≫ (prod.fst : prod C (base C) ⟶ C) := by
      dsimp only [baseChangedTotalMap, spectralProjection]
      simp only [Category.assoc, toCurveBase_first]
    _ = baseChangedProjection F s ≫ prod.map (𝟙 C) s ≫
        (prod.fst : prod C (base C) ⟶ C) := by
      rw [← Category.assoc, pullback.condition]
      rfl
    _ = _ := by simp

/-- Tautological y after every actual coefficient-scheme base change. -/
def baseChangedTautological {C T : ComplexScheme} [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] {S : SectionBases C}
    (F : SpectralFamily C S) (s : T ⟶ base C) :
    Section ((Scheme.Modules.pullback (baseChangedProjection F s).left).obj
      ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (canonicalLine C))) :=
  pulledTautological (toCurve C F.totalLine) (universalTautological C F.totalLine)
    (baseChangedProjection F s ≫ (prod.fst : prod C T ⟶ C))
    (baseChangedTotalMap F s) (baseChangedTotalMap_curve F s) ≫
    (Scheme.Modules.pullbackComp (baseChangedProjection F s).left
      (prod.fst : prod C T ⟶ C).left).inv.app (canonicalLine C)

variable (C : ComplexScheme) [IsProperCurve C.hom] [HasConstantGlobalSections C.hom]
    (B : BaseChanges C) (M : ModuliModel C B)
  (S : SectionBases C) (H : HitchinModel C B M S) (F : SpectralFamily C S)
  (Ω : Type) [Field Ω] [Algebra ℂ Ω] (s : complexField Ω ⟶ base C)

def spectralOverField : Over (Spec (.of Ω)) :=
  Over.mk (baseChangedProjection F s ≫ (prod.snd : prod C (complexField Ω) ⟶ complexField Ω)).left

/-- Ordinary spectral degree for a directly pushed degree-one Higgs sheaf: one plus the degree
`2g - 2` of the canonical line. -/
def spectralDegree : ℤ := 2 * (genus C.hom : ℤ) - 1

/-- Rank-one torsion-free sheaves on the spectral fibre, a proper curve, whose degree
`χ(E) - χ(𝒪)` is the spectral degree. -/
def RankOneProperty : ObjectProperty (Core (baseChangedSpectral F s).left.Modules) := fun E =>
  ∃ (_ : IsProperCurve (spectralOverField C S F Ω s).hom) (hF : IsFiniteTypeQuasicoherent E.of),
    IsTorsionFree E.of ∧ HasGenericRankOne E.of ∧
      euler (spectralOverField C S F Ω s).hom E.of hF -
          CurveCohomologyCalculus.finrankEuler01 (spectralOverField C S F Ω s).hom
            (structureModule (spectralOverField C S F Ω s).left) =
        spectralDegree C

abbrev RankOneSheaves := (RankOneProperty C S F Ω s).FullSubcategory

def HiggsFibreProperty : ObjectProperty (StableFamily C (complexField Ω)) := fun E =>
  M.classes.map (complexField Ω) E ≫ H.map = s

abbrev HiggsFibre := (HiggsFibreProperty C B M S H Ω s).FullSubcategory

/-- Data and conditions for pushing rank-one sheaves on the spectral fibre over an `Ω`-point `s` of
the Hitchin base forward to Higgs bundles. Write `π` for the projection from the spectral fibre
over `s` to `C × Spec Ω`, and `K` for the pullback of the canonical line bundle of `C` to
`C × Spec Ω`. The fields are: a comparison of pullback along `π` with tensor products (`tensor`);
`K` is a line bundle (`line`); and, for every rank-one torsion-free sheaf `E` on the spectral fibre
of degree `2g - 1`, where `g` is the genus of `C` (an object of `RankOneSheaves`), the
projection-formula map `π_* E ⊗ K ⟶ π_* (E ⊗ π^* K)` is an isomorphism (`formula`), `π_* E` is a
vector bundle of rank two (`rank`), and the Higgs bundle on `π_* E` whose field is the pushforward
of multiplication by the tautological section followed by the inverse of the projection-formula
map is admissible, that is, stable of rank two and degree one on every geometric fibre (`stable`),
and lies over `s` under the Hitchin map (`characteristic`); finally, the pushforward of every
isomorphism `E ≅ E'` of such sheaves commutes with the Higgs fields (`arrows`). -/
structure PushforwardProofs where
  tensor : TensorPullbackComparison (baseChangedProjection F s).left
  line : IsLineBundle
    ((Scheme.Modules.pullback (prod.fst : prod C (complexField Ω) ⟶ C).left).obj (canonicalLine C))
  formula : ∀ E : RankOneSheaves C S F Ω s, IsIso
    (projectionFormulaMap (baseChangedProjection F s).left tensor E.obj.of
      ((Scheme.Modules.pullback (prod.fst : prod C (complexField Ω) ⟶ C).left).obj
        (canonicalLine C)))
  rank : ∀ E : RankOneSheaves C S F Ω s, CurveVectorBundles.IsVectorBundle
    ((Scheme.Modules.pushforward (baseChangedProjection F s).left).obj E.obj.of) 2
  stable : ∀ E : RankOneSheaves C S F Ω s, Admissible C (complexField Ω)
    (nativeTwistedImage (baseChangedProjection F s).left E.obj.of
      ((Scheme.Modules.pullback (prod.fst : prod C (complexField Ω) ⟶ C).left).obj
        (canonicalLine C))
      (baseChangedTautological F s) tensor line (rank E) (formula E))
  characteristic : ∀ E : RankOneSheaves C S F Ω s,
    M.classes.map (complexField Ω) ⟨nativeTwistedImage (baseChangedProjection F s).left E.obj.of
      ((Scheme.Modules.pullback (prod.fst : prod C (complexField Ω) ⟶ C).left).obj
        (canonicalLine C))
      (baseChangedTautological F s) tensor line (rank E) (formula E), stable E⟩ ≫ H.map = s
  arrows : ∀ {E E' : RankOneSheaves C S F Ω s} (a : E ⟶ E'),
    ((Scheme.Modules.pushforward (baseChangedProjection F s).left).mapIso a.hom.iso).hom ≫
      (nativeTwistedImage (baseChangedProjection F s).left E'.obj.of
        ((Scheme.Modules.pullback (prod.fst : prod C (complexField Ω) ⟶ C).left).obj
          (canonicalLine C))
        (baseChangedTautological F s) tensor line (rank E') (formula E')).field =
      (nativeTwistedImage (baseChangedProjection F s).left E.obj.of
        ((Scheme.Modules.pullback (prod.fst : prod C (complexField Ω) ⟶ C).left).obj
          (canonicalLine C))
        (baseChangedTautological F s) tensor line (rank E) (formula E)).field ≫
        tensorMap ((Scheme.Modules.pushforward (baseChangedProjection F s).left).mapIso
          a.hom.iso).hom (𝟙 _)

def pushforwardFunctor (P : PushforwardProofs C B M S H F Ω s) :
    RankOneSheaves C S F Ω s ⥤ HiggsFibre C B M S H Ω s where
  obj E := ⟨⟨nativeTwistedImage (baseChangedProjection F s).left E.obj.of
    ((Scheme.Modules.pullback (prod.fst : prod C (complexField Ω) ⟶ C).left).obj (canonicalLine C))
    (baseChangedTautological F s) P.tensor P.line (P.rank E) (P.formula E), P.stable E⟩,
    P.characteristic E⟩
  map a := ⟨⟨⟨(Scheme.Modules.pushforward (baseChangedProjection F s).left).mapIso a.hom.iso,
    P.arrows a⟩⟩⟩
  map_id E := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply TwistedBundle.Hom.ext
    apply Iso.ext
    change (Scheme.Modules.pushforward (baseChangedProjection F s).left).map
      (𝟙 E.obj.of) = 𝟙 _
    exact (Scheme.Modules.pushforward (baseChangedProjection F s).left).map_id E.obj.of
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply TwistedBundle.Hom.ext
    apply Iso.ext
    change (Scheme.Modules.pushforward (baseChangedProjection F s).left).map
      (a.hom.iso.hom ≫ b.hom.iso.hom) =
        (Scheme.Modules.pushforward (baseChangedProjection F s).left).map a.hom.iso.hom ≫
          (Scheme.Modules.pushforward (baseChangedProjection F s).left).map b.hom.iso.hom
    exact (Scheme.Modules.pushforward (baseChangedProjection F s).left).map_comp _ _

end MathlibExt.AlgebraicGeometry.RankTwoSpectralPushforward
