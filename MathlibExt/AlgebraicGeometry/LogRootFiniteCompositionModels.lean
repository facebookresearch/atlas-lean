/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogRootFiniteCompositeCoordinates
public import MathlibExt.AlgebraicGeometry.NativeRootFamilyLineMaps

/-!
# Native finite-root line composition

All line maps below are computed from the original finite-fibre
counits and the literal DF restriction. A composition cell is normalized
on these actual n-root lines, including zero sections; its n-th-power
restriction alone would not fix a root-of-unity phase.
Source: Talpo--Vistoli1410.1164v2, Sections3--6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogRootFiniteCompositionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels LogRootMorphismModels
open GeometricFiniteRootArrowModels CanonicalLogRootArrowModels LogRootCompositionModels
open LogRootFiniteCompositeCoordinates

variable [InverseImageTheory.{0}] (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y)
  (RX : RootRealization X D I) (RY : RootRealization Y D I)

/-- The finite arrow on the original native root-line dictionaries:
`CanonicalLogRootArrowModels.nativeFiniteLineMap`. -/
abbrev nativeFiniteLineMap (F : FiniteArrow I D f RX RY) (T : Over X.scheme) (n : Exponent)
    (r : (RX.finite n).stack.Fibre T) (V : T.left.Etale)
    (b : (targetMonoid D f RY.dictionary T).obj.obj (op V)) :=
  CanonicalLogRootArrowModels.nativeFiniteLineMap I D f RX RY F T n r V b

local instance chainComposeIsIso {S : Scheme.{0}}
    (C : NativeRootFamilyLineMaps.IsoChain3 S) : IsIso C.compose := by
  dsimp only [NativeRootFamilyLineMaps.IsoChain3.compose]
  infer_instance

/-- The inverse is also the literal inverse of the computed three-comparison chain. -/
def nativeFamilyLineIso (Z : LogScheme.{0}) (RZ : RootRealization Z D I) (n : Exponent)
    {T U : Over Z.scheme} (a : T ⟶ U) (r : (RZ.finite n).stack.Fibre U)
    (V : U.left.Etale) (b : (pulledMonoids (InfiniteDenominatorRoots.fibreBase U)
      RZ.dictionary.characteristic).obj.obj (op V)) :=
  asIso ((NativeRootFamilyLineMaps.familyLineChain I RZ.dictionary.df
    (powerMap RZ.dictionary.characteristic n.val) (RZ.finite n) a r V b).compose)

variable {Z : LogScheme.{0}} (g : EtaleLogSchemes.Hom Y Z) (h : EtaleLogSchemes.Hom X Z)
  (RZ : RootRealization Z D I) (F : FiniteArrow I D f RX RY)
  (G : FiniteArrow I D g RY RZ) (H : FiniteArrow I D h RX RZ) (S : OriginalSquare f g h)

omit [InverseImageTheory] in
/-- The parameter equality has the literal identity as underlying scheme map. -/
theorem parameterArrow_left (T : Over X.scheme) :
    (parameterArrow f g h S T).left = 𝟙 T.left := by
  change (Over.forget Z.scheme).map (eqToHom (parameter_test_eq f g h S T)) = _
  rw [eqToHom_map]
  rfl

/-- Its actual small-etale projection is an arrow over that same parameter scheme. -/
def parameterEtaleArrow (T : Over X.scheme) (V : T.left.Etale) :
    (SmallEtaleGeometry.etaleBaseChange (parameterArrow f g h S T).left).obj V ⟶ V := by
  refine MorphismProperty.Over.homMk
    (SmallEtaleGeometry.projection (parameterArrow f g h S T).left V) ?_
  change pullback.fst V.hom (parameterArrow f g h S T).left ≫ V.hom =
    pullback.snd V.hom (parameterArrow f g h S T).left
  exact (pullback.condition (f := V.hom) (g := (parameterArrow f g h S T).left)).trans
    ((congrArg (fun k : T.left ⟶ T.left =>
      pullback.snd V.hom (parameterArrow f g h S T).left ≫ k)
      (parameterArrow_left f g h S T)).trans (Category.comp_id _))

/-- The coefficient on the h-test is the native monoid compositor's actual image. -/
def compositeTargetCoefficient (T : Over X.scheme) (V : T.left.Etale)
    (b : (targetMonoid D g RZ.dictionary ((Over.map f.map).obj T)).obj.obj (op V)) :=
  NativeRootFamilyLineMaps.familyCoefficient
    (B := RZ.dictionary.characteristic) (b := 𝟙 Z.scheme)
    (parameterArrow f g h S T) V b

/-- The original f,g and h characteristic maps agree after the actual parameter reindexing. -/
def compositionCoefficientCondition (T : Over X.scheme) (V : T.left.Etale)
    (b : (targetMonoid D g RZ.dictionary ((Over.map f.map).obj T)).obj.obj (op V)) : Prop :=
  (sourceMonoid D RX.dictionary T).obj.map (parameterEtaleArrow f g h S T V).op
    ((F.parameter T).characteristic.hom.app (op V)
      ((G.parameter ((Over.map f.map).obj T)).characteristic.hom.app (op V) b)) =
  (H.parameter T).characteristic.hom.app
    (op ((SmallEtaleGeometry.etaleBaseChange (parameterArrow f g h S T).left).obj V))
    (compositeTargetCoefficient I D f g h RZ S T V b)

-- Five native line maps retain all original parameter and coefficient comparisons.
set_option maxHeartbeats 2000000 in
/-- The actual composite root line runs through parameter reindexing, g, f and the original etale restriction. -/
def compositeRootLine (T : Over X.scheme) (n : Exponent)
    (r : (RX.finite n).stack.Fibre T) (V : T.left.Etale)
    (b : (targetMonoid D g RZ.dictionary ((Over.map f.map).obj T)).obj.obj (op V))
    (hc : compositionCoefficientCondition I D f RX RY g h RZ F G H S T V b) :=
  let Ty := (Over.map f.map).obj T
  let a := parameterArrow f g h S T
  let W := (SmallEtaleGeometry.etaleBaseChange a.left).obj V
  let rF := (F.functor T n).obj r
  let rG := (G.functor Ty n).obj rF
  let cG := (G.parameter Ty).characteristic.hom.app (op V) b
  let cF := (F.parameter T).characteristic.hom.app (op V) cG
  let E := ((RX.finite n).fibre T).functor.obj r
  let P := Scheme.Modules.pullback (SmallEtaleGeometry.projection a.left V)
  (nativeFamilyLineIso I D Z RZ n a rG V b).inv ≫
    P.map (nativeFiniteLineMap I D g RY RZ G Ty n rF V b) ≫
    P.map (nativeFiniteLineMap I D f RX RY F T n r V cG) ≫
    (E.of.extended.reindex (parameterEtaleArrow f g h S T V) cF).hom ≫
    eqToHom (congrArg (E.of.extended.chart W).module hc)

/-- An actual finite comparison cell is fixed on every native n-root line, not merely on n-th powers. -/
def finiteCompositionLineCondition (T : Over X.scheme) (n : Exponent)
    (C : FiniteComparison f g h I D RX RY RZ F G H S T n)
    (r : (RX.finite n).stack.Fibre T) (V : T.left.Etale)
    (b : (targetMonoid D g RZ.dictionary ((Over.map f.map).obj T)).obj.obj (op V))
    (hc : compositionCoefficientCondition I D f RX RY g h RZ F G H S T V b) : Prop :=
  let W := (SmallEtaleGeometry.etaleBaseChange (parameterArrow f g h S T).left).obj V
  let c := compositeTargetCoefficient I D f g h RZ S T V b
  (((((RZ.finite n).fibre ((Over.map h.map).obj T)).functor.map
    (C.hom.app r)).iso.hom.hom.comparison W c).hom) ≫
      compositeRootLine I D f RX RY g h RZ F G H S T n r V b hc =
  nativeFiniteLineMap I D h RX RZ H T n r W c

/-- Finite composition data are normalized through the original characteristic square and every root coefficient. -/
structure FiniteComposition where
  comparison : ∀ (T : Over X.scheme) (n : Exponent),
    FiniteComparison f g h I D RX RY RZ F G H S T n
  coefficient : ∀ (T : Over X.scheme) (V : T.left.Etale)
    (b : (targetMonoid D g RZ.dictionary ((Over.map f.map).obj T)).obj.obj (op V)),
    compositionCoefficientCondition I D f RX RY g h RZ F G H S T V b
  line : ∀ (T : Over X.scheme) (n : Exponent)
    (r : (RX.finite n).stack.Fibre T) (V : T.left.Etale)
    (b : (targetMonoid D g RZ.dictionary ((Over.map f.map).obj T)).obj.obj (op V)),
    finiteCompositionLineCondition I D f RX RY g h RZ F G H S T n
      (comparison T n) r V b (coefficient T V b)

end MathlibExt.AlgebraicGeometry.LogRootFiniteCompositionModels
