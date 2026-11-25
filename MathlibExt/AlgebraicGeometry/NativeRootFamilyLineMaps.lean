/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DenominatorRootStacks

/-!
# Native finite-root family line maps

The line arrow is the original DF inverse-image comparison, its root
reindexing comparison and the inverse finite-stack fibre normalization.
It fixes all coefficient sections, including zero sections.
Source: Talpo--Vistoli1410.1164v2, Sections3--5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeRootFamilyLineMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open EtaleMonoidInverseImage DeligneFaltingsSheaves DenominatorRootFamilies DenominatorRootStacks

variable {X Y : Scheme.{0}} [∀ (T Z : Scheme.{0}) (f : T ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X} (D : Structure A) (j : A ⟶ B)
  {b : Y ⟶ X} (R : Model I D j b)

/-- The actual direct-family coefficient after the native monoid compositor. -/
def familyCoefficient {T U : Over Y} (a : T ⟶ U) (V : U.left.Etale)
    (c : (pulledMonoids ((Over.map b).obj U) B).obj.obj (op V)) :=
  (monoidOverComparison B ((Over.map b).map a)).hom.hom.app
    (op ((SmallEtaleGeometry.etaleBaseChange a.left).obj V))
    (generator a.left (pulledMonoids ((Over.map b).obj U) B) V c)

/-- The original inverse-image line isomorphism on the coefficient generator. -/
def inverseImageLine {T U : Over Y} (a : T ⟶ U) (r : R.stack.Fibre U)
    (V : U.left.Etale) (c : (pulledMonoids ((Over.map b).obj U) B).obj.obj (op V)) :=
  ((I T.left U.left a.left (pulledMonoids ((Over.map b).obj U) B)).object
    ((R.fibre U).functor.obj r).of.extended).comparison V c

/-- Evaluate an original root reindexing comparison before selecting a stack-fibre dictionary. -/
def rootComparisonLine {T U : Over X} (a : T ⟶ U) (E : rootsAt I D j U)
    (Q : RootReindexing I D j a) (V : U.left.Etale)
    (c : (pulledMonoids U B).obj.obj (op V)) :=
  (Q.rootComparison E).comparison ((SmallEtaleGeometry.etaleBaseChange a.left).obj V)
    (generator a.left (pulledMonoids U B) V c)

/-- The native root-family comparison on that same generator. -/
def reindexingLine {T U : Over Y} (a : T ⟶ U) (r : R.stack.Fibre U)
    (V : U.left.Etale) (c : (pulledMonoids ((Over.map b).obj U) B).obj.obj (op V)) :=
  rootComparisonLine I D j ((Over.map b).map a) ((R.fibre U).functor.obj r) (R.reindexing a) V c

/-- The original finite-fibre comparison, in the direction into the native pulled root. -/
def fibreLine {T U : Over Y} (a : T ⟶ U) (r : R.stack.Fibre U)
    (V : U.left.Etale) (c : (pulledMonoids ((Over.map b).obj U) B).obj.obj (op V)) :=
  ((R.mapComparison a).inv.app r).iso.hom.hom.comparison
    ((SmallEtaleGeometry.etaleBaseChange a.left).obj V) (familyCoefficient (B := B) a V c)

/-- A finite chain packages actual module objects to share dependent coefficient conversions. -/
structure IsoChain3 (S : Scheme.{0}) where
  source : S.Modules
  first : S.Modules
  second : S.Modules
  target : S.Modules
  source_first : source ≅ first
  first_second : first ≅ second
  second_target : second ≅ target

/-- Native composition of the three displayed line maps. -/
def IsoChain3.compose {S : Scheme.{0}} (C : IsoChain3 S) : C.source ⟶ C.target :=
  C.source_first.hom ≫ C.first_second.hom ≫ C.second_target.hom

-- The chain shares native dependent line objects; its kernel conversion is large.
set_option maxHeartbeats 2000000 in
/-- The chain is computed from the original inverse-image, root and finite-fibre comparisons. -/
def familyLineChain {T U : Over Y} (a : T ⟶ U) (r : R.stack.Fibre U)
    (V : U.left.Etale) (c : (pulledMonoids ((Over.map b).obj U) B).obj.obj (op V)) :
    IsoChain3 ((SmallEtaleGeometry.etaleBaseChange a.left).obj V).left := by
  let W := (SmallEtaleGeometry.etaleBaseChange a.left).obj V
  let E := (R.fibre U).functor.obj r
  let M := pulledMonoids ((Over.map b).obj U) B
  let g := generator a.left M V c
  let d := familyCoefficient (B := B) a V c
  exact {
    source := (Scheme.Modules.pullback (SmallEtaleGeometry.projection a.left V)).obj
      ((E.of.extended.chart V).module c)
    first := (((I T.left U.left a.left M).object E.of.extended).pulled.chart W).module g
    second := (((R.reindexing a).functor.obj E).of.extended.chart W).module d
    target := (((R.fibre T).functor.obj
      ((R.stack.toPseudofunctor.map a.op.toLoc).toFunctor.obj r)).of.extended.chart W).module d
    source_first := inverseImageLine I D j R a r V c
    first_second := reindexingLine I D j R a r V c
    second_target := fibreLine I D j R a r V c }

/-- The literal composite through all three original native line maps. -/
def familyLineMap {T U : Over Y} (a : T ⟶ U) (r : R.stack.Fibre U)
    (V : U.left.Etale) (c : (pulledMonoids ((Over.map b).obj U) B).obj.obj (op V)) :=
  (familyLineChain I D j R a r V c).compose

end MathlibExt.AlgebraicGeometry.NativeRootFamilyLineMaps
