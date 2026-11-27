/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LiGlobalSourceIndex
public import MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Native whole-index Li source assembly

The source is the actual global Li diagram with every marked-curve,
Cech, target-frame, coefficient and torus map. It is restricted to the
complete lifted-source index, raised as a WHOLE module-presheaf diagram,
and replaced by a genuine K-injective complex before the right Kan
extension is applied. The Kan functor is the actual right adjoint of
native restriction, so its limits include every actual source object and
map, rather than only one selected lift of an affine parent.

The comparison is the native adjunction unit followed by the source
resolution map. Requiring this ONE global cochain map to be a
quasi-isomorphism retains all overlap and coefficient-action data.
No objectwise collection of bundle isomorphisms substitutes for it.

Construction of the normalized source/assembly is an explicit Wanted
output. It does not assume a final POT or a chosen obstruction bundle.
Source: Jun Li, arXiv:math/0110113v1 §§1–2, with native diagram descent
and K-injective derived limits in the coefficient category.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LiGlobalSourceAssemblyModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeProjectiveLineModels ExpandedTargetChainGeometry
open StandardRelativeExpansionModels RubberMapFamilies RubberModuliStackModels
open StackAffineModules LiGlobalSourceIndex
open MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift
attribute [local instance] HasDerivedCategory.standard

variable {k : Type} [Field k]
  (O : ProjectiveLine (Spec (.of k)) (structureModule (Spec (.of k))))
  (P : RelativePair (k := k)) (D : OriginalRubberPair O P)
  (R : ProjectiveLine P.divisor.left (normalLineModule P)) (S : StandardSystem P R)
  {g n : ℕ} (a : Fin n → ℤ) (B : RubberModuliModel O P D R S (g := g) a)

abbrev IndexComplex := CochainComplex (LargeModules O P D R S a B) ℤ
abbrev LiftComplex := CochainComplex (LargeLiftModules O P D R S a B) ℤ
abbrev SmallModules := PresheafOfModules.{0} (coefficientRings O P D R S a B)

instance : (restrictToLifts O P D R S a B).Additive where
  map_add := by intros; rfl

instance : (parentRestriction O P D R S a B).Additive where
  map_add := by intros; rfl

/-- The actual base-point diagram is transported to the enriched source index. -/
def fromParents : ModulePresheaf B.stack ⥤ SmallModules O P D R S a B :=
  PresheafOfModules.pushforward₀ (projection O P D R S a B)
    (rings B.stack ⋙ forget₂ CommRingCat RingCat)

instance : (fromParents O P D R S a B).Additive where
  map_add := by intros; rfl

def raisedSource
    (L : LiFamilySourceDescent.GlobalComplex (B := B)) : IndexComplex O P D R S a B :=
  ((MathlibExt.Algebra.Category.ModuleCat.ModulePresheafUniverseLift.functor
    (coefficientRings O P D R S a B)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
      (((fromParents O P D R S a B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)

def localSource (L : LiFamilySourceDescent.GlobalComplex (B := B)) :
    LiftComplex O P D R S a B :=
  ((restrictToLifts O P D R S a B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (raisedSource O P D R S a B L)

/-- The genuine right Kan extension, identified by its native adjunction
with the actual source restriction functor. -/
structure RightKan where
  functor : LargeLiftModules O P D R S a B ⥤ LargeModules O P D R S a B
  adjunction : restrictToLifts O P D R S a B ⊣ functor
  [additive : functor.Additive]
attribute [instance] RightKan.additive

def RightKan.complex (K : RightKan O P D R S a B) :
    LiftComplex O P D R S a B ⥤ IndexComplex O P D R S a B :=
  K.functor.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The actual cochain adjunction unit, before any geometric comparison. -/
def RightKan.unit (K : RightKan O P D R S a B) (L : IndexComplex O P D R S a B) :
    L ⟶ K.complex.obj
      (((restrictToLifts O P D R S a B).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) where
  f i := K.adjunction.unit.app (L.X i)
  comm' i j _ := (K.adjunction.unit.naturality (L.d i j)).symm

/-- This is one global map on the whole source diagram. -/
def assemblyMap (K : RightKan O P D R S a B)
    (L : LiFamilySourceDescent.GlobalComplex (B := B))
    (I : LiftComplex O P D R S a B) (q : localSource O P D R S a B L ⟶ I) :
    raisedSource O P D R S a B L ⟶ K.complex.obj I :=
  RightKan.unit O P D R S a B K (raisedSource O P D R S a B L) ≫ K.complex.map q

/-- The native source and replacement are constructed outputs. The
replacement is K-injective in the ENTIRE coefficient-diagram category,
not separately in each individual affine component. -/
structure Assembly where
  native : LiFamilySourceDescent.Descent
    (O := O) (P := P) (D := D) (R := R) (S := S) (a := a) (B := B)
  kan : RightKan O P D R S a B
  replacement : LiftComplex O P D R S a B
  map : localSource O P D R S a B native.complex ⟶ replacement
  [resolution : QuasiIso map]
  [injective : replacement.IsKInjective]
  [comparison : QuasiIso (assemblyMap O P D R S a B kan native.complex replacement map)]
attribute [instance] Assembly.resolution Assembly.injective Assembly.comparison

def globalComplex (A : Assembly O P D R S a B) : IndexComplex O P D R S a B :=
  A.kan.complex.obj A.replacement

def globalDerived (A : Assembly O P D R S a B) :=
  DerivedCategory.Q.obj (globalComplex O P D R S a B A)

/-- The assembled object is tied to the whole original source diagram
by a single native derived isomorphism. -/
def sourceIso (A : Assembly O P D R S a B) :
    DerivedCategory.Q.obj (raisedSource O P D R S a B A.native.complex) ≅
      globalDerived O P D R S a B A :=
  asIso (DerivedCategory.Q.map
    (assemblyMap O P D R S a B A.kan A.native.complex A.replacement A.map))

end MathlibExt.AlgebraicGeometry.LiGlobalSourceAssemblyModels
