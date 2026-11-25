/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`StacksFrontier/AlgebraicGeometry/GroupScheme/AbelianSchemeBaseChange.lean`
(AxiomMath/Stacks at commit c496df0d9beea9deaeabcea8492605f9a0a2313b,
https://github.com/AxiomMath/Stacks): the group-object base-change constructions.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Modification notice: the smooth, proper, geometrically connected definition is used
directly on Mathlib scheme morphisms; schemes are bundled; relative Poincaré-family
interfaces over arbitrary base schemes are added.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies

/-!
# General abelian schemes and relative Poincaré-family interfaces

An abelian scheme is an actual smooth proper commutative group scheme with
geometrically connected fibres over an arbitrary actual base scheme. Base
change is constructed and all geometric properties are transported by
native pullback theorems. No characteristic, field or closed-base assumption
is included in the interface.

The relative dual contract uses actual line-module sheaves on actual fibre
products, both zero normalizations, geometric Picard-zero fibres, tensor
addition and universality for every base scheme T. These are public data
interfaces; constructing the relative dual remains separate Wanted work.

References: Conrad, *Néron models, Tamagawa factors, and Tate-Shafarevich
groups*, p. 1 for the smooth-proper-geometrically-connected definition,
https://math.stanford.edu/~conrad/BSDseminar/Notes/L3.pdf;
Kleiman, *The Picard scheme*, FGA Explained, §9.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.AbelianSchemes

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AlgebraicLineBundleFamilies
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

universe u

/-- An abelian scheme over `S`: a smooth proper commutative group scheme over `S` with
geometrically connected fibres. -/
structure AbelianScheme (S : Scheme.{u}) where
  /-- The underlying scheme over `S`. -/
  model : Over S
  [group : GrpObj model]
  [commutative : IsCommMonObj model]
  [smooth : Smooth model.hom]
  [proper : IsProper model.hom]
  [connected : GeometricallyConnected model.hom]

attribute [instance] AbelianScheme.group AbelianScheme.commutative
  AbelianScheme.smooth AbelianScheme.proper AbelianScheme.connected

/-- The source-complete actual group-object pullback. -/
instance pullbackGrpObj {S T : Scheme.{u}} (f : T ⟶ S) (G : Over S)
    [GrpObj G] : GrpObj ((Over.pullback f).obj G) :=
  ((Over.pullback f).mapGrp.obj (.mk G)).grp

/-- Commutativity is transported by the actual cartesian pullback functor. -/
instance pullbackCommMonObj {S T : Scheme.{u}} (f : T ⟶ S) (G : Over S)
    [GrpObj G] [IsCommMonObj G] : IsCommMonObj ((Over.pullback f).obj G) :=
  inferInstanceAs (IsCommMonObj ((Over.pullback f).mapCommMon.obj (.mk G)).X)

namespace AbelianScheme

variable {S T : Scheme.{u}} (A : AbelianScheme S)

/-- General base change on the actual fibre-product scheme and group law. -/
def baseChange (f : T ⟶ S) : AbelianScheme T where
  model := (Over.pullback f).obj A.model
  group := inferInstance
  commutative := inferInstance
  smooth := inferInstanceAs (Smooth (pullback.snd A.model.hom f))
  proper := inferInstanceAs (IsProper (pullback.snd A.model.hom f))
  connected := inferInstanceAs
    (GeometricallyConnected (pullback.snd A.model.hom f))

/-- The actual fibre as an abelian scheme over the actual residue field. -/
def fibre (s : S) : AbelianScheme (Spec (S.residueField s)) :=
  A.baseChange (S.fromSpecResidueField s)

/-- The actual identity section. -/
abbrev zero : 𝟙_ (Over S) ⟶ A.model := η[A.model]

/-- Actual T-valued points. With `CategoryTheory.MonObj` open, they form a commutative group
by Mathlib's `CategoryTheory.Hom.commGroup`. -/
abbrev Points (T : Over S) := T ⟶ A.model

/-- Multiplication by n is the actual internal power map. -/
def multiplication (n : ℤ) : A.model ⟶ A.model := (𝟙 A.model) ^ n

end AbelianScheme

/-- The actual zero section in a relative product, over any base scheme. -/
def zeroSectionAt {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) :
    T ⟶ prod A.model T :=
  prod.lift (toUnit T ≫ A.zero) (𝟙 T)

/-- Zero-section rigidification is an actual module isomorphism. -/
def IsNormalizedAtZero {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S)
    (L : (prod A.model T).left.Modules) : Prop :=
  Nonempty ((Scheme.Modules.pullback (zeroSectionAt A T).left).obj L ≅
    structureModule T.left)

export AlgebraicLineBundleFamilies (familyPullback)

/-- A relative dual abelian scheme with both normalized origins and a
universal actual geometric Picard-zero line family. -/
structure DualAbelianScheme {S : Scheme.{u}} (A : AbelianScheme S) where
  /-- The dual abelian scheme. -/
  dual : AbelianScheme S
  /-- The Poincaré line bundle on `A ×_S Aᵛ`. -/
  poincare : (prod A.model dual.model).left.Modules
  lineBundle : IsLineBundle poincare
  normalized : IsNormalizedAtZero A dual.model poincare
  normalizedDual : Nonempty
    ((Scheme.Modules.pullback
      (prod.lift (𝟙 A.model) (toUnit A.model ≫ dual.zero)).left).obj poincare ≅
        structureModule A.model.left)
  fibrewisePicardZero : IsFibrewiseAlgebraicallyTrivial
    (prod.snd : prod A.model dual.model ⟶ dual.model).left poincare
  addition : ∀ (T : Over S) (f g : T ⟶ dual.model), Nonempty
    (familyPullback A.model dual.model T poincare
      (CartesianMonoidalCategory.lift f g ≫ μ[dual.model]) ≅
        moduleTensor (prod A.model T).left
          (familyPullback A.model dual.model T poincare f)
          (familyPullback A.model dual.model T poincare g))
  universal : ∀ (T : Over S) (L : (prod A.model T).left.Modules),
    IsLineBundle L → IsNormalizedAtZero A T L →
    IsFibrewiseAlgebraicallyTrivial (prod.snd : prod A.model T ⟶ T).left L →
      ∃! f : T ⟶ dual.model,
        Nonempty (familyPullback A.model dual.model T poincare f ≅ L)

namespace DualAbelianScheme

variable {S : Scheme.{u}} {A : AbelianScheme S} (D : DualAbelianScheme A)

/-- The classifying map is the inverse of the normalized universal family,
applied to this actual module sheaf and its geometric membership proofs. -/
def classifyingMap (T : Over S) (L : (prod A.model T).left.Modules)
    (hL : IsLineBundle L) (hN : IsNormalizedAtZero A T L)
    (hP : IsFibrewiseAlgebraicallyTrivial
      (prod.snd : prod A.model T ⟶ T).left L) : T ⟶ D.dual.model :=
  Classical.choose (D.universal T L hL hN hP)

theorem classifyingMap_family (T : Over S) (L : (prod A.model T).left.Modules)
    (hL : IsLineBundle L) (hN : IsNormalizedAtZero A T L)
    (hP : IsFibrewiseAlgebraicallyTrivial
      (prod.snd : prod A.model T ⟶ T).left L) :
    Nonempty (familyPullback A.model D.dual.model T D.poincare
      (D.classifyingMap T L hL hN hP) ≅ L) :=
  (Classical.choose_spec (D.universal T L hL hN hP)).1

end DualAbelianScheme

end MathlibExt.AlgebraicGeometry.AbelianSchemes
