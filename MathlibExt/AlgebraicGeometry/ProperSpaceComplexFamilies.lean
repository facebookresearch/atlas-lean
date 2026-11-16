/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites
public import MathlibExt.AlgebraicGeometry.ProperComplexFamilySources
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# General algebraic-space source families of the native complexes stack

The family sheaf is the actual fppf pullback X times_Y T. A chosen
étale presentation is normalized by a global isomorphism to that fixed
sheaf, and both projections and every family arrow use it literally.

The proper/flat/finitely-presented source guard uses actual étale
chart scheme maps, affine étale source covers for quasi-compactness,
the actual represented relative diagonal, and the actual valuative
lifting property on fppf sheaf points. These are source morphism
criteria, not freely named flags.

References: Stacks 0DLE, 03G8, 03ML, 03XR and the valuative criterion
for proper algebraic-space morphisms. The native quotient and proper
source results at AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b
remain source reuse; adaptation/provider proofs are tracked separately.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.EtaleSpacePresentations
open MathlibExt.AlgebraicGeometry.AlgebraicSpaceComplexSourceSites

universe u

/-- A presentation is globally identified with the specified actual source fibre sheaf. -/
structure SpaceModel (F : FppfSheaf.{u}) where
  space : SourceSpace.{u}
  identification : space.sheaf ≅ F

/-- The actual scheme map underlying a chart's structural sheaf map. -/
def chartStructuralMap {X : SourceSpace.{u}} {T : Scheme.{u}}
    (π : X.sheaf ⟶ represented.obj T) (U : EtaleChart X) : U.scheme ⟶ T :=
  represented.preimage (U.map ≫ π)

/-- Its normalization holds as an equality of the full represented-sheaf maps. -/
theorem chartStructuralMap_normalized {X : SourceSpace.{u}} {T : Scheme.{u}}
    (π : X.sheaf ⟶ represented.obj T) (U : EtaleChart X) :
    represented.map (chartStructuralMap π U) = U.map ≫ π :=
  represented.map_preimage _

/-- The actual relative diagonal map of two source charts. -/
def relativeDiagonalMap {X : SourceSpace.{u}} {T : Scheme.{u}}
    (π : X.sheaf ⟶ represented.obj T) {U V : EtaleChart X}
    (P : SchemeFibreModel U.map V.map) :
    P.scheme ⟶ pullback (chartStructuralMap π U) (chartStructuralMap π V) :=
  pullback.lift P.fst P.snd (by
    apply represented.map_injective
    rw [Functor.map_comp, Functor.map_comp, chartStructuralMap_normalized,
      chartStructuralMap_normalized, ← Category.assoc, P.commutes, Category.assoc])

/-- The native source valuative criterion concerns actual sheaf points and their generic restriction. -/
def HasValuativeLifts {X Y : SourceSpace.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (x : X.sheaf.obj.obj (op (Spec (CommRingCat.of (FractionRing R)))))
    (y : Y.sheaf.obj.obj (op (Spec (CommRingCat.of R)))),
    f.hom.app (op (Spec (CommRingCat.of (FractionRing R)))) x =
      Y.sheaf.obj.map (Spec.algebraMap R (FractionRing R)).op y →
    ∃ xR : X.sheaf.obj.obj (op (Spec (CommRingCat.of R))),
      X.sheaf.obj.map (Spec.algebraMap R (FractionRing R)).op xR = x ∧
        f.hom.app (op (Spec (CommRingCat.of R))) xR = y

/-- The full source situation retains actual source spaces, every fixed fibre sheaf, and native geometric guards. -/
structure ProperSpaceSituation where
  X : SourceSpace.{u}
  Y : SourceSpace.{u}
  f : X ⟶ Y
  family : ∀ (T : Scheme.{u}) (g : represented.obj T ⟶ Y.sheaf), SpaceModel (pullback (sheafMap f) g)
  flat : ∀ (T : Scheme.{u}) (g : represented.obj T ⟶ Y.sheaf)
    (U : EtaleChart (family T g).space),
    Flat (chartStructuralMap ((family T g).identification.hom ≫ pullback.snd (sheafMap f) g) U)
  locallyFinitePresentation : ∀ (T : Scheme.{u}) (g : represented.obj T ⟶ Y.sheaf)
    (U : EtaleChart (family T g).space),
    LocallyOfFinitePresentation
      (chartStructuralMap ((family T g).identification.hom ≫ pullback.snd (sheafMap f) g) U)
  quasiCompact : ∀ (T : Scheme.{u}) [IsAffine T] (g : represented.obj T ⟶ Y.sheaf),
    ∃ U : EtaleChart (family T g).space, IsAffine U.scheme ∧ Epi U.map
  separated : ∀ (T : Scheme.{u}) (g : represented.obj T ⟶ Y.sheaf)
    (U V : EtaleChart (family T g).space),
    ∃ P : SchemeFibreModel U.map V.map,
      IsClosedImmersion
        (relativeDiagonalMap ((family T g).identification.hom ≫ pullback.snd (sheafMap f) g) P)
  valuative : HasValuativeLifts f

/-- Every ordinary scheme test over the actual target space. -/
structure FamilyTest (D : ProperSpaceSituation.{u}) where
  scheme : Scheme.{u}
  map : represented.obj scheme ⟶ D.Y.sheaf

abbrev familySpace (D : ProperSpaceSituation.{u}) (T : FamilyTest D) :=
  (D.family T.scheme T.map).space

/-- The actual native fibre projection to the ordinary test scheme. -/
def familyProjection (D : ProperSpaceSituation.{u}) (T : FamilyTest D) :
    (familySpace D T).sheaf ⟶ represented.obj T.scheme :=
  (D.family T.scheme T.map).identification.hom ≫ pullback.snd (sheafMap D.f) T.map

/-- The actual other projection to the original source space. -/
def familySourceProjection (D : ProperSpaceSituation.{u}) (T : FamilyTest D) :
    (familySpace D T).sheaf ⟶ D.X.sheaf :=
  (D.family T.scheme T.map).identification.hom ≫ pullback.fst (sheafMap D.f) T.map

/-- Test arrows are native scheme maps over the same actual target sheaf. -/
structure FamilyHom {D : ProperSpaceSituation.{u}} (T T' : FamilyTest D) where
  schemeMap : T.scheme ⟶ T'.scheme
  commutes : represented.map schemeMap ≫ T'.map = T.map

instance {D : ProperSpaceSituation.{u}} : Category (FamilyTest D) where
  Hom T T' := FamilyHom T T'
  id T := ⟨𝟙 T.scheme, by simp⟩
  comp f g := ⟨f.schemeMap ≫ g.schemeMap, by
    rw [Functor.map_comp, Category.assoc, g.commutes, f.commutes]⟩
  id_comp f := by cases f; simp
  comp_id f := by cases f; simp
  assoc f g h := by cases f; cases g; cases h; congr 1

/-- The actual native map X_h is the fibre-product map through the fixed family identifications. -/
def familyMap {D : ProperSpaceSituation.{u}} {T T' : FamilyTest D} (h : T ⟶ T') :
    familySpace D T ⟶ familySpace D T' :=
  show (familySpace D T).sheaf ⟶ (familySpace D T').sheaf from
  (D.family T.scheme T.map).identification.hom ≫
    pullback.map (sheafMap D.f) T.map (sheafMap D.f) T'.map (𝟙 D.X.sheaf) (represented.map h.schemeMap) (𝟙 D.Y.sheaf)
      (by simp) (by simpa using h.commutes.symm) ≫
    (D.family T'.scheme T'.map).identification.inv

/-- All test-field maps use that same actual familyMap construction. -/
def fieldFamily {D : ProperSpaceSituation.{u}} (T : FamilyTest D)
    (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ T.scheme) : FamilyTest D :=
  ⟨Spec (CommRingCat.of K), represented.map y ≫ T.map⟩

def fieldFamilyMap {D : ProperSpaceSituation.{u}} (T : FamilyTest D)
    (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ T.scheme) : fieldFamily T K y ⟶ T :=
  ⟨y, rfl⟩

/-- Native source condition 0DLD(2) on the literal source field fibres. -/
def HasNoNegativeFibreExt [SourceTheory.{u}] (P : PullbackSystem.{u})
    (D : ProperSpaceSituation.{u}) (T : FamilyTest D) (E : Derived (familySpace D T)) : Prop :=
  ∀ (K : Type u) [Field K] (y : Spec (CommRingCat.of K) ⟶ T.scheme) (i : ℤ), i < 0 →
    Subsingleton ((pull P (familyMap (fieldFamilyMap T K y))).obj E ⟶
      ((pull P (familyMap (fieldFamilyMap T K y))).obj E)⟦i⟧)

end MathlibExt.AlgebraicGeometry.ProperSpaceComplexFamilies
