/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BerkovichStructureSheaf

/-!
# Bounded affinoid maps and actual chart refinements

The affinoid-to-locally-ringed-space construction is not full. A morphism
therefore carries an actual bounded algebra map and agrees on every rational
component with the unique bounded extension of that map. Charts and their
overlaps are locally refined by these normalized maps. Abstract maps of
locally ringed spaces alone are not an analytic-morphism contract.

Reference: Zomervrucht, *Berkovich analytification*, p. 1,
Remark 1.1 and Definition 1.2.
https://www.mi.fu-berlin.de/math/groups/arithmetic_geometry/research_seminar/documents/berkovich03.pdf
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.AlgebraicGeometry.BoundedAffinoidMorphisms

open CategoryTheory Opposite TopologicalSpace Topology
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.NonarchimedeanAnalyticSpaces
open MathlibExt.AlgebraicGeometry.BerkovichStructureSheaf

variable {K : Type} [NormedField K] [IsUltrametricDist K]
  {A B : AffinoidAlgebra K}
  {RA : RationalRestrictionTheory A} {RB : RationalRestrictionTheory B}
  {GA : RationalSpectrumGeometry RA} {GB : RationalSpectrumGeometry RB}
  (SA : AffinoidSheafGeometry RA GA) (SB : AffinoidSheafGeometry RB GB)
  (f : B ⟶ A)

def presheafedMap
    (c : presheaf RB ⟶
      (TopCat.Presheaf.pushforward CommRingCat (spectrumMap f)).obj
        (presheaf RA)) :
    SA.locallyRingedSpace.toPresheafedSpace.Hom
      SB.locallyRingedSpace.toPresheafedSpace :=
  { base := spectrumMap f, c := c }

/-- A canonical affinoid map agrees with the actual bounded rational-ring
extensions on every component on which the pulled domain lands. -/
structure AffinoidMorphism where
  c : presheaf RB ⟶
    (TopCat.Presheaf.pushforward CommRingCat (spectrumMap f)).obj (presheaf RA)
  stalk_local : ∀ p : spectrum A,
    IsLocalHom ((presheafedMap SA SB f c).stalkMap p).hom
  component_normalization : ∀ (U : Opens (spectrum B)) (s : sections RB U)
      (E : Inside ((Opens.map (spectrumMap f)).obj U)) (D : Inside U)
      (_h : comapPoint f '' rationalSet A E.1 ⊆ rationalSet B D.1),
    ∃ g : (RB.localization D.1).algebra ⟶ (RA.localization E.1).algebra,
      g.hom.comp (RB.localization D.1).baseMap.hom =
        (RA.localization E.1).baseMap.hom.comp f.hom ∧
      (show sections RA ((Opens.map (spectrumMap f)).obj U) from
        c.app (op U) s).1 E = g.hom (s.1 D)

namespace AffinoidMorphism

variable {SA SB f} (M : AffinoidMorphism SA SB f)

/-- The underlying locally ringed map has the fixed weak-spectrum base. -/
def map : SA.locallyRingedSpace ⟶ SB.locallyRingedSpace :=
  ⟨presheafedMap SA SB f M.c, M.stalk_local⟩

/-- Open restrictions are pinned by the actual affinoid map square. -/
structure OpenRestriction (U : Opens (spectrum A))
    (V : Opens (spectrum B)) where
  map : SA.locallyRingedSpace.restrict (Opens.isOpenEmbedding U) ⟶
    SB.locallyRingedSpace.restrict (Opens.isOpenEmbedding V)
  square : map ≫ SB.locallyRingedSpace.ofRestrict (Opens.isOpenEmbedding V) =
    SA.locallyRingedSpace.ofRestrict (Opens.isOpenEmbedding U) ≫ M.map

end AffinoidMorphism

/-- A genuine ringed chart on an open part of an actual affinoid spectrum. -/
structure AffinoidChart (Z : RingedSpace) where
  algebra : AffinoidAlgebra K
  rational : RationalRestrictionTheory algebra
  spectrum : RationalSpectrumGeometry rational
  geometry : AffinoidSheafGeometry rational spectrum
  source : Opens (NonarchimedeanAnalyticSpaces.spectrum algebra)
  map : (geometry.locallyRingedSpace.restrict
    (Opens.isOpenEmbedding source)).toRingedSpace ⟶ Z
  isOpen : IsOpenEmbedding map.hom.base
  stalkIso : ∀ p, IsIso (map.hom.stalkMap p)

/-- A local diagram induced by actual bounded maps to both chart algebras.
Its source is an actual open ringed neighbourhood, covering the given point. -/
structure BoundedDiagram {Z W : RingedSpace}
    (C : AffinoidChart (K := K) Z) (D : AffinoidChart (K := K) W)
    (φ : Z ⟶ W) (p : Z) where
  algebra : AffinoidAlgebra K
  rational : RationalRestrictionTheory algebra
  spectrum : RationalSpectrumGeometry rational
  geometry : AffinoidSheafGeometry rational spectrum
  source : Opens (NonarchimedeanAnalyticSpaces.spectrum algebra)
  sourceAlgebraMap : C.algebra ⟶ algebra
  sourceMorphism : AffinoidMorphism geometry C.geometry sourceAlgebraMap
  sourceRestriction : sourceMorphism.OpenRestriction source C.source
  targetAlgebraMap : D.algebra ⟶ algebra
  targetMorphism : AffinoidMorphism geometry D.geometry targetAlgebraMap
  targetRestriction : targetMorphism.OpenRestriction source D.source
  square : sourceRestriction.map.toShHom ≫ C.map ≫ φ =
    targetRestriction.map.toShHom ≫ D.map
  isOpenSource :
    IsOpenEmbedding (sourceRestriction.map.toShHom ≫ C.map).hom.base
  sourceStalkIso : ∀ q, IsIso
    ((sourceRestriction.map.toShHom ≫ C.map).hom.stalkMap q)
  covers : p ∈ Set.range (sourceRestriction.map.toShHom ≫ C.map).hom.base

/-- Covering charts have actual bounded common refinements on every overlap. -/
structure AffinoidAtlas (Z : RingedSpace) where
  Index : Type
  chart : Index → AffinoidChart (K := K) Z
  covers : ∀ p : Z, ∃ i, p ∈ Set.range (chart i).map.hom.base
  overlaps : ∀ (i j : Index) (p : Z),
    p ∈ Set.range (chart i).map.hom.base →
    p ∈ Set.range (chart j).map.hom.base →
    Nonempty (BoundedDiagram (chart i) (chart j) (𝟙 Z) p)

end MathlibExt.AlgebraicGeometry.BoundedAffinoidMorphisms
