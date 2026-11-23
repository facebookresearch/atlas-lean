/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.GoodPair
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.GoodPairPointQuotientNeighborhood
public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.Reduced
public import MathlibExt.Topology.Category.TopPair.GoodPairPointQuotientExcision

/-!
# Relative homology of a good pair and its point quotient

Excision and the chosen good-pair neighborhood identify the relative homology
of a good pair with the reduced homology of its point quotient. The comparison
is natural in the good pair and in the homology theory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe w u v

namespace TopPair

local notation "forgetToArrow" => MorphismProperty.Arrow.forget _ _ _

namespace HomologyTheoryData.IsExcisive

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false

/-- The quotient projection between the chosen neighborhood pairs induces an
isomorphism on relative homology. -/
theorem isIso_map_neighborhoodPairToPointQuotientNeighborhoodPair
    (E : HomologyTheoryData.{w} C) [E.IsExcisive]
    (n : ℤ) {P : TopPair.{w}} (d : GoodPairData P) :
    IsIso ((E.Hₚ n).map d.neighborhoodPairToPointQuotientNeighborhoodPair) := by
  let leftExcision :=
    TopPair.excisionHom P.fst d.neighborhood
      ((Set.range P.map)ᶜ : Set P.fst)
  let rightExcision :=
    TopPair.excisionHom
      (TopCat.pointQuotient ((forgetToArrow).obj P))
      d.pointQuotientNeighborhood
      (({TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit} :
        Set (TopCat.pointQuotient ((forgetToArrow).obj P)))ᶜ :
          Set (TopCat.pointQuotient ((forgetToArrow).obj P)))
  let sourceIso := d.pointQuotientExcisionSourceIso
  let _ : IsIso ((E.Hₚ n).map leftExcision) :=
    HomologyTheoryData.IsExcisive.isIso_map_excision_compl E n P.fst
      d.neighborhood (Set.range P.map)
      d.closure_range_subset_interior_neighborhood
  let _ : IsIso ((E.Hₚ n).map rightExcision) :=
    HomologyTheoryData.IsExcisive.isIso_map_excision_compl E n
      (TopCat.pointQuotient ((forgetToArrow).obj P))
      d.pointQuotientNeighborhood
      ({TopCat.pointQuotientPoint ((forgetToArrow).obj P) PUnit.unit})
      d.closure_point_subset_interior_pointQuotientNeighborhood
  let _ : IsIso ((E.Hₚ n).map sourceIso.hom) := by infer_instance
  have hComm :
      (E.Hₚ n).map leftExcision ≫
          (E.Hₚ n).map d.neighborhoodPairToPointQuotientNeighborhoodPair =
        (E.Hₚ n).map sourceIso.hom ≫ (E.Hₚ n).map rightExcision := by
    calc
      _ = (E.Hₚ n).map
          (leftExcision ≫ d.neighborhoodPairToPointQuotientNeighborhoodPair) :=
        (Functor.map_comp _ _ _).symm
      _ = (E.Hₚ n).map (sourceIso.hom ≫ rightExcision) :=
        congrArg (fun f => (E.Hₚ n).map f)
          d.pointQuotientExcision_square.symm
      _ = _ := Functor.map_comp _ _ _
  exact IsIso.of_isIso_fac_left hComm

end HomologyTheoryData.IsExcisive

namespace HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false

/-- The canonical map from a good pair to its pointed quotient pair induces an
isomorphism on relative homology. -/
theorem isIso_map_pointQuotientComparison
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive]
    [E.IsHomotopyInvariant] (n : ℤ) {P : TopPair.{w}}
    (d : GoodPairData P) :
    IsIso ((E.Hₚ n).map (pointQuotientComparison.app P)) := by
  let _ : IsIso ((E.Hₚ n).map d.toNeighborhoodPair) :=
    isIso_map_goodPairToNeighborhoodPair E n d
  let _ : IsIso ((E.Hₚ n).map
      d.neighborhoodPairToPointQuotientNeighborhoodPair) :=
    HomologyTheoryData.IsExcisive.isIso_map_neighborhoodPairToPointQuotientNeighborhoodPair
      E n d
  let _ : IsIso ((E.Hₚ n).map d.pointQuotientPairToNeighborhoodPair) :=
    isIso_map_pointQuotientPairToNeighborhoodPair E n d
  have hComm :
      (E.Hₚ n).map (pointQuotientComparison.app P) ≫
          (E.Hₚ n).map d.pointQuotientPairToNeighborhoodPair =
        (E.Hₚ n).map d.toNeighborhoodPair ≫
          (E.Hₚ n).map d.neighborhoodPairToPointQuotientNeighborhoodPair := by
    calc
      _ = (E.Hₚ n).map
          (pointQuotientComparison.app P ≫
            d.pointQuotientPairToNeighborhoodPair) :=
        (Functor.map_comp _ _ _).symm
      _ = (E.Hₚ n).map
          (d.toNeighborhoodPair ≫
            d.neighborhoodPairToPointQuotientNeighborhoodPair) :=
        congrArg (fun f => (E.Hₚ n).map f)
          d.pointQuotientComparison_neighborhood_square.symm
      _ = _ := Functor.map_comp _ _ _
  exact IsIso.of_isIso_fac_right hComm

/-- Relative homology of a good pair is naturally isomorphic to reduced
homology of its point quotient. -/
noncomputable def goodPairPointQuotientRelativeHomologyNatIso
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive]
    [E.IsHomotopyInvariant] (n : ℤ) :
    GoodPair.inclusion ⋙ E.Hₚ n ≅
      GoodPair.inclusion ⋙ pointQuotientFunctor ⋙ E.reducedH n := by
  let α := Functor.whiskerRight
    (Functor.whiskerLeft GoodPair.inclusion pointQuotientComparison) (E.Hₚ n)
  let _ (P : GoodPair.{w}) : IsIso (α.app P) :=
    isIso_map_pointQuotientComparison E n (GoodPair.data P)
  exact NatIso.ofComponents (fun P => asIso (α.app P))
    (fun f => α.naturality f)

/-- The hom component of the good-pair point-quotient comparison is induced by
the canonical quotient map of pairs. -/
@[simp]
theorem goodPairPointQuotientRelativeHomologyNatIso_hom_app
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsExcisive]
    [E.IsHomotopyInvariant] (n : ℤ) (P : GoodPair.{w}) :
    (goodPairPointQuotientRelativeHomologyNatIso E n).hom.app P =
      (E.Hₚ n).map (pointQuotientComparison.app P.obj) :=
  rfl

/-- The good-pair point-quotient comparison is natural in morphisms of raw
homology theories. -/
theorem goodPairPointQuotientRelativeHomologyNatIso_hom_naturality_theory
    {E F : HomologyTheoryData.{w} C}
    [E.IsExact] [E.IsExcisive] [E.IsHomotopyInvariant]
    [F.IsExact] [F.IsExcisive] [F.IsHomotopyInvariant]
    (f : E ⟶ F) (n : ℤ) (P : GoodPair.{w}) :
    (goodPairPointQuotientRelativeHomologyNatIso E n).hom.app P ≫
        (f.homₚ n).app (pointQuotientPairFunctor.obj P.obj) =
      (f.homₚ n).app P.obj ≫
        (goodPairPointQuotientRelativeHomologyNatIso F n).hom.app P :=
  (f.homₚ n).naturality (pointQuotientComparison.app P.obj)

end HomologyTheoryData.IsExact

namespace GeneralizedHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Relative homology of a good pair is reduced homology of its point quotient
for a generalized homology theory. -/
noncomputable def goodPairPointQuotientRelativeHomologyNatIso
    (E : GeneralizedHomologyTheory.{u, v, w} C) (n : ℤ) :
    GoodPair.inclusion ⋙ E.Hₚ n ≅
      GoodPair.inclusion ⋙ pointQuotientFunctor ⋙ E.reducedH n :=
  HomologyTheoryData.IsExact.goodPairPointQuotientRelativeHomologyNatIso E.obj n

/-- Naturality of the generalized good-pair point-quotient comparison in the
homology theory. -/
theorem goodPairPointQuotientRelativeHomologyNatIso_hom_naturality_theory
    {E F : GeneralizedHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (P : GoodPair.{w}) :
    (E.goodPairPointQuotientRelativeHomologyNatIso n).hom.app P ≫
        (f.hom.homₚ n).app (pointQuotientPairFunctor.obj P.obj) =
      (f.hom.homₚ n).app P.obj ≫
        (F.goodPairPointQuotientRelativeHomologyNatIso n).hom.app P :=
  HomologyTheoryData.IsExact.goodPairPointQuotientRelativeHomologyNatIso_hom_naturality_theory
    f.hom n P

end GeneralizedHomologyTheory

namespace OrdinaryHomologyTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Relative homology of a good pair is reduced homology of its point quotient
for an ordinary homology theory. -/
noncomputable def goodPairPointQuotientRelativeHomologyNatIso
    (E : OrdinaryHomologyTheory.{u, v, w} C) (n : ℤ) :
    GoodPair.inclusion ⋙ E.Hₚ n ≅
      GoodPair.inclusion ⋙ pointQuotientFunctor ⋙ E.reducedH n :=
  (forgetDimension.obj E).goodPairPointQuotientRelativeHomologyNatIso n

/-- Naturality of the ordinary good-pair point-quotient comparison in the
homology theory. -/
theorem goodPairPointQuotientRelativeHomologyNatIso_hom_naturality_theory
    {E F : OrdinaryHomologyTheory.{u, v, w} C} (f : E ⟶ F)
    (n : ℤ) (P : GoodPair.{w}) :
    (E.goodPairPointQuotientRelativeHomologyNatIso n).hom.app P ≫
        (f.hom.homₚ n).app (pointQuotientPairFunctor.obj P.obj) =
      (f.hom.homₚ n).app P.obj ≫
        (F.goodPairPointQuotientRelativeHomologyNatIso n).hom.app P :=
  HomologyTheoryData.IsExact.goodPairPointQuotientRelativeHomologyNatIso_hom_naturality_theory
    f.hom n P

end OrdinaryHomologyTheory

end TopPair
