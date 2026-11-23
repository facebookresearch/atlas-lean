/-
Copyright (c) 2026 Avocado. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-
Modified for Atlas library integration. Standalone author labels were removed;
source attributions are retained in NOTICE.
-/
module

public import MathlibExt.AlgebraicTopology.EilenbergSteenrod.PairSequenceExact
public import MathlibExt.Topology.Category.TopPair.GoodPairPointQuotientHomotopy

/-!
# Relative homology of a good-pair quotient neighborhood

The distinguished point is homotopy equivalent to the chosen quotient
neighborhood, so the canonical enlargement of the pointed quotient pair
induces an isomorphism on relative homology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Enlarging the distinguished point to the chosen quotient neighborhood
induces an isomorphism on relative homology. -/
theorem isIso_map_pointQuotientPairToNeighborhoodPair
    (E : HomologyTheoryData.{w} C) [E.IsExact] [E.IsHomotopyInvariant]
    (n : ℤ) {P : TopPair.{w}} (d : GoodPairData P) :
    IsIso ((E.Hₚ n).map d.pointQuotientPairToNeighborhoodPair) := by
  let f := d.pointQuotientPairToNeighborhoodPair
  have hIncl :
      TopCat.ofHom d.pointQuotientNeighborhoodHomotopyEquiv.toFun =
        d.pointQuotientNeighborhoodInclusion := by
    apply TopCat.hom_ext
    exact d.pointQuotientNeighborhoodHomotopyEquiv_toFun
  let _ : IsIso ((E.H n).map (TopPair.Hom.snd f)) := by
    change IsIso ((E.H n).map d.pointQuotientNeighborhoodInclusion)
    rw [← hIncl]
    exact
      (E.absoluteIsoOfHomotopyEquiv
        (X := TopCat.of PUnit)
        (Y := TopCat.of d.pointQuotientNeighborhood)
        d.pointQuotientNeighborhoodHomotopyEquiv n).isIso_hom
  let _ : IsIso ((E.H n).map (TopPair.Hom.fst f)) := by
    change IsIso ((E.H n).map (𝟙 _))
    infer_instance
  let _ : IsIso ((E.H (n - 1)).map (TopPair.Hom.snd f)) := by
    change IsIso ((E.H (n - 1)).map d.pointQuotientNeighborhoodInclusion)
    rw [← hIncl]
    exact
      (E.absoluteIsoOfHomotopyEquiv
        (X := TopCat.of PUnit)
        (Y := TopCat.of d.pointQuotientNeighborhood)
        d.pointQuotientNeighborhoodHomotopyEquiv (n - 1)).isIso_hom
  let _ : IsIso ((E.H (n - 1)).map (TopPair.Hom.fst f)) := by
    change IsIso ((E.H (n - 1)).map (𝟙 _))
    infer_instance
  exact isIso_relativeMap_of_isIso_absoluteMaps E n f

end TopPair.HomologyTheoryData.IsExact
