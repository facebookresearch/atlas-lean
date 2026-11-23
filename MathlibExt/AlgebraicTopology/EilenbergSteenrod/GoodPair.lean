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
public import MathlibExt.Topology.Category.TopPair.GoodPair

/-!
# Homology of good-pair neighborhood enlargements

This file proves that enlarging the subspace of a good pair to its chosen
neighborhood induces an isomorphism on relative homology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w u v

namespace TopPair.HomologyTheoryData.IsExact

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Enlarging a good pair's subspace to its chosen neighborhood induces an
isomorphism on relative homology. -/
theorem isIso_map_goodPairToNeighborhoodPair
    (E : HomologyTheoryData.{w} C) [E.IsExact]
    [E.IsHomotopyInvariant] (n : ℤ) {P : TopPair.{w}}
    (d : GoodPairData P) :
    IsIso ((E.Hₚ n).map d.toNeighborhoodPair) := by
  let f := d.toNeighborhoodPair
  have hIncl : TopCat.ofHom d.neighborhoodHomotopyEquiv.toFun = d.inclusion := by
    apply TopCat.hom_ext
    exact d.neighborhoodHomotopyEquiv_toFun
  let _ : IsIso ((E.H n).map (TopPair.Hom.snd f)) := by
    change IsIso ((E.H n).map d.inclusion)
    rw [← hIncl]
    exact
      (E.absoluteIsoOfHomotopyEquiv
        (X := P.snd) (Y := TopCat.of d.neighborhood)
        d.neighborhoodHomotopyEquiv n).isIso_hom
  let _ : IsIso ((E.H n).map (TopPair.Hom.fst f)) := by
    change IsIso ((E.H n).map (𝟙 P.fst))
    infer_instance
  let _ : IsIso ((E.H (n - 1)).map (TopPair.Hom.snd f)) := by
    change IsIso ((E.H (n - 1)).map d.inclusion)
    rw [← hIncl]
    exact
      (E.absoluteIsoOfHomotopyEquiv
        (X := P.snd) (Y := TopCat.of d.neighborhood)
        d.neighborhoodHomotopyEquiv (n - 1)).isIso_hom
  let _ : IsIso ((E.H (n - 1)).map (TopPair.Hom.fst f)) := by
    change IsIso ((E.H (n - 1)).map (𝟙 P.fst))
    infer_instance
  exact isIso_relativeMap_of_isIso_absoluteMaps E n f

end TopPair.HomologyTheoryData.IsExact
