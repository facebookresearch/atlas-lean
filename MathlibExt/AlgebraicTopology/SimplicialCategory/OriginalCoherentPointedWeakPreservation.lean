/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentPointedHomMap
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentQuillenPreservation

/-!
# Original coherent Hom weakness from a categorical weak source map

The genuine original left Quillen theorem applies to the same entire
source map. Both original endpoint equations then retain the whole Hom
map through canonical equality isomorphisms.
-/

noncomputable section

universe u

open CategoryTheory Opposite MorphismProperty
open scoped Simplicial

namespace CategoryTheory.CoherentRealization

open SimplicialEnrichment

/-- A same original categorical weak map gives a weak entire original pointed Hom map at both supplied endpoints. -/
theorem pointedHomMap_weak_of_categorical {K L : SSet.{u}} (f : K ⟶ L)
    (hf : SSet.categoricalEquivalences f)
    {x y : K _⦋0⦌} {x' y' : L _⦋0⦌}
    (hx : f.app (op ⦋0⦌) x = x') (hy : f.app (op ⦋0⦌) y = y') :
    SSet.realizationWeakEquivalences (pointedHomMap f hx hy) := by
  have hw := (OriginalQuillenComparison.realizationMap_weak_of_categorical f hf).1 x y
  let _ : IsIso (EqualityTransport.hom (C := realization L) hx hy) := by
    unfold EqualityTransport.hom
    infer_instance
  exact RespectsIso.postcomp SSet.realizationWeakEquivalences
    (EqualityTransport.hom (C := realization L) hx hy) ((realizationMap f).map x y) hw

end CategoryTheory.CoherentRealization
