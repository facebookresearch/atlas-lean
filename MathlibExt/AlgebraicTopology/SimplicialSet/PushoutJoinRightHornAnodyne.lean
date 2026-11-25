/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.JoinHorn
public import MathlibExt.AlgebraicTopology.SimplicialSet.PushoutJoinGeneratedLifting
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

/-!
# Pushout joins with right horns

Joining an original right horn to a monomorphism gives an inner anodyne
map. The proof uses the existing boundary--horn isomorphism, including
one-dimensional right horns, and the existing generated lifting theorem.
The order of the two join factors is retained.
-/

@[expose] public section

open CategoryTheory MorphismProperty
open scoped Simplicial

universe u

namespace SSet

/-- A right horn followed by a monomorphism has an inner-anodyne pushout join. -/
theorem innerAnodyneExtensions_pushoutJoin_rightHorn
    {n : ℕ} (i : Fin (n + 1)) (hi : 0 < i)
    {K₀ K : SSet.{u}} (j : K₀ ⟶ K) [Mono j] :
    innerAnodyneExtensions (joinOverPushoutObjObj j (horn n i).ι).ι := by
  rw [innerAnodyneExtensions_eq_llp_rlp]
  apply pushoutJoin_mem_rlp_llp (MorphismProperty.single (horn n i).ι)
    modelCategoryQuillen.I innerHornInclusions
  · intro A B L M a ha b hb
    obtain ⟨⟨⟩⟩ := ha
    obtain ⟨q⟩ := hb
    obtain _ | p := n
    · have hi' : 0 < i.val := hi
      have hil := i.isLt
      omega
    · change innerHornInclusions.rlp.llp
        (joinHornBoundaryLeftPushoutObjObj p q i).ι
      apply (innerHornInclusions.rlp.llp.arrow_mk_iso_iff
        (joinHornBoundaryLeftArrowIso p q i)).mpr
      exact innerHornInclusions.le_llp_rlp _
        (horn_ι_mem_innerHornInclusions
          (by change 0 < i.val; exact hi)
          (by change i.val < (p + 1) + q + 1; omega))
  · exact MorphismProperty.le_llp_rlp _ _
      (MorphismProperty.prop_single (horn n i).ι)
  · rw [modelCategoryQuillen.llp_rlp_I]
    exact monomorphisms.infer_property j

end SSet
