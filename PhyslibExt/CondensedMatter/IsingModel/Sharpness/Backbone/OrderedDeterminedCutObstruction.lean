/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.OrderedDeterminedCut
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SupportLexK4Realization

/-!
# The support-ordered selector is not local to the accepted edge

On the complete graph `K₄`, whether the support-ordered backbone selector chooses the direct edge
`{0, 3}` is not a function of whether that edge is present: two edge sets with boundary `{0, 3}`,
both containing or both missing the direct edge, differ in whether it is selected.

## i. Overview

The determined-cut switching of `OrderedDeterminedCut` needs the selection event to be local to a
determined cut. For the support-ordered selector on `K₄` (encoded in `SupportLexK4Realization`),
`shb_supportLex_not_local_to_acceptedPath` exhibits two edge sets with boundary `{0, 3}` that agree
on the direct edge `{0, 3}` but only one of which selects it, and
`shb_no_directEdge_local_characterization` shows that no Boolean function of the presence of the
direct edge decides its selection. Both are proved by `decide`.

All results are proved unconditionally.

## ii. Key results

- `shb_supportLex_not_local_to_acceptedPath` : two edge sets agreeing on the direct edge, only one
  selecting it
- `shb_no_directEdge_local_characterization` : no local characterization of selecting the direct
  edge

## iii. Table of contents

- A. Non-locality of the support-ordered selector on `K₄`

## iv. References

None beyond those in the imported modules.

-/

@[expose] public section

open Finset

namespace StatMech.Sharpness

/-! ## A. Non-locality of the support-ordered selector on `K₄` -/

/-- On `K₄`, two edge sets with boundary `{0, 3}` agree on the direct edge `{0, 3}`, yet only one of
them selects the direct edge. -/
lemma shb_supportLex_not_local_to_acceptedPath :
    ∃ A B : Finset shbK4Edge,
      A ⊆ shbK4G ∧ B ⊆ shbK4G ∧
      shbK4Boundary A = {(0 : Fin 4), 3} ∧
      shbK4Boundary B = {(0 : Fin 4), 3} ∧
      (shbK4Edge.e03 ∈ A ↔ shbK4Edge.e03 ∈ B) ∧
      shbK4SelectsDirect03 A ∧ ¬shbK4SelectsDirect03 B := by
  decide

/-- On `K₄`, selection of the direct edge `{0, 3}` is not a function of its presence. -/
theorem shb_no_directEdge_local_characterization :
    ¬∃ q : Bool -> Bool,
      ∀ A : Finset shbK4Edge,
        A ⊆ shbK4G -> shbK4Boundary A = {(0 : Fin 4), 3} ->
          decide (shbK4SelectsDirect03 A) = q (decide (shbK4Edge.e03 ∈ A)) := by
  decide

end StatMech.Sharpness
