/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.OffCentreDomination

/-!
# Boundary-condition random-cluster measures with equal boundary graphs

Equal boundary graphs give equal boundary-condition random-cluster probabilities, whatever their
decidability instances.

## i. Overview

`bcProb G C p q` takes a boundary graph `C` together with a decidable adjacency relation. Two equal
graphs, such as an induced wiring that is empty and `⊥`, can carry different `DecidableRel`
instances; `bcProb_congr_boundary` identifies the two measures.

For `q ≥ 1`, the free domination of an embedded box by the free measure on a larger graph is
`bdp_condBcProb_innerRestrict_ge` (conditionally on the outside configuration) and
`bdp_free_inner_dominated_fkProb` (averaged over it), stated with the empty boundary predicate
`bdp_noBdry`, in `FreeTranslationInvariance`.

## ii. Key results

- `bcProb_congr_boundary` : equal boundary graphs give equal boundary-condition probabilities.

## iii. Table of contents

- A. Equal boundary graphs

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace StatMech.FK

noncomputable section

/-! ## A. Equal boundary graphs -/

lemma bcProb_congr_boundary {V : Type*} [Fintype V] [DecidableEq V]
    (G C D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel C.Adj] [DecidableRel D.Adj]
    (h : C = D) (p q : Real) (omega : ConfigSpace (Sym2 V)) :
    bcProb G C p q omega = bcProb G D p q omega := by
  subst D
  congr 1

end

end StatMech.FK
