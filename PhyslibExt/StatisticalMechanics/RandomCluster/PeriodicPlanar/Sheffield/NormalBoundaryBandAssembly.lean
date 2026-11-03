/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.BoundaryBandAssembly

/-!
# Matching primal and dual normal boundary bands

A primal and a dual normal boundary-band seed with the same margin fit in common squares of the
same half-width.

## i. Overview

Given a normal boundary-band seed for the primal lattice and one for the dual lattice
(`Sheffield.BoundaryBandAssembly`), take `M` to be the common half-width
`commonPrimalDualBandHalfWidth` of their eight radii; by translation invariance both seeds move
into the square `[-M, M]²` (`NormalBoundaryBandSeed.toCommonSquare`).

Headline fidelity. `exists_matched_commonSquareNormalBoundaryBandData` is conditional only on
translation invariance of both measures and on the two seeds being given; it is not vacuous.

## ii. Key results

- `exists_matched_commonSquareNormalBoundaryBandData`

## iii. Table of contents

- A. Common squares for primal and dual bands

## iv. References

- S. Sheffield, *Random Surfaces*, Astérisque 304 (2005), Ch. 9.
-/

@[expose] public section

open MeasureTheory

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

/-! ## A. Common squares for primal and dual bands -/

/-- A primal and a dual normal boundary-band seed with the same margin give common-square band data
of the same half-width `M` (translation invariance of both measures). -/
lemma exists_matched_commonSquareNormalBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W))) [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {margin : Nat}
    {p pDual : Real}
    (primal : E.NormalBoundaryBandSeed mu S margin p)
    (dual : Edual.NormalBoundaryBandSeed muDual Sdual margin pDual) :
    ∃ M : Nat,
      Nonempty (E.CommonSquareNormalBoundaryBandData
        mu S margin M p) ∧
      Nonempty (Edual.CommonSquareNormalBoundaryBandData
        muDual Sdual margin M pDual) := by
  let M := commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight dual.radiusBottom dual.radiusTop
  have h := le_commonPrimalDualBandHalfWidth
    primal.radiusLeft primal.radiusRight
    primal.radiusBottom primal.radiusTop
    dual.radiusLeft dual.radiusRight dual.radiusBottom dual.radiusTop
  dsimp only at h
  exact ⟨M,
    ⟨primal.toCommonSquare E mu hTI M
      h.1 h.2.1 h.2.2.1 h.2.2.2.1⟩,
    ⟨dual.toCommonSquare Edual muDual hTIDual M
      h.2.2.2.2.1 h.2.2.2.2.2.1
      h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2⟩⟩

end StatMech.FK.PeriodicPlanar
