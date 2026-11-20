/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly









open MeasureTheory

namespace StatMech.FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}



theorem exists_matched_commonSquareNormalBoundaryBandData
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
