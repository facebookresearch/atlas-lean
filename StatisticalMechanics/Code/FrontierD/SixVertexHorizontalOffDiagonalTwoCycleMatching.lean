/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexHorizontalDiagonalDeficit
import Code.FrontierD.SixVertexHorizontalResidualCompletions
import Code.FrontierD.SixVertexPairTwoCycleHall










namespace StatMech.FrontierD

noncomputable section

def sixVertexHorizontalOffDiagonalTwoCycleSupport
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) :
    forall grade,
      SixVertexHorizontalActualDeficitTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle ->
        SixVertexHorizontalActualSurplusTokens T grade
          (sixVertexHorizontalLowerSector middle hmiddle_pos)
          (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle -> Prop :=
  sixVertexHorizontalResidualConfigurationSupport T
    (sixVertexHorizontalLowerSector middle hmiddle_pos)
    (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
    (fun _ source target =>
      SixVertexConfigurationPairTwoCycleFineRelated source.1 target.1)


def SixVertexHorizontalOffDiagonalTwoCycleMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width) : Prop :=
  SixVertexHorizontalActualDeficitSupportedMatching T
    (sixVertexHorizontalLowerSector middle hmiddle_pos)
    (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle
    (sixVertexHorizontalOffDiagonalTwoCycleSupport T middle
      hmiddle_pos hmiddle_lt)

theorem sixVertexHorizontalOffDiagonalTwoCycleSupport_profiles_ne
    {T : EvenTorus} {middle : Fin (T.width + 1)}
    {hmiddle_pos : 0 < middle.val} {hmiddle_lt : middle.val < T.width} :
    forall grade
      (source : SixVertexHorizontalActualDeficitTokens T grade
        (sixVertexHorizontalLowerSector middle hmiddle_pos)
        (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle),
      Not (source.1.1 = source.1.2) := by
  intro grade source
  exact sixVertexHorizontalActualDeficitToken_profiles_ne
    middle hmiddle_pos hmiddle_lt source

theorem sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    (hmatching : SixVertexHorizontalOffDiagonalTwoCycleMatching
      T middle hmiddle_pos hmiddle_lt) :
    SixVertexMarkedTraceCoefficientwiseLogConcave
      T.width T.height middle.val := by
  let lower := sixVertexHorizontalLowerSector middle hmiddle_pos
  let upper := sixVertexHorizontalUpperSector middle hmiddle_lt
  let support := sixVertexHorizontalOffDiagonalTwoCycleSupport
    T middle hmiddle_pos hmiddle_lt
  have hHall : SixVertexHorizontalActualDeficitTokenHall T
      lower upper middle middle support :=
    (actualDeficitTokenHall_iff_supportedMatching T
      lower upper middle middle support).mpr hmatching
  have hfiber : SixVertexConfigurationPairBigradeFiberDominates T
      lower upper middle middle := by
    apply configurationBigradeFibers_of_residualConfigurationHall T
      lower upper middle middle
      (fun _ source target =>
        SixVertexConfigurationPairTwoCycleFineRelated source.1 target.1)
    exact hHall
  exact sixVertexMarkedTraceCoefficientwiseLogConcave_of_configurationBigradeFibers
    T middle hmiddle_pos hmiddle_lt hfiber

theorem sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching
    (T : EvenTorus) (middle : Fin (T.width + 1))
    (hmiddle_pos : 0 < middle.val) (hmiddle_lt : middle.val < T.width)
    {c : Real} (hc : 2 <= c)
    (hmatching : SixVertexHorizontalOffDiagonalTwoCycleMatching
      T middle hmiddle_pos hmiddle_lt) :
    Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) *
        Matrix.trace
          (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <=
      Matrix.trace
          (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 :=
  sixVertexSectorTrace_logConcave_of_markedCoefficientwise
    T.width T.height middle.val hc
      (sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching
        T middle hmiddle_pos hmiddle_lt hmatching)

end

end StatMech.FrontierD
