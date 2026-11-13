/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexCanonicalUnitPrefix










namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDegreeTwoOrderedStep_zeroOrUnit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : SixVertexOrientedDisagreementDart omega eta) :
    sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 0 \/
      sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 1 \/
      sixVertexDegreeTwoStrandStepSeamSign hdegree dart = -1 := by
  by_cases hzero :
      sixVertexDegreeTwoStrandStepSeamSign hdegree dart = 0
  · exact Or.inl hzero
  · exact Or.inr
      (sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero
        hdegree dart hzero)

theorem sixVertexDegreeTwoOrderedAllStrands_map_sum_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    ((sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 2 := by
  rw [sum_map_sixVertexDegreeTwoOrderedAllStrands]
  exact sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
    homega heta hdegree middle homegaSector hetaSector hmiddle


noncomputable def sixVertexDegreeTwoCanonicalUnitCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) : Nat :=
  sixVertexCanonicalUnitItemPrefixLength
    (sixVertexDegreeTwoOrderedAllStrands homega heta hdegree)
    (sixVertexDegreeTwoStrandStepSeamSign hdegree)
    (fun dart _ => sixVertexDegreeTwoOrderedStep_zeroOrUnit hdegree dart)
    (sixVertexDegreeTwoOrderedAllStrands_map_sum_eq_two
      homega heta hdegree middle homegaSector hetaSector hmiddle)


noncomputable def sixVertexDegreeTwoCanonicalUnitPrefix
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    List (SixVertexOrientedDisagreementDart omega eta) :=
  (sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).take
    (sixVertexDegreeTwoCanonicalUnitCut homega heta hdegree middle
      homegaSector hetaSector hmiddle)


noncomputable def sixVertexDegreeTwoCanonicalUnitSuffix
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    List (SixVertexOrientedDisagreementDart omega eta) :=
  (sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).drop
    (sixVertexDegreeTwoCanonicalUnitCut homega heta hdegree middle
      homegaSector hetaSector hmiddle)

theorem sixVertexDegreeTwoCanonicalUnitPrefix_sum
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    ((sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
      homegaSector hetaSector hmiddle).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 1 :=
  sixVertexCanonicalUnitItemPrefix_sum _ _ _ _

theorem sixVertexDegreeTwoCanonicalUnitSuffix_sum
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    ((sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle
      homegaSector hetaSector hmiddle).map
      (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum = 1 :=
  sixVertexCanonicalUnitItemSuffix_sum _ _ _ _

theorem sixVertexDegreeTwoCanonicalUnitPrefix_ne_nil
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
      homegaSector hetaSector hmiddle ≠ [] :=
  sixVertexCanonicalUnitItemPrefix_ne_nil _ _ _ _

theorem sixVertexDegreeTwoCanonicalUnitSuffix_ne_nil
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle
      homegaSector hetaSector hmiddle ≠ [] :=
  sixVertexCanonicalUnitItemSuffix_ne_nil _ _ _ _

theorem sixVertexDegreeTwoCanonicalUnitPrefix_append_suffix
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle ++
      sixVertexDegreeTwoCanonicalUnitSuffix homega heta hdegree middle
        homegaSector hetaSector hmiddle =
      sixVertexDegreeTwoOrderedAllStrands homega heta hdegree :=
  List.take_append_drop _ _

end

end StatMech.FrontierD
