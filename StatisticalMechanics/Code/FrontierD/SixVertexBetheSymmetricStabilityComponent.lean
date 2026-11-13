/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricCovering










open Filter Topology

namespace StatMech.FrontierD

noncomputable section



theorem sixVertex_stabilityGauge_lt_eq_le
    {X : Type*} [TopologicalSpace X] (g : X → Real) {inner outer : Real}
    (hio : inner < outer)
    (hgap : ∀ x, ¬(inner < g x ∧ g x < outer)) :
    {x | g x < outer} = {x | g x ≤ inner} := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    have hinner : inner < g x := lt_of_not_ge hnot
    exact hgap x ⟨hinner, hx⟩
  · intro hx
    exact hx.trans_lt hio




theorem exists_sixVertexContinuousEvenSymmetricBetheBranch_of_stabilityGauge
    {a b c₀ : Real} (ha : 2 < a) (hab : a ≤ b)
    (hc₀ : c₀ ∈ Set.Icc a b) {N m : Nat} (hN : 0 < N)
    (hhalf : 2 * (m + m) ≤ N)
    (g : SixVertexBetheContinuationSpace a b N (m + m) → Real)
    (hg : Continuous g) {inner outer : Real} (hio : inner < outer)
    (hgap : ∀ z, ¬(inner < g z ∧ g z < outer))
    (hjac : ∀ z, g z < outer → Function.Injective
      (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1
        (sixVertexEvenPositiveHalfProjection m z.1.2)))
    (z₀ : SixVertexBetheContinuationSpace a b N (m + m))
    (hz₀g : g z₀ < outer)
    (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
    ∃ roots : C(Real, Fin (m + m) → Real),
      roots c₀ = z₀.1.2 ∧
      ∀ t ∈ Set.Icc a b,
        SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
  let C : Set (SixVertexBetheContinuationSpace a b N (m + m)) :=
    {z | g z < outer}
  have hCopen : IsOpen C := isOpen_lt hg continuous_const
  have hCeq : C = {z | g z ≤ inner} :=
    sixVertex_stabilityGauge_lt_eq_le g hio hgap
  have hCcompact : IsCompact C := by
    rw [hCeq]
    letI : CompactSpace (SixVertexBetheContinuationSpace a b N (m + m)) :=
      isCompact_iff_compactSpace.mp
        (isCompact_sixVertexBetheContinuationSet ha hN)
    exact (isClosed_le hg continuous_const).isCompact
  let zC : C := ⟨z₀, hz₀g⟩
  have hzC : sixVertexBetheContinuationProjectionOn C zC = ⟨c₀, hc₀⟩ := by
    simpa [zC, sixVertexBetheContinuationProjectionOn] using hz₀
  exact exists_sixVertexContinuousEvenSymmetricBetheBranch_of_regularComponent
    ha hab hc₀ hN hhalf C hCopen hCcompact
      (fun z hz => hjac z hz) zC hzC

end
end StatMech.FrontierD
