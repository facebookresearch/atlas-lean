/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectTorusDualEdges










open Finset SimpleGraph

namespace StatMech.FrontierD

noncomputable section



def FKRectRawHorizontalCrossingComponent
    (R : FKRectTorus) (eta : R.Configuration)
    (C : (fkRectOpenGraph R eta).ConnectedComponent) : Prop :=
  (∃ y : Fin R.height,
      (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectLeftColumn R, y) = C) ∧
    ∃ z : Fin R.height,
      (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectRightColumn R, z) = C


noncomputable def fkRectRawHorizontalCrossingClusterCount
    (R : FKRectTorus) (eta : R.Configuration) : Nat := by
  classical
  exact Fintype.card
    {C // FKRectRawHorizontalCrossingComponent R eta C}



def FKRectRawHorizontalCrossingSource
    (R : FKRectTorus) (eta : R.Configuration) (y : Fin R.height) : Prop :=
  ∃ z : Fin R.height,
    (fkRectOpenGraph R eta).Reachable
      (fkRectLeftColumn R, y) (fkRectRightColumn R, z)

noncomputable def fkRectRawHorizontalCrossingSourceCount
    (R : FKRectTorus) (eta : R.Configuration) : Nat := by
  classical
  exact (Finset.univ.filter fun y : Fin R.height =>
    FKRectRawHorizontalCrossingSource R eta y).card

theorem card_fkRectRawHorizontalCrossingSource
    (R : FKRectTorus) (eta : R.Configuration) :
    Fintype.card
        {y : Fin R.height // FKRectRawHorizontalCrossingSource R eta y} =
      fkRectRawHorizontalCrossingSourceCount R eta := by
  classical
  unfold fkRectRawHorizontalCrossingSourceCount
  rw [Fintype.card_subtype]

theorem fkRectRawHorizontalCrossingSourceCount_le_height
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawHorizontalCrossingSourceCount R eta ≤ R.height := by
  classical
  unfold fkRectRawHorizontalCrossingSourceCount
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem fkRectRawHorizontalCrossingClusterCount_le_sourceCount
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawHorizontalCrossingClusterCount R eta ≤
      fkRectRawHorizontalCrossingSourceCount R eta := by
  classical
  let G := fkRectOpenGraph R eta
  let Source := {y : Fin R.height //
    FKRectRawHorizontalCrossingSource R eta y}
  let Crossing := {C : G.ConnectedComponent //
    FKRectRawHorizontalCrossingComponent R eta C}
  let sourceComponent : Source → Crossing := fun y =>
    ⟨G.connectedComponentMk (fkRectLeftColumn R, y.1), by
      rcases y.2 with ⟨z, hyz⟩
      exact ⟨⟨y.1, rfl⟩,
        ⟨z, (SimpleGraph.ConnectedComponent.sound hyz).symm⟩⟩⟩
  have hsurj : Function.Surjective sourceComponent := by
    rintro ⟨C, ⟨⟨y, hy⟩, ⟨z, hz⟩⟩⟩
    have hyz : G.Reachable (fkRectLeftColumn R, y)
        (fkRectRightColumn R, z) :=
      SimpleGraph.ConnectedComponent.exact (hy.trans hz.symm)
    refine ⟨⟨y, ⟨z, hyz⟩⟩, ?_⟩
    apply Subtype.ext
    exact hy
  have hcard := Fintype.card_le_of_surjective sourceComponent hsurj
  have hsourceCard : Fintype.card Source =
      fkRectRawHorizontalCrossingSourceCount R eta := by
    unfold Source fkRectRawHorizontalCrossingSourceCount
    exact Fintype.card_ofFinset
      (Finset.univ.filter fun y : Fin R.height =>
        FKRectRawHorizontalCrossingSource R eta y)
      (fun y => by
        constructor
        · intro hy
          exact (Finset.mem_filter.mp hy).2
        · intro hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
  rw [← hsourceCard]
  simpa [Crossing, fkRectRawHorizontalCrossingClusterCount] using hcard

theorem fkRectRawHorizontalCrossingClusterCount_le_height
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawHorizontalCrossingClusterCount R eta ≤ R.height :=
  (fkRectRawHorizontalCrossingClusterCount_le_sourceCount R eta).trans
    (fkRectRawHorizontalCrossingSourceCount_le_height R eta)


noncomputable def fkRectRawHorizontalCrossingRepresentative
    (R : FKRectTorus) (eta : R.Configuration)
    (C : {C : (fkRectOpenGraph R eta).ConnectedComponent //
      FKRectRawHorizontalCrossingComponent R eta C}) : Fin R.height :=
  Classical.choose C.2.1

theorem fkRectRawHorizontalCrossingRepresentative_component
    (R : FKRectTorus) (eta : R.Configuration)
    (C : {C : (fkRectOpenGraph R eta).ConnectedComponent //
      FKRectRawHorizontalCrossingComponent R eta C}) :
    (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectLeftColumn R,
          fkRectRawHorizontalCrossingRepresentative R eta C) = C.1 :=
  Classical.choose_spec C.2.1

theorem fkRectRawHorizontalCrossingRepresentative_source
    (R : FKRectTorus) (eta : R.Configuration)
    (C : {C : (fkRectOpenGraph R eta).ConnectedComponent //
      FKRectRawHorizontalCrossingComponent R eta C}) :
    FKRectRawHorizontalCrossingSource R eta
      (fkRectRawHorizontalCrossingRepresentative R eta C) := by
  rcases C.2.2 with ⟨z, hz⟩
  refine ⟨z, SimpleGraph.ConnectedComponent.exact ?_⟩
  exact (fkRectRawHorizontalCrossingRepresentative_component R eta C).trans
    hz.symm

theorem fkRectRawHorizontalCrossingRepresentative_injective
    (R : FKRectTorus) (eta : R.Configuration) :
    Function.Injective
      (fkRectRawHorizontalCrossingRepresentative R eta) := by
  intro C D hCD
  apply Subtype.ext
  exact (fkRectRawHorizontalCrossingRepresentative_component R eta C).symm.trans
    ((congrArg
      (fun y => (fkRectOpenGraph R eta).connectedComponentMk
        (fkRectLeftColumn R, y)) hCD).trans
      (fkRectRawHorizontalCrossingRepresentative_component R eta D))



noncomputable def fkRectRawHorizontalCrossingRepresentativeIndices
    (R : FKRectTorus) (eta : R.Configuration) :
    Finset (Fin R.height) := by
  classical
  exact Finset.univ.image
    (fkRectRawHorizontalCrossingRepresentative R eta)

theorem card_fkRectRawHorizontalCrossingRepresentativeIndices
    (R : FKRectTorus) (eta : R.Configuration) :
    (fkRectRawHorizontalCrossingRepresentativeIndices R eta).card =
      fkRectRawHorizontalCrossingClusterCount R eta := by
  classical
  unfold fkRectRawHorizontalCrossingRepresentativeIndices
  rw [Finset.card_image_of_injective]
  · rfl
  · exact fkRectRawHorizontalCrossingRepresentative_injective R eta

theorem fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources
    (R : FKRectTorus) (eta : R.Configuration) :
    ∀ i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta,
      FKRectRawHorizontalCrossingSource R eta i := by
  classical
  intro i hi
  unfold fkRectRawHorizontalCrossingRepresentativeIndices at hi
  rw [Finset.mem_image] at hi
  rcases hi with ⟨C, _, rfl⟩
  exact fkRectRawHorizontalCrossingRepresentative_source R eta C



theorem eq_of_representativeIndices_of_component_eq
    (R : FKRectTorus) (eta : R.Configuration)
    {i j : Fin R.height}
    (hi : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta)
    (hj : j ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta)
    (hcomponent :
      (fkRectOpenGraph R eta).connectedComponentMk
          (fkRectLeftColumn R, i) =
        (fkRectOpenGraph R eta).connectedComponentMk
          (fkRectLeftColumn R, j)) :
    i = j := by
  classical
  unfold fkRectRawHorizontalCrossingRepresentativeIndices at hi hj
  rw [Finset.mem_image] at hi hj
  rcases hi with ⟨C, _, rfl⟩
  rcases hj with ⟨D, _, rfl⟩
  have hCD : C = D := by
    apply Subtype.ext
    exact (fkRectRawHorizontalCrossingRepresentative_component R eta C).symm.trans
      (hcomponent.trans
        (fkRectRawHorizontalCrossingRepresentative_component R eta D))
  exact congrArg (fkRectRawHorizontalCrossingRepresentative R eta) hCD



theorem fkRectCutHorizontalCrossingClusterCount_eq_raw
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectCutHorizontalCrossingClusterCount R omega =
      fkRectRawHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) := by
  rfl




def fkRectRawPrimalDualHorizontalCrossingClusterCount
    (R : FKRectTorus) (eta : R.Configuration) : Nat :=
  fkRectRawHorizontalCrossingClusterCount R eta +
    fkRectRawHorizontalCrossingClusterCount R
      (fkRectDualConfigurationEquiv R eta)




def fkRectPrimalDualHorizontalCrossingClusterCount
    (R : FKRectTorus) (omega : R.Configuration) : Nat :=
  fkRectRawPrimalDualHorizontalCrossingClusterCount R
    (fkRectForceCutClosed R omega)

@[simp] theorem fkRectPrimalDualHorizontalCrossingClusterCount_forceCutClosed
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectPrimalDualHorizontalCrossingClusterCount R
        (fkRectForceCutClosed R omega) =
      fkRectPrimalDualHorizontalCrossingClusterCount R omega := by
  simp [fkRectPrimalDualHorizontalCrossingClusterCount]


def fkRectPrimalDualCrossingSourceIndexEquiv (R : FKRectTorus) :
    Fin R.height ⊕ Fin R.height ≃ Fin (2 * R.height) :=
  finSumFinEquiv.trans (finCongr (two_mul R.height).symm)

def FKRectPrimalDualCrossingSourceSum
    (R : FKRectTorus) (eta : R.Configuration) :
    Fin R.height ⊕ Fin R.height -> Prop
  | Sum.inl y => FKRectRawHorizontalCrossingSource R
      (fkRectForceCutClosed R eta) y
  | Sum.inr y => FKRectRawHorizontalCrossingSource R
      (fkRectDualConfigurationEquiv R
        (fkRectForceCutClosed R eta)) y



def FKRectPrimalDualCrossingSource
    (R : FKRectTorus) (eta : R.Configuration)
    (i : Fin (2 * R.height)) : Prop :=
  FKRectPrimalDualCrossingSourceSum R eta
    ((fkRectPrimalDualCrossingSourceIndexEquiv R).symm i)

noncomputable def fkRectPrimalDualCrossingSourceSubtypeEquiv
    (R : FKRectTorus) (eta : R.Configuration) :
    {i : Fin (2 * R.height) // FKRectPrimalDualCrossingSource R eta i} ≃
      {y : Fin R.height // FKRectRawHorizontalCrossingSource R
        (fkRectForceCutClosed R eta) y} ⊕
      {y : Fin R.height // FKRectRawHorizontalCrossingSource R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R eta)) y} := by
  let e := fkRectPrimalDualCrossingSourceIndexEquiv R
  let h :
      {s : Fin R.height ⊕ Fin R.height //
        FKRectPrimalDualCrossingSourceSum R eta s} ≃
        {i : Fin (2 * R.height) //
          FKRectPrimalDualCrossingSource R eta i} :=
    Equiv.subtypeEquiv e (fun s => by
      change FKRectPrimalDualCrossingSourceSum R eta s ↔
        FKRectPrimalDualCrossingSourceSum R eta (e.symm (e s))
      rw [e.symm_apply_apply])
  exact h.symm.trans Equiv.subtypeSum

theorem card_fkRectPrimalDualCrossingSource
    (R : FKRectTorus) (eta : R.Configuration) :
    Fintype.card
        {i : Fin (2 * R.height) //
          FKRectPrimalDualCrossingSource R eta i} =
      fkRectRawHorizontalCrossingSourceCount R
          (fkRectForceCutClosed R eta) +
        fkRectRawHorizontalCrossingSourceCount R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R eta)) := by
  rw [Fintype.card_congr
    (fkRectPrimalDualCrossingSourceSubtypeEquiv R eta),
    Fintype.card_sum,
    card_fkRectRawHorizontalCrossingSource,
    card_fkRectRawHorizontalCrossingSource]

theorem fkRectRawPrimalDualHorizontalCrossingClusterCount_le_sourceCount
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawPrimalDualHorizontalCrossingClusterCount R eta <=
      fkRectRawHorizontalCrossingSourceCount R eta +
        fkRectRawHorizontalCrossingSourceCount R
          (fkRectDualConfigurationEquiv R eta) := by
  unfold fkRectRawPrimalDualHorizontalCrossingClusterCount
  exact Nat.add_le_add
    (fkRectRawHorizontalCrossingClusterCount_le_sourceCount R eta)
    (fkRectRawHorizontalCrossingClusterCount_le_sourceCount R
      (fkRectDualConfigurationEquiv R eta))

theorem fkRectPrimalDualHorizontalCrossingClusterCount_le_sourceCount
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectPrimalDualHorizontalCrossingClusterCount R eta <=
      fkRectRawHorizontalCrossingSourceCount R
          (fkRectForceCutClosed R eta) +
        fkRectRawHorizontalCrossingSourceCount R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R eta)) := by
  unfold fkRectPrimalDualHorizontalCrossingClusterCount
  exact
    fkRectRawPrimalDualHorizontalCrossingClusterCount_le_sourceCount R _



noncomputable def fkRectPrimalDualCrossingRepresentativeSourceIndex
    (R : FKRectTorus) (eta : R.Configuration) :
    ({C : (fkRectOpenGraph R
          (fkRectForceCutClosed R eta)).ConnectedComponent //
        FKRectRawHorizontalCrossingComponent R
          (fkRectForceCutClosed R eta) C} ⊕
      {C : (fkRectOpenGraph R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R eta))).ConnectedComponent //
        FKRectRawHorizontalCrossingComponent R
          (fkRectDualConfigurationEquiv R
            (fkRectForceCutClosed R eta)) C}) →
      Fin (2 * R.height)
  | Sum.inl C => fkRectPrimalDualCrossingSourceIndexEquiv R
      (Sum.inl (fkRectRawHorizontalCrossingRepresentative R
        (fkRectForceCutClosed R eta) C))
  | Sum.inr C => fkRectPrimalDualCrossingSourceIndexEquiv R
      (Sum.inr (fkRectRawHorizontalCrossingRepresentative R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R eta)) C))

theorem fkRectPrimalDualCrossingRepresentativeSourceIndex_injective
    (R : FKRectTorus) (eta : R.Configuration) :
    Function.Injective
      (fkRectPrimalDualCrossingRepresentativeSourceIndex R eta) := by
  intro C D hCD
  rcases C with C | C <;> rcases D with D | D
  · simp only [fkRectPrimalDualCrossingRepresentativeSourceIndex,
      Equiv.apply_eq_iff_eq, Sum.inl.injEq] at hCD
    exact congrArg Sum.inl
      (fkRectRawHorizontalCrossingRepresentative_injective R _ hCD)
  · simp [fkRectPrimalDualCrossingRepresentativeSourceIndex] at hCD
  · simp [fkRectPrimalDualCrossingRepresentativeSourceIndex] at hCD
  · simp only [fkRectPrimalDualCrossingRepresentativeSourceIndex,
      Equiv.apply_eq_iff_eq, Sum.inr.injEq] at hCD
    exact congrArg Sum.inr
      (fkRectRawHorizontalCrossingRepresentative_injective R _ hCD)

noncomputable def fkRectPrimalDualCrossingRepresentativeSourceIndices
    (R : FKRectTorus) (eta : R.Configuration) :
    Finset (Fin (2 * R.height)) := by
  classical
  exact Finset.univ.image
    (fkRectPrimalDualCrossingRepresentativeSourceIndex R eta)

theorem card_fkRectPrimalDualCrossingRepresentativeSourceIndices
    (R : FKRectTorus) (eta : R.Configuration) :
    (fkRectPrimalDualCrossingRepresentativeSourceIndices R eta).card =
      fkRectPrimalDualHorizontalCrossingClusterCount R eta := by
  classical
  unfold fkRectPrimalDualCrossingRepresentativeSourceIndices
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, Fintype.card_sum]
    rfl
  · exact fkRectPrimalDualCrossingRepresentativeSourceIndex_injective R eta

theorem fkRectPrimalDualCrossingRepresentativeSourceIndices_subset_sources
    (R : FKRectTorus) (eta : R.Configuration) :
    ∀ i ∈ fkRectPrimalDualCrossingRepresentativeSourceIndices R eta,
      FKRectPrimalDualCrossingSource R eta i := by
  classical
  intro i hi
  unfold fkRectPrimalDualCrossingRepresentativeSourceIndices at hi
  rw [Finset.mem_image] at hi
  rcases hi with ⟨C, hCuniv, rfl⟩
  rcases C with C | C
  · simpa [FKRectPrimalDualCrossingSource,
      fkRectPrimalDualCrossingRepresentativeSourceIndex] using
      (fkRectRawHorizontalCrossingRepresentative_source R
        (fkRectForceCutClosed R eta) C)
  · simpa [FKRectPrimalDualCrossingSource,
      fkRectPrimalDualCrossingRepresentativeSourceIndex] using
      (fkRectRawHorizontalCrossingRepresentative_source R
        (fkRectDualConfigurationEquiv R
          (fkRectForceCutClosed R eta)) C)

theorem fkRectRawPrimalDualHorizontalCrossingClusterCount_le_two_height
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectRawPrimalDualHorizontalCrossingClusterCount R eta ≤
      2 * R.height := by
  unfold fkRectRawPrimalDualHorizontalCrossingClusterCount
  have hp := fkRectRawHorizontalCrossingClusterCount_le_height R eta
  have hd := fkRectRawHorizontalCrossingClusterCount_le_height R
    (fkRectDualConfigurationEquiv R eta)
  omega

theorem fkRectPrimalDualHorizontalCrossingClusterCount_le_two_height
    (R : FKRectTorus) (eta : R.Configuration) :
    fkRectPrimalDualHorizontalCrossingClusterCount R eta <=
      2 * R.height :=
  fkRectRawPrimalDualHorizontalCrossingClusterCount_le_two_height R _

end

end StatMech.FrontierD
