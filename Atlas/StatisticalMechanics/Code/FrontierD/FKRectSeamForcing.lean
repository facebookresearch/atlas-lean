/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectNoLoopNormalization









open Finset

namespace StatMech.FrontierD

noncomputable section



def fkRectHorizontalCutEdges (R : FKRectTorus) : Finset R.EdgeIndex :=
  Finset.univ.image fun bx : Bool × Fin R.width =>
    (bx.1, (bx.2, (⟨0, R.height_pos⟩ : Fin R.height)))



def fkRectVerticalCutEdges (R : FKRectTorus) : Finset R.EdgeIndex :=
  Finset.univ.image fun y : Fin R.height =>
    (false, ((⟨0, R.width_pos⟩ : Fin R.width), y))


def fkRectTorusCutEdges (R : FKRectTorus) : Finset R.EdgeIndex :=
  fkRectHorizontalCutEdges R ∪ fkRectVerticalCutEdges R

theorem fkRectHorizontalCutEdges_card (R : FKRectTorus) :
    (fkRectHorizontalCutEdges R).card = 2 * R.width := by
  classical
  unfold fkRectHorizontalCutEdges
  rw [Finset.card_image_of_injective]
  · simp [Fintype.card_prod]
  · intro a b h
    exact Prod.ext (congrArg (fun x => x.1) h)
      (congrArg (fun x => x.2.1) h)

theorem fkRectVerticalCutEdges_card (R : FKRectTorus) :
    (fkRectVerticalCutEdges R).card = R.height := by
  classical
  unfold fkRectVerticalCutEdges
  rw [Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg (fun x => x.2.2) h

theorem fkRectTorusCutEdges_card_le (R : FKRectTorus) :
    (fkRectTorusCutEdges R).card ≤ 2 * R.width + R.height := by
  unfold fkRectTorusCutEdges
  calc
    (fkRectHorizontalCutEdges R ∪ fkRectVerticalCutEdges R).card ≤
        (fkRectHorizontalCutEdges R).card +
          (fkRectVerticalCutEdges R).card :=
      Finset.card_union_le _ _
    _ = 2 * R.width + R.height := by
      rw [fkRectHorizontalCutEdges_card, fkRectVerticalCutEdges_card]

theorem fkRectCritical_cFE_nonneg
    {q : Real} (hq : 1 ≤ q) :
    0 ≤ StatMech.FK.cFE (fkRectCriticalP q) q :=
  (StatMech.FK.cFE_pos
    (fkRectCriticalP_pos (zero_lt_one.trans_le hq))
    (fkRectCriticalP_lt_one (zero_lt_one.trans_le hq)) hq).le

theorem fkRectCritical_cFE_le_one
    {q : Real} (hq : 1 ≤ q) :
    StatMech.FK.cFE (fkRectCriticalP q) q ≤ 1 := by
  unfold StatMech.FK.cFE
  exact (min_le_right _ _).trans
    (sub_le_self 1
      (fkRectCriticalP_pos (zero_lt_one.trans_le hq)).le)



theorem fkRectCritical_cutClosedMass_lower
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) :
    StatMech.FK.cFE (fkRectCriticalP q) q ^
        (2 * R.width + R.height) ≤
      fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) := by
  calc
    StatMech.FK.cFE (fkRectCriticalP q) q ^
          (2 * R.width + R.height) ≤
        StatMech.FK.cFE (fkRectCriticalP q) q ^
          (fkRectTorusCutEdges R).card :=
      pow_le_pow_of_le_one (fkRectCritical_cFE_nonneg hq)
        (fkRectCritical_cFE_le_one hq)
        (fkRectTorusCutEdges_card_le R)
    _ ≤ fkRectCriticalClosedMass R q (fkRectTorusCutEdges R) :=
      fkRectCritical_cFE_pow_le_closedMass R hq _


def fkRectForceCutClosed (R : FKRectTorus)
    (omega : R.Configuration) : R.Configuration :=
  fun a => if a ∈ fkRectTorusCutEdges R then false else omega a

@[simp] theorem fkRectForceCutClosed_of_mem
    (R : FKRectTorus) (omega : R.Configuration) (a : R.EdgeIndex)
    (ha : a ∈ fkRectTorusCutEdges R) :
    fkRectForceCutClosed R omega a = false := by
  simp [fkRectForceCutClosed, ha]

@[simp] theorem fkRectForceCutClosed_of_not_mem
    (R : FKRectTorus) (omega : R.Configuration) (a : R.EdgeIndex)
    (ha : a ∉ fkRectTorusCutEdges R) :
    fkRectForceCutClosed R omega a = omega a := by
  simp [fkRectForceCutClosed, ha]

@[simp] theorem fkRectForceCutClosed_idem
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectForceCutClosed R (fkRectForceCutClosed R omega) =
      fkRectForceCutClosed R omega := by
  funext a
  by_cases ha : a ∈ fkRectTorusCutEdges R <;>
    simp [fkRectForceCutClosed, ha]


def FKRectCutClosedConfiguration
    (R : FKRectTorus) (eta : R.Configuration) : Prop :=
  fkRectForceCutClosed R eta = eta

@[simp] theorem fkRectCutClosedConfiguration_forceCutClosed
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectCutClosedConfiguration R (fkRectForceCutClosed R omega) := by
  simp [FKRectCutClosedConfiguration]

theorem fkRectCutClosedConfiguration_iff
    (R : FKRectTorus) (eta : R.Configuration) :
    FKRectCutClosedConfiguration R eta ↔
      ∀ a ∈ fkRectTorusCutEdges R, eta a = false := by
  constructor
  · intro hclosed a ha
    rw [<- hclosed]
    exact fkRectForceCutClosed_of_mem R eta a ha
  · intro hclosed
    unfold FKRectCutClosedConfiguration
    funext a
    by_cases ha : a ∈ fkRectTorusCutEdges R
    · rw [fkRectForceCutClosed_of_mem R eta a ha, hclosed a ha]
    · rw [fkRectForceCutClosed_of_not_mem R eta a ha]


def fkRectLeftColumn (R : FKRectTorus) : Fin R.width :=
  ⟨0, R.width_pos⟩


def fkRectRightColumn (R : FKRectTorus) : Fin R.width :=
  ⟨R.width - 1, Nat.sub_lt R.width_pos Nat.zero_lt_one⟩



def FKRectCutHorizontalCrossingSource
    (R : FKRectTorus) (omega : R.Configuration) (y : Fin R.height) : Prop :=
  ∃ z : Fin R.height,
    (fkRectOpenGraph R (fkRectForceCutClosed R omega)).Reachable
      (fkRectLeftColumn R, y) (fkRectRightColumn R, z)


def FKRectCutHorizontalCrossingComponent
    (R : FKRectTorus) (omega : R.Configuration)
    (C : (fkRectOpenGraph R
      (fkRectForceCutClosed R omega)).ConnectedComponent) : Prop :=
  (∃ y : Fin R.height,
      (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).connectedComponentMk
          (fkRectLeftColumn R, y) = C) ∧
    ∃ z : Fin R.height,
      (fkRectOpenGraph R
        (fkRectForceCutClosed R omega)).connectedComponentMk
          (fkRectRightColumn R, z) = C



noncomputable def fkRectCutHorizontalCrossingClusterCount
    (R : FKRectTorus) (omega : R.Configuration) : Nat := by
  classical
  exact Fintype.card {C // FKRectCutHorizontalCrossingComponent R omega C}




noncomputable def fkRectCutHorizontalCrossingSourceCount
    (R : FKRectTorus) (omega : R.Configuration) : Nat := by
  classical
  exact (Finset.univ.filter fun y : Fin R.height =>
    FKRectCutHorizontalCrossingSource R omega y).card

theorem fkRectCutHorizontalCrossingSourceCount_le_height
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectCutHorizontalCrossingSourceCount R omega ≤ R.height := by
  classical
  unfold fkRectCutHorizontalCrossingSourceCount
  calc
    (Finset.univ.filter fun y : Fin R.height =>
        FKRectCutHorizontalCrossingSource R omega y).card ≤
        (Finset.univ : Finset (Fin R.height)).card :=
      Finset.card_filter_le _ _
    _ = R.height := by simp

theorem fkRectCutHorizontalCrossingClusterCount_le_sourceCount
    (R : FKRectTorus) (omega : R.Configuration) :
    fkRectCutHorizontalCrossingClusterCount R omega ≤
      fkRectCutHorizontalCrossingSourceCount R omega := by
  classical
  let G := fkRectOpenGraph R (fkRectForceCutClosed R omega)
  let Source := {y : Fin R.height //
    FKRectCutHorizontalCrossingSource R omega y}
  let Crossing := {C : G.ConnectedComponent //
    FKRectCutHorizontalCrossingComponent R omega C}
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
      fkRectCutHorizontalCrossingSourceCount R omega := by
    unfold Source fkRectCutHorizontalCrossingSourceCount
    exact Fintype.card_ofFinset
      (Finset.univ.filter fun y : Fin R.height =>
        FKRectCutHorizontalCrossingSource R omega y)
      (fun y => by
        constructor
        · intro hy
          exact (Finset.mem_filter.mp hy).2
        · intro hy
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)
  rw [← hsourceCard]
  simpa [Crossing, fkRectCutHorizontalCrossingClusterCount] using hcard



noncomputable def fkRectCriticalCutHorizontalCrossingSourceMass
    (R : FKRectTorus) (q : Real) (y : Fin R.height) : Real := by
  classical
  exact ∑ omega : R.Configuration,
    if FKRectCutHorizontalCrossingSource R omega y then
      fkRectCriticalRandomClusterProb R q omega
    else 0


def fkRectCriticalCutHorizontalCrossingSourceExpectation
    (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : R.Configuration,
    fkRectCriticalRandomClusterProb R q omega *
      fkRectCutHorizontalCrossingSourceCount R omega


def fkRectCriticalCutHorizontalCrossingClusterExpectation
    (R : FKRectTorus) (q : Real) : Real :=
  ∑ omega : R.Configuration,
    fkRectCriticalRandomClusterProb R q omega *
      fkRectCutHorizontalCrossingClusterCount R omega

theorem fkRectCriticalCutHorizontalCrossingSourceExpectation_eq_sum
    (R : FKRectTorus) (q : Real) :
    fkRectCriticalCutHorizontalCrossingSourceExpectation R q =
      ∑ y : Fin R.height,
        fkRectCriticalCutHorizontalCrossingSourceMass R q y := by
  classical
  unfold fkRectCriticalCutHorizontalCrossingSourceExpectation
    fkRectCriticalCutHorizontalCrossingSourceMass
    fkRectCutHorizontalCrossingSourceCount
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          ↑((Finset.univ.filter fun y : Fin R.height =>
            FKRectCutHorizontalCrossingSource R omega y).card)) =
        ∑ omega : R.Configuration, ∑ y : Fin R.height,
          if FKRectCutHorizontalCrossingSource R omega y then
            fkRectCriticalRandomClusterProb R q omega else 0 := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hcross : FKRectCutHorizontalCrossingSource R omega y
      · simp [hcross]
      · simp [hcross]
    _ = ∑ y : Fin R.height, ∑ omega : R.Configuration,
          if FKRectCutHorizontalCrossingSource R omega y then
            fkRectCriticalRandomClusterProb R q omega else 0 := by
      rw [Finset.sum_comm]

theorem fkRectCriticalCutHorizontalCrossingSourceExpectation_le_height
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectCriticalCutHorizontalCrossingSourceExpectation R q ≤ R.height := by
  unfold fkRectCriticalCutHorizontalCrossingSourceExpectation
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectCutHorizontalCrossingSourceCount R omega) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega * R.height := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast
          fkRectCutHorizontalCrossingSourceCount_le_height R omega)
        (fkRectCriticalRandomClusterProb_nonneg R hq omega)
    _ = R.height := by
      rw [← Finset.sum_mul, sum_fkRectCriticalRandomClusterProb R hq,
        one_mul]

theorem fkRectCriticalCutHorizontalCrossingClusterExpectation_le_source
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    fkRectCriticalCutHorizontalCrossingClusterExpectation R q ≤
      fkRectCriticalCutHorizontalCrossingSourceExpectation R q := by
  unfold fkRectCriticalCutHorizontalCrossingClusterExpectation
    fkRectCriticalCutHorizontalCrossingSourceExpectation
  apply Finset.sum_le_sum
  intro omega homega
  exact mul_le_mul_of_nonneg_left
    (by exact_mod_cast
      fkRectCutHorizontalCrossingClusterCount_le_sourceCount R omega)
    (fkRectCriticalRandomClusterProb_nonneg R hq omega)





theorem fkRectCriticalZeroTurnExpectation_le_two_width_add_cutCrossing
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (hcut : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + fkRectCutHorizontalCrossingSourceCount R omega) :
    fkRectCriticalZeroTurnExpectation R q ≤
      2 * R.width +
        fkRectCriticalCutHorizontalCrossingSourceExpectation R q := by
  unfold fkRectCriticalZeroTurnExpectation
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnLoopCount R omega) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            (2 * R.width +
              fkRectCutHorizontalCrossingSourceCount R omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast hcut omega)
        (fkRectCriticalRandomClusterProb_nonneg R hq omega)
    _ = 2 * R.width +
        fkRectCriticalCutHorizontalCrossingSourceExpectation R q := by
      unfold fkRectCriticalCutHorizontalCrossingSourceExpectation
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_fkRectCriticalRandomClusterProb R hq, one_mul]



theorem fkRectCriticalZeroTurnExpectation_le_two_width_add_cutClusters
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (hcut : ∀ omega : R.Configuration,
      fkRectZeroTurnLoopCount R omega ≤
        2 * R.width + fkRectCutHorizontalCrossingClusterCount R omega) :
    fkRectCriticalZeroTurnExpectation R q ≤
      2 * R.width +
        fkRectCriticalCutHorizontalCrossingClusterExpectation R q := by
  unfold fkRectCriticalZeroTurnExpectation
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalRandomClusterProb R q omega *
          fkRectZeroTurnLoopCount R omega) ≤
        ∑ omega : R.Configuration,
          fkRectCriticalRandomClusterProb R q omega *
            (2 * R.width +
              fkRectCutHorizontalCrossingClusterCount R omega) := by
      apply Finset.sum_le_sum
      intro omega homega
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast hcut omega)
        (fkRectCriticalRandomClusterProb_nonneg R hq omega)
    _ = 2 * R.width +
        fkRectCriticalCutHorizontalCrossingClusterExpectation R q := by
      unfold fkRectCriticalCutHorizontalCrossingClusterExpectation
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        sum_fkRectCriticalRandomClusterProb R hq, one_mul]

end

end StatMech.FrontierD
