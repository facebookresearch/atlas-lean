/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierB.FreeMultipointEdwardsSokal
import Mathlib.Algebra.BigOperators.Ring.Nat

open Set
open scoped BigOperators

namespace StatMech.FK

open StatMech.ConfigSpace

variable {V : Type*} (G : SimpleGraph V)

noncomputable def markedComponents (omega : ConfigSpace (Sym2 V))
    (A : Finset V) : Finset (openSub G omega).ConnectedComponent := by
  classical
  exact A.image fun x => (openSub G omega).connectedComponentMk x

theorem clusterMarkCount_union (omega : ConfigSpace (Sym2 V))
    [DecidableEq V] (A B : Finset V) (hdisj : Disjoint A B)
    (C : (openSub G omega).ConnectedComponent) :
    clusterMarkCount G omega (A ∪ B) C =
      clusterMarkCount G omega A C + clusterMarkCount G omega B C := by
  classical
  unfold clusterMarkCount
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter hdisj)

theorem sum_clusterMarkCount_markedComponents
    (omega : ConfigSpace (Sym2 V)) (A : Finset V) :
    ∑ C ∈ markedComponents G omega A, clusterMarkCount G omega A C = A.card := by
  classical
  have hmaps : ∀ x ∈ A,
      (openSub G omega).connectedComponentMk x ∈ markedComponents G omega A := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmaps (fun _ => (1 : Nat))
  simpa [markedComponents, clusterMarkCount] using hsum

theorem mem_markedComponents_of_odd_clusterMarkCount
    (omega : ConfigSpace (Sym2 V)) (A : Finset V)
    (C : (openSub G omega).ConnectedComponent)
    (hodd : Odd (clusterMarkCount G omega A C)) :
    C ∈ markedComponents G omega A := by
  classical
  have hpos : 0 < clusterMarkCount G omega A C :=
    Nat.pos_of_ne_zero (fun hzero => by simp [hzero] at hodd)
  rw [clusterMarkCount, Finset.card_pos] at hpos
  obtain ⟨x, hx⟩ := hpos
  rw [Finset.mem_filter] at hx
  exact Finset.mem_image.mpr ⟨x, hx.1, hx.2⟩


def TwoOddCrossClusters (omega : ConfigSpace (Sym2 V))
    (A B : Finset V) : Prop :=
  ∃ C₁ C₂ : (openSub G omega).ConnectedComponent,
    C₁ ≠ C₂ ∧
    Odd (clusterMarkCount G omega A C₁) ∧
    Odd (clusterMarkCount G omega B C₁) ∧
    Odd (clusterMarkCount G omega A C₂) ∧
    Odd (clusterMarkCount G omega B C₂)



theorem allClustersEven_union_of_disjoint
    (omega : ConfigSpace (Sym2 V))
    [DecidableEq V] (A B : Finset V) (hdisj : Disjoint A B)
    (hA : AllClustersEven G omega A)
    (hB : AllClustersEven G omega B) :
    AllClustersEven G omega (A ∪ B) := by
  intro C
  rw [clusterMarkCount_union G omega A B hdisj C]
  exact (hA C).add (hB C)





theorem allClustersEven_union_error_subset_twoOddCrossClusters
    (omega : ConfigSpace (Sym2 V))
    [DecidableEq V] (A B : Finset V) (hdisj : Disjoint A B)
    (hAcard : Even A.card) (hBcard : Even B.card)
    (hUnion : AllClustersEven G omega (A ∪ B))
    (herror : ¬ (AllClustersEven G omega A ∧
      AllClustersEven G omega B)) :
    TwoOddCrossClusters G omega A B := by
  classical
  have obtain_pair
      (X Y : Finset V) (hXY : Disjoint X Y)
      (hXcard : Even X.card)
      (hU : AllClustersEven G omega (X ∪ Y))
      (hnotX : ¬ AllClustersEven G omega X) :
      ∃ C₁ C₂ : (openSub G omega).ConnectedComponent,
        C₁ ≠ C₂ ∧
        Odd (clusterMarkCount G omega X C₁) ∧
        Odd (clusterMarkCount G omega Y C₁) ∧
        Odd (clusterMarkCount G omega X C₂) ∧
        Odd (clusterMarkCount G omega Y C₂) := by
    have hnotAll : ¬ ∀ C : (openSub G omega).ConnectedComponent,
        Even (clusterMarkCount G omega X C) := by
      simpa [AllClustersEven] using hnotX
    rw [Classical.not_forall] at hnotAll
    obtain ⟨C₁, hC₁notEven⟩ := hnotAll
    have hC₁X : Odd (clusterMarkCount G omega X C₁) :=
      Nat.not_even_iff_odd.mp hC₁notEven
    have hC₁sum : Even (clusterMarkCount G omega X C₁ +
        clusterMarkCount G omega Y C₁) := by
      rw [← clusterMarkCount_union G omega X Y hXY C₁]
      exact hU C₁
    have hC₁Y : Odd (clusterMarkCount G omega Y C₁) := by
      apply Nat.not_even_iff_odd.mp
      intro hEvenY
      exact hC₁notEven ((Nat.even_add.mp hC₁sum).mpr hEvenY)
    let O : Finset (openSub G omega).ConnectedComponent :=
      (markedComponents G omega X).filter fun C =>
        Odd (clusterMarkCount G omega X C)
    have hsumEven : Even (∑ C ∈ markedComponents G omega X,
        clusterMarkCount G omega X C) := by
      rw [sum_clusterMarkCount_markedComponents G omega X]
      exact hXcard
    have hOeven : Even O.card := by
      exact (Finset.even_sum_iff_even_card_odd
        (s := markedComponents G omega X)
        (fun C => clusterMarkCount G omega X C)).mp hsumEven
    have hC₁O : C₁ ∈ O := by
      exact Finset.mem_filter.mpr
        ⟨mem_markedComponents_of_odd_clusterMarkCount G omega X C₁ hC₁X, hC₁X⟩
    have hOneLt : 1 < O.card := by
      have hpos : 0 < O.card := Finset.card_pos.mpr ⟨C₁, hC₁O⟩
      have hne : O.card ≠ 1 := by
        intro hone
        rw [hone] at hOeven
        norm_num at hOeven
      omega
    obtain ⟨C₂, hC₂O, hC₂ne⟩ := Finset.exists_mem_ne hOneLt C₁
    have hC₂X : Odd (clusterMarkCount G omega X C₂) :=
      (Finset.mem_filter.mp hC₂O).2
    have hC₂sum : Even (clusterMarkCount G omega X C₂ +
        clusterMarkCount G omega Y C₂) := by
      rw [← clusterMarkCount_union G omega X Y hXY C₂]
      exact hU C₂
    have hC₂Y : Odd (clusterMarkCount G omega Y C₂) := by
      apply Nat.not_even_iff_odd.mp
      intro hEvenY
      exact (Nat.not_even_iff_odd.mpr hC₂X)
        ((Nat.even_add.mp hC₂sum).mpr hEvenY)
    exact ⟨C₁, C₂, hC₂ne.symm, hC₁X, hC₁Y, hC₂X, hC₂Y⟩
  rcases not_and_or.mp herror with hnotA | hnotB
  · exact obtain_pair A B hdisj hAcard hUnion hnotA
  · obtain ⟨C₁, C₂, hne, hC₁B, hC₁A, hC₂B, hC₂A⟩ :=
      obtain_pair B A hdisj.symm hBcard (by
        simpa [Finset.union_comm] using hUnion) hnotB
    exact ⟨C₁, C₂, hne, hC₁A, hC₁B, hC₂A, hC₂B⟩

def allClustersEvenEvent (A : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  {omega | AllClustersEven G omega A}

def twoOddCrossClustersEvent (A B : Finset V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | TwoOddCrossClusters G omega A B}

theorem allClustersEven_factorization_error_subset
    [DecidableEq V] (A B : Finset V) (hdisj : Disjoint A B)
    (hAcard : Even A.card) (hBcard : Even B.card) :
    allClustersEvenEvent G (A ∪ B) \ 
        (allClustersEvenEvent G A ∩ allClustersEvenEvent G B) ⊆
      twoOddCrossClustersEvent G A B := by
  intro omega homega
  exact allClustersEven_union_error_subset_twoOddCrossClusters G omega A B
    hdisj hAcard hBcard homega.1 homega.2

end StatMech.FK
