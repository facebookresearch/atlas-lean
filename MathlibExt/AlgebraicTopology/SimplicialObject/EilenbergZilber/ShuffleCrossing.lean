/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShufflePosition

@[expose] public section

noncomputable section

namespace AlgebraicTopology.EilenbergZilber

namespace Shuffle

variable {p q : ℕ}

private def inversionPairs (s : Shuffle p q) :
    Finset (Σ _j : Fin (p + q), Fin (p + q)) :=
  Finset.univ.sigma fun i =>
    Finset.univ.filter fun j => j < i ∧ s.perm i < s.perm j

private def inversionNumber (s : Shuffle p q) : ℕ :=
  ∑ i : Fin (p + q),
    (Finset.univ.filter fun j => j < i ∧ s.perm i < s.perm j).card

private theorem card_inversionPairs (s : Shuffle p q) :
    (inversionPairs s).card = inversionNumber s := by
  unfold inversionPairs inversionNumber
  simp only [Finset.card_sigma]

private theorem inversion_sources (s : Shuffle p q) {a b : Fin (p + q)}
    (hlt : b < a) (hrev : s.perm a < s.perm b) :
    ∃ i : Fin p, ∃ j : Fin q, b = Fin.castAdd q i ∧ a = Fin.natAdd p j := by
  obtain ⟨hL, hR⟩ := s.isShuffle
  obtain ⟨x, rfl⟩ :=
    (_root_.finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective a
  obtain ⟨y, rfl⟩ :=
    (_root_.finSumFinEquiv : Fin p ⊕ Fin q ≃ Fin (p + q)).surjective b
  rcases x with i | j
  · rcases y with i' | j'
    · exfalso
      change Fin.castAdd q i' < Fin.castAdd q i at hlt
      have hval : (Fin.castAdd q i').val < (Fin.castAdd q i).val := hlt
      simp only [Fin.val_castAdd] at hval
      have hlt' : i' < i := hval
      change s.perm (Fin.castAdd q i) < s.perm (Fin.castAdd q i') at hrev
      have hperm := hL hlt'
      exact lt_irrefl _ (lt_trans hperm hrev)
    · exfalso
      change Fin.natAdd p j' < Fin.castAdd q i at hlt
      have hval : (Fin.natAdd p j').val < (Fin.castAdd q i).val := hlt
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
      omega
  · rcases y with i' | j'
    · exact ⟨i', j, rfl, rfl⟩
    · exfalso
      change Fin.natAdd p j' < Fin.natAdd p j at hlt
      have hval : (Fin.natAdd p j').val < (Fin.natAdd p j).val := hlt
      simp only [Fin.val_natAdd] at hval
      have hlt' : j' < j := by omega
      change s.perm (Fin.natAdd p j) < s.perm (Fin.natAdd p j') at hrev
      have hperm := hR hlt'
      exact lt_irrefl _ (lt_trans hperm hrev)

def crossingNumber (s : Shuffle p q) : ℕ :=
  (((↑s.leftPositions : Finset (Fin (p + q))) ×ˢ
      (↑s.rightPositions : Finset (Fin (p + q)))).filter
    fun ij => ij.2 < ij.1).card

private theorem inversionNumber_eq_crossingNumber (s : Shuffle p q) :
    inversionNumber s = crossingNumber s := by
  rw [← card_inversionPairs]
  unfold crossingNumber
  apply Finset.card_bij (fun x _ => (s.perm x.2, s.perm x.1))
  · intro x hx
    obtain ⟨i, j⟩ := x
    simp only [inversionPairs, Finset.mem_sigma, Finset.mem_univ,
      Finset.mem_filter, true_and] at hx
    obtain ⟨hlt, hrev⟩ := hx
    obtain ⟨i₀, j₀, hb, ha⟩ := inversion_sources s hlt hrev
    simp only [Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Set.powersetCard.mem_coe_iff.mpr
      rw [mem_leftPositions_iff]
      exact ⟨i₀, by rw [← hb]⟩
    · apply Set.powersetCard.mem_coe_iff.mpr
      rw [mem_rightPositions_iff]
      exact ⟨j₀, by rw [← ha]⟩
    · show s.perm i < s.perm j
      exact hrev
  · intro a₁ _ha₁ a₂ _ha₂ h
    obtain ⟨i₁, j₁⟩ := a₁
    obtain ⟨i₂, j₂⟩ := a₂
    have h1 : s.perm j₁ = s.perm j₂ := congrArg Prod.fst h
    have h2 : s.perm i₁ = s.perm i₂ := congrArg Prod.snd h
    have hj : j₁ = j₂ := s.perm.injective h1
    have hi : i₁ = i₂ := s.perm.injective h2
    subst hj
    subst hi
    rfl
  · intro b hb
    simp only [Finset.mem_filter] at hb
    obtain ⟨hmem, hlt⟩ := hb
    obtain ⟨ha_mem, hb_mem⟩ := Finset.mem_product.mp hmem
    have ha' : b.1 ∈ s.leftPositions :=
      Set.powersetCard.mem_coe_iff.mp ha_mem
    have hb' : b.2 ∈ s.rightPositions :=
      Set.powersetCard.mem_coe_iff.mp hb_mem
    rw [mem_leftPositions_iff] at ha'
    rw [mem_rightPositions_iff] at hb'
    obtain ⟨i, hi⟩ := ha'
    obtain ⟨j, hj⟩ := hb'
    refine ⟨⟨Fin.natAdd p j, Fin.castAdd q i⟩, ?_, ?_⟩
    · simp only [inversionPairs, Finset.mem_sigma, Finset.mem_univ,
        Finset.mem_filter, true_and]
      refine ⟨?_, ?_⟩
      · show Fin.castAdd q i < Fin.natAdd p j
        have hval : (Fin.castAdd q i).val < (Fin.natAdd p j).val := by
          simp only [Fin.val_castAdd, Fin.val_natAdd]
          omega
        exact hval
      · show s.perm (Fin.natAdd p j) < s.perm (Fin.castAdd q i)
        rw [hj, hi]
        exact hlt
    · change (s.perm (Fin.castAdd q i), s.perm (Fin.natAdd p j)) = b
      rw [hi, hj]

private theorem shuffleSign_eq_neg_one_pow_inversionNumber (s : Shuffle p q) :
    shuffleSign s = (-1 : ℤˣ) ^ inversionNumber s := by
  rw [shuffleSign_eq_prod_prod_Iio]
  have hinner : ∀ i : Fin (p + q),
      (∏ j ∈ Finset.Iio i, (if s.perm j < s.perm i then (1 : ℤˣ) else -1)) =
        (-1 : ℤˣ) ^ ((Finset.univ.filter fun j => j < i ∧ s.perm i < s.perm j).card) := by
    intro i
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul]
    have hfilter : (Finset.Iio i).filter (fun j => ¬ s.perm j < s.perm i) =
        Finset.univ.filter (fun j => j < i ∧ s.perm i < s.perm j) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_Iio, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hj_lt, hj_nlt⟩
        refine ⟨hj_lt, ?_⟩
        rcases lt_trichotomy (s.perm j) (s.perm i) with h | h | h
        · exact absurd h hj_nlt
        · exfalso
          have hj_eq := s.perm.injective h
          subst hj_eq
          exact lt_irrefl _ hj_lt
        · exact h
      · intro ⟨hj_lt, hj_gt⟩
        exact ⟨hj_lt, not_lt_of_gt hj_gt⟩
    rw [hfilter, Finset.prod_const]
  have hprod : (∏ i : Fin (p + q), ∏ j ∈ Finset.Iio i,
      (if s.perm j < s.perm i then (1 : ℤˣ) else -1)) =
      ∏ i : Fin (p + q),
        (-1 : ℤˣ) ^ ((Finset.univ.filter fun j => j < i ∧ s.perm i < s.perm j).card) :=
    Finset.prod_congr rfl (fun i _ => hinner i)
  rw [hprod, Finset.prod_pow_eq_pow_sum]
  simp only [inversionNumber]

theorem shuffleSign_eq_neg_one_pow_crossingNumber (s : Shuffle p q) :
    shuffleSign s = (-1 : ℤˣ) ^ crossingNumber s := by
  rw [shuffleSign_eq_neg_one_pow_inversionNumber, inversionNumber_eq_crossingNumber]

theorem shuffleSignZ_eq_neg_one_pow_crossingNumber (s : Shuffle p q) :
    shuffleSignZ s = (-1 : ℤ) ^ crossingNumber s := by
  unfold shuffleSignZ
  rw [shuffleSign_eq_neg_one_pow_crossingNumber]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]

end Shuffle

end AlgebraicTopology.EilenbergZilber
