/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixHS100MathieuOrbits

/-! Genuine maximality of the actual Mathieu point stabilizer in the actual flag stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- A predicate constant on a whole family selects either none or all of its original points. -/
theorem leechNormSixHS100Constant_subset_card {α : Type} (p : α → Prop)
    (hp : ∀ a b, p a ↔ p b) :
    Nat.card {a // p a} = 0 ∨ Nat.card {a // p a} = Nat.card α := by
  by_cases h : ∃ a, p a
  · right
    obtain ⟨a, ha⟩ := h
    exact Nat.card_congr (Equiv.subtypeUnivEquiv (fun b => (hp a b).mp ha))
  · left
    let : IsEmpty {a // p a} := ⟨fun a => h ⟨a.val, a.property⟩⟩
    exact Nat.card_of_isEmpty

/-- An overgroup of the actual point stabilizer includes an entire Mathieu orbit once it includes one point. -/
theorem leechNormSixHS100Overgroup_orbit_mem
    (S : Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion))
    (hS : leechNormSixHS100PairPointStabilizer ≤ S)
    (z w : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion)
    (hzw : z.val.val 0 = w.val.val 0)
    (hz : z ∈ MulAction.orbit S leechNormSixHS100PairPoint) :
    w ∈ MulAction.orbit S leechNormSixHS100PairPoint := by
  obtain ⟨k, hk⟩ := (leechNormSixHS100Mathieu_same_orbit_iff z w).mpr hzw
  let ks : S := ⟨k.val, hS k.property⟩
  have hks : ks • z = w := hk
  obtain ⟨s, hs⟩ := hz
  change s • leechNormSixHS100PairPoint = z at hs
  exact ⟨ks * s, by
    change (ks * s) • leechNormSixHS100PairPoint = w
    rw [mul_smul, hs, hks]⟩

/-- Original family membership in an overgroup orbit is constant within each Mathieu family. -/
theorem leechNormSixHS100Overgroup_orbit_mem_iff
    (S : Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion))
    (hS : leechNormSixHS100PairPointStabilizer ≤ S)
    (z w : LeechNormSixHS100Points leechNormSixHS100Root leechNormSixHS100Companion)
    (hzw : z.val.val 0 = w.val.val 0) :
    z ∈ MulAction.orbit S leechNormSixHS100PairPoint ↔
      w ∈ MulAction.orbit S leechNormSixHS100PairPoint :=
  ⟨leechNormSixHS100Overgroup_orbit_mem S hS z w hzw,
    leechNormSixHS100Overgroup_orbit_mem S hS w z hzw.symm⟩

/-- Every overgroup orbit is the pair together with zero, one, or both complete remaining families. -/
theorem leechNormSixHS100Overgroup_orbit_card_cases
    (S : Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion))
    (hS : leechNormSixHS100PairPointStabilizer ≤ S) :
    Nat.card (MulAction.orbit S leechNormSixHS100PairPoint) = 1 ∨
    Nat.card (MulAction.orbit S leechNormSixHS100PairPoint) = 23 ∨
    Nat.card (MulAction.orbit S leechNormSixHS100PairPoint) = 78 ∨
    Nat.card (MulAction.orbit S leechNormSixHS100PairPoint) = 100 := by
  have hpair (u : Unit) : leechNormSixHS100LabelPoint (Sum.inl u) ∈
      MulAction.orbit S leechNormSixHS100PairPoint := by
    simpa only [leechNormSixHS100LabelPoint, leechNormSixHS100PairPoint] using
      MulAction.mem_orbit_self (M := S) leechNormSixHS100PairPoint
  have hp : Nat.card {u : Unit // leechNormSixHS100LabelPoint (Sum.inl u) ∈
      MulAction.orbit S leechNormSixHS100PairPoint} = 1 := by
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hpair)]
    exact Nat.card_unique
  have ho := leechNormSixHS100Constant_subset_card
    (fun o : generatedFeasibleOctadContainingLabels =>
      leechNormSixHS100LabelPoint (Sum.inr (Sum.inl o)) ∈ MulAction.orbit S leechNormSixHS100PairPoint)
    (fun a b => leechNormSixHS100Overgroup_orbit_mem_iff S hS _ _ (by
      rw [leechNormSixHS100LabelPoint_zero, leechNormSixHS100LabelPoint_zero]))
  have hj := leechNormSixHS100Constant_subset_card
    (fun j : LeechNormSixHS100OddPositions =>
      leechNormSixHS100LabelPoint (Sum.inr (Sum.inr j)) ∈ MulAction.orbit S leechNormSixHS100PairPoint)
    (fun a b => leechNormSixHS100Overgroup_orbit_mem_iff S hS _ _ (by
      rw [leechNormSixHS100LabelPoint_zero, leechNormSixHS100LabelPoint_zero]))
  have hoc : Nat.card generatedFeasibleOctadContainingLabels = 77 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, generatedFeasibleOctadContainingLabels_card]
  rw [hoc] at ho
  rw [leechNormSixHS100OddPositions_card] at hj
  have h := leechNormSixHS100Catalogue_subset_card (MulAction.orbit S leechNormSixHS100PairPoint)
  rw [hp] at h
  rcases ho with ho | ho <;> rcases hj with hj | hj <;> omega

/-- The point stabilizer in any actual overgroup is exactly the original actual Mathieu point subgroup. -/
def leechNormSixHS100OvergroupPointEquiv
    (S : Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion))
    (hS : leechNormSixHS100PairPointStabilizer ≤ S) :
    MulAction.stabilizer S leechNormSixHS100PairPoint ≃* leechNormSixHS100PairPointStabilizer where
  toFun g := ⟨g.val.val, g.property⟩
  invFun g := ⟨⟨g.val, hS g.property⟩, g.property⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv g := by
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    rfl

/-- The actual order of an overgroup is its complete original point orbit size times443520. -/
theorem leechNormSixHS100Overgroup_card
    (S : Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion))
    (hS : leechNormSixHS100PairPointStabilizer ≤ S) :
    Nat.card S = Nat.card (MulAction.orbit S leechNormSixHS100PairPoint) * 443520 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup S leechNormSixHS100PairPoint)
  rw [Nat.card_prod, Nat.card_congr (leechNormSixHS100OvergroupPointEquiv S hS).toEquiv,
    leechNormSixHS100PairPointStabilizer_card] at h
  exact h.symm

/-- Lagrange forces every actual overgroup orbit size to divide one hundred. -/
theorem leechNormSixHS100Overgroup_orbit_card_dvd
    (S : Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion))
    (hS : leechNormSixHS100PairPointStabilizer ≤ S) :
    Nat.card (MulAction.orbit S leechNormSixHS100PairPoint) ∣ 100 := by
  have h := S.card_subgroup_dvd_card
  rw [leechNormSixHS100Overgroup_card S hS, leechNormSixActualPairStabilizer_card _ _
    leechNormSixHS100Root_square leechNormSixHS100Companion_square
    leechNormSixHS100Flag_pairing] at h
  change _ * 443520 ∣ 100 * 443520 at h
  exact (Nat.mul_dvd_mul_iff_right (by decide : 0 < 443520)).mp h

/-- Adding any genuine element moving the positive pair to its full actual point stabilizer gives the whole flag group. -/
theorem leechNormSixHS100PointStabilizer_maximal
    (S : Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion))
    (hS : leechNormSixHS100PairPointStabilizer ≤ S)
    (hm : ∃ g : S, g • leechNormSixHS100PairPoint ≠ leechNormSixHS100PairPoint) : S = ⊤ := by
  have hn : Nat.card (MulAction.orbit S leechNormSixHS100PairPoint) ≠ 1 := by
    intro h
    let : Subsingleton (MulAction.orbit S leechNormSixHS100PairPoint) :=
      (Nat.card_eq_one_iff_unique.mp h).1
    obtain ⟨g, hg⟩ := hm
    have he := Subsingleton.elim
      (⟨g • leechNormSixHS100PairPoint, MulAction.mem_orbit _ g⟩ :
        MulAction.orbit S leechNormSixHS100PairPoint)
      ⟨leechNormSixHS100PairPoint, MulAction.mem_orbit_self _⟩
    exact hg (congrArg Subtype.val he)
  have hd := leechNormSixHS100Overgroup_orbit_card_dvd S hS
  have h100 : Nat.card (MulAction.orbit S leechNormSixHS100PairPoint) = 100 := by
    rcases leechNormSixHS100Overgroup_orbit_card_cases S hS with h | h | h | h
    · exact (hn h).elim
    · rw [h] at hd
      norm_num at hd
    · rw [h] at hd
      norm_num at hd
    · exact h
  let : Finite S := Nat.finite_of_card_ne_zero (by
    rw [leechNormSixHS100Overgroup_card S hS, h100]
    decide)
  apply Subgroup.eq_top_of_card_eq
  rw [leechNormSixHS100Overgroup_card S hS, h100,
    leechNormSixActualPairStabilizer_card _ _ leechNormSixHS100Root_square
      leechNormSixHS100Companion_square leechNormSixHS100Flag_pairing]

/-- The full original point subgroup together with one original point-moving element generates the actual flag group. -/
theorem leechNormSixHS100PointStabilizer_generate
    (g : leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion)
    (hg : g • leechNormSixHS100PairPoint ≠ leechNormSixHS100PairPoint) :
    leechNormSixHS100PairPointStabilizer ⊔ Subgroup.zpowers g = ⊤ := by
  apply leechNormSixHS100PointStabilizer_maximal _ le_sup_left
  have hm : g ∈ leechNormSixHS100PairPointStabilizer ⊔ Subgroup.zpowers g :=
    (show Subgroup.zpowers g ≤ leechNormSixHS100PairPointStabilizer ⊔ Subgroup.zpowers g
      from le_sup_right) (Subgroup.mem_zpowers g)
  exact ⟨⟨g, hm⟩, hg⟩

/-- Every actual overgroup of the Mathieu point subgroup is either that subgroup or the whole actual flag group. -/
theorem leechNormSixHS100PointStabilizer_overgroups
    (S : Subgroup (leechNormSixActualPairStabilizer leechNormSixHS100Root leechNormSixHS100Companion))
    (hS : leechNormSixHS100PairPointStabilizer ≤ S) :
    S = leechNormSixHS100PairPointStabilizer ∨ S = ⊤ := by
  by_cases h : S ≤ leechNormSixHS100PairPointStabilizer
  · exact Or.inl (le_antisymm h hS)
  · right
    apply leechNormSixHS100PointStabilizer_maximal S hS
    change ¬ ∀ g, g ∈ S → g ∈ leechNormSixHS100PairPointStabilizer at h
    push Not at h
    obtain ⟨g, hgS, hgK⟩ := h
    exact ⟨⟨g, hgS⟩, hgK⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
