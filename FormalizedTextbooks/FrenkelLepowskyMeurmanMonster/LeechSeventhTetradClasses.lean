/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechSeventhTetradClassesData

/-! The ten signed tetrad classes are genuine distinct classes,
separate from the coordinate frame. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- A genuine omitted coordinate and one of the two tetrad sign classes. -/
abbrev leechSeventhTetradParameter := {i // i ∈ generatedSeventhFiveFrameCoordinates} × Bool

/-- The actual lattice quotient class of a stated signed tetrad. -/
def leechSeventhTetradClass (a : leechSeventhTetradParameter) : LeechModTwo :=
  leechReduction (leechSeventhTetradLattice a.1 a.2)

private theorem half_difference (t u : {i // i ∈ generatedSeventhFiveFrameCoordinates})
    (b c : Bool) :
    (leechSeventhTetradLattice t b).val - (leechSeventhTetradLattice u c).val =
      (2 : ℤ) • ((2 : ℤ) •
        (leechSeventhTetradCoefficients t.val b - leechSeventhTetradCoefficients u.val c)) := by
  funext i
  simp only [leechSeventhTetradLattice, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- All ten stated sign-and-support choices are distinct
in the actual quotient by twice the lattice. -/
theorem leechSeventhTetradClass_injective : Function.Injective leechSeventhTetradClass := by
  rintro ⟨⟨t, ht⟩, b⟩ ⟨⟨u, hu⟩, c⟩ h
  change leechReduction (leechSeventhTetradLattice ⟨t, ht⟩ b) =
    leechReduction (leechSeventhTetradLattice ⟨u, hu⟩ c) at h
  have hm := (leechSeventh_reduction_eq_iff_half _ _ _
    (half_difference ⟨t, ht⟩ ⟨u, hu⟩ b c)).mp h
  have htu : t = u := by
    by_contra htu
    have hc := leechSeventh_double_coordinate_code _ hm
    rw [leechSeventhTetrad_difference_parity t u ht hu htu b c] at hc
    exact leechSeventh_pair_parity_not_code t u htu hc
  subst u
  have hbc : b = c := by
    by_contra hbc
    rw [leechSeventhTetrad_sign_half t b c] at hm
    have he := (leechSeventh_four_coordinate_mem_iff _).mp hm
    exact leechSeventhTetrad_sign_half_odd t ht b c hbc he
  exact Prod.ext (Subtype.ext rfl) hbc

/-- No stated tetrad class is the original coordinate-frame class. -/
theorem leechSeventhTetradClass_ne_base (a : leechSeventhTetradParameter) :
    leechSeventhTetradClass a ≠ leechReduction (leechCoordinateFrameLattice 0) := by
  intro h
  let u := leechSeventhTetradLattice a.1 a.2
  have hm : u - leechCoordinateFrameLattice 0 ∈ twiceLeechIntegral :=
    QuotientAddGroup.eq_iff_sub_mem.mp h
  obtain ⟨w, hw⟩ := hm
  change (2 : ℕ) • w = u - leechCoordinateFrameLattice 0 at hw
  rw [two_nsmul] at hw
  have hu : u.val = fun i => 2 * w.val i + leechCoordinateFrameVector 0 i := by
    have he : u = (w + w) + leechCoordinateFrameLattice 0 :=
      sub_eq_iff_eq_add.mp hw.symm
    funext i
    have hi := congrArg (fun x : leechIntegral => x.val i) he
    change u.val i = w.val i + w.val i + leechCoordinateFrameVector 0 i at hi
    simpa only [two_mul] using hi
  have hs : leechSquareSum u.val = 64 :=
    leechSeventhTetrad_square a.1.val a.1.property a.2
  obtain ⟨i, hi | hi⟩ := leechNormEight_coordinate_frame_class u w hs hu
  all_goals
    have hb : |u.val i| ≤ 4 := by
      change |4 * leechSeventhTetradCoefficients a.1.val a.2 i| ≤ 4
      simp only [leechSeventhTetradCoefficients]
      split_ifs <;> norm_num
    have he := congrArg (fun v : Fin 24 → ℤ => v i) hi
    simp only [leechCoordinateFrameVector, Pi.single_eq_same, Pi.neg_apply] at he
    rw [he] at hb
    norm_num at hb

/-- Eleven actual frame classes: the coordinate frame and the ten distinct signed tetrads. -/
def leechSeventhElevenFrameClass (a : Option leechSeventhTetradParameter) : LeechModTwo :=
  match a with
  | none => leechReduction (leechCoordinateFrameLattice 0)
  | some a => leechSeventhTetradClass a

/-- The eleven stated original lattice classes are all distinct. -/
theorem leechSeventhElevenFrameClass_injective :
    Function.Injective leechSeventhElevenFrameClass := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (leechSeventhTetradClass_ne_base b h.symm)
  | some a =>
    cases b with
    | none => exact False.elim (leechSeventhTetradClass_ne_base a h)
    | some b => exact congrArg Option.some (leechSeventhTetradClass_injective h)

/-- The parameter domain has eleven elements, with no assumed geometric coverage. -/
theorem leechSeventhElevenFrameClass_domain_card :
    Nat.card (Option leechSeventhTetradParameter) = 11 := by
  have h : Fintype.card {i // i ∈ generatedSeventhFiveFrameCoordinates} = 5 := by
    rw [Fintype.card_coe]
    decide +kernel
  simp [leechSeventhTetradParameter, Nat.card_eq_fintype_card, h]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
