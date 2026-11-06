/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Actual E7 subgroup membership of literal signed table-edge coefficients. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTransportE7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationTCIndexEdges
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationFiniteEquationSources

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Original E7 letters and actual H-prefix auxiliary names belong to the genuine parabolic. -/
theorem y322TCIndexE7Letter_mem (v : Fin 48648)
    (h : v.val < 7 ∨ (8 ≤ v.val ∧ v.val < 38548)) :
    y322FiniteAuxiliaryValue y322TransportProgram v ∈ y322E7Parabolic := by
  obtain h | ⟨ha, hb⟩ := h
  · let g : Fin 8 := ⟨v.val, by omega⟩
    have he : finSumFinEquiv (Sum.inl g : Fin 8 ⊕ Fin 48640) = v := by
      apply Fin.ext
      rfl
    rw [← he, y322FiniteAuxiliaryValue_number]
    exact y322E7Parabolic_generator_mem g h
  · let ref : Fin 48640 := ⟨v.val - 8, by omega⟩
    have he : finSumFinEquiv (Sum.inr ref : Fin 8 ⊕ Fin 48640) = v := by
      apply Fin.ext
      dsimp [ref, finSumFinEquiv]
      omega
    rw [← he, y322FiniteAuxiliaryValue_number]
    exact y322TransportE7Prefix_mem ref (by dsimp [ref]; omega)

/-- Signed words over genuine E7 generator and H-prefix letters stay inside that subgroup. -/
theorem y322TCIndexE7SignedWord_mem (word : List (Fin 48648 × Bool))
    (h : ∀ letter ∈ word, letter.1.val < 7 ∨
      (8 ≤ letter.1.val ∧ letter.1.val < 38548)) :
    y322EquationWordValue (y322FiniteAuxiliaryValue y322TransportProgram) word ∈
      y322E7Parabolic := by
  unfold y322EquationWordValue
  rw [FreeGroup.lift_mk]
  induction word with
  | nil => exact y322E7Parabolic.one_mem
  | cons letter rest ih =>
    have hl := y322TCIndexE7Letter_mem letter.1 (h letter (by simp))
    have ht := ih (fun v hv => h v (by simp only [List.mem_cons]; exact Or.inr hv))
    simp only [List.map_cons, List.prod_cons]
    apply y322E7Parabolic.mul_mem _ ht
    cases letter.2 with
    | false => exact y322E7Parabolic.inv_mem hl
    | true => exact hl

/-- Exact bound-checked decoding of an E7 coefficient preserves its actual subgroup membership. -/
theorem y322TCIndexE7DecodedWord_mem (word : List ℕ) (h : y322TCIndexE7WordAllowed word) :
    y322EquationWordValue (y322FiniteAuxiliaryValue y322TransportProgram)
      (y322RawEquationWordDecode 48648 word (y322TCIndexE7WordAllowed_alphabet word h)) ∈
      y322E7Parabolic := by
  apply y322TCIndexE7SignedWord_mem
  intro letter hl
  simp only [y322RawEquationWordDecode, List.mem_pmap] at hl
  obtain ⟨packed, hp, he⟩ := hl
  subst letter
  exact h packed hp

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
