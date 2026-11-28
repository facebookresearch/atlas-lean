/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HornCoreDefs

namespace MetaMathlibExt.Complexity.NPComplete.HornCore

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Logic.LegacyPL Cslib.Algorithms.SAT.Horn

private theorem accepts_encoding (i : HornCoreInstance) :
    hornCoreDec (bitEncode i) = true ↔ WellFormed i ∧ HornCoreFeasible i := by
  simp [hornCoreDec, bitDecode_bitEncode]

/-- The assignments `11`, `10` and `01` on two variables. -/
private abbrev models : List (List Bool) := [[true, true], [true, false], [false, true]]

/-- The models of a Horn formula are closed under componentwise conjunction. -/
private theorem satisfies_and {φ : CNF} (hφ : IsHorn φ) {n : ℕ} {a b : Fin n → Bool}
    (ha : φ.Satisfies (extend a)) (hb : φ.Satisfies (extend b)) :
    φ.Satisfies (extend fun k => a k && b k) := by
  have hext : ∀ x, extend (fun k => a k && b k) x = (extend a x && extend b x) := by
    intro x
    unfold extend
    split <;> simp
  intro C hC
  obtain ⟨l, hl, hla⟩ := (CNFClause.satisfies_def).1 (ha C hC)
  obtain ⟨m, hm, hmb⟩ := (CNFClause.satisfies_def).1 (hb C hC)
  rw [CNFClause.satisfies_def]
  cases hl2 : l.2 with
  | false => exact ⟨l, hl, by rw [hext, hla.trans hl2]; simp [hl2]⟩
  | true =>
    cases hm2 : m.2 with
    | false => exact ⟨m, hm, by rw [hext, hmb.trans hm2]; simp [hm2]⟩
    | true =>
      have hlm : l = m := hφ C hC l hl m hm hl2 hm2
      subst hlm
      exact ⟨l, hl, by rw [hext, hla, hmb, hl2]; rfl⟩

/-- A lone continuation bit is a truncated instance encoding. -/
example : hornCoreDec [true] = false := by
  have h : bitDecode (α := HornCoreInstance) [true] = none := rfl
  simp [hornCoreDec, h]

/-- The core `{11, 10}` is the model set of the Horn formula `x₀`. -/
example : hornCoreDec (bitEncode ((2, models, 2) : HornCoreInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [[true, true], [true, false]], by decide,
    ⟨[[(0, true)]], ?_, ?_, ?_⟩, by decide⟩
  · unfold IsHorn
    decide
  · decide
  · intro a
    simp only [CNF.satisfies_cons, CNF.satisfies_nil, CNFClause.satisfies_cons,
      CNFClause.satisfies_nil, CNFLiteral.satisfies_def, and_true, or_false, extend]
    simp only [show (0 : ℕ) < 2 from by decide, dite_true, List.ofFn_succ, List.ofFn_zero]
    revert a
    decide

/-- The whole set `{11, 10, 01}` is not a Horn model set: `10 ∧ 01 = 00` is missing. So no core
has three assignments. -/
example : hornCoreDec (bitEncode ((2, models, 3) : HornCoreInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, M', hsub, ⟨φ, hhorn, -, hmod⟩, hlen⟩ := (accepts_encoding _).1 hacc
  have hM' : M' = models := hsub.eq_of_length_le (by simpa using hlen)
  subst hM'
  have h10 := (hmod fun k => decide (k.val = 0)).2 (by decide)
  have h01 := (hmod fun k => decide (k.val = 1)).2 (by decide)
  have h00 := (hmod _).1 (satisfies_and hhorn h10 h01)
  revert h00
  decide

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((2, models, 3) : HornCoreInstance) :=
  by unfold WellFormed; decide

end MetaMathlibExt.Complexity.NPComplete.HornCore
