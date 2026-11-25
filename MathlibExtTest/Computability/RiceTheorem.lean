/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.PartrecCode
public import MathlibExt.Computability.RiceTheorem

public section

abbrev riceTheoremTest_standardNumbering (e : ℕ) : ℕ →. ℕ :=
  Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code e)

theorem riceTheoremTest_standardNumbering_row (e : ℕ) :
    Nat.Partrec (riceTheoremTest_standardNumbering e) :=
  Partrec.nat_iff.1 <|
    Nat.Partrec.Code.eval_part.comp (Computable.const _) Computable.id

theorem riceTheoremTest_standardNumbering_univ :
    Nat.Partrec (Nat.unpaired riceTheoremTest_standardNumbering) := by
  apply Partrec₂.unpaired'.2
  change Partrec fun p : ℕ × ℕ =>
    Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code p.1) p.2
  exact Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Nat.Partrec.Code).comp Computable.fst) Computable.snd

theorem riceTheoremTest_standardNumbering_index (f : ℕ →. ℕ) (hf : Nat.Partrec f) :
    ∃ e, ∀ n, riceTheoremTest_standardNumbering e n = f n := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hf
  refine ⟨Encodable.encode c, fun n => ?_⟩
  simp only [riceTheoremTest_standardNumbering, Denumerable.ofNat_encode, hc]

theorem riceTheoremTest_standardNumbering_smn (g : ℕ → ℕ →. ℕ)
    (hg : Nat.Partrec (Nat.unpaired g)) :
    ∃ s : ℕ → ℕ, Nat.Partrec (fun n => Part.some (s n)) ∧
      ∀ e n, riceTheoremTest_standardNumbering (s e) n = g e n := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 hg
  obtain ⟨curry, hcurry, hcurry_spec⟩ := Nat.Partrec.Code.smn
  let s : ℕ → ℕ := fun e => Encodable.encode (curry c e)
  refine ⟨s, ?_, ?_⟩
  · exact Partrec.nat_iff.1 <|
      Computable.encode.comp (hcurry.comp (Computable.const c) Computable.id)
  · intro e n
    simp only [riceTheoremTest_standardNumbering, s, Denumerable.ofNat_encode, hcurry_spec, hc,
      Nat.unpaired, Nat.unpair_pair]

-- The standard numbering has a fixed point for the successor index transformer.
example : ∃ e, ∀ n, riceTheoremTest_standardNumbering e n =
    riceTheoremTest_standardNumbering (e + 1) n := by
  exact MetaMathlibExt.acceptableNumbering_fixed_point riceTheoremTest_standardNumbering
    riceTheoremTest_standardNumbering_univ riceTheoremTest_standardNumbering_index
    riceTheoremTest_standardNumbering_smn Computable.succ

-- No computable decider recognizes exactly the programs returning zero at input zero.
example : ¬ ∃ dec : ℕ → ℕ, Nat.Partrec (fun n => Part.some (dec n)) ∧
    ∀ e, (riceTheoremTest_standardNumbering e 0 = Part.some 0 ↔ dec e = 1) ∧
      (riceTheoremTest_standardNumbering e 0 ≠ Part.some 0 ↔ dec e = 0) := by
  apply MetaMathlibExt.rice_theorem riceTheoremTest_standardNumbering
    riceTheoremTest_standardNumbering_row riceTheoremTest_standardNumbering_univ
    riceTheoremTest_standardNumbering_index riceTheoremTest_standardNumbering_smn
    {e | riceTheoremTest_standardNumbering e 0 = Part.some 0}
  · intro a b hab
    change (riceTheoremTest_standardNumbering a 0 = Part.some 0 ↔
      riceTheoremTest_standardNumbering b 0 = Part.some 0)
    rw [hab 0]
  · obtain ⟨a, ha⟩ :=
      riceTheoremTest_standardNumbering_index (fun _ => Part.some 0) Nat.Partrec.zero
    exact ⟨a, ha 0⟩
  · obtain ⟨b, hb⟩ :=
      riceTheoremTest_standardNumbering_index (fun n => Part.some (n + 1)) Nat.Partrec.succ
    refine ⟨b, ?_⟩
    change riceTheoremTest_standardNumbering b 0 ≠ Part.some 0
    rw [hb 0]
    simp
