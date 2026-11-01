/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddSpinStates

/-! All 8192 two-point Hadamard states are attained by the original Q operators. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Insert the eleven lower spin bits and the last spin bit. -/
def generatedOddSpinInsert (a : Fin 11 → ZMod 2) (z : ZMod 2) : SpinIndex :=
  Fin.snoc a z

private theorem insert_last (a : Fin 11 → ZMod 2) (z : ZMod 2) :
    generatedOddSpinInsert a z (11 : Fin 12) = z := by
  have hj : (11 : Fin 12) = Fin.last 11 := by decide +kernel
  rw [hj]
  exact Fin.snoc_last (α := fun _ : Fin 12 => ZMod 2) z a

private theorem insert_low (a : Fin 11 → ZMod 2) (z : ZMod 2) (j : Fin 11) :
    generatedOddSpinInsert a z j.castSucc = a j :=
  Fin.snoc_castSucc (α := fun _ : Fin 12 => ZMod 2) z a j

/-- An actual Q element producing any prescribed lower support and two signs. -/
def generatedOddSpinQ (a : Fin 11 → ZMod 2) (e c : ZMod 2) : Q :=
  ⟨ofAdd (Fin.append (generatedOddSpinInsert a 0)
    (generatedOddSpinInsert (0 : Fin 11 → ZMod 2) (e + 1))), ofAdd c⟩

/-- The prescribed actual Q element has the required translation. -/
theorem generatedOddSpinQ_translation (a : Fin 11 → ZMod 2) (e c : ZMod 2) :
    spinTranslation (generatedOddSpinQ a e c) = generatedOddSpinInsert a 0 := by
  ext j
  simp only [spinTranslation, generatedOddSpinQ, toAdd_ofAdd, Fin.append_left]

/-- The prescribed actual Q element has the required modulation. -/
theorem generatedOddSpinQ_modulation (a : Fin 11 → ZMod 2) (e c : ZMod 2) :
    spinModulation (generatedOddSpinQ a e c) =
      generatedOddSpinInsert (0 : Fin 11 → ZMod 2) (e + 1) := by
  ext j
  simp only [spinModulation, generatedOddSpinQ, toAdd_ofAdd, Fin.append_right]

/-- Every specified two-point state is genuinely reached by an actual Q element. -/
theorem generatedOddSpinQ_state (a : Fin 11 → ZMod 2) (e c : ZMod 2) :
    spinOperator (generatedOddSpinQ a e c) (generatedOddSpinState 0 1 0) =
      generatedOddSpinState a e c := by
  rw [generatedOddSpinState_pauli, generatedOddSpinQ_translation,
    generatedOddSpinQ_modulation]
  have hl : generatedOddSpinLow (generatedOddSpinInsert a 0) = a := by
    ext j
    exact insert_low _ _ _
  have hlast : (generatedOddSpinInsert (0 : Fin 11 → ZMod 2) (e + 1)) 11 = e + 1 :=
    insert_last _ _
  have hs : generatedOddSpinOutputSign (generatedOddSpinQ a e c) = c := by
    unfold generatedOddSpinOutputSign
    rw [generatedOddSpinQ_translation, generatedOddSpinQ_modulation]
    simp only [generatedOddSpinQ, toAdd_ofAdd, insert_last, insert_low,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  rw [hl, hlast, hs]
  have he : e + 1 + 1 = e := by
    rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]
  rw [he]

private theorem sign_injective : Function.Injective qSign := by
  intro a b h
  have he : qSign (a + b) = 1 := by rw [qSign_add, h, qSign_sq]
  have hab := (qSign_eq_one_iff _).mp he
  have haa : ∀ c : ZMod 2, c + c = 0 := by decide +kernel
  exact add_left_cancel ((haa a).trans hab.symm)

/-- Support and both signs are determined uniquely by a two-point real state. -/
theorem generatedOddSpinState_injective :
    Function.Injective (fun p : (Fin 11 → ZMod 2) × ZMod 2 × ZMod 2 =>
      generatedOddSpinState p.1 p.2.1 p.2.2) := by
  rintro ⟨a, e, c⟩ ⟨b, f, d⟩ h
  have ha : a = b := by
    by_contra hn
    have he := congrFun h (generatedOddSpinInsert a 0)
    have hl : generatedOddSpinLow (generatedOddSpinInsert a 0) = a := by
      ext j
      exact insert_low _ _ _
    simp only [generatedOddSpinState, hl, hn, ite_false, ite_true,
      insert_last, mul_zero, add_zero] at he
    have hs := qSign_sq c
    rw [he, zero_mul] at hs
    norm_num at hs
  subst b
  have he0 := congrFun h (generatedOddSpinInsert a 0)
  have he1 := congrFun h (generatedOddSpinInsert a 1)
  have hl (z : ZMod 2) : generatedOddSpinLow (generatedOddSpinInsert a z) = a := by
    ext j
    exact insert_low _ _ _
  simp only [generatedOddSpinState, hl, ite_true, insert_last, mul_zero,
    mul_one, add_zero] at he0 he1
  have hc : c = d := sign_injective he0
  rw [hc] at he1
  have hef : e = f := add_left_cancel (sign_injective he1)
  exact Prod.ext rfl (Prod.ext hef hc)

/-- The actual Q orbit of the distinguished state is precisely the finite state family. -/
theorem generatedOddSpinOrbit_eq_range :
    Set.range (fun q : Q => spinOperator q (generatedOddSpinState 0 1 0)) =
      Set.range (fun p : (Fin 11 → ZMod 2) × ZMod 2 × ZMod 2 =>
        generatedOddSpinState p.1 p.2.1 p.2.2) := by
  ext v
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(generatedOddSpinLow (spinTranslation q), spinModulation q 11 + 1,
      generatedOddSpinOutputSign q), (generatedOddSpinState_pauli q).symm⟩
  · rintro ⟨⟨a, e, c⟩, rfl⟩
    exact ⟨generatedOddSpinQ a e c, generatedOddSpinQ_state a e c⟩

/-- The genuine spin-operator orbit has exactly 8192 elements. -/
theorem generatedOddSpinOrbit_card :
    Nat.card (Set.range (fun q : Q => spinOperator q (generatedOddSpinState 0 1 0))) = 8192 := by
  rw [generatedOddSpinOrbit_eq_range]
  have he := Equiv.ofInjective _ generatedOddSpinState_injective
  rw [← Nat.card_congr he]
  simp [Nat.card_eq_fintype_card, ZMod.card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
