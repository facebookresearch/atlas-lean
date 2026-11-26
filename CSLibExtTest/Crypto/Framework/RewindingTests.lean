/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Rewinding

/-!
# Tests for the rewinding lemma

* A non-vacuous instance: a test that passes exactly when a fair coin `x` shows `true`, with
  challenges in `Fin 4`, has `ε = 1/2`, so two runs with distinct challenges both pass with
  probability at least `1/4 - 1/8 = 1/8`.
* The constant test `f ≡ 1`: `ε = 1`, and the lemma bounds the probability that two uniform
  challenges differ below by `1 - 1/N`; that probability is exactly `1 - 1/N`, so the bound is
  attained.
* One challenge (`N = 1`): two challenges never differ, so the event has probability `0`, and the
  lemma's bound `ε ^ 2 - ε` is at most `0`.
-/

@[expose] public section

namespace Cslib.Crypto.FrameworkTests.Rewinding

open Cslib.Crypto.Framework Cslib.Probability.PMF

/-- **A non-vacuous instance**: the test passes exactly when the fair coin `x` shows `true`,
whatever the challenge in `Fin 4`. Then `ε = 1/2`, and two runs with distinct challenges both pass
with probability at least `1/4 - 1/8 = 1/8`. -/
example : (1 : ℝ) / 8 ≤ winProb (fairCoin.bind fun x => (uniformOfFintype (Fin 4)).bind fun y =>
    (uniformOfFintype (Fin 4)).map fun y' => x && x && decide (y ≠ y')) := by
  have h := sq_sub_div_card_le_winProb_rewind fairCoin fun (x : Bool) (_ : Fin 4) => x
  have hε :
      winProb (fairCoin.bind fun x => (uniformOfFintype (Fin 4)).map fun _ => x) = 1 / 2 := by
    simp_rw [show ∀ x : Bool, (fun _ : Fin 4 => x) = Function.const _ x from fun _ => rfl,
      PMF.map_const]
    rw [PMF.bind_pure, winProb_fairCoin]
  rw [hε] at h
  norm_num at h ⊢
  linarith

/-- **The constant test `f ≡ 1`**: here `ε = 1`, so for every distribution `X` the lemma bounds the
probability that two independent uniform challenges differ below by `1 - 1/N`. -/
example {S T : Type*} [Fintype T] [Nonempty T] [DecidableEq T] (X : PMF S) :
    1 - 1 / (Fintype.card T : ℝ) ≤ winProb (X.bind fun _ => (uniformOfFintype T).bind fun y =>
      (uniformOfFintype T).map fun y' => true && true && decide (y ≠ y')) := by
  have h := sq_sub_div_card_le_winProb_rewind X fun (_ : S) (_ : T) => true
  have hε : winProb (X.bind fun _ => (uniformOfFintype T).map fun _ => true) = 1 := by
    rw [show (fun _ : T => true) = Function.const _ true from rfl, PMF.map_const, PMF.bind_const,
      winProb_pure]
    rfl
  rw [hε, one_pow] at h
  exact h

/-- **The bound is attained for `f ≡ 1`**: two independent uniform challenges differ with
probability exactly `1 - 1/N`. -/
example {S T : Type*} [Fintype T] [Nonempty T] [DecidableEq T] (X : PMF S) :
    winProb (X.bind fun _ => (uniformOfFintype T).bind fun y =>
      (uniformOfFintype T).map fun y' => true && true && decide (y ≠ y')) =
        1 - 1 / (Fintype.card T : ℝ) := by
  rw [PMF.bind_const]
  have hN : (0 : ℝ) < Fintype.card T := Nat.cast_pos.mpr Fintype.card_pos
  have hprod : ((uniformOfFintype T).bind fun y =>
      (uniformOfFintype T).map fun y' => true && true && decide (y ≠ y')) =
        (uniformOfFintype (T × T)).map fun p => decide (p.1 ≠ p.2) := by
    rw [← uniformOfFintype_prod T T, PMF.map_bind]
    simp_rw [PMF.map_comp]
    rfl
  have hfilter : (Finset.univ.filter fun p : T × T => decide (p.1 ≠ p.2) = true) =
      Finset.univ.offDiag := by
    ext p
    simp [Finset.mem_offDiag]
  rw [hprod, winProb_map_uniform, hfilter, Finset.offDiag_card, Fintype.card_prod,
    Finset.card_univ, Nat.cast_sub (Nat.le_mul_self _)]
  push_cast
  field_simp

/-- **One challenge (`N = 1`)**: two challenges in `Unit` never differ, so two runs with distinct
challenges never both pass, and the lemma's bound `ε ^ 2 - ε` is at most `0`. -/
example {S : Type*} (X : PMF S) (f : S → Unit → Bool) :
    winProb (X.bind fun x => (uniformOfFintype Unit).bind fun y =>
        (uniformOfFintype Unit).map fun y' => f x y && f x y' && decide (y ≠ y')) = 0 ∧
      winProb (X.bind fun x => (uniformOfFintype Unit).map (f x)) ^ 2 -
        winProb (X.bind fun x => (uniformOfFintype Unit).map (f x)) / Fintype.card Unit ≤ 0 := by
  refine ⟨?_, ?_⟩
  · simp only [ne_eq, not_true_eq_false, decide_false, Bool.and_false]
    rw [show (fun _ : Unit => false) = Function.const _ false from rfl, PMF.map_const,
      PMF.bind_const, PMF.bind_const, winProb_pure]
    rfl
  · have h0 := winProb_nonneg (X.bind fun x => (uniformOfFintype Unit).map (f x))
    have h1 := winProb_le_one (X.bind fun x => (uniformOfFintype Unit).map (f x))
    rw [Fintype.card_unit, Nat.cast_one, div_one]
    nlinarith

end Cslib.Crypto.FrameworkTests.Rewinding
