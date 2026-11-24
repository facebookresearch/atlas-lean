/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Distributed.Byzantine.Agreement

/-!
# Tests for the Byzantine agreement impossibility

* Positive control with no fault: in one round every process tells every process its input,
  and every process decides the input of process `0`. This reaches agreement with `m = 0`
  faulty processes, so the conditions are not vacuous.
* The main theorems apply to it with three processes and one fault.
* With one process, deciding one's own input tolerates one fault, so the hypothesis `2 ≤ n` of
  `not_solves_of_two_le_card` cannot be dropped.
* With two processes, the separate argument `not_solves_of_card_eq_two` applies.
* The reduction: the commander protocol built from the positive control solves the Byzantine
  generals problem with no traitor.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Distributed.Byzantine.AgreementBound.Tests

open AgreementProtocol

/-- Every process broadcasts its input and adopts the value it receives from process `0`. -/
def follow0 (n : ℕ) : AgreementProtocol (Fin (n + 1)) Bool Bool Bool where
  init _ x := x
  send _ _ s _ := s
  recv _ _ _ msg := msg 0
  decide _ s := s

/-- With no faulty process, `follow0` reaches agreement in one round. -/
theorem follow0_solves (n : ℕ) : (follow0 n).Solves 0 1 := by
  intro x faulty hf adv
  have h0 : faulty = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hf)
  subst h0
  refine ⟨fun i j _ _ => rfl, fun v hv i _ => ?_⟩
  exact hv 0 (Finset.notMem_empty 0)

/-- The values decided by `follow0` with no fault: the input of process `0`. -/
example (n : ℕ) (x : Fin (n + 1) → Bool) (adv : ℕ → Fin (n + 1) → Fin (n + 1) → Bool)
    (i : Fin (n + 1)) : (follow0 n).decision x ∅ adv 1 i = x 0 := rfl

/-- A faulty process `0` breaks `follow0` when it sends different values to processes `1` and
`2`: agreement fails. -/
example : ¬ (follow0 2).Agreement (fun _ => true) {0} (fun _ _ i => decide (i = 1)) 1 := by
  intro h
  have := h 1 2 (by decide) (by decide)
  simp [decision, state, follow0] at this

/-- The impossibility theorem applies to `follow0` with three processes and one fault. -/
example (T : ℕ) : ¬ (follow0 2).Solves 1 T := not_solves_three _ T

/-- And to every protocol for six processes with two faults. -/
example {σ M : Type} (Q : AgreementProtocol (Fin 6) Bool σ M) (T : ℕ) : ¬ Q.Solves 2 T :=
  Q.not_solves_of_card_le_three_mul (by simp) (by simp) T

/-- Two processes and one fault: the separate argument applies. -/
example {σ M : Type} (Q : AgreementProtocol (Fin 2) Bool σ M) (T : ℕ) : ¬ Q.Solves 1 T :=
  Q.not_solves_of_card_eq_two (by simp) le_rfl T

/-- With a single process, deciding one's own input tolerates one fault (`n = 1 ≤ 3 m`). -/
def own : AgreementProtocol (Fin 1) Bool Bool Bool where
  init _ x := x
  send _ _ s _ := s
  recv _ _ s _ := s
  decide _ s := s

/-- `own` reaches agreement with one faulty process: the bound needs `2 ≤ n`. -/
theorem own_solves : own.Solves 1 0 := by
  intro x faulty _ adv
  refine ⟨fun i j _ _ => by rw [Subsingleton.elim i j], fun v hv i hi => hv i hi⟩

/-- The reduction applied to the positive control solves the Byzantine generals problem with
no traitor, with one extra round. -/
example (n : ℕ) : ((follow0 n).toOral 0 false false).Solves 0 0 2 :=
  (follow0 n).solves_toOral (follow0_solves n) 0 false false

end Cslib.Distributed.Byzantine.AgreementBound.Tests
