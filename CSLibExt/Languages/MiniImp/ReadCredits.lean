/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.ReadCost
public import CSLibExt.Languages.MiniImp.Hoare

/-!
# Successful-read credits

One credit pays for one successful bounds-checked immutable-array read. The
judgment is successful-run partial correctness: it bounds successful runs and
threads their remaining natural credits. It asserts neither termination nor
safety nor a credit bound on failed prefixes. Natural subtraction is paired
with an explicit spending bound so saturation cannot conceal overspending.
-/

@[expose] public section

namespace CSLibExt.Languages.MiniImp

/-- Successful-run partial correctness with natural read credits, over the
existing `ReadSteps`. States remain unrestricted functions. -/
def ReadCredits (P : State → Nat → Prop) (c : Stmt) (Q : State → Nat → Prop) :
  Prop :=
  ∀ s k t n, P s k → ReadSteps c s t n → n ≤ k ∧ Q t (k - n)

namespace ReadCredits

/-- Skip preserves the exact credit assertion. -/
theorem skip (P : State → Nat → Prop) : ReadCredits P .skip P := by
  intro s k t n hP h
  cases h
  exact ⟨Nat.zero_le k, hP⟩

/-- Assignment performs the ordinary state update without spending credits. -/
theorem assign {x : String} {e : AExp} {Q : State → Nat → Prop} :
    ReadCredits (fun s k => Q (s.update x (evalA e s)) k) (.assign x e) Q := by
  intro s k t n hP h
  cases h
  exact ⟨Nat.zero_le k, hP⟩

/-- A successful read needs one credit, its actual index bound, and the
postcondition after the bounds-checked state update at one fewer credit. -/
theorem read {x : String} {xs : Array Nat} {e : AExp} {Q : State → Nat → Prop} :
    ReadCredits (fun s k => 1 ≤ k ∧ ∃ h : evalA e s < xs.size,
      Q (s.update x xs[evalA e s]) (k - 1)) (.read x xs e) Q := by
  intro s k t n hP h
  cases h with
  | read hb =>
      obtain ⟨hk, hb', hQ⟩ := hP
      exact ⟨hk, hQ⟩

/-- Sequence gives the second command the intermediate state and remaining
credits. Its successful cost is the sum of the two counts. -/
theorem seq {P R Q : State → Nat → Prop} {a b : Stmt}
    (ha : ReadCredits P a R) (hb : ReadCredits R b Q) :
    ReadCredits P (.seq a b) Q := by
  intro s k t count hP h
  cases h with
  | seq h₁ h₂ =>
      obtain ⟨hn, hR⟩ := ha _ _ _ _ hP h₁
      obtain ⟨hm, hQ⟩ := hb _ _ _ _ hR h₂
      constructor
      · omega
      · simpa only [Nat.sub_sub] using hQ

/-- The conditional charges and establishes the postcondition of the taken
branch alone, using the existing proposition-valued guard. -/
theorem if_ {P Q : State → Nat → Prop} {b : BExp} {a c : Stmt}
    (ha : ReadCredits (fun s k => P s k ∧ beval b s) a Q)
    (hc : ReadCredits (fun s k => P s k ∧ ¬ beval b s) c Q) :
    ReadCredits P (.if_ b a c) Q := by
  intro s k t n hP h
  cases h with
  | ifTrue hb h₁ => exact ha _ _ _ _ ⟨hP, hb⟩ h₁
  | ifFalse hb h₁ => exact hc _ _ _ _ ⟨hP, hb⟩ h₁

/-- The state/credit invariant `J` is preserved through every successful body
run and holds with a false guard at exit. The arbitrary syntax annotation `A`
is ghost state-only data: `ReadSteps` neither checks nor evaluates it. -/
theorem «while» {J : State → Nat → Prop} {b : BExp} {A : State → Prop} {c :
  Stmt}
    (hbody : ReadCredits (fun s k => J s k ∧ beval b s) c J) :
    ReadCredits J (.while b A c) (fun s k => J s k ∧ ¬ beval b s) := by
  intro s k t n hJ h
  have key : ∀ {c' : Stmt} {s t : State} {n : Nat}, ReadSteps c' s t n →
      ∀ (b : BExp) (A : State → Prop) (c₀ : Stmt), c' = .while b A c₀ →
        ReadCredits (fun s k => J s k ∧ beval b s) c₀ J →
        ∀ k, J s k → n ≤ k ∧ (J t (k - n) ∧ ¬ beval b t) := by
    intro c' s t n h
    induction h with
    | skip => intro _ _ _ heq _ _ _; cases heq
    | assign => intro _ _ _ heq _ _ _; cases heq
    | read _ => intro _ _ _ heq _ _ _; cases heq
    | seq _ _ _ _ => intro _ _ _ heq _ _ _; cases heq
    | ifTrue _ _ _ => intro _ _ _ heq _ _ _; cases heq
    | ifFalse _ _ _ => intro _ _ _ heq _ _ _; cases heq
    | whileFalse hn =>
        intro _ _ _ heq _ k hJ
        cases heq
        exact ⟨Nat.zero_le k, hJ, hn⟩
    | whileTrue hb h₁ _ _ ih₂ =>
        intro _ _ _ heq hbody' k hJ
        cases heq
        obtain ⟨hn, hMid⟩ := hbody' _ _ _ _ ⟨hJ, hb⟩ h₁
        obtain ⟨hm, hExit⟩ := ih₂ _ _ _ rfl hbody' _ hMid
        constructor
        · omega
        · simpa only [Nat.sub_sub] using hExit
  exact key h b A c rfl hbody k hJ

/-- Consequence changes assertions by pointwise implication at the same
credits. No monotonicity in credits is assumed. -/
theorem consequence {P P' Q Q' : State → Nat → Prop} {c : Stmt}
    (hpre : ∀ s k, P' s k → P s k) (h : ReadCredits P c Q)
    (hpost : ∀ s k, Q s k → Q' s k) : ReadCredits P' c Q' := by
  intro s k t n hP hrun
  obtain ⟨hn, hQ⟩ := h _ _ _ _ (hpre _ _ hP) hrun
  exact ⟨hn, hpost _ _ hQ⟩

/-- The successful interpreter bridge retains the concrete return identity
and bounds its concrete recorded time, using `execReads_sound`. -/
theorem execReads {P Q : State → Nat → Prop} {c : Stmt}
    (h : ReadCredits P c Q) {fuel k : Nat} {s t : State}
    (hP : P s k) (hret : (MiniImp.execReads fuel c s).ret = some t) :
    (MiniImp.execReads fuel c s).time ≤ k ∧
      Q t (k - (MiniImp.execReads fuel c s).time) :=
  h _ _ _ _ hP (execReads_sound hret)

/-- Existentially forgetting initial and final credits gives the existing
ordinary `Hoare`, through `BigStep.exists_readSteps`. -/
theorem hoare {P Q : State → Nat → Prop} {c : Stmt} (h : ReadCredits P c Q) :
    Hoare (fun s => ∃ k, P s k) c (fun t => ∃ k, Q t k) := by
  intro s t hP hrun
  obtain ⟨k, hPk⟩ := hP
  obtain ⟨n, hn⟩ := hrun.exists_readSteps
  exact ⟨k - n, (h _ _ _ _ hPk hn).2⟩

end ReadCredits
end CSLibExt.Languages.MiniImp
