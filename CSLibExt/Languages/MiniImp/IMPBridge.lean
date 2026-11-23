/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.MiniImp.Hoare
public import CSLibExt.Languages.IMP.Hoare

/-!
# Embedding the canonical IMP language in MiniImp

This translates every command of Atlas's `Cslib.IMP` using an explicit variable
renaming. Execution correspondence requires that renaming to be injective.
Projection forgets target variables outside its range; those variables are
preserved by translated executions, not identified by projection.

This is not a translation of MiniImp's binary search back into canonical IMP:
canonical IMP has neither division nor immutable array reads. The extension's
binary-search result, read-safety and executable-termination claims remain
separate from this partial-correctness compatibility bridge.
-/

@[expose] public section

namespace CSLibExt.Languages.MiniImp.IMPBridge

/-- Observe the canonical numeric variables through a target renaming. -/
def project (ρ : Nat → String) (s : State) : Cslib.IMP.State :=
  fun n => s (ρ n)

/-- Translate the entire canonical arithmetic language. -/
def arith (ρ : Nat → String) : Cslib.IMP.AExp → AExp
  | .const n => .lit n
  | .var n => .var (ρ n)
  | .add a b => .add (arith ρ a) (arith ρ b)
  | .sub a b => .sub (arith ρ a) (arith ρ b)
  | .mul a b => .mul (arith ρ a) (arith ρ b)

/-- Arithmetic evaluation commutes with state projection. -/
theorem eval_arith (ρ : Nat → String) (a : Cslib.IMP.AExp) (s : State) :
    evalA (arith ρ a) s = a.eval (project ρ s) := by
  induction a <;> simp [arith, evalA, Cslib.IMP.AExp.eval, project, *]

/-- Canonical Boolean equality is encoded by the two natural inequalities. -/
def boolean (ρ : Nat → String) : Cslib.IMP.BExp → BExp
  | .truth true => .tru
  | .truth false => .not .tru
  | .eq a b => .and (.le (arith ρ a) (arith ρ b))
      (.le (arith ρ b) (arith ρ a))
  | .le a b => .le (arith ρ a) (arith ρ b)
  | .not b => .not (boolean ρ b)
  | .and a b => .and (boolean ρ a) (boolean ρ b)

/-- Boolean truth agrees with canonical evaluation on the projected state. -/
theorem eval_boolean (ρ : Nat → String) (b : Cslib.IMP.BExp) (s : State) :
    beval (boolean ρ b) s ↔ b.eval (project ρ s) = true := by
  induction b with
  | truth v => cases v <;> simp [boolean, beval, Cslib.IMP.BExp.eval]
  | eq a b =>
      simp only [boolean, beval, eval_arith,
        Cslib.IMP.BExp.eval_eq_eq_true]
      constructor
      · exact fun ⟨hl, hr⟩ => Nat.le_antisymm hl hr
      · intro h
        rw [h]
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | le a b => simp [boolean, beval, eval_arith]
  | not b ih =>
      simp only [boolean, beval, ih, Cslib.IMP.BExp.eval_not_eq_true]
      cases b.eval (project ρ s) <;> simp
  | and a b iha ihb => simp [boolean, beval, iha, ihb]

/-- Translate the full command language; loop annotations are unused ghost
data. -/
def command (ρ : Nat → String) : Cslib.IMP.Cmd → Stmt
  | .skip => .skip
  | .assign n a => .assign (ρ n) (arith ρ a)
  | .seq a b => .seq (command ρ a) (command ρ b)
  | .ite b c d => .if_ (boolean ρ b) (command ρ c) (command ρ d)
  | .while b c => .while (boolean ρ b) (fun _ => True) (command ρ c)

/-- Injective renaming makes a concrete target update project to exactly the
canonical update, without identifying unrelated target variables. -/
theorem project_update {ρ : Nat → String} (hρ : Function.Injective ρ)
    (s : State) (n v : Nat) :
    project ρ (s.update (ρ n) v) = Function.update (project ρ s) n v := by
  funext m
  by_cases h : m = n
  · subst m
    simp [project, State.update]
  · have hn : ρ m ≠ ρ n := fun heq => h (hρ heq)
    simp [project, State.update, h, hn]

/-- False canonical guards correspond to negated MiniImp guards. -/
theorem eval_boolean_false (ρ : Nat → String) (b : Cslib.IMP.BExp)
    (s : State) :
    ¬ beval (boolean ρ b) s ↔ b.eval (project ρ s) = false := by
  rw [eval_boolean]
  cases b.eval (project ρ s) <;> simp

/-- Every canonical execution lifts from any target state with the right
projection. Only the projected final state is prescribed. -/
theorem lift_execution {ρ : Nat → String} (hρ : Function.Injective ρ)
    {c : Cslib.IMP.Cmd} {i f : Cslib.IMP.State}
    (h : Cslib.IMP.BigStep c i f) :
    ∀ s, project ρ s = i →
      ∃ t, BigStep (command ρ c) s t ∧ project ρ t = f := by
  induction h with
  | skip i =>
      intro s hs
      exact ⟨s, .skip, hs⟩
  | assign i n a =>
      intro s hs
      refine ⟨s.update (ρ n) (evalA (arith ρ a) s), .assign, ?_⟩
      rw [project_update hρ, eval_arith, hs]
  | seq _ _ ih₁ ih₂ =>
      intro s hs
      obtain ⟨u, hu, hp⟩ := ih₁ s hs
      obtain ⟨t, ht, hq⟩ := ih₂ u hp
      exact ⟨t, .seq hu ht, hq⟩
  | iteTrue hb _ ih =>
      intro s hs
      obtain ⟨t, ht, hp⟩ := ih s hs
      refine ⟨t, .ifTrue ?_ ht, hp⟩
      apply (eval_boolean ρ _ s).mpr
      simpa only [hs] using hb
  | iteFalse hb _ ih =>
      intro s hs
      obtain ⟨t, ht, hp⟩ := ih s hs
      refine ⟨t, .ifFalse ?_ ht, hp⟩
      apply (eval_boolean_false ρ _ s).mpr
      simpa only [hs] using hb
  | whileFalse hb =>
      intro s hs
      refine ⟨s, .whileFalse ?_, hs⟩
      apply (eval_boolean_false ρ _ s).mpr
      simpa only [hs] using hb
  | whileTrue hb _ _ ih₁ ih₂ =>
      intro s hs
      obtain ⟨u, hu, hp⟩ := ih₁ s hs
      obtain ⟨t, ht, hq⟩ := ih₂ u hp
      refine ⟨t, .whileTrue ?_ hu ht, hq⟩
      apply (eval_boolean ρ _ s).mpr
      simpa only [hs] using hb

private theorem reflect_and_frame {ρ : Nat → String}
    (hρ : Function.Injective ρ) {d : Stmt} {s t : State}
    (h : BigStep d s t) :
    ∀ c, d = command ρ c →
      Cslib.IMP.BigStep c (project ρ s) (project ρ t) ∧
        ∀ x, (∀ n, x ≠ ρ n) → t x = s x := by
  induction h with
  | skip =>
      intro c heq
      cases c <;> simp only [command] at heq <;> cases heq
      exact ⟨.skip _, fun _ _ => rfl⟩
  | assign =>
      intro c heq
      cases c <;> simp only [command] at heq <;> cases heq
      rename_i n a
      constructor
      · simpa only [project_update hρ, eval_arith] using
          Cslib.IMP.BigStep.assign (project ρ _) n a
      · intro x hx
        simp [State.update, hx n]
  | read _ =>
      intro c heq
      cases c <;> simp only [command] at heq <;> cases heq
  | seq _ _ ih₁ ih₂ =>
      intro c heq
      cases c <;> simp only [command] at heq <;> cases heq
      obtain ⟨h₁, hf₁⟩ := ih₁ _ rfl
      obtain ⟨h₂, hf₂⟩ := ih₂ _ rfl
      exact ⟨.seq h₁ h₂, fun x hx => (hf₂ x hx).trans (hf₁ x hx)⟩
  | ifTrue hb _ ih =>
      intro c heq
      cases c <;> simp only [command] at heq <;> cases heq
      obtain ⟨hc, hf⟩ := ih _ rfl
      exact ⟨.iteTrue ((eval_boolean ρ _ _).mp hb) hc, hf⟩
  | ifFalse hb _ ih =>
      intro c heq
      cases c <;> simp only [command] at heq <;> cases heq
      obtain ⟨hc, hf⟩ := ih _ rfl
      exact ⟨.iteFalse ((eval_boolean_false ρ _ _).mp hb) hc, hf⟩
  | whileFalse hb =>
      intro c heq
      cases c <;> simp only [command] at heq <;> cases heq
      rename_i b c
      exact ⟨.whileFalse ((eval_boolean_false ρ b _).mp hb),
        fun _ _ => rfl⟩
  | whileTrue hb _ _ ih₁ ih₂ =>
      intro c heq
      cases c <;> simp only [command] at heq <;> cases heq
      obtain ⟨h₁, hf₁⟩ := ih₁ _ rfl
      obtain ⟨h₂, hf₂⟩ := ih₂ (.while _ _) rfl
      exact ⟨.whileTrue ((eval_boolean ρ _ _).mp hb) h₁ h₂,
        fun x hx => (hf₂ x hx).trans (hf₁ x hx)⟩

/-- Every execution of a translated command projects to canonical IMP. -/
theorem reflect_execution {ρ : Nat → String} (hρ : Function.Injective ρ)
    {c : Cslib.IMP.Cmd} {s t : State} (h : BigStep (command ρ c) s t) :
    Cslib.IMP.BigStep c (project ρ s) (project ρ t) :=
  (reflect_and_frame hρ h c rfl).1

/-- Translated executions leave every target variable outside the renaming
range unchanged. Projection alone would not imply this property. -/
theorem unmapped_preserved {ρ : Nat → String} (hρ : Function.Injective ρ)
    {c : Cslib.IMP.Cmd} {s t : State} (h : BigStep (command ρ c) s t)
    (x : String) (hx : ∀ n, x ≠ ρ n) : t x = s x :=
  (reflect_and_frame hρ h c rfl).2 x hx

/-- Exact execution correspondence with existential target state completion. -/
theorem execution_iff {ρ : Nat → String} (hρ : Function.Injective ρ)
    (c : Cslib.IMP.Cmd) (s : State) (f : Cslib.IMP.State) :
    Cslib.IMP.BigStep c (project ρ s) f ↔
      ∃ t, BigStep (command ρ c) s t ∧ project ρ t = f := by
  constructor
  · intro h
    exact lift_execution hρ h s rfl
  · rintro ⟨t, ht, rfl⟩
    exact reflect_execution hρ ht

/-- Canonical semantic partial-correctness triples hold for the translated
program and projected assertions. This does not assert termination. -/
theorem valid_to_hoare {ρ : Nat → String} (hρ : Function.Injective ρ)
    {P Q : Cslib.IMP.Assertion} {c : Cslib.IMP.Cmd}
    (h : Cslib.IMP.Valid P c Q) :
    Hoare (fun s => P (project ρ s)) (command ρ c)
      (fun t => Q (project ρ t)) := by
  intro s t hP ht
  exact h hP (reflect_execution hρ ht)

end CSLibExt.Languages.MiniImp.IMPBridge
