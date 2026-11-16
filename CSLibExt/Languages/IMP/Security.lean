/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Security typing for IMP
-/
module

public import CSLibExt.Languages.IMP.BigStep

/-!
# IMP security

Two-point Volpano-Smith-Irvine security typing with low-equivalence,
simple security, confinement, and termination-insensitive
noninterference over the canonical big-step semantics.
-/

@[expose] public section

namespace Cslib.IMP

/-- Two-point security lattice. -/
inductive SecLevel where
  | Low
  | High
  deriving DecidableEq, Repr

namespace SecLevel

/-- Order: `Low` flows to anything; `High` flows only to `High`. -/
def le : SecLevel → SecLevel → Prop
  | .Low, _ => True
  | .High, .High => True
  | .High, .Low => False

/-- Join (least upper bound) of two levels. -/
def join : SecLevel → SecLevel → SecLevel
  | .Low, .Low => .Low
  | .Low, .High => .High
  | .High, _ => .High

/-- Decidability of the level order, kept out of typeclass search. -/
def decLe (a b : SecLevel) : Decidable (le a b) := by
  cases a <;> cases b <;> simp only [le] <;> infer_instance

@[simp] theorem le_low (l : SecLevel) : le .Low l := by
  cases l <;> simp [le]

@[simp] theorem le_high_high : le .High .High := by simp [le]

@[simp] theorem not_le_high_low : ¬ le .High .Low := by simp [le]

theorem le_refl (l : SecLevel) : le l l := by
  cases l <;> simp [le]

/-- Only `Low` flows to `Low`. -/
theorem of_le_low {a : SecLevel} (h : le a .Low) : a = .Low := by
  cases a
  · rfl
  · simp [le] at h

/-- `High` below `l` forces `l` to be `High`. -/
theorem eq_high_of_le_high {l : SecLevel} (h : le .High l) :
    l = .High := by
  cases l
  · simp [le] at h
  · rfl

@[simp] theorem join_high_left (l : SecLevel) :
    (SecLevel.join .High l) = .High := by
  cases l <;> rfl

@[simp] theorem join_high_right (l : SecLevel) :
    (l.join .High) = .High := by
  cases l <;> rfl

@[simp] theorem join_low_left (l : SecLevel) :
    (SecLevel.join .Low l) = l := by
  cases l <;> rfl

@[simp] theorem join_low_right (l : SecLevel) : (l.join .Low) = l := by
  cases l <;> rfl

/-- A join is `Low` exactly when both sides are `Low`. -/
theorem join_eq_low_iff (a b : SecLevel) :
    (a.join b) = .Low ↔ a = .Low ∧ b = .Low := by
  cases a <;> cases b <;> simp

/-- A level that is not `Low` is `High`. -/
theorem eq_high_of_ne_low {l : SecLevel} (h : l ≠ .Low) :
    l = .High := by
  cases l
  · simp at h
  · rfl

end SecLevel

/-- A variable environment assigns a level to every variable. -/
abbrev SecEnv := Nat → SecLevel

/-- Low-equivalence: agreement on every `Low` variable. -/
def LowEq (Γ : SecEnv) (s t : State) : Prop :=
  ∀ x, Γ x = .Low → s x = t x

theorem LowEq_refl (Γ : SecEnv) (s : State) : LowEq Γ s s := by
  intro x _
  rfl

theorem LowEq_symm {Γ : SecEnv} {s t : State} (h : LowEq Γ s t) :
    LowEq Γ t s := by
  intro x hx
  exact (h x hx).symm

theorem LowEq_trans {Γ : SecEnv} {s t u : State} (h1 : LowEq Γ s t)
    (h2 : LowEq Γ t u) : LowEq Γ s u := by
  intro x hx
  exact (h1 x hx).trans (h2 x hx)

/-- Updating a `High` variable keeps low-equivalence with the old state. -/
theorem LowEq_update_high {Γ : SecEnv} {s : State} {x v : Nat}
    (hx : Γ x = .High) : LowEq Γ s (Function.update s x v) := by
  intro y hy
  have hne : y ≠ x := by
    intro heq
    rw [heq] at hy
    rw [hx] at hy
    simp at hy
  simp [Function.update, hne]

/-- Updating any variable with equal values preserves low-equivalence. -/
theorem LowEq_update_low {Γ : SecEnv} {s1 s2 : State} {x v1 v2 : Nat}
    (heq : LowEq Γ s1 s2) (hv : v1 = v2) :
    LowEq Γ (Function.update s1 x v1) (Function.update s2 x v2) := by
  intro y hy
  by_cases h : y = x
  · subst h
    simp only [Function.update]
    exact hv
  · simp only [Function.update, dite_eq_right h]
    exact heq y hy

/-- Updating a `High` variable on both sides preserves low-equivalence. -/
theorem LowEq_update_high_both {Γ : SecEnv} {s1 s2 : State}
    {x v1 v2 : Nat} (heq : LowEq Γ s1 s2) (hx : Γ x = .High) :
    LowEq Γ (Function.update s1 x v1) (Function.update s2 x v2) := by
  intro y hy
  have hne : y ≠ x := by
    intro heq2
    rw [heq2] at hy
    rw [hx] at hy
    simp at hy
  simp only [Function.update, dite_eq_right hne]
  exact heq y hy

namespace AExp

/-- Security label of an arithmetic expression under `Γ`. -/
def label (Γ : SecEnv) : AExp → SecLevel
  | .const _ => .Low
  | .var x => Γ x
  | .add l r => (label Γ l).join (label Γ r)
  | .sub l r => (label Γ l).join (label Γ r)
  | .mul l r => (label Γ l).join (label Γ r)

@[simp] theorem label_const (Γ : SecEnv) (n : Nat) :
    label Γ (.const n) = .Low := rfl

@[simp] theorem label_var (Γ : SecEnv) (x : Nat) :
    label Γ (.var x) = Γ x := rfl

@[simp] theorem label_add (Γ : SecEnv) (l r : AExp) :
    label Γ (.add l r) = (label Γ l).join (label Γ r) := rfl

@[simp] theorem label_sub (Γ : SecEnv) (l r : AExp) :
    label Γ (.sub l r) = (label Γ l).join (label Γ r) := rfl

@[simp] theorem label_mul (Γ : SecEnv) (l r : AExp) :
    label Γ (.mul l r) = (label Γ l).join (label Γ r) := rfl

/-- Simple security for arithmetic expressions. -/
theorem eval_eq_of_low_label {Γ : SecEnv} {e : AExp} {s t : State} :
    label Γ e = .Low → LowEq Γ s t → e.eval s = e.eval t := by
  induction e with
  | const n =>
      intro _ _
      rfl
  | var x =>
      intro hlow heq
      simp only [label_var] at hlow
      exact heq x hlow
  | add l r ihl ihr =>
      intro hlow heq
      simp only [label_add, SecLevel.join_eq_low_iff] at hlow
      obtain ⟨hl, hr⟩ := hlow
      simp only [eval_add]
      rw [ihl hl heq, ihr hr heq]
  | sub l r ihl ihr =>
      intro hlow heq
      simp only [label_sub, SecLevel.join_eq_low_iff] at hlow
      obtain ⟨hl, hr⟩ := hlow
      simp only [eval_sub]
      rw [ihl hl heq, ihr hr heq]
  | mul l r ihl ihr =>
      intro hlow heq
      simp only [label_mul, SecLevel.join_eq_low_iff] at hlow
      obtain ⟨hl, hr⟩ := hlow
      simp only [eval_mul]
      rw [ihl hl heq, ihr hr heq]

end AExp

namespace BExp

/-- Security label of a Boolean expression under `Γ`. -/
def label (Γ : SecEnv) : BExp → SecLevel
  | .truth _ => .Low
  | .eq l r => (AExp.label Γ l).join (AExp.label Γ r)
  | .le l r => (AExp.label Γ l).join (AExp.label Γ r)
  | .not b => label Γ b
  | .and l r => (label Γ l).join (label Γ r)

@[simp] theorem label_truth (Γ : SecEnv) (v : Bool) :
    label Γ (.truth v) = .Low := rfl

@[simp] theorem label_eq (Γ : SecEnv) (l r : AExp) :
    label Γ (.eq l r) = (AExp.label Γ l).join (AExp.label Γ r) := rfl

@[simp] theorem label_le (Γ : SecEnv) (l r : AExp) :
    label Γ (.le l r) = (AExp.label Γ l).join (AExp.label Γ r) := rfl

@[simp] theorem label_not (Γ : SecEnv) (b : BExp) :
    label Γ (.not b) = label Γ b := rfl

@[simp] theorem label_and (Γ : SecEnv) (l r : BExp) :
    label Γ (.and l r) = (label Γ l).join (label Γ r) := rfl

/-- Simple security for Boolean expressions. -/
theorem eval_eq_of_low_label {Γ : SecEnv} {e : BExp} {s t : State} :
    label Γ e = .Low → LowEq Γ s t → e.eval s = e.eval t := by
  induction e with
  | truth v =>
      intro _ _
      rfl
  | eq l r =>
      intro hlow heq
      simp only [label_eq, SecLevel.join_eq_low_iff] at hlow
      obtain ⟨hl, hr⟩ := hlow
      have h1 : l.eval s = l.eval t :=
        AExp.eval_eq_of_low_label hl heq
      have h2 : r.eval s = r.eval t :=
        AExp.eval_eq_of_low_label hr heq
      simp only [eval]
      rw [h1, h2]
  | le l r =>
      intro hlow heq
      simp only [label_le, SecLevel.join_eq_low_iff] at hlow
      obtain ⟨hl, hr⟩ := hlow
      have h1 : l.eval s = l.eval t :=
        AExp.eval_eq_of_low_label hl heq
      have h2 : r.eval s = r.eval t :=
        AExp.eval_eq_of_low_label hr heq
      simp only [eval]
      rw [h1, h2]
  | not b ih =>
      intro hlow heq
      simp only [label_not] at hlow
      simp only [eval]
      rw [ih hlow heq]
  | and l r ihl ihr =>
      intro hlow heq
      simp only [label_and, SecLevel.join_eq_low_iff] at hlow
      obtain ⟨hl, hr⟩ := hlow
      simp only [eval]
      rw [ihl hl heq, ihr hr heq]

end BExp

/-- Volpano-Smith-Irvine security typing with explicit program counter. -/
inductive SecTyped (Γ : SecEnv) : SecLevel → Cmd → Prop where
  | skip (pc : SecLevel) : SecTyped Γ pc .skip
  | assign (pc : SecLevel) (x : Nat) (a : AExp) :
      SecLevel.le (pc.join (AExp.label Γ a)) (Γ x) →
      SecTyped Γ pc (.assign x a)
  | seq (pc : SecLevel) (c1 c2 : Cmd) :
      SecTyped Γ pc c1 → SecTyped Γ pc c2 → SecTyped Γ pc (.seq c1 c2)
  | ite (pc : SecLevel) (g : BExp) (c1 c2 : Cmd) :
      SecTyped Γ (pc.join (BExp.label Γ g)) c1 →
      SecTyped Γ (pc.join (BExp.label Γ g)) c2 →
      SecTyped Γ pc (.ite g c1 c2)
  | while (pc : SecLevel) (g : BExp) (c : Cmd) :
      SecTyped Γ (pc.join (BExp.label Γ g)) c →
      SecTyped Γ pc (.while g c)

/-- Confinement, by induction on the terminating run. -/
theorem SecTyped.confinement_aux {Γ : SecEnv} {c : Cmd} {s t : State}
    (hrun : BigStep c s t) : SecTyped Γ .High c → LowEq Γ s t := by
  induction hrun with
  | skip =>
      intro _
      exact LowEq_refl Γ _
  | assign s x a =>
      intro ht
      cases ht with
      | assign _ _ _ hle =>
          simp only [SecLevel.join_high_left] at hle
          have hx : Γ x = .High := SecLevel.eq_high_of_le_high hle
          exact LowEq_update_high hx
  | seq h1 h2 ih1 ih2 =>
      intro ht
      cases ht with
      | seq _ _ _ ht1 ht2 =>
          exact LowEq_trans (ih1 ht1) (ih2 ht2)
  | iteTrue hg hb ih =>
      intro ht
      cases ht with
      | ite _ _ _ _ ht1 ht2 =>
          have ht1High := ht1
          simp only [SecLevel.join_high_left] at ht1High
          exact ih ht1High
  | iteFalse hg hb ih =>
      intro ht
      cases ht with
      | ite _ _ _ _ ht1 ht2 =>
          have ht2High := ht2
          simp only [SecLevel.join_high_left] at ht2High
          exact ih ht2High
  | whileFalse hg =>
      intro _
      exact LowEq_refl Γ _
  | whileTrue hg hb hl ihb ihl =>
      intro ht
      cases ht with
      | «while» _ _ _ hbody =>
          have hbodyHigh := hbody
          simp only [SecLevel.join_high_left] at hbodyHigh
          have hwhileHigh : SecTyped Γ .High (.while _ _) :=
            SecTyped.while .High _ _ hbody
          exact LowEq_trans (ihb hbodyHigh) (ihl hwhileHigh)

/-- Confinement: `High`-pc commands preserve low-equivalence. -/
theorem SecTyped.confinement {Γ : SecEnv} {c : Cmd} {s t : State}
    (ht : SecTyped Γ .High c) (hrun : BigStep c s t) :
    LowEq Γ s t :=
  SecTyped.confinement_aux hrun ht

/-- A `while` loop with `High`-typed body preserves low-equivalence. -/
theorem SecTyped.while_high_body {Γ : SecEnv} {g : BExp} {c : Cmd}
    {s t : State} (hbody : SecTyped Γ .High c)
    (hrun : BigStep (.while g c) s t) : LowEq Γ s t := by
  have hbody' : SecTyped Γ (SecLevel.join .High (BExp.label Γ g)) c := by
    rw [SecLevel.join_high_left]
    exact hbody
  exact SecTyped.confinement (SecTyped.while .High g c hbody') hrun

/-- Termination-insensitive noninterference, by run induction. -/
theorem SecTyped.tini_aux {Γ : SecEnv} {c : Cmd} {s1 t1 : State}
    (h1 : BigStep c s1 t1) : ∀ {s2 t2 : State},
    SecTyped Γ .Low c → LowEq Γ s1 s2 → BigStep c s2 t2 →
    LowEq Γ t1 t2 := by
  induction h1 with
  | skip =>
      intro s2 t2 _ heq h2
      rw [BigStep.skip_iff] at h2
      subst h2
      exact heq
  | assign s x a =>
      intro s2 t2 ht heq h2
      cases ht with
      | assign _ _ _ hle =>
          simp only [SecLevel.join_low_left] at hle
          rw [BigStep.assign_iff] at h2
          subst h2
          by_cases hx : Γ x = .Low
          · rw [hx] at hle
            have hlabel : AExp.label Γ a = .Low :=
              SecLevel.of_le_low hle
            have hv : a.eval s = a.eval s2 :=
              AExp.eval_eq_of_low_label hlabel heq
            exact LowEq_update_low heq hv
          · have hxHigh : Γ x = .High :=
              SecLevel.eq_high_of_ne_low hx
            exact LowEq_update_high_both heq hxHigh
  | seq h1a h1b ih1 ih2 =>
      intro s2 t2 ht heq h2
      cases ht with
      | seq _ _ _ ht1 ht2 =>
          rw [BigStep.seq_iff] at h2
          obtain ⟨m2, h2a, h2b⟩ := h2
          exact ih2 ht2 (ih1 ht1 heq h2a) h2b
  | iteTrue hg hb ih =>
      clear c s1 t1
      rename_i g c1 c2 s1 t1
      intro s2 t2 ht heq h2
      cases ht with
      | ite _ g _ _ ht1 ht2 =>
          rw [BigStep.ite_iff] at h2
          by_cases hguard : BExp.label Γ g = .Low
          · have hgeval : g.eval s1 = g.eval s2 :=
              BExp.eval_eq_of_low_label hguard heq
            rw [hg] at hgeval
            have ht1Low := ht1
            simp only [hguard, SecLevel.join_low_right] at ht1Low
            rcases h2 with ⟨h2t, h2b⟩ | ⟨h2f, _⟩
            · exact ih ht1Low heq h2b
            · rw [h2f] at hgeval
              simp at hgeval
          · have hgHigh : BExp.label Γ g = .High :=
              SecLevel.eq_high_of_ne_low hguard
            have ht1High := ht1
            simp only [hgHigh, SecLevel.join_high_right] at ht1High
            have ht2High := ht2
            simp only [hgHigh, SecLevel.join_high_right] at ht2High
            have hconf1 : LowEq Γ s1 t1 :=
              SecTyped.confinement ht1High hb
            rcases h2 with ⟨_, h2b⟩ | ⟨_, h2b⟩
            · have hconf2 : LowEq Γ s2 t2 :=
                SecTyped.confinement ht1High h2b
              exact LowEq_trans (LowEq_trans (LowEq_symm hconf1) heq)
                hconf2
            · have hconf2 : LowEq Γ s2 t2 :=
                SecTyped.confinement ht2High h2b
              exact LowEq_trans (LowEq_trans (LowEq_symm hconf1) heq)
                hconf2
  | iteFalse hg hb ih =>
      clear c s1 t1
      rename_i g c1 c2 s1 t1
      intro s2 t2 ht heq h2
      cases ht with
      | ite _ g _ _ ht1 ht2 =>
          rw [BigStep.ite_iff] at h2
          by_cases hguard : BExp.label Γ g = .Low
          · have hgeval : g.eval s1 = g.eval s2 :=
              BExp.eval_eq_of_low_label hguard heq
            rw [hg] at hgeval
            have ht2Low := ht2
            simp only [hguard, SecLevel.join_low_right] at ht2Low
            rcases h2 with ⟨h2t, _⟩ | ⟨h2f, h2b⟩
            · rw [h2t] at hgeval
              simp at hgeval
            · exact ih ht2Low heq h2b
          · have hgHigh : BExp.label Γ g = .High :=
              SecLevel.eq_high_of_ne_low hguard
            have ht1High := ht1
            simp only [hgHigh, SecLevel.join_high_right] at ht1High
            have ht2High := ht2
            simp only [hgHigh, SecLevel.join_high_right] at ht2High
            have hconf1 : LowEq Γ s1 t1 :=
              SecTyped.confinement ht2High hb
            rcases h2 with ⟨_, h2b⟩ | ⟨_, h2b⟩
            · have hconf2 : LowEq Γ s2 t2 :=
                SecTyped.confinement ht1High h2b
              exact LowEq_trans (LowEq_trans (LowEq_symm hconf1) heq)
                hconf2
            · have hconf2 : LowEq Γ s2 t2 :=
                SecTyped.confinement ht2High h2b
              exact LowEq_trans (LowEq_trans (LowEq_symm hconf1) heq)
                hconf2
  | whileFalse hg =>
      clear c s1 t1
      rename_i g c s1
      intro s2 t2 ht heq h2
      have h2run := h2
      cases ht with
      | «while» _ g _ hbody =>
          rw [BigStep.while_iff] at h2
          by_cases hguard : BExp.label Γ g = .Low
          · have hgeval : g.eval s1 = g.eval s2 :=
              BExp.eval_eq_of_low_label hguard heq
            rw [hg] at hgeval
            rcases h2 with ⟨h2f, hteq⟩ | ⟨h2t, _, _, _⟩
            · subst hteq
              exact heq
            · rw [h2t] at hgeval
              simp at hgeval
          · have hgHigh : BExp.label Γ g = .High :=
              SecLevel.eq_high_of_ne_low hguard
            have hbodyHigh := hbody
            simp only [hgHigh, SecLevel.join_high_right] at hbodyHigh
            rcases h2 with ⟨_, hteq⟩ | ⟨_, _, _, _⟩
            · subst hteq
              exact heq
            · have hconf : LowEq Γ s2 t2 :=
                SecTyped.while_high_body hbodyHigh h2run
              exact LowEq_trans heq hconf
  | whileTrue hg hb hl ihb ihl =>
      clear c s1 t1
      rename_i g c s1 m t1
      intro s2 t2 ht heq h2
      have h2run := h2
      cases ht with
      | «while» _ g _ hbody =>
          rw [BigStep.while_iff] at h2
          by_cases hguard : BExp.label Γ g = .Low
          · have hgeval : g.eval s1 = g.eval s2 :=
              BExp.eval_eq_of_low_label hguard heq
            rw [hg] at hgeval
            have hbodyLow := hbody
            simp only [hguard, SecLevel.join_low_right] at hbodyLow
            have hwhileLow : SecTyped Γ .Low (.while g _) :=
              SecTyped.while .Low g _ hbody
            rcases h2 with ⟨h2f, _⟩ | ⟨h2t, m2, hb2, hl2⟩
            · rw [h2f] at hgeval
              simp at hgeval
            · have hmid : LowEq Γ _ m2 := ihb hbodyLow heq hb2
              exact ihl hwhileLow hmid hl2
          · have hgHigh : BExp.label Γ g = .High :=
              SecLevel.eq_high_of_ne_low hguard
            have hbodyHigh := hbody
            simp only [hgHigh, SecLevel.join_high_right] at hbodyHigh
            have hconf1 : LowEq Γ s1 t1 :=
              SecTyped.while_high_body hbodyHigh
                (BigStep.whileTrue hg hb hl)
            have hconf2 : LowEq Γ s2 t2 :=
              SecTyped.while_high_body hbodyHigh h2run
            exact LowEq_trans (LowEq_trans (LowEq_symm hconf1) heq)
              hconf2

/-- Termination-insensitive noninterference for `Low`-pc commands. -/
theorem SecTyped.tini {Γ : SecEnv} {c : Cmd} {s1 s2 t1 t2 : State}
    (ht : SecTyped Γ .Low c) (heq : LowEq Γ s1 s2)
    (h1 : BigStep c s1 t1) (h2 : BigStep c s2 t2) : LowEq Γ t1 t2 :=
  SecTyped.tini_aux h1 ht heq h2

end Cslib.IMP
