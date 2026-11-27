/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Languages.IMP.BigStep
public import Mathlib.Data.Set.Operations
public import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Function

/-!
# The two-run product of IMP commands

The sequential self-composition in Clarkson and Schneider, *Hyperproperties*, §4, motivates
running disjoint renamed copies of one command. Here we prove the exact terminating big-step
correspondence for IMP. This does not compare divergence, timing, or intermediate states.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.IMP

/-- Rename the variables read by an arithmetic expression. -/
def AExp.rename (ρ : ℕ → ℕ) : AExp → AExp
  | .const n => .const n
  | .var i => .var (ρ i)
  | .add a b => .add (a.rename ρ) (b.rename ρ)
  | .sub a b => .sub (a.rename ρ) (b.rename ρ)
  | .mul a b => .mul (a.rename ρ) (b.rename ρ)

/-- Rename the variables read by a Boolean expression. -/
def BExp.rename (ρ : ℕ → ℕ) : BExp → BExp
  | .truth b => .truth b
  | .eq a b => .eq (a.rename ρ) (b.rename ρ)
  | .le a b => .le (a.rename ρ) (b.rename ρ)
  | .not b => .not (b.rename ρ)
  | .and a b => .and (a.rename ρ) (b.rename ρ)

/-- Rename every read and write of a command. -/
def Cmd.rename (ρ : ℕ → ℕ) : Cmd → Cmd
  | .skip => .skip
  | .assign i a => .assign (ρ i) (a.rename ρ)
  | .seq c d => .seq (c.rename ρ) (d.rename ρ)
  | .ite b c d => .ite (b.rename ρ) (c.rename ρ) (d.rename ρ)
  | .while b c => .while (b.rename ρ) (c.rename ρ)

@[simp]
theorem AExp.eval_rename (ρ : ℕ → ℕ) (a : AExp) (u : State) :
    (a.rename ρ).eval u = a.eval (u ∘ ρ) := by
  induction a <;> simp [AExp.rename, AExp.eval, Function.comp_def, *]

@[simp]
theorem BExp.eval_rename (ρ : ℕ → ℕ) (b : BExp) (u : State) :
    (b.rename ρ).eval u = b.eval (u ∘ ρ) := by
  induction b <;> simp [BExp.rename, BExp.eval, *]

private theorem rename_project {ρ : ℕ → ℕ} (hρ : Function.Injective ρ)
    {d : Cmd} {u v : State} (h : BigStep d u v) {c : Cmd} (hc : c.rename ρ = d) :
    BigStep c (u ∘ ρ) (v ∘ ρ) ∧ ∀ i, i ∉ Set.range ρ → v i = u i := by
  induction h generalizing c with
  | skip =>
      cases c <;> cases hc
      exact ⟨.skip _, fun _ _ => rfl⟩
  | assign u i a =>
      cases c with
      | assign j b =>
          change Cmd.assign (ρ j) (b.rename ρ) = Cmd.assign i a at hc
          obtain ⟨rfl, rfl⟩ := Cmd.assign.inj hc
          constructor
          · rw [Function.update_comp_eq_of_injective u hρ, AExp.eval_rename]
            exact .assign _ _ _
          · intro k hk
            exact Function.update_of_ne (fun he => hk ⟨j, he.symm⟩) _ _
      | skip | seq | ite | «while» => cases hc
  | seq h₁ h₂ ih₁ ih₂ =>
      cases c with
      | seq c₁ c₂ =>
          obtain ⟨e₁, e₂⟩ := Cmd.seq.inj hc
          obtain ⟨p₁, f₁⟩ := ih₁ e₁
          obtain ⟨p₂, f₂⟩ := ih₂ e₂
          exact ⟨.seq p₁ p₂, fun i hi => (f₂ i hi).trans (f₁ i hi)⟩
      | skip | assign | ite | «while» => cases hc
  | iteTrue hg hb ih =>
      cases c with
      | ite b c₁ c₂ =>
          obtain ⟨rfl, e₁, _⟩ := Cmd.ite.inj hc
          obtain ⟨p₁, f₁⟩ := ih e₁
          exact ⟨.iteTrue (by simpa only [BExp.eval_rename] using hg) p₁, f₁⟩
      | skip | assign | seq | «while» => cases hc
  | iteFalse hg hb ih =>
      cases c with
      | ite b c₁ c₂ =>
          obtain ⟨rfl, _, e₂⟩ := Cmd.ite.inj hc
          obtain ⟨p₂, f₂⟩ := ih e₂
          exact ⟨.iteFalse (by simpa only [BExp.eval_rename] using hg) p₂, f₂⟩
      | skip | assign | seq | «while» => cases hc
  | whileFalse hg =>
      cases c with
      | «while» b c =>
          obtain ⟨rfl, _⟩ := Cmd.while.inj hc
          exact ⟨.whileFalse (by simpa only [BExp.eval_rename] using hg), fun _ _ => rfl⟩
      | skip | assign | seq | ite => cases hc
  | whileTrue hg hb hl ihb ihl =>
      cases c with
      | «while» b c =>
          obtain ⟨e₁, e₂⟩ := Cmd.while.inj hc
          obtain ⟨pb, fb⟩ := ihb e₂
          obtain ⟨pl, fl⟩ := ihl hc
          rw [← e₁, BExp.eval_rename] at hg
          exact ⟨.whileTrue hg pb pl, fun i hi => (fl i hi).trans (fb i hi)⟩
      | skip | assign | seq | ite => cases hc

private theorem rename_lift {ρ : ℕ → ℕ} (hρ : Function.Injective ρ)
    {c : Cmd} {s t : State} (h : BigStep c s t) {u : State} (hu : u ∘ ρ = s) :
    ∃ v, BigStep (c.rename ρ) u v ∧ v ∘ ρ = t ∧ ∀ i, i ∉ Set.range ρ → v i = u i := by
  induction h generalizing u with
  | skip => exact ⟨u, .skip _, hu, fun _ _ => rfl⟩
  | assign s i a =>
      refine ⟨_, .assign u (ρ i) (a.rename ρ), ?_, ?_⟩
      · rw [Function.update_comp_eq_of_injective u hρ, AExp.eval_rename, hu]
      · intro j hj
        exact Function.update_of_ne (fun he => hj ⟨i, he.symm⟩) _ _
  | seq h₁ h₂ ih₁ ih₂ =>
      obtain ⟨v, p₁, hv, f₁⟩ := ih₁ hu
      obtain ⟨w, p₂, hw, f₂⟩ := ih₂ hv
      exact ⟨w, .seq p₁ p₂, hw, fun i hi => (f₂ i hi).trans (f₁ i hi)⟩
  | iteTrue hg hb ih =>
      obtain ⟨v, p, hv, f⟩ := ih hu
      exact ⟨v, .iteTrue (by simpa only [BExp.eval_rename, hu] using hg) p, hv, f⟩
  | iteFalse hg hb ih =>
      obtain ⟨v, p, hv, f⟩ := ih hu
      exact ⟨v, .iteFalse (by simpa only [BExp.eval_rename, hu] using hg) p, hv, f⟩
  | whileFalse hg =>
      exact ⟨u, .whileFalse (by simpa only [BExp.eval_rename, hu] using hg), hu, fun _ _ => rfl⟩
  | whileTrue hg hb hl ihb ihl =>
      obtain ⟨v, pb, hv, fb⟩ := ihb hu
      obtain ⟨w, pl, hw, fl⟩ := ihl hv
      refine ⟨w, .whileTrue ?_ pb pl, hw, fun i hi => (fl i hi).trans (fb i hi)⟩
      simpa only [BExp.eval_rename, hu] using hg

/-- **Big-step renaming with a frame.** Injective renaming preserves the big-step execution read
through the variable map and leaves every location outside its range unchanged. -/
theorem bigStep_rename_iff {ρ : ℕ → ℕ} (hρ : Function.Injective ρ)
    (c : Cmd) (u v : State) : BigStep (c.rename ρ) u v ↔
      BigStep c (u ∘ ρ) (v ∘ ρ) ∧ ∀ i, i ∉ Set.range ρ → v i = u i := by
  constructor
  · intro h
    exact rename_project hρ h rfl
  · rintro ⟨h, hv⟩
    obtain ⟨w, hw, he, hf⟩ := rename_lift hρ h (u := u) rfl
    have heq : w = v := by
      funext i
      by_cases hi : i ∈ Set.range ρ
      · obtain ⟨j, rfl⟩ := hi
        exact congrFun he j
      · exact (hf i hi).trans (hv i hi).symm
    exact heq ▸ hw

/-- Place the first state on even indices and the second on odd indices. -/
def pairStates (s₀ s₁ : State) : State := fun i => if i % 2 = 0 then s₀ (i / 2) else s₁ (i / 2)

@[simp]
theorem pairStates_even (s₀ s₁ : State) (i : ℕ) : pairStates s₀ s₁ (2 * i) = s₀ i := by
  have hm : (2 * i) % 2 = 0 := by omega
  have hd : (2 * i) / 2 = i := by omega
  simp only [pairStates, hm, ite_true, hd]

@[simp]
theorem pairStates_odd (s₀ s₁ : State) (i : ℕ) : pairStates s₀ s₁ (2 * i + 1) = s₁ i := by
  have hm : (2 * i + 1) % 2 ≠ 0 := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp only [pairStates, ite_eq_right hm, hd]

/-- Reading a state at even and odd positions is inverse to interleaving. -/
def pairStatesEquiv : State × State ≃ State where
  toFun s := pairStates s.1 s.2
  invFun u := (u ∘ (fun i => 2 * i), u ∘ (fun i => 2 * i + 1))
  left_inv s := by
    ext i <;> simp
  right_inv u := by
    funext i
    by_cases hi : i % 2 = 0
    · have he : 2 * (i / 2) = i := by omega
      simp only [pairStates, hi, ite_true, Function.comp_apply, he]
    · have he : 2 * (i / 2) + 1 = i := by omega
      simp only [pairStates, ite_eq_right hi, Function.comp_apply, he]

private theorem even_injective : Function.Injective (fun i : ℕ => 2 * i) := by
  intro a b h
  change 2 * a = 2 * b at h
  omega

private theorem odd_injective : Function.Injective (fun i : ℕ => 2 * i + 1) := by
  intro a b h
  change 2 * a + 1 = 2 * b + 1 at h
  omega

private theorem odd_not_mem_even (i : ℕ) : 2 * i + 1 ∉ Set.range (fun j : ℕ => 2 * j) := by
  rintro ⟨j, h⟩
  change 2 * j = 2 * i + 1 at h
  omega

private theorem even_not_mem_odd (i : ℕ) : 2 * i ∉ Set.range (fun j : ℕ => 2 * j + 1) := by
  rintro ⟨j, h⟩
  change 2 * j + 1 = 2 * i at h
  omega

/-- Run the even-indexed copy, then the odd-indexed copy of the command. -/
def Cmd.twoRunProduct (c : Cmd) : Cmd :=
  .seq (c.rename (fun i => 2 * i)) (c.rename (fun i => 2 * i + 1))

/-- **Two-run product of IMP commands.** Running the two renamed copies in sequence from the
paired input terminates at the paired output exactly when both independent runs terminate at
those outputs. The two runs need not have the same length or make the same control choices. -/
theorem bigStep_twoRunProduct_iff (c : Cmd) (s₀ s₁ t₀ t₁ : State) :
    BigStep c s₀ t₀ ∧ BigStep c s₁ t₁ ↔
      BigStep c.twoRunProduct (pairStates s₀ s₁) (pairStates t₀ t₁) := by
  have even₀ (s t : State) : pairStates s t ∘ (fun i => 2 * i) = s :=
    funext (pairStates_even s t)
  have odd₁ (s t : State) : pairStates s t ∘ (fun i => 2 * i + 1) = t :=
    funext (pairStates_odd s t)
  rw [Cmd.twoRunProduct, BigStep.seq_iff]
  constructor
  · rintro ⟨h₀, h₁⟩
    refine ⟨pairStates t₀ s₁, ?_, ?_⟩
    · apply (bigStep_rename_iff even_injective _ _ _).mpr
      refine ⟨by simpa only [even₀] using h₀, ?_⟩
      intro i hi
      have ho : i = 2 * (i / 2) + 1 := by
        by_contra hn
        apply hi
        exact ⟨i / 2, show 2 * (i / 2) = i by omega⟩
      rw [ho, pairStates_odd, pairStates_odd]
    · apply (bigStep_rename_iff odd_injective _ _ _).mpr
      refine ⟨by simpa only [odd₁] using h₁, ?_⟩
      intro i hi
      have he : i = 2 * (i / 2) := by
        by_contra hn
        apply hi
        exact ⟨i / 2, show 2 * (i / 2) + 1 = i by omega⟩
      rw [he, pairStates_even, pairStates_even]
  · rintro ⟨u, h₀, h₁⟩
    obtain ⟨p₀, f₀⟩ := (bigStep_rename_iff even_injective _ _ _).mp h₀
    obtain ⟨p₁, f₁⟩ := (bigStep_rename_iff odd_injective _ _ _).mp h₁
    have he : u ∘ (fun i => 2 * i) = t₀ := by
      funext i
      exact (f₁ _ (even_not_mem_odd i)).symm.trans (pairStates_even t₀ t₁ i)
    have ho : u ∘ (fun i => 2 * i + 1) = s₁ := by
      funext i
      exact (f₀ _ (odd_not_mem_even i)).trans (pairStates_odd s₀ s₁ i)
    exact ⟨by simpa only [even₀, he] using p₀, by simpa only [odd₁, ho] using p₁⟩

end Cslib.IMP
