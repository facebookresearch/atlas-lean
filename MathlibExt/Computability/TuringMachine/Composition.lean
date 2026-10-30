/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright 2026 Joshua Tan.
Authors: Joshua Tan (original development); ported by Adam Kiezun and Metamate.

Adapted from `Comp.lean` of `JoshuaTan42/millennium-cook-levin` at commit
`879c4835640119ad009abeb62ebd7a96f87eb9e8`
(<https://github.com/JoshuaTan42/millennium-cook-levin/blob/879c4835640119ad009abeb62ebd7a96f87eb9e8/Comp.lean>),
licensed under the Apache License, Version 2.0
(<https://www.apache.org/licenses/LICENSE-2.0>). Changes: module-system header and imports,
`MetaMathlibExt` namespaces, Mathlib-pin proof repairs, removal of the source repository's
`Millennium` hypothesis wrapper, the `IsPolyTime` corollaries at the end of this file, and
`iter_none` taken from `MetaMathlibExt.TM2Program`.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.TuringMachine.Program

/-!
# Composition of polynomial-time two-stack Turing machines

`TM2ComputableInPolyTime` is closed under composition: from machines computing `f : α → β`
and `g : β → γ` in polynomial time we build one machine computing `g ∘ f` in polynomial time.
Mathlib PR #44441 (`TM2ComputableInPolyTime.comp`, stacked on #44440) proves the same result
upstream; once it reaches the pinned Mathlib, prefer it and retire this file.

The composite machine has stacks `K₁ ⊕ K₂ ⊕ Unit`. It runs `M₁`, pops `M₁`'s output onto a
scratch stack and from there onto `M₂`'s input stack (the two reversals cancel), then runs `M₂`.
Each copy loop takes `2m + 1` steps for an intermediate string of length `m`, and
`m ≤ n + c · p₁(n)` where `c` bounds the pushes per step of `M₁` (`pushBound`), so the
composite runs within `p₁ + 4 (X + c p₁) + 2 + p₂ ∘ (X + c p₁)` steps (`compTime`).

## Main declarations

* `MetaMathlibExt.TM2Composition.compComputable`: the composite machine with its time bound.
* `MetaMathlibExt.tm2ComputableInPolyTime_comp`: closure under composition, as `Nonempty`.
* `MetaMathlibExt.ComplexityTheory.IsPolyTime.comp`: closure of `IsPolyTime` under composition.
* `MetaMathlibExt.ComplexityTheory.comp_mem_P`: `P` is closed under polynomial-time preimages.
-/

@[expose] public section

namespace MetaMathlibExt.TM2Composition

open Turing StateTransition Function

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin

variable (M₁ M₂ : FinTM2)

/-- Stack indices of the composite machine: `M₁`'s stacks, `M₂`'s stacks, one scratch stack. -/
abbrev CK := M₁.K ⊕ M₂.K ⊕ Unit

/-- `M₂`'s input alphabet, used for the scratch stack and for symbols held in the control. -/
abbrev X := M₂.Γ M₂.k₀

/-- Stack alphabets of the composite machine. -/
@[reducible] def CΓ : CK M₁ M₂ → Type
  | .inl k => M₁.Γ k
  | .inr (.inl k) => M₂.Γ k
  | .inr (.inr _) => X M₂

/-- Labels: `M₁`'s, `M₂`'s, and the two copy loops (`none` = pop, `some x` = push `x`). -/
abbrev CΛ := M₁.Λ ⊕ M₂.Λ ⊕ (Option (X M₂) ⊕ Option (X M₂))

/-- States: `M₁`'s state, `M₂`'s state, and the symbol just popped by a copy loop. -/
abbrev Cσ := M₁.σ × M₂.σ × Option (X M₂)

/-- Label: pop from `M₁`'s output stack. -/
abbrev pop1 : CΛ M₁ M₂ := .inr (.inr (.inl none))
/-- Label: push `x` on the scratch stack. -/
abbrev push1 (x : X M₂) : CΛ M₁ M₂ := .inr (.inr (.inl (some x)))
/-- Label: pop from the scratch stack. -/
abbrev pop2 : CΛ M₁ M₂ := .inr (.inr (.inr none))
/-- Label: push `x` on `M₂`'s input stack. -/
abbrev push2 (x : X M₂) : CΛ M₁ M₂ := .inr (.inr (.inr (some x)))

/-- The scratch stack index. -/
abbrev tmp : CK M₁ M₂ := .inr (.inr ())

/-- Lift a statement of `M₁`; halting jumps to the first copy loop instead. -/
def lift₁ : TM2.Stmt M₁.Γ M₁.Λ M₁.σ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .push k f q => .push (.inl k) (fun s => f s.1) (lift₁ q)
  | .peek k f q => .peek (.inl k) (fun s o => (f s.1 o, s.2)) (lift₁ q)
  | .pop k f q => .pop (.inl k) (fun s o => (f s.1 o, s.2)) (lift₁ q)
  | .load a q => .load (fun s => (a s.1, s.2)) (lift₁ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (lift₁ q₁) (lift₁ q₂)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => pop1 M₁ M₂)

/-- Lift a statement of `M₂`; halting halts. -/
def lift₂ : TM2.Stmt M₂.Γ M₂.Λ M₂.σ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .push k f q => .push (.inr (.inl k)) (fun s => f s.2.1) (lift₂ q)
  | .peek k f q => .peek (.inr (.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .pop k f q => .pop (.inr (.inl k)) (fun s o => (s.1, f s.2.1 o, s.2.2)) (lift₂ q)
  | .load a q => .load (fun s => (s.1, a s.2.1, s.2.2)) (lift₂ q)
  | .branch f q₁ q₂ => .branch (fun s => f s.2.1) (lift₂ q₁) (lift₂ q₂)
  | .goto f => .goto (fun s => .inr (.inl (f s.2.1)))
  | .halt => .halt

variable (φ : M₁.Γ M₁.k₁ → X M₂)

/-- The composite program. `φ` translates `M₁`'s output symbols into `M₂`'s input symbols. -/
def prog : CΛ M₁ M₂ → TM2.Stmt (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂)
  | .inl l => lift₁ M₁ M₂ (M₁.m l)
  | .inr (.inl l) => lift₂ M₁ M₂ (M₂.m l)
  | .inr (.inr (.inl none)) =>
      .pop (.inl M₁.k₁) (fun s o => (s.1, s.2.1, o.map φ))
        (.goto fun s => match s.2.2 with
          | some x => push1 M₁ M₂ x
          | none => pop2 M₁ M₂)
  | .inr (.inr (.inl (some x))) =>
      .push (tmp M₁ M₂) (fun _ => x) (.goto fun _ => pop1 M₁ M₂)
  | .inr (.inr (.inr none)) =>
      .pop (tmp M₁ M₂) (fun s o => (s.1, s.2.1, o))
        (.goto fun s => match s.2.2 with
          | some x => push2 M₁ M₂ x
          | none => .inr (.inl M₂.main))
  | .inr (.inr (.inr (some x))) =>
      .push (.inr (.inl M₂.k₀)) (fun _ => x) (.goto fun _ => pop2 M₁ M₂)

/-- The composite machine. -/
noncomputable def compTM : FinTM2 where
  K := CK M₁ M₂
  k₀ := .inl M₁.k₀
  k₁ := .inr (.inl M₂.k₁)
  Γ := CΓ M₁ M₂
  Λ := CΛ M₁ M₂
  main := .inl M₁.main
  σ := Cσ M₁ M₂
  initialState := (M₁.initialState, M₂.initialState, none)
  Γk₀Fin := M₁.Γk₀Fin
  m := prog M₁ M₂ φ

/-! ### Stacks of the composite machine -/

/-- Assemble composite stacks from `M₁`'s stacks, `M₂`'s stacks and the scratch stack. -/
def mkStk (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂)) :
    ∀ k : CK M₁ M₂, List (CΓ M₁ M₂ k)
  | .inl k => S₁ k
  | .inr (.inl k) => S₂ k
  | .inr (.inr _) => t

variable {M₁ M₂}

theorem update_mkStk_inl (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (k : M₁.K) (x : List (M₁.Γ k)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (.inl k) x = mkStk M₁ M₂ (update S₁ k x) S₂ t := by
  funext k'
  rcases k' with k' | k' | u
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl
  · rw [update_of_ne (by simp)]; rfl

theorem update_mkStk_inr (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (k : M₂.K) (x : List (M₂.Γ k)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (.inr (.inl k)) x = mkStk M₁ M₂ S₁ (update S₂ k x) t := by
  funext k'
  rcases k' with k' | k' | u
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k' = k
    · subst h; simp [mkStk]
    · rw [update_of_ne (by simpa using h)]; exact (update_of_ne h _ _).symm
  · rw [update_of_ne (by simp)]; rfl

theorem update_mkStk_tmp (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (x : List (X M₂)) :
    update (mkStk M₁ M₂ S₁ S₂ t) (tmp M₁ M₂) x = mkStk M₁ M₂ S₁ S₂ x := by
  funext k'
  rcases k' with k' | k' | ⟨⟩
  · rw [update_of_ne (by simp)]; rfl
  · rw [update_of_ne (by simp)]; rfl
  · simp [mkStk]

/-! ### Simulating one statement of `M₁` or `M₂` -/

/-- Composite label of a (possibly halted) `M₁` label: halting becomes the first copy loop. -/
def lab₁ : Option M₁.Λ → CΛ M₁ M₂
  | some l => .inl l
  | none => pop1 M₁ M₂

theorem stepAux_lift₁ (q : TM2.Stmt M₁.Γ M₁.Λ M₁.σ) (v : M₁.σ) (S₁ : ∀ k, List (M₁.Γ k))
    (v₂ : M₂.σ) (o : Option (X M₂)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂)) :
    TM2.stepAux (lift₁ M₁ M₂ q) (v, v₂, o) (mkStk M₁ M₂ S₁ S₂ t) =
      ⟨some (lab₁ (TM2.stepAux q v S₁).l), ((TM2.stepAux q v S₁).var, v₂, o),
        mkStk M₁ M₂ (TM2.stepAux q v S₁).stk S₂ t⟩ := by
  induction q generalizing v S₁ with
  | push k f q ih =>
      simp only [lift₁, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inl k) = S₁ k from rfl, update_mkStk_inl, ih]
  | peek k f q ih =>
      simp only [lift₁, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [lift₁, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inl k) = S₁ k from rfl, update_mkStk_inl, ih]
  | load a q ih =>
      simp only [lift₁, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lift₁, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₁, TM2.stepAux, lab₁]
  | halt => simp [lift₁, TM2.stepAux, lab₁]

theorem stepAux_lift₂ (q : TM2.Stmt M₂.Γ M₂.Λ M₂.σ) (v : M₂.σ) (S₂ : ∀ k, List (M₂.Γ k))
    (v₁ : M₁.σ) (o : Option (X M₂)) (S₁ : ∀ k, List (M₁.Γ k)) (t : List (X M₂)) :
    TM2.stepAux (lift₂ M₁ M₂ q) (v₁, v, o) (mkStk M₁ M₂ S₁ S₂ t) =
      ⟨(TM2.stepAux q v S₂).l.map (fun l => .inr (.inl l)), (v₁, (TM2.stepAux q v S₂).var, o),
        mkStk M₁ M₂ S₁ (TM2.stepAux q v S₂).stk t⟩ := by
  induction q generalizing v S₂ with
  | push k f q ih =>
      simp only [lift₂, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inr (.inl k)) = S₂ k from rfl, update_mkStk_inr, ih]
  | peek k f q ih =>
      simp only [lift₂, TM2.stepAux]
      exact ih _ _
  | pop k f q ih =>
      simp only [lift₂, TM2.stepAux]
      rw [show mkStk M₁ M₂ S₁ S₂ t (.inr (.inl k)) = S₂ k from rfl, update_mkStk_inr, ih]
  | load a q ih =>
      simp only [lift₂, TM2.stepAux]
      exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [lift₂, TM2.stepAux]
      cases f v <;> simp [ih₁, ih₂]
  | goto f => simp [lift₂, TM2.stepAux]
  | halt => simp [lift₂, TM2.stepAux]

/-! ### Phase embeddings and one-step simulation -/

/-- Composite configuration while running `M₁` (all other stacks empty). -/
def emb₁ (c : TM2.Cfg M₁.Γ M₁.Λ M₁.σ) : TM2.Cfg (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂) :=
  ⟨some (lab₁ c.l), (c.var, M₂.initialState, none), mkStk M₁ M₂ c.stk (fun _ => []) []⟩

/-- Composite configuration while running `M₂` (all other stacks empty). -/
def emb₂ (c : TM2.Cfg M₂.Γ M₂.Λ M₂.σ) : TM2.Cfg (CΓ M₁ M₂) (CΛ M₁ M₂) (Cσ M₁ M₂) :=
  ⟨c.l.map (fun l => .inr (.inl l)), (M₁.initialState, c.var, none),
    mkStk M₁ M₂ (fun _ => []) c.stk []⟩

theorem step_emb₁ {c c' : TM2.Cfg M₁.Γ M₁.Λ M₁.σ} (h : TM2.step M₁.m c = some c') :
    TM2.step (prog M₁ M₂ φ) (emb₁ c) = some (emb₁ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [emb₁, lab₁, TM2.step, prog]
    rw [stepAux_lift₁]
    rfl

theorem step_emb₂ {c c' : TM2.Cfg M₂.Γ M₂.Λ M₂.σ} (h : TM2.step M₂.m c = some c') :
    TM2.step (prog M₁ M₂ φ) (emb₂ c) = some (emb₂ c') := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [TM2.step] at h
  · simp only [TM2.step, Option.some.injEq] at h
    subst h
    simp only [emb₂, Option.map_some, TM2.step, prog]
    rw [stepAux_lift₂]

theorem iter_step {σ : Type} {f : σ → Option σ} {c c' : σ} (h : f c = some c') (n : ℕ) :
    (flip bind f)^[n + 1] (some c) = (flip bind f)^[n] (some c') := by
  rw [iterate_succ_apply]
  change (flip bind f)^[n] (f c) = _
  rw [h]

/-- A step-respecting embedding transports runs. Halted configurations are absorbing, so every
intermediate configuration of a run that ends in `some d` is live. -/
theorem iter_sim {α β : Type} {f : α → Option α} {g : β → Option β} (e : α → β)
    (H : ∀ c c', f c = some c' → g (e c) = some (e c')) :
    ∀ (n : ℕ) (c d : α), (flip bind f)^[n] (some c) = some d →
      (flip bind g)^[n] (some (e c)) = some (e d) := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h ⊢
      rw [h]
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind f)^[n] (f c) = some d at h
      cases hc : f c with
      | none => rw [hc, TM2Program.iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          rw [iter_step (H c c' hc)]
          exact ih c' d h

/-! ### The copy loops -/

section copy

variable (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂)) (S₁ : ∀ k, List (M₁.Γ k))
  (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))

theorem step_pop1_cons (y : M₁.Γ M₁.k₁) (ys : List (M₁.Γ M₁.k₁)) (hy : S₁ M₁.k₁ = y :: ys) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (push1 M₁ M₂ (φ y)), (v₁, v₂, some (φ y)),
        mkStk M₁ M₂ (update S₁ M₁.k₁ ys) S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, hy, update_mkStk_inl]

theorem step_pop1_nil (hy : S₁ M₁.k₁ = []) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop2 M₁ M₂), (v₁, v₂, none), mkStk M₁ M₂ (update S₁ M₁.k₁ []) S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, hy, update_mkStk_inl]

theorem step_push1 (x : X M₂) (s : Cσ M₁ M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (push1 M₁ M₂ x), s, mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop1 M₁ M₂), s, mkStk M₁ M₂ S₁ S₂ (x :: t)⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_pop2_cons (x : X M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ (x :: t)⟩ =
      some ⟨some (push2 M₁ M₂ x), (v₁, v₂, some x), mkStk M₁ M₂ S₁ S₂ t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_pop2_nil :
    TM2.step (prog M₁ M₂ φ) ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ []⟩ =
      some ⟨some (.inr (.inl M₂.main)), (v₁, v₂, none), mkStk M₁ M₂ S₁ S₂ []⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_tmp]

theorem step_push2 (x : X M₂) (s : Cσ M₁ M₂) :
    TM2.step (prog M₁ M₂ φ) ⟨some (push2 M₁ M₂ x), s, mkStk M₁ M₂ S₁ S₂ t⟩ =
      some ⟨some (pop2 M₁ M₂), s, mkStk M₁ M₂ S₁ (update S₂ M₂.k₀ (x :: S₂ M₂.k₀)) t⟩ := by
  simp [TM2.step, prog, TM2.stepAux, mkStk, update_mkStk_inr]

end copy

/-- First copy loop: move `M₁`'s output onto the scratch stack (reversing it). -/
theorem copy₁ (ys : List (M₁.Γ M₁.k₁)) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂))
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) (t : List (X M₂))
    (hy : S₁ M₁.k₁ = ys) :
    (flip bind (TM2.step (prog M₁ M₂ φ)))^[2 * ys.length + 1]
        (some ⟨some (pop1 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩) =
      some ⟨some (pop2 M₁ M₂), (v₁, v₂, none),
        mkStk M₁ M₂ (update S₁ M₁.k₁ []) S₂ ((ys.map φ).reverse ++ t)⟩ := by
  induction ys generalizing o S₁ t with
  | nil =>
      rw [List.length_nil, Nat.mul_zero, iter_step (step_pop1_nil φ v₁ v₂ o S₁ S₂ t hy)]
      simp
  | cons y ys ih =>
      rw [show 2 * (y :: ys).length + 1 = (2 * ys.length + 1) + 1 + 1 by
          simp only [List.length_cons]; omega,
        iter_step (step_pop1_cons φ v₁ v₂ o S₁ S₂ t y ys hy), iter_step (step_push1 φ _ _ _ _ _),
        ih _ _ _ (update_self _ _ _)]
      simp [update_idem]

/-- Second copy loop: move the scratch stack onto `M₂`'s input stack (reversing it back). -/
theorem copy₂ (t : List (X M₂)) (v₁ : M₁.σ) (v₂ : M₂.σ) (o : Option (X M₂))
    (S₁ : ∀ k, List (M₁.Γ k)) (S₂ : ∀ k, List (M₂.Γ k)) :
    (flip bind (TM2.step (prog M₁ M₂ φ)))^[2 * t.length + 1]
        (some ⟨some (pop2 M₁ M₂), (v₁, v₂, o), mkStk M₁ M₂ S₁ S₂ t⟩) =
      some ⟨some (.inr (.inl M₂.main)), (v₁, v₂, none),
        mkStk M₁ M₂ S₁ (update S₂ M₂.k₀ (t.reverse ++ S₂ M₂.k₀)) []⟩ := by
  induction t generalizing o S₂ with
  | nil =>
      rw [List.length_nil, Nat.mul_zero, iter_step (step_pop2_nil φ v₁ v₂ o S₁ S₂)]
      simp
  | cons x t ih =>
      rw [show 2 * (x :: t).length + 1 = (2 * t.length + 1) + 1 + 1 by
          simp only [List.length_cons]; omega,
        iter_step (step_pop2_cons φ v₁ v₂ o S₁ S₂ t x), iter_step (step_push2 φ _ _ _ _ _), ih]
      simp [update_idem]

/-! ### Output length is bounded by input length plus pushes -/

section length

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Number of `push` nodes in a statement tree: an upper bound on pushes per step. -/
def pushes : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => pushes q + 1
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q₁ q₂ => pushes q₁ + pushes q₂
  | .goto _ => 0
  | .halt => 0

theorem length_stepAux (k : K) (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushes q := by
  induction q generalizing v S with
  | push k' f q ih =>
      simp only [TM2.stepAux, pushes]
      refine (ih _ _).trans ?_
      by_cases h : k = k'
      · subst h; simp; omega
      · simp [update_of_ne h]
  | peek k' f q ih => exact ih _ _
  | pop k' f q ih =>
      simp only [TM2.stepAux, pushes]
      refine (ih _ _).trans ?_
      by_cases h : k = k'
      · subst h; simp
      · simp [update_of_ne h]
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      simp only [TM2.stepAux, pushes]
      cases f v
      · exact (ih₂ v S).trans (by omega)
      · exact (ih₁ v S).trans (by omega)
  | goto f => simp [TM2.stepAux]
  | halt => simp [TM2.stepAux]

end length

/-- Per-step push budget of a machine. -/
noncomputable def pushBound (M : FinTM2) : ℕ := ∑ l, pushes (M.m l)

theorem length_step (M : FinTM2) (k : M.K) {c c' : M.Cfg} (h : M.step c = some c') :
    (c'.stk k).length ≤ (c.stk k).length + pushBound M := by
  rcases c with ⟨_ | l, v, S⟩
  · simp [FinTM2.step, TM2.step] at h
  · simp only [FinTM2.step, TM2.step] at h
    rw [← Option.some.inj h]
    have hl : pushes (M.m l) ≤ pushBound M :=
      Finset.single_le_sum (f := fun l => pushes (M.m l)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ l)
    exact (length_stepAux k _ v S).trans (Nat.add_le_add_left hl _)

theorem length_iter (M : FinTM2) (k : M.K) :
    ∀ (n : ℕ) (c d : M.Cfg), (flip bind M.step)^[n] (some c) = some d →
      (d.stk k).length ≤ (c.stk k).length + pushBound M * n := by
  intro n
  induction n with
  | zero =>
      intro c d h
      simp only [iterate_zero, id, Option.some.injEq] at h
      subst h; simp
  | succ n ih =>
      intro c d h
      rw [iterate_succ_apply] at h
      change (flip bind M.step)^[n] (M.step c) = some d at h
      cases hc : M.step c with
      | none => rw [hc, TM2Program.iter_none] at h; cases h
      | some c' =>
          rw [hc] at h
          have h₁ := ih c' d h
          have h₂ := length_step M k hc
          rw [Nat.mul_succ]
          omega

/-! ### Monotonicity of `Polynomial ℕ` evaluation -/

theorem eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval_add]; omega
  | monomial n c =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h n)

/-! ### Initial and halting configurations -/

theorem initList_stk_length_le (M : FinTM2) (l : List (M.Γ M.k₀)) (k : M.K) :
    ((initList M l).stk k).length ≤ l.length := by
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem haltList_stk_self (M : FinTM2) (l : List (M.Γ M.k₁)) : (haltList M l).stk M.k₁ = l := by
  simp [haltList]

theorem update_haltList_stk (M : FinTM2) (l : List (M.Γ M.k₁)) :
    update (haltList M l).stk M.k₁ [] = fun _ => [] := by
  funext k
  by_cases h : k = M.k₁
  · subst h; simp
  · simp [haltList, h]

theorem update_nil_eq_initList (M : FinTM2) (l : List (M.Γ M.k₀)) :
    update (fun _ => []) M.k₀ l = (initList M l).stk := by
  funext k
  by_cases h : k = M.k₀
  · subst h; simp [initList]
  · simp [initList, h]

theorem initList_compTM (l : List (M₁.Γ M₁.k₀)) :
    initList (compTM M₁ M₂ φ) l = emb₁ (initList M₁ l) := by
  simp only [initList, emb₁, lab₁]
  congr 1
  funext k
  rcases k with k | k | u
  · by_cases h : k = M₁.k₀
    · subst h; simp [mkStk, compTM]; try rfl
    · simp [mkStk, compTM, h]
  · simp [mkStk, compTM]
  · simp [mkStk, compTM]

theorem haltList_compTM (l : List (M₂.Γ M₂.k₁)) :
    haltList (compTM M₁ M₂ φ) l = emb₂ (haltList M₂ l) := by
  simp only [haltList, emb₂, Option.map_none]
  congr 1
  funext k
  rcases k with k | k | u
  · simp [mkStk, compTM]
  · by_cases h : k = M₂.k₁
    · subst h; simp [mkStk, compTM]; try rfl
    · simp [mkStk, compTM, h]
  · simp [mkStk, compTM]

/-! ### The composition theorem -/

section main

variable {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ} {eβ : β → List βΓ} {eγ : γ → List γΓ}
  {f : α → β} {g : β → γ}

/-- Symbol translation from `M₁`'s output alphabet to `M₂`'s input alphabet. -/
def glue (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    h₁.tm.Γ h₁.tm.k₁ → X h₂.tm :=
  fun y => h₂.inputAlphabet.symm (h₁.outputAlphabet y)

/-- `n + c·p₁(n)`: a bound on the length of the intermediate string. -/
noncomputable def midPoly (h₁ : TM2ComputableInPolyTime eα eβ f) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (pushBound h₁.tm) * h₁.time

/-- Time bound of the composite machine: `p₁ + 4·(X + c·p₁) + 2 + p₂ ∘ (X + c·p₁)`
(two copy loops of `2m + 1` steps each, with `m ≤ n + c·p₁(n)`). -/
noncomputable def compTime (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : Polynomial ℕ :=
  h₁.time + Polynomial.C 4 * midPoly h₁ + Polynomial.C 2 + h₂.time.comp (midPoly h₁)

/-- The composite machine computes `g ∘ f` within `compTime`. -/
noncomputable def compOutputs (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) (a : α) :
    TM2OutputsInTime (compTM h₁.tm h₂.tm (glue h₁ h₂))
      (List.map h₁.inputAlphabet.invFun (eα a))
      (some (List.map h₂.outputAlphabet.invFun (eγ (g (f a)))))
      ((compTime h₁ h₂).eval (eα a).length) := by
  let φ := glue h₁ h₂
  let inp := List.map h₁.inputAlphabet.invFun (eα a)
  let L := List.map h₁.outputAlphabet.invFun (eβ (f a))
  let inp₂ := List.map h₂.inputAlphabet.invFun (eβ (f a))
  let out := List.map h₂.outputAlphabet.invFun (eγ (g (f a)))
  obtain ⟨⟨s₁, e₁⟩, hs₁⟩ := h₁.outputsFun a
  obtain ⟨⟨s₂, e₂⟩, hs₂⟩ := h₂.outputsFun (f a)
  change (flip bind h₁.tm.step)^[s₁] (some (initList h₁.tm inp)) =
      some (haltList h₁.tm L) at e₁
  change (flip bind h₂.tm.step)^[s₂] (some (initList h₂.tm inp₂)) =
      some (haltList h₂.tm out) at e₂
  -- Phase 1: run `M₁`.
  have P₁ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[s₁]
      (some (emb₁ (M₂ := h₂.tm) (initList h₁.tm inp))) =
      some (emb₁ (M₂ := h₂.tm) (haltList h₁.tm L)) :=
    iter_sim (emb₁ (M₂ := h₂.tm)) (fun _ _ h => step_emb₁ φ h) _ _ _ e₁
  -- Copy loop 1.
  have P₂ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[2 * L.length + 1]
      (some (emb₁ (M₂ := h₂.tm) (haltList h₁.tm L))) =
      some ⟨some (pop2 h₁.tm h₂.tm), (h₁.tm.initialState, h₂.tm.initialState, none),
        mkStk h₁.tm h₂.tm (update (haltList h₁.tm L).stk h₁.tm.k₁ []) (fun _ => [])
          ((L.map φ).reverse ++ [])⟩ :=
    copy₁ φ L _ _ _ _ _ _ (haltList_stk_self _ _)
  -- Copy loop 2, ending in `M₂`'s initial configuration.
  have hT : ((L.map φ).reverse ++ []).reverse ++ [] = inp₂ := by
    simp [L, inp₂, φ, glue, List.map_map, Function.comp_def]
  have P₃ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[2 * ((L.map φ).reverse ++ []).length + 1]
      (some ⟨some (pop2 h₁.tm h₂.tm), (h₁.tm.initialState, h₂.tm.initialState, none),
        mkStk h₁.tm h₂.tm (update (haltList h₁.tm L).stk h₁.tm.k₁ []) (fun _ => [])
          ((L.map φ).reverse ++ [])⟩) =
      some (emb₂ (M₁ := h₁.tm) (initList h₂.tm inp₂)) := by
    rw [copy₂, update_haltList_stk]
    rw [hT, update_nil_eq_initList]
    rfl
  -- Phase 2: run `M₂`.
  have P₄ : (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[s₂]
      (some (emb₂ (M₁ := h₁.tm) (initList h₂.tm inp₂))) =
      some (emb₂ (M₁ := h₁.tm) (haltList h₂.tm out)) :=
    iter_sim (emb₂ (M₁ := h₁.tm)) (fun _ _ h => step_emb₂ φ h) _ _ _ e₂
  refine ⟨⟨s₂ + (2 * ((L.map φ).reverse ++ []).length + 1) + (2 * L.length + 1) +
    s₁, ?_⟩, ?_⟩
  · change (flip bind (compTM h₁.tm h₂.tm φ).step)^[_]
        (some (initList (compTM h₁.tm h₂.tm φ) inp)) =
      Option.map (haltList (compTM h₁.tm h₂.tm φ)) (some out)
    rw [initList_compTM]; simp only [Option.map]; rw [haltList_compTM]
    change (flip bind (TM2.step (prog h₁.tm h₂.tm φ)))^[_] _ = _
    erw [iterate_add_apply, iterate_add_apply, iterate_add_apply]
    erw [P₁, P₂, P₃, P₄]
    rfl
  · -- Time bound.
    change s₁ ≤ h₁.time.eval (eα a).length at hs₁
    change s₂ ≤ h₂.time.eval (eβ (f a)).length at hs₂
    have hlen := length_iter h₁.tm h₁.tm.k₁ _ _ _ e₁
    rw [haltList_stk_self] at hlen
    have hinit := initList_stk_length_le h₁.tm inp h₁.tm.k₁
    have hL : L.length = (eβ (f a)).length := by simp [L]
    have hinp : inp.length = (eα a).length := by simp [inp]
    have hm : (eβ (f a)).length ≤
        (eα a).length + pushBound h₁.tm * h₁.time.eval (eα a).length := by
      have := Nat.mul_le_mul_left (pushBound h₁.tm) hs₁
      omega
    have hp₂ := eval_mono h₂.time hm
    have hmid : (midPoly h₁).eval (eα a).length =
        (eα a).length + pushBound h₁.tm * h₁.time.eval (eα a).length := by
      simp [midPoly]
    simp only [compTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_comp, hmid]
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_nil,
      Nat.add_zero, hL]
    omega

/-- `TM2ComputableInPolyTime` is closed under composition (Mathlib's `proof_wanted`). -/
noncomputable def compComputable (h₁ : TM2ComputableInPolyTime eα eβ f)
    (h₂ : TM2ComputableInPolyTime eβ eγ g) : TM2ComputableInPolyTime eα eγ (g ∘ f) where
  tm := compTM h₁.tm h₂.tm (glue h₁ h₂)
  inputAlphabet := h₁.inputAlphabet
  outputAlphabet := h₂.outputAlphabet
  time := compTime h₁ h₂
  outputsFun := compOutputs h₁ h₂

end main

end MetaMathlibExt.TM2Composition

namespace MetaMathlibExt

open Turing

/-- Composition of polynomial-time TM2-computable functions is polynomial-time
TM2-computable. Mathlib PR #44441 states the same result as `TM2ComputableInPolyTime.comp`. -/
theorem tm2ComputableInPolyTime_comp {α β γ αΓ βΓ γΓ : Type} {eα : α → List αΓ}
    {eβ : β → List βΓ} {eγ : γ → List γΓ} {f : α → β} {g : β → γ}
    (h₁ : TM2ComputableInPolyTime eα eβ f) (h₂ : TM2ComputableInPolyTime eβ eγ g) :
    Nonempty (TM2ComputableInPolyTime eα eγ (g ∘ f)) :=
  ⟨TM2Composition.compComputable h₁ h₂⟩

namespace ComplexityTheory

open Computability

/-- Polynomial-time computability under explicit encodings is closed under composition. -/
theorem IsPolyTimeWithEncoding.comp {α β γ Γα Γβ Γγ : Type} {ea : Encoding α Γα}
    {eb : Encoding β Γβ} {ec : Encoding γ Γγ} {f : α → β} {g : β → γ}
    (hf : IsPolyTimeWithEncoding ea eb f) (hg : IsPolyTimeWithEncoding eb ec g) :
    IsPolyTimeWithEncoding ea ec (g ∘ f) :=
  let ⟨h₁⟩ := hf
  let ⟨h₂⟩ := hg
  tm2ComputableInPolyTime_comp h₁ h₂

/-- `IsPolyTime` is closed under composition. -/
theorem IsPolyTime.comp {α β γ : Type} [BitstringEncoding α] [BitstringEncoding β]
    [BitstringEncoding γ] {f : α → β} {g : β → γ} (hf : IsPolyTime f) (hg : IsPolyTime g) :
    IsPolyTime (g ∘ f) :=
  IsPolyTimeWithEncoding.comp hf hg

/-- `P` is closed under polynomial-time preimages: if `L ∈ P` and `f` is polynomial-time,
then `L ∘ f ∈ P`. In particular `P` is closed under polynomial-time many-one reductions. -/
theorem comp_mem_P {L : DecisionProblem} {f : List Bool → List Bool} (hL : L ∈ P)
    (hf : IsPolyTime f) : L ∘ f ∈ P :=
  IsPolyTime.comp hf hL

end ComplexityTheory

end MetaMathlibExt
