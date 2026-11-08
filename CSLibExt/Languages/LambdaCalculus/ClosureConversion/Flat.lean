/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Flat closure conversion
-/
module

public import CSLibExt.Languages.LambdaCalculus.ClosureConversion.Correctness
public import Mathlib.Data.List.Dedup

/-!
# Flat closure conversion

The free-variable variant of closure conversion (Appel, *Compiling with
Continuations*, Chapter 10, "flat closures"): a lambda captures only the free
variables of its body, each once, instead of the whole environment of
`Correctness.lean`.

For `λ. b`, let `fvs := (freeIndices 1 b).dedup` be the outer variables free in
the lambda. `convertFlat acc t` translates `t` with accessors `acc`:

* `x_i ↦ acc i`;
* `λ. b ↦ (code ⟦b⟧', env)`, where `env` packs `acc i` for `i ∈ fvs` in order,
  and `⟦b⟧'` converts `b` with `x₀ ↦ fst #0` and `x_{j+1} ↦ fst (sndᵏ (snd #0))`
  for `k` the position of `j` in `fvs`;
* `f a ↦ let c = ⟦f⟧ in (fst c) (⟦a⟧, snd c)`, as before.

Correctness (`convertFlat_correct`) only asks the accessors to implement the
variables free in the term (`FlatAccRel`), and relates source closures to
target closures whose environment holds values related to exactly the
captured variables (`FlatValRel`). Closed programs are converted correctly
(`closureConvertFlat_correct`), every code body is closed
(`convertFlat_scoped`, `closureConvertFlat_scoped`), and each closure's
environment has exactly one entry per distinct free variable
(`envFlat_length`).
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ClosureConversion

universe u

variable {Base : Type u}

open Target Target.Tm Stlc.RawTm

/-- Membership in the free variables one binder deeper. -/
theorem mem_freeIndices_succ (t : Stlc.RawTm Base) (d j : Nat) :
    j ∈ freeIndices (d + 1) t ↔ j + 1 ∈ freeIndices d t := by
  induction t generalizing d with
  | var n =>
      simp only [freeIndices]
      by_cases h₁ : d + 1 ≤ n
      · have h₂ : d ≤ n := by omega
        simp only [h₁, h₂, ↓reduceIte, List.mem_singleton]
        omega
      · by_cases h₂ : d ≤ n
        · simp only [h₁, h₂, ↓reduceIte, List.mem_singleton, List.not_mem_nil, false_iff]
          omega
        · simp [h₁, h₂]
  | app f a ihf iha => simp [ihf, iha]
  | lam A body ih => simp only [freeIndices_lam]; exact ih (d + 1)

/-- The outer variables a lambda with body `b` captures: the free variables of
`λ. b`, without duplicates. -/
def captured (body : Stlc.RawTm Base) : List Nat := (freeIndices 1 body).dedup

theorem mem_captured {body : Stlc.RawTm Base} {j : Nat} :
    j ∈ captured body ↔ j + 1 ∈ freeIndices 0 body := by
  rw [captured, List.mem_dedup, mem_freeIndices_succ]

/-- Pack `acc i` for each `i` in a list as nested pairs ending in `unit`. -/
def envFlat (acc : Nat → Tm) : List Nat → Tm
  | [] => .unit
  | i :: is => .pair (acc i) (envFlat acc is)

/-- Accessors inside flat code: variable `0` is the argument, variable `j + 1`
is the entry of the environment at the position of `j` in `fvs`. -/
def flatAcc (fvs : List Nat) : Nat → Tm
  | 0 => .fst (.var 0)
  | j + 1 => .fst (snds (fvs.idxOf j) (.snd (.var 0)))

/-- Flat closure conversion with accessors `acc`. -/
def convertFlat : (Nat → Tm) → Stlc.RawTm Base → Tm
  | acc, .var i => acc i
  | acc, .lam _ body =>
      .pair (.code (convertFlat (flatAcc (captured body)) body)) (envFlat acc (captured body))
  | acc, .app f a =>
      .letIn (convertFlat acc f)
        (.app (.fst (.var 0)) (.pair (convertFlat (fun i => (acc i).shift) a) (.snd (.var 0))))

/-- Flat closure conversion of a closed term. -/
def closureConvertFlat (t : Stlc.RawTm Base) : Tm := convertFlat .var t

/-- Source closures and flat target closures: the environment of the target
closure holds, at position `k`, a value related to the captured source
variable `(captured body)[k]`. -/
inductive FlatValRel : Source.Value Base → Value → Prop
  | clo {body : Stlc.RawTm Base} {ρ : List (Source.Value Base)} {ws : List Value}
      (hlen : (captured body).length = ws.length)
      (hbound : ∀ k (h₁ : k < (captured body).length), (captured body)[k] < ρ.length)
      (hrel : ∀ k (h₁ : k < (captured body).length) (h₂ : k < ws.length),
        FlatValRel (ρ[(captured body)[k]]'(hbound k h₁)) ws[k]) :
      FlatValRel (.clo body ρ)
        (.pair (.code (convertFlat (flatAcc (captured body)) body)) (encodeEnv ws))

/-- The accessors implement every variable free in `t`. -/
def FlatAccRel (ρ : List (Source.Value Base)) (ρt : List Value) (acc : Nat → Tm)
    (t : Stlc.RawTm Base) : Prop :=
  ∀ i ∈ freeIndices 0 t, ∃ h : i < ρ.length, ∃ w, Eval ρt (acc i) w ∧ FlatValRel ρ[i] w

theorem FlatAccRel.mono {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm}
    {t t' : Stlc.RawTm Base} (h : FlatAccRel ρ ρt acc t)
    (hsub : ∀ i, i ∈ freeIndices 0 t' → i ∈ freeIndices 0 t) : FlatAccRel ρ ρt acc t' :=
  fun i hi => h i (hsub i hi)

theorem FlatAccRel.shift {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm}
    {t : Stlc.RawTm Base} (h : FlatAccRel ρ ρt acc t) (x : Value) :
    FlatAccRel ρ (x :: ρt) (fun i => (acc i).shift) t := by
  intro i hi
  obtain ⟨hlt, w, hw, hrel⟩ := h i hi
  exact ⟨hlt, w, hw.shift x, hrel⟩

/-- Packing the accessors of a list of implemented variables. -/
theorem eval_envFlat {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm} :
    ∀ (is : List Nat), (∀ i ∈ is, ∃ h : i < ρ.length, ∃ w, Eval ρt (acc i) w ∧
      FlatValRel ρ[i] w) →
    ∃ ws : List Value, Eval ρt (envFlat acc is) (encodeEnv ws) ∧ is.length = ws.length ∧
      ∃ hbound : ∀ k (h₁ : k < is.length), is[k] < ρ.length,
      ∀ k (h₁ : k < is.length) (h₂ : k < ws.length), FlatValRel (ρ[is[k]]'(hbound k h₁)) ws[k]
  | [], _ => ⟨[], .unit, rfl, fun k h₁ => absurd h₁ (Nat.not_lt_zero k),
      fun k h₁ => absurd h₁ (Nat.not_lt_zero k)⟩
  | i :: is, h => by
      obtain ⟨hi, w, hw, hrel⟩ := h i List.mem_cons_self
      obtain ⟨ws, hws, hlen, hbound, hrels⟩ :=
        eval_envFlat is fun j hj => h j (List.mem_cons_of_mem i hj)
      refine ⟨w :: ws, .pair hw hws, by simp [hlen], fun k h₁ => ?_, fun k h₁ h₂ => ?_⟩
      · cases k with
        | zero => exact hi
        | succ k => exact hbound k (Nat.lt_of_succ_lt_succ h₁)
      · cases k with
        | zero => exact hrel
        | succ k => exact hrels k (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

/-- The environment of a flat closure has one entry per captured variable. -/
theorem envFlat_length {ρt : List Value} {acc : Nat → Tm}
    {is : List Nat} {ws : List Value} (h : Eval ρt (envFlat acc is) (encodeEnv ws)) :
    ws.length = is.length := by
  induction is generalizing ws with
  | nil =>
      cases ws with
      | nil => rfl
      | cons w ws => cases h
  | cons i is ih =>
      cases ws with
      | nil => cases h
      | cons w ws =>
          cases h with
          | pair _ hb => simp [ih hb]

/-- Inside flat code, the flat accessors implement the free variables of the
body in the closure's environment extended with the argument. -/
theorem flatAccRel_flatAcc {v : Source.Value Base} {ρ : List (Source.Value Base)}
    {body : Stlc.RawTm Base} {w : Value} {ws : List Value} (hvw : FlatValRel v w)
    (hlen : (captured body).length = ws.length)
    (hbound : ∀ k (h₁ : k < (captured body).length), (captured body)[k] < ρ.length)
    (hrel : ∀ k (h₁ : k < (captured body).length) (h₂ : k < ws.length),
      FlatValRel (ρ[(captured body)[k]]'(hbound k h₁)) ws[k]) :
    FlatAccRel (v :: ρ) [.pair w (encodeEnv ws)] (flatAcc (captured body)) body := by
  intro i hi
  cases i with
  | zero => exact ⟨Nat.zero_lt_succ _, w, .fst (.var rfl), hvw⟩
  | succ j =>
      have hj : j ∈ captured body := mem_captured.mpr hi
      have hk : (captured body).idxOf j < (captured body).length :=
        List.idxOf_lt_length_of_mem hj
      have hkws : (captured body).idxOf j < ws.length := hlen ▸ hk
      have hget : (captured body)[(captured body).idxOf j] = j := List.getElem_idxOf hk
      have hlt : j < ρ.length := hget ▸ hbound _ hk
      refine ⟨Nat.succ_lt_succ hlt, ws[(captured body).idxOf j],
        eval_fst_snds (.snd (.var rfl)) hkws, ?_⟩
      have hrelk := hrel _ hk hkws
      have hρ : ρ[(captured body)[(captured body).idxOf j]]'(hbound _ hk) = ρ[j] := by
        simp only [hget]
      rw [hρ] at hrelk
      exact hrelk

/-- Correctness of flat closure conversion. -/
theorem convertFlat_correct {ρ : List (Source.Value Base)} {t : Stlc.RawTm Base}
    {v : Source.Value Base} (h : Source.Eval ρ t v) {ρt : List Value} {acc : Nat → Tm}
    (hacc : FlatAccRel ρ ρt acc t) :
    ∃ w, Eval ρt (convertFlat acc t) w ∧ FlatValRel v w := by
  induction h generalizing ρt acc with
  | @var ρ n v hn =>
      obtain ⟨hlt, w, hw, hrel⟩ := hacc n (by simp)
      have hv : ρ[n] = v := (List.getElem?_eq_some_iff.mp hn).2
      exact ⟨w, hw, hv ▸ hrel⟩
  | @lam ρ A body =>
      have hcap : ∀ i ∈ captured body, i ∈ freeIndices 0 (Stlc.RawTm.lam A body) := by
        intro i hi
        rw [freeIndices_lam, mem_freeIndices_succ]
        exact mem_captured.mp hi
      obtain ⟨ws, hws, hlen, hbound, hrel⟩ :=
        eval_envFlat (acc := acc) (captured body) fun i hi => hacc i (hcap i hi)
      exact ⟨_, .pair .code hws, .clo hlen hbound hrel⟩
  | @app ρ ρ' f a body v w' _ _ _ ihf iha ihb =>
      obtain ⟨wf, hwf, hrelf⟩ := ihf (hacc.mono fun i hi => by simp [hi])
      cases hrelf with
      | @clo _ _ ws hlen hbound hrel =>
          obtain ⟨wa, hwa, hrela⟩ := iha ((hacc.mono fun i hi => by simp [hi]).shift _)
          obtain ⟨wb, hwb, hrelb⟩ := ihb (flatAccRel_flatAcc hrela hlen hbound hrel)
          refine ⟨wb, .letIn hwf (.app (.fst (.var rfl)) (.pair hwa (.snd (.var rfl))) ?_), hrelb⟩
          simpa using hwb

/-- Correctness for closed programs. -/
theorem closureConvertFlat_correct {t : Stlc.RawTm Base} {v : Source.Value Base}
    (ht : t.Closed) (h : Source.Eval [] t v) :
    ∃ w, Eval [] (closureConvertFlat t) w ∧ FlatValRel v w :=
  convertFlat_correct h fun i hi => by rw [ht] at hi; exact absurd hi List.not_mem_nil

theorem scoped_envFlat {m : Nat} {acc : Nat → Tm} :
    ∀ is : List Nat, (∀ i ∈ is, Scoped m (acc i)) → Scoped m (envFlat acc is)
  | [], _ => .unit
  | i :: is, h => .pair (h i List.mem_cons_self)
      (scoped_envFlat is fun j hj => h j (List.mem_cons_of_mem i hj))

theorem scoped_flatAcc (fvs : List Nat) (i : Nat) : Scoped 1 (flatAcc fvs i) := by
  cases i with
  | zero => exact .fst (.var Nat.zero_lt_one)
  | succ j => exact .fst (scoped_snds (.snd (.var Nat.zero_lt_one)))

/-- Every code body produced by flat conversion is closed: the converted term
is scoped wherever the accessors of its free variables are. -/
theorem convertFlat_scoped {m : Nat} (t : Stlc.RawTm Base) {acc : Nat → Tm}
    (hacc : ∀ i ∈ freeIndices 0 t, Scoped m (acc i)) : Scoped m (convertFlat acc t) := by
  induction t generalizing m acc with
  | var i => exact hacc i (by simp)
  | lam A body ih =>
      refine .pair (.code (ih fun i _ => scoped_flatAcc _ i)) (scoped_envFlat _ fun i hi => ?_)
      apply hacc
      rw [freeIndices_lam, mem_freeIndices_succ]
      exact mem_captured.mp hi
  | app f a ihf iha =>
      exact .letIn (ihf fun i hi => hacc i (by simp [hi]))
        (.app (.fst (.var (Nat.zero_lt_succ _)))
          (.pair (iha fun i hi => (hacc i (by simp [hi])).shift)
            (.snd (.var (Nat.zero_lt_succ _)))))

/-- Flat conversion of a closed program is closed, with closed code. -/
theorem closureConvertFlat_scoped {t : Stlc.RawTm Base} (ht : t.Closed) :
    Scoped 0 (closureConvertFlat t) :=
  convertFlat_scoped t fun i hi => by rw [ht] at hi; exact absurd hi List.not_mem_nil

end Cslib.Languages.LambdaCalculus.ClosureConversion
