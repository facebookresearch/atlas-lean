/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Closure conversion and its correctness
-/
module

public import CSLibExt.Languages.LambdaCalculus.ClosureConversion.Source
public import CSLibExt.Languages.LambdaCalculus.ClosureConversion.Target
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.ElaborationStructural

/-!
# Closure conversion and its correctness

Closure conversion turns every lambda into an explicit closure: a pair of
closed code and a data structure holding the environment. This file uses the
whole-environment variant: a lambda in a scope of `n` variables captures all
`n` of them, as the nested pairs `(x₀, (x₁, … (xₙ₋₁, ())))`. Code receives the
pair `(argument, environment)` as its single parameter.

`convert acc n t` translates a source term `t` scoped in `n` variables, where
`acc i` is the target expression that fetches source variable `i`:

* `x_i ↦ acc i`;
* `λ. b ↦ (code ⟦b⟧', env)`, where `env` packs `acc 0, …, acc (n-1)` and `⟦b⟧'`
  converts `b` with the accessors `x₀ ↦ fst #0` and `x_{i+1} ↦ fst (sndⁱ (snd #0))`
  of the code's parameter `#0`;
* `f a ↦ let c = ⟦f⟧ in (fst c) (⟦a⟧, snd c)`.

Correctness (`convert_correct`): if the source term evaluates to `v` in the
environment semantics, the converted term evaluates to a target value related
to `v` (`ValRel`: a source closure is related to a pair of the converted code
of its body and an encoding of a pointwise-related environment). Every code
body produced is closed (`convert_scoped`), which is the point of closure
conversion: code can be hoisted to the top level.

The construction follows the textbook presentation of closure conversion
(Appel, *Compiling with Continuations*, Chapter 10) without the CPS stage and
with whole-environment rather than free-variable capture.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.ClosureConversion

universe u

variable {Base : Type u}

open Target Target.Tm

/-- `snds k e` applies the second projection `k` times. -/
def snds : Nat → Tm → Tm
  | 0, e => e
  | k + 1, e => .snd (snds k e)

/-- The target expression packing `acc 0, …, acc (n-1)` as nested pairs ending
in `unit`. -/
def envOf (acc : Nat → Tm) : Nat → Tm
  | 0 => .unit
  | n + 1 => .pair (acc 0) (envOf (fun i => acc (i + 1)) n)

/-- Accessors inside converted code: the parameter `#0` is the pair
`(argument, environment)`; variable `0` is the argument and variable `i + 1`
is entry `i` of the environment. -/
def codeAcc : Nat → Tm
  | 0 => .fst (.var 0)
  | i + 1 => .fst (snds i (.snd (.var 0)))

/-- Closure conversion of a source term in a scope of `n` variables, with
accessors `acc`. -/
def convert : (Nat → Tm) → Nat → Stlc.RawTm Base → Tm
  | acc, _, .var i => acc i
  | acc, n, .lam _ body => .pair (.code (convert codeAcc (n + 1) body)) (envOf acc n)
  | acc, n, .app f a =>
      .letIn (convert acc n f)
        (.app (.fst (.var 0)) (.pair (convert (fun i => (acc i).shift) n a) (.snd (.var 0))))

/-- Closure conversion of a closed source term. -/
def closureConvert (t : Stlc.RawTm Base) : Tm :=
  convert .var 0 t

/-- Encode a list of target values as nested pairs ending in `unit`. -/
def encodeEnv : List Value → Value
  | [] => .unit
  | w :: ws => .pair w (encodeEnv ws)

/-- The relation between source and target values: a closure of `body` over
`ρ` is related to the pair of the converted code of `body` and the encoding of
an environment pointwise related to `ρ`. -/
inductive ValRel : Source.Value Base → Value → Prop
  | clo {body : Stlc.RawTm Base} {ρ : List (Source.Value Base)} {ws : List Value}
      (hlen : ρ.length = ws.length)
      (hrel : ∀ i (h₁ : i < ρ.length) (h₂ : i < ws.length), ValRel ρ[i] ws[i]) :
      ValRel (.clo body ρ) (.pair (.code (convert codeAcc (ρ.length + 1) body)) (encodeEnv ws))

/-- Accessors `acc` implement the source environment `ρ` in the target
environment `ρt`: each `acc i` evaluates to a value related to `ρ[i]`. -/
def AccRel (ρ : List (Source.Value Base)) (ρt : List Value) (acc : Nat → Tm) : Prop :=
  ∀ i (h : i < ρ.length), ∃ w, Eval ρt (acc i) w ∧ ValRel ρ[i] w

theorem AccRel.shift {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm}
    (h : AccRel ρ ρt acc) (x : Value) : AccRel ρ (x :: ρt) (fun i => (acc i).shift) := by
  intro i hi
  obtain ⟨w, hw, hrel⟩ := h i hi
  exact ⟨w, hw.shift x, hrel⟩

/-- Packing the accessors builds the encoding of a pointwise-related list of
values. -/
theorem AccRel.envOf {ρ : List (Source.Value Base)} {ρt : List Value} {acc : Nat → Tm}
    (h : AccRel ρ ρt acc) :
    ∃ ws : List Value, Eval ρt (ClosureConversion.envOf acc ρ.length) (encodeEnv ws) ∧
      ρ.length = ws.length ∧
      ∀ i (h₁ : i < ρ.length) (h₂ : i < ws.length), ValRel ρ[i] ws[i] := by
  induction ρ generalizing acc with
  | nil => exact ⟨[], .unit, rfl, fun i h₁ => absurd h₁ (Nat.not_lt_zero i)⟩
  | cons v ρ ih =>
      obtain ⟨w, hw, hvw⟩ := h 0 (Nat.zero_lt_succ _)
      have htail : AccRel ρ ρt (fun i => acc (i + 1)) := fun i hi =>
        h (i + 1) (Nat.succ_lt_succ hi)
      obtain ⟨ws, hws, hlen, hrel⟩ := ih htail
      refine ⟨w :: ws, .pair hw hws, by simp [hlen], ?_⟩
      intro i h₁ h₂
      cases i with
      | zero => exact hvw
      | succ i => exact hrel i (Nat.lt_of_succ_lt_succ h₁) (Nat.lt_of_succ_lt_succ h₂)

/-- Projecting through an encoded environment. -/
theorem eval_snds {ρt : List Value} {e : Tm} {ws : List Value}
    (he : Eval ρt e (encodeEnv ws)) {k : Nat} (hk : k ≤ ws.length) :
    Eval ρt (snds k e) (encodeEnv (ws.drop k)) := by
  induction k with
  | zero => simpa [snds] using he
  | succ k ih =>
      have hk' : k < ws.length := hk
      have h := ih (Nat.le_of_lt hk')
      rw [List.drop_eq_getElem_cons hk'] at h
      exact .snd h

theorem eval_fst_snds {ρt : List Value} {e : Tm} {ws : List Value}
    (he : Eval ρt e (encodeEnv ws)) {i : Nat} (hi : i < ws.length) :
    Eval ρt (.fst (snds i e)) ws[i] := by
  have h := eval_snds he (Nat.le_of_lt hi)
  rw [List.drop_eq_getElem_cons hi] at h
  exact .fst h

/-- Inside converted code, the code accessors implement the closure's
environment extended with the argument. -/
theorem accRel_codeAcc {v : Source.Value Base} {ρ : List (Source.Value Base)} {w : Value}
    {ws : List Value} (hvw : ValRel v w) (hlen : ρ.length = ws.length)
    (hrel : ∀ i (h₁ : i < ρ.length) (h₂ : i < ws.length), ValRel ρ[i] ws[i]) :
    AccRel (v :: ρ) [.pair w (encodeEnv ws)] codeAcc := by
  intro i hi
  cases i with
  | zero => exact ⟨w, .fst (.var rfl), hvw⟩
  | succ i =>
      have hiρ : i < ρ.length := Nat.lt_of_succ_lt_succ hi
      have hiws : i < ws.length := hlen ▸ hiρ
      exact ⟨ws[i], eval_fst_snds (.snd (.var rfl)) hiws, hrel i hiρ hiws⟩

/-- Correctness of closure conversion: if `t` evaluates to `v` in the source
environment `ρ`, and the accessors implement `ρ` in the target environment
`ρt`, then the converted term evaluates to a target value related to `v`. -/
theorem convert_correct {ρ : List (Source.Value Base)} {t : Stlc.RawTm Base}
    {v : Source.Value Base} (h : Source.Eval ρ t v) {ρt : List Value} {acc : Nat → Tm}
    (hacc : AccRel ρ ρt acc) :
    ∃ w, Eval ρt (convert acc ρ.length t) w ∧ ValRel v w := by
  induction h generalizing ρt acc with
  | @var ρ n v hn =>
      have hlt : n < ρ.length := (List.getElem?_eq_some_iff.mp hn).1
      obtain ⟨w, hw, hrel⟩ := hacc n hlt
      have hv : ρ[n] = v := (List.getElem?_eq_some_iff.mp hn).2
      exact ⟨w, hw, hv ▸ hrel⟩
  | @lam ρ A body =>
      obtain ⟨ws, hws, hlen, hrel⟩ := hacc.envOf
      exact ⟨_, .pair .code hws, .clo hlen hrel⟩
  | @app ρ ρ' f a body v w' _ _ _ ihf iha ihb =>
      obtain ⟨wf, hwf, hrelf⟩ := ihf hacc
      cases hrelf with
      | @clo _ _ ws hlen hrel =>
          obtain ⟨wa, hwa, hrela⟩ := iha (hacc.shift _)
          obtain ⟨wb, hwb, hrelb⟩ := ihb (accRel_codeAcc hrela hlen hrel)
          refine ⟨wb, .letIn hwf (.app (.fst (.var rfl)) (.pair hwa (.snd (.var rfl))) ?_), hrelb⟩
          simpa using hwb

/-- Correctness for closed programs. -/
theorem closureConvert_correct {t : Stlc.RawTm Base} {v : Source.Value Base}
    (h : Source.Eval [] t v) : ∃ w, Eval [] (closureConvert t) w ∧ ValRel v w :=
  convert_correct h (fun i hi => absurd hi (Nat.not_lt_zero i))

theorem scoped_snds {m k : Nat} {e : Tm} (h : Scoped m e) : Scoped m (snds k e) := by
  induction k with
  | zero => exact h
  | succ k ih => exact .snd ih

theorem scoped_envOf {m : Nat} {acc : Nat → Tm} :
    ∀ {n : Nat}, (∀ i, i < n → Scoped m (acc i)) → Scoped m (ClosureConversion.envOf acc n)
  | 0, _ => .unit
  | n + 1, h => .pair (h 0 (Nat.zero_lt_succ n))
      (scoped_envOf fun i hi => h (i + 1) (Nat.succ_lt_succ hi))

theorem scoped_codeAcc (i : Nat) : Scoped 1 (codeAcc i) := by
  cases i with
  | zero => exact .fst (.var Nat.zero_lt_one)
  | succ i => exact .fst (scoped_snds (.snd (.var Nat.zero_lt_one)))

/-- The converted term is scoped in the target scope of its accessors, and every
code body it contains is closed. The hypothesis says `t` is scoped in `n`
variables (`Stlc.RawTm.freeIndices n t = []`). -/
theorem convert_scoped {m : Nat} (t : Stlc.RawTm Base) :
    ∀ {n : Nat}, Stlc.RawTm.freeIndices n t = [] →
      ∀ {acc : Nat → Tm}, (∀ i, i < n → Scoped m (acc i)) → Scoped m (convert acc n t) := by
  induction t generalizing m with
  | var i =>
      intro n ht acc hacc
      have hi : i < n := by
        by_contra hni
        simp [Stlc.RawTm.freeIndices, Nat.le_of_not_lt hni] at ht
      exact hacc i hi
  | app f a ihf iha =>
      intro n ht acc hacc
      rw [Stlc.RawTm.freeIndices_app, List.append_eq_nil_iff] at ht
      exact .letIn (ihf ht.1 hacc) (.app (.fst (.var (Nat.zero_lt_succ m)))
        (.pair (iha ht.2 fun i hi => (hacc i hi).shift) (.snd (.var (Nat.zero_lt_succ m)))))
  | lam A body ih =>
      intro n ht acc hacc
      rw [Stlc.RawTm.freeIndices_lam] at ht
      exact .pair (.code (ih ht fun i _ => scoped_codeAcc i)) (scoped_envOf hacc)

/-- Closure conversion of a closed source term (`Stlc.RawTm.Closed`) is closed,
with closed code. -/
theorem closureConvert_scoped {t : Stlc.RawTm Base} (ht : t.Closed) :
    Scoped 0 (closureConvert t) :=
  convert_scoped t ht fun i hi => absurd hi (Nat.not_lt_zero i)

end Cslib.Languages.LambdaCalculus.ClosureConversion
