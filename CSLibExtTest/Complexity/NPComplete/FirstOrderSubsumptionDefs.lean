/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FirstOrderSubsumptionDefs

namespace MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption

open FirstOrder FirstOrder.Language
open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras (lang tokens)

private theorem accepts_encoding (i : FirstOrderSubsumptionInstance) :
    firstOrderSubsumptionDec (bitEncode i) = true ↔
      WellFormed i ∧ FirstOrderSubsumptionFeasible i := by
  simp [firstOrderSubsumptionDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : firstOrderSubsumptionDec [true] = false := by
  have h : bitDecode (α := FirstOrderSubsumptionInstance) [true] = none := rfl
  simp [firstOrderSubsumptionDec, h]

/-- The symbols: a constant `c` (symbol `0`) and a unary `f` (symbol `1`). -/
private abbrev ar : List ℕ := [0, 1]

/-- The pattern `f(x)` over one variable, with the targets `fs`, given by their token lists. -/
private abbrev withTargets (fs : List (List (ℕ × ℕ))) : FirstOrderSubsumptionInstance :=
  (ar, 1, [ [(1, 1), (0, 0)] ], fs)

private def cSym : (lang ar).Functions 0 := ⟨⟨0, by decide⟩, rfl⟩
private def fSym : (lang ar).Functions 1 := ⟨⟨1, by decide⟩, rfl⟩

/-- The constant `c`. -/
private def cT {α : Type} : (lang ar).Term α := .func cSym Fin.elim0
/-- The expression `f(x)` over the variable `x`. -/
private def fx : (lang ar).Term (Fin 1) := .func fSym fun _ => .var 0
/-- The expression `f(c)`. -/
private def fc : (lang ar).Term Empty := .func fSym fun _ => cT

/-- The token lists of the three expressions. -/
example : tokens Fin.val fx = [(1, 1), (0, 0)] ∧ tokens Empty.elim fc = [(1, 1), (1, 0)] ∧
    tokens Empty.elim (cT (α := Empty)) = [(1, 0)] := ⟨rfl, rfl, rfl⟩

/-- Substituting `c` for `x` maps the pattern `f(x)` to the target `f(c)`. -/
example : firstOrderSubsumptionDec
    (bitEncode (withTargets [ [(1, 1), (1, 0)] ])) = true :=
  (accepts_encoding _).2 ⟨⟨⟨[fx], rfl⟩, ⟨[fc], rfl⟩⟩, [fx], rfl, [fc], rfl, fun _ => cT,
    fun e he => by
      obtain rfl := List.mem_singleton.1 he
      exact List.mem_singleton.2 rfl⟩

/-- The pattern `f(x)` and the target `c` are both well formed, but every substitution instance
of `f(x)` starts with `f`. -/
example : firstOrderSubsumptionDec
    (bitEncode (withTargets [ [(1, 0)] ])) = false := by
  have wf : WellFormed (withTargets [ [(1, 0)] ]) :=
    ⟨⟨[fx], rfl⟩, ⟨[cT], rfl⟩⟩
  have h : ¬ FirstOrderSubsumptionFeasible (withTargets [ [(1, 0)] ]) := by
    rintro ⟨es, hes, fs, hfs, s, hsub⟩
    rcases es with _ | ⟨e, _ | ⟨e', es⟩⟩ <;> simp [Patterns] at hes
    rcases fs with _ | ⟨g, _ | ⟨g', fs⟩⟩ <;> simp [Targets] at hfs
    have hg := List.mem_singleton.1 (hsub e (by simp))
    cases e with
    | var v => simp [tokens, Term.listEncode] at hes
    | func h ts =>
      subst hg
      have h₁ := congrArg List.head? hes
      have h₂ := congrArg List.head? hfs
      simp [tokens, Term.listEncode, Term.subst] at h₁ h₂
      omega
  simp [firstOrderSubsumptionDec, bitDecode_bitEncode, wf, h]

end MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption
