/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FirstOrderSubsumptionFixedTargetsDefs

namespace MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumptionFixedTargets

open FirstOrder FirstOrder.Language
open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras (lang tokens)
open MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumption
  (FirstOrderSubsumptionInstance FirstOrderSubsumptionFeasible)

private theorem accepts_encoding (n : ℕ) (i : FirstOrderSubsumptionInstance) :
    firstOrderSubsumptionFixedTargetsDec n (bitEncode i) = true ↔
      WellFormed n i ∧ FirstOrderSubsumptionFeasible i := by
  simp [firstOrderSubsumptionFixedTargetsDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding, for every number of targets. -/
example (n : ℕ) : firstOrderSubsumptionFixedTargetsDec n [true] = false := by
  have h : bitDecode (α := FirstOrderSubsumptionInstance) [true] = none := rfl
  simp [firstOrderSubsumptionFixedTargetsDec, h]

/-- The symbols: a constant `c` (symbol `0`) and a unary `f` (symbol `1`). -/
private abbrev ar : List ℕ := [0, 1]

private def cSym : (lang ar).Functions 0 := ⟨⟨0, by decide⟩, rfl⟩
private def fSym : (lang ar).Functions 1 := ⟨⟨1, by decide⟩, rfl⟩

/-- The constant `c`. -/
private def cT {α : Type} : (lang ar).Term α := .func cSym Fin.elim0
/-- The expression `f(x)` over the variable `x`. -/
private def fx : (lang ar).Term (Fin 1) := .func fSym fun _ => .var 0
/-- The expression `f(c)`. -/
private def fc : (lang ar).Term Empty := .func fSym fun _ => cT

/-- The pattern `f(x)` with the targets `fs`, given by their token lists. -/
private abbrev withTargets (fs : List (List (ℕ × ℕ))) : FirstOrderSubsumptionInstance :=
  (ar, 1, [ [(1, 1), (0, 0)] ], fs)

/-- Substituting `c` for `x` maps `f(x)` to `f(c)`, and the targets `f(c)` and `c` are two
distinct expressions. -/
example : firstOrderSubsumptionFixedTargetsDec 2
    (bitEncode (withTargets [ [(1, 1), (1, 0)], [(1, 0)] ])) = true :=
  (accepts_encoding _ _).2 ⟨⟨⟨⟨[fx], rfl⟩, ⟨[fc, cT], rfl⟩⟩, rfl, by decide⟩,
    [fx], rfl, [fc, cT], rfl, fun _ => cT, fun e he => by
      obtain rfl := List.mem_singleton.1 he
      exact List.mem_cons_self⟩

/-- The same instance has two targets, not one. -/
example : firstOrderSubsumptionFixedTargetsDec 1
    (bitEncode (withTargets [ [(1, 1), (1, 0)], [(1, 0)] ])) = false := by
  have h : ¬ WellFormed 1 (withTargets [ [(1, 1), (1, 0)], [(1, 0)] ]) := fun h =>
    absurd h.2.1 (by decide)
  simp [firstOrderSubsumptionFixedTargetsDec, bitDecode_bitEncode, h]

/-- Listing the target `f(c)` twice still gives a subsumable instance of FIRST ORDER
SUBSUMPTION. -/
example : FirstOrderSubsumptionFeasible (withTargets [ [(1, 1), (1, 0)], [(1, 1), (1, 0)] ]) :=
  ⟨[fx], rfl, [fc, fc], rfl, fun _ => cT, fun e he => by
    obtain rfl := List.mem_singleton.1 he
    exact List.mem_cons_self⟩

/-- But its two target entries are not two distinct expressions. -/
example : firstOrderSubsumptionFixedTargetsDec 2
    (bitEncode (withTargets [ [(1, 1), (1, 0)], [(1, 1), (1, 0)] ])) = false := by
  have h : ¬ WellFormed 2 (withTargets [ [(1, 1), (1, 0)], [(1, 1), (1, 0)] ]) := fun h => by
    simpa using h.2.2
  simp [firstOrderSubsumptionFixedTargetsDec, bitDecode_bitEncode, h]

end MetaMathlibExt.Complexity.NPComplete.FirstOrderSubsumptionFixedTargets
