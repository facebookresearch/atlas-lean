/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebrasDefs

namespace MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open FirstOrder FirstOrder.Language

private theorem accepts_encoding (i : UnificationForFinitelyPresentedAlgebrasInstance) :
    unificationForFinitelyPresentedAlgebrasDec (bitEncode i) = true ↔
      WellFormed i ∧ UnificationForFinitelyPresentedAlgebrasFeasible i := by
  simp [unificationForFinitelyPresentedAlgebrasDec, bitDecode_bitEncode]

/-- One generator `a` (symbol `0`, arity `0`) and one unary operator `f` (symbol `1`). -/
private abbrev ar : List ℕ := [0, 1]

private abbrev symA : (lang ar).Functions 0 := ⟨⟨0, by decide⟩, rfl⟩

private abbrev symF : (lang ar).Functions 1 := ⟨⟨1, by decide⟩, rfl⟩

/-- The generator `a` as a term. -/
private abbrev tmA {α : Type} : (lang ar).Term α := Term.func symA Fin.elim0

/-- `f(t)`. -/
private abbrev tmF {α : Type} (t : (lang ar).Term α) : (lang ar).Term α :=
  Term.func symF fun _ => t

/-- The symbol at the root of a term, shifted by one (`0` for a variable). -/
private def head {α : Type} : (lang ar).Term α → ℕ
  | .var _ => 0
  | .func f _ => f.1.val + 1

/-- Unify `x = f(v₀)` with `y = a` under the relations `Γ` (one variable, generator `a`,
unary `f`). -/
private abbrev problem (Γ : List (List (ℕ × ℕ) × List (ℕ × ℕ))) :
    UnificationForFinitelyPresentedAlgebrasInstance :=
  (1, [1], Γ, 1, [(1, 1), (0, 0)], [(1, 0)])

/-- A lone continuation bit is a truncated instance encoding. -/
example : unificationForFinitelyPresentedAlgebrasDec [true] = false := by
  have h : bitDecode (α := UnificationForFinitelyPresentedAlgebrasInstance) [true] = none := rfl
  simp [unificationForFinitelyPresentedAlgebrasDec, h]

/-- Under the relation `f(a) = a`, the assignment `v₀ ↦ a` makes `f(v₀)` and `a` congruent. -/
example :
    unificationForFinitelyPresentedAlgebrasDec
      (bitEncode (problem [([(1, 1), (1, 0)], [(1, 0)])])) = true := by
  apply (accepts_encoding _).2
  have hΓ : DefiningRelations (problem [([(1, 1), (1, 0)], [(1, 0)])])
      [(tmF tmA, tmA)] := rfl
  have hx : tokens Fin.val (tmF (Term.var (0 : Fin 1)) : (lang ar).Term (Fin 1)) =
      [(1, 1), (0, 0)] := rfl
  have hy : tokens Fin.val (tmA : (lang ar).Term (Fin 1)) = [(1, 0)] := rfl
  refine ⟨⟨⟨_, hΓ⟩, ⟨_, hx⟩, ⟨_, hy⟩⟩, _, hΓ, _, _, hx, hy, fun _ => tmA, ?_⟩
  have e : ((tmA : (lang ar).Term (Fin 1)).subst fun _ => (tmA : (lang ar).Term Empty)) =
      tmA := by
    simp only [Term.subst]
    congr
    funext i
    exact i.elim0
  intro R _ hR _
  exact (congrArg (R (tmF tmA)) e).mpr (hR _ List.mem_cons_self)

/-- Without relations congruence is syntactic equality, and `f(I(v₀))` never equals the
generator `a`, whatever closed term `I(v₀)` is. -/
example : unificationForFinitelyPresentedAlgebrasDec (bitEncode (problem [])) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, Γ, hΓ, x, y, hx, hy, I, hcong⟩ := (accepts_encoding _).1 hacc
  have heq := hcong (· = ·) ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩
    (fun p hp => by rw [List.map_eq_nil_iff.1 hΓ] at hp; simp at hp)
    (fun f u v h => by rw [funext h])
  have hhx : head (x.subst I) = 2 := by
    cases x with
    | var v => simp [tokens, Term.listEncode] at hx
    | func f ts =>
      simp only [tokens, Term.listEncode, List.map_cons, List.cons.injEq] at hx
      simp only [Term.subst, head]
      simp at hx
      omega
  have hhy : head (y.subst I) = 1 := by
    cases y with
    | var v => simp [tokens, Term.listEncode] at hy
    | func f ts =>
      simp only [tokens, Term.listEncode, List.map_cons, List.cons.injEq] at hy
      simp only [Term.subst, head]
      simp at hy
      omega
  rw [heq] at hhx
  omega

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed (problem []) :=
  ⟨⟨[], rfl⟩, ⟨tmF (Term.var 0), rfl⟩, ⟨tmA, rfl⟩⟩

end MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras
