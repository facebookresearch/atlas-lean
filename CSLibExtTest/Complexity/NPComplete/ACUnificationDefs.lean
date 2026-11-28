/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ACUnificationDefs

namespace MetaMathlibExt.Complexity.NPComplete.ACUnification

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ACUnificationInstance) :
    acUnificationDec (bitEncode i) = true ↔
      WellFormed i ∧ ACUnificationFeasible i := by
  simp [acUnificationDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : acUnificationDec [true] = false := by
  have h : bitDecode (α := ACUnificationInstance) [true] = none := rfl
  simp [acUnificationDec, h]

open FirstOrder FirstOrder.Language
open UnificationForFinitelyPresentedAlgebras (lang tokens)

/-- Symbols: `f` (index `0`, binary), `a` and `b` (indices `1` and `2`, constants). -/
private abbrev ar : List ℕ := [2, 0, 0]

private def f : (lang ar).Functions 2 := ⟨0, rfl⟩
private def a {β : Type} : (lang ar).Term β :=
  Term.func (⟨1, rfl⟩ : (lang ar).Functions 0) Fin.elim0
private def b {β : Type} : (lang ar).Term β :=
  Term.func (⟨2, rfl⟩ : (lang ar).Functions 0) Fin.elim0

/-- `f(x, a)`, with `x` the variable `0`. -/
private def s : (lang ar).Term (Fin 2) := f.apply₂ (Term.var 0) a

/-- `f(y, b)`, with `y` the variable `1`. -/
private def t : (lang ar).Term (Fin 2) := f.apply₂ (Term.var 1) b

private theorem tokens_s : tokens Fin.val s = [(1, 0), (0, 0), (1, 1)] := rfl
private theorem tokens_t : tokens Fin.val t = [(1, 0), (0, 1), (1, 2)] := rfl

/-- The substitution `x ↦ b`, `y ↦ a`. -/
private def σ : Fin 2 → (lang ar).Term ℕ := fun v => if v = 0 then b else a

private theorem subst_const {β γ : Type} (c : (lang ar).Functions 0) (τ : β → (lang ar).Term γ) :
    (Term.func c Fin.elim0).subst τ = Term.func c Fin.elim0 := by
  simp only [Term.subst]
  congr 1
  funext i
  exact i.elim0

private theorem subst_s : s.subst σ = f.apply₂ b a := by
  unfold s Functions.apply₂
  simp only [Term.subst]
  congr 1
  funext k
  rcases k with ⟨_ | _ | k, hk⟩
  · rfl
  · exact subst_const _ _
  · exact absurd hk (by omega)

private theorem subst_t : t.subst σ = f.apply₂ a b := by
  unfold t Functions.apply₂
  simp only [Term.subst]
  congr 1
  funext k
  rcases k with ⟨_ | _ | k, hk⟩
  · rfl
  · exact subst_const _ _
  · exact absurd hk (by omega)

/-- With `f` commutative, `x ↦ b`, `y ↦ a` unifies `f(x, a)` and `f(y, b)`; syntactically they
do not unify, since `a ≠ b`. -/
example : acUnificationDec (bitEncode
    ((ar, [0], 2, [(1, 0), (0, 0), (1, 1)], [(1, 0), (0, 1), (1, 2)]) : ACUnificationInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨⟨by decide, ⟨s, tokens_s⟩, ⟨t, tokens_t⟩⟩,
    s, t, tokens_s, tokens_t, σ, ?_⟩
  intro R _ _ _ hC
  rw [subst_s, subst_t]
  exact hC f (by decide) b a

private theorem head_tokens_func {β : Type} (g : β → ℕ) {l : ℕ} (c : (lang ar).Functions l)
    (ts : Fin l → (lang ar).Term β) :
    (tokens g (Term.func c ts)).head? = some (1, c.1.val) := by
  simp [tokens, Term.listEncode]

/-- `a` and `f(y, b)` do not unify: substitution keeps the head symbols `a` and `f`, and equality
modulo associativity and commutativity preserves the head symbol (witnessed by the relation
"same first token"). -/
example : acUnificationDec (bitEncode
    ((ar, [0], 1, [(1, 1)], [(1, 0), (0, 0), (1, 2)]) : ACUnificationInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, s', t', hs', ht', τ, hR⟩
  have key := hR (fun u v => (tokens id u).head? = (tokens id v).head?)
    ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    (fun c _ _ _ => by rw [head_tokens_func, head_tokens_func])
    (fun c _ _ _ _ => by simp only [Functions.apply₂]; rw [head_tokens_func, head_tokens_func])
    (fun c _ _ _ => by simp only [Functions.apply₂]; rw [head_tokens_func, head_tokens_func])
  cases s' with
  | var x => simp [tokens, Term.listEncode] at hs'
  | func c ts =>
    cases t' with
    | var y => simp [tokens, Term.listEncode] at ht'
    | func d us =>
      have hc := congrArg List.head? hs'
      have hd := congrArg List.head? ht'
      rw [head_tokens_func] at hc hd
      simp only [Term.subst] at key
      rw [head_tokens_func, head_tokens_func] at key
      simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hc hd key
      omega

/-- Malformed: declaring the constant `a` (index `1`) associative-commutative; AC symbols must be
binary. -/
example : acUnificationDec (bitEncode
    ((ar, [1], 2, [(1, 0), (0, 0), (1, 1)], [(1, 0), (0, 1), (1, 2)]) : ACUnificationInstance)) =
    false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨⟨hac, -⟩, -⟩
  exact absurd (hac 1 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.ACUnification
