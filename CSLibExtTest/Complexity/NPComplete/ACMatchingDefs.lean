/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ACMatchingDefs

namespace MetaMathlibExt.Complexity.NPComplete.ACMatching

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ACMatchingInstance) :
    acMatchingDec (bitEncode i) = true ↔
      WellFormed i ∧ ACMatchingFeasible i := by
  simp [acMatchingDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : acMatchingDec [true] = false := by
  have h : bitDecode (α := ACMatchingInstance) [true] = none := rfl
  simp [acMatchingDec, h]

open FirstOrder FirstOrder.Language
open UnificationForFinitelyPresentedAlgebras (lang tokens)

/-- Symbols: `f` (index `0`, binary), `a` and `b` (indices `1` and `2`, constants). -/
private abbrev ar : List ℕ := [2, 0, 0]

private def f : (lang ar).Functions 2 := ⟨0, rfl⟩
private def a {β : Type} : (lang ar).Term β :=
  Term.func (⟨1, rfl⟩ : (lang ar).Functions 0) Fin.elim0
private def b {β : Type} : (lang ar).Term β :=
  Term.func (⟨2, rfl⟩ : (lang ar).Functions 0) Fin.elim0

/-- The pattern `f(x, a)`. -/
private def s : (lang ar).Term (Fin 1) := f.apply₂ (Term.var 0) a

/-- The subject `f(a, b)`. -/
private def t : (lang ar).Term Empty := f.apply₂ a b

private theorem tokens_s : tokens Fin.val s = [(1, 0), (0, 0), (1, 1)] := rfl
private theorem tokens_t : tokens Empty.elim t = [(1, 0), (1, 1), (1, 2)] := rfl

/-- With `f` commutative, `x ↦ b` matches `f(x, a)` to `f(a, b)`; syntactically the pattern
does not match, since `a ≠ b`. -/
example : acMatchingDec (bitEncode
    ((ar, [0], 1, [(1, 0), (0, 0), (1, 1)], [(1, 0), (1, 1), (1, 2)]) : ACMatchingInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨⟨by decide, ⟨s, tokens_s⟩, ⟨t, tokens_t⟩⟩,
    s, tokens_s, t, tokens_t, fun _ => (b : (lang ar).Term Empty), ?_⟩
  intro R _ _ _ hC
  have e : s.subst (fun _ => (b : (lang ar).Term Empty)) = f.apply₂ b a := by
    unfold s Functions.apply₂
    simp only [Term.subst]
    congr 1
    funext k
    rcases k with ⟨_ | _ | k, hk⟩
    · rfl
    · show (a : (lang ar).Term (Fin 1)).subst _ = a
      unfold a
      simp only [Term.subst]
      congr 1
      funext i
      exact i.elim0
    · exact absurd hk (by omega)
  rw [e]
  exact hC f (by decide) b a

private theorem head_tokens_func {β : Type} (g : β → ℕ) {l : ℕ} (c : (lang ar).Functions l)
    (ts : Fin l → (lang ar).Term β) :
    (tokens g (Term.func c ts)).head? = some (1, c.1.val) := by
  simp [tokens, Term.listEncode]

/-- The pattern `a` cannot match the subject `f(a, b)`: every substitution leaves the pattern
headed by `a`, while equality modulo associativity and commutativity preserves the head symbol
(here witnessed by the relation "same first token"). -/
example : acMatchingDec (bitEncode
    ((ar, [0], 1, [(1, 1)], [(1, 0), (1, 1), (1, 2)]) : ACMatchingInstance)) = false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨-, s', hs', t', ht', σ, hR⟩
  have key := hR (fun u v => (tokens Empty.elim u).head? = (tokens Empty.elim v).head?)
    ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    (fun c _ _ _ => by rw [head_tokens_func, head_tokens_func])
    (fun c _ _ _ _ => by simp only [Functions.apply₂]; rw [head_tokens_func, head_tokens_func])
    (fun c _ _ _ => by simp only [Functions.apply₂]; rw [head_tokens_func, head_tokens_func])
  simp only at ht'
  rw [ht'] at key
  cases s' with
  | var x => simp [tokens, Term.listEncode] at hs'
  | func c ts =>
    have hc := congrArg List.head? hs'
    rw [head_tokens_func] at hc
    simp only [Term.subst] at key
    rw [head_tokens_func] at key
    simp only [List.head?_cons, Option.some.injEq, Prod.mk.injEq] at hc key
    omega

/-- Malformed: declaring the constant `a` (index `1`) associative-commutative is not well formed: AC
symbols must be binary. -/
example : acMatchingDec (bitEncode
    ((ar, [1], 1, [(1, 0), (0, 0), (1, 1)], [(1, 0), (1, 1), (1, 2)]) : ACMatchingInstance)) =
    false := by
  rw [Bool.eq_false_iff, Ne, accepts_encoding]
  rintro ⟨⟨hac, -⟩, -⟩
  exact absurd (hac 1 (by simp)) (by decide)

end MetaMathlibExt.Complexity.NPComplete.ACMatching
