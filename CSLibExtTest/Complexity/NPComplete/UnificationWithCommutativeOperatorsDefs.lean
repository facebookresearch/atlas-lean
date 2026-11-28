/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsDefs

namespace MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperators

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open Cslib.Unification

private theorem accepts_encoding (i : UnificationWithCommutativeOperatorsInstance) :
    unificationWithCommutativeOperatorsDec (bitEncode i) = true ↔
      WellFormed i ∧ UnificationWithCommutativeOperatorsFeasible i := by
  simp [unificationWithCommutativeOperatorsDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : unificationWithCommutativeOperatorsDec [true] = false := by
  have h : bitDecode (α := UnificationWithCommutativeOperatorsInstance) [true] = none := rfl
  simp [unificationWithCommutativeOperatorsDec, h]

/-- Every expression has at least one token. -/
private theorem tokens_length_pos {k : ℕ} (t : Term (Fin k)) : 0 < (tokens t).length := by
  cases t <;> simp [tokens]

/-- A three-token expression is a sum of two one-token expressions. -/
private theorem eq_node_of_tokens {k : ℕ} (t : Term (Fin k)) (y z : ℕ × ℕ)
    (h : tokens t = [(2, 0), y, z]) :
    ∃ l r, t = .node l r ∧ tokens l = [y] ∧ tokens r = [z] := by
  cases t with
  | var v => simp [tokens] at h
  | const c => simp [tokens] at h
  | node l r =>
    simp only [tokens, List.cons.injEq, true_and] at h
    have hl := tokens_length_pos l
    have hr := tokens_length_pos r
    have hlen := congrArg List.length h
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 (show (tokens l).length = 1 by omega)
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 (show (tokens r).length = 1 by omega)
    rw [ha, hb] at h
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at h
    exact ⟨l, r, rfl, h.1 ▸ ha, h.2 ▸ hb⟩

/-- A one-token expression with a constant token is that constant. -/
private theorem eq_const_of_tokens {k : ℕ} (t : Term (Fin k)) (c : ℕ)
    (h : tokens t = [(1, c)]) : ∃ c' : Fin k, c'.val = c ∧ t = .const c' := by
  cases t with
  | var v => simp [tokens] at h
  | const c' => simp [tokens] at h; exact ⟨c', h, rfl⟩
  | node l r => simp [tokens] at h

/-- Commutative equivalence between constants is equality. -/
private theorem const_of_commEquiv {k : ℕ} {c d : Fin k}
    (h : CommEquiv (Term.const c) (Term.const d)) : c = d := by
  cases h
  rfl

/-- `x + a ≡ a + b` holds modulo commutativity with `x := b`; without commutativity it would
need `a = b`. -/
example :
    unificationWithCommutativeOperatorsDec
      (bitEncode ((1, 2, [([(2, 0), (0, 0), (1, 0)], [(2, 0), (1, 0), (1, 1)])]) :
        UnificationWithCommutativeOperatorsInstance)) = true := by
  apply (accepts_encoding _).2
  have hes : Pairs (1, 2, [([(2, 0), (0, 0), (1, 0)], [(2, 0), (1, 0), (1, 1)])])
      [(.node (.var 0) (.const 0), .node (.const 0) (.const 1))] := rfl
  refine ⟨⟨⟨_, hes⟩, by decide⟩, _, hes, fun _ => .const 1, fun _ _ => rfl, ?_⟩
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp
  exact .swap (.refl _) (.refl _)

/-- `x + a ≡ b + b` has no solution: either operand order would need `a = b`. -/
example :
    unificationWithCommutativeOperatorsDec
      (bitEncode ((1, 2, [([(2, 0), (0, 0), (1, 0)], [(2, 0), (1, 1), (1, 1)])]) :
        UnificationWithCommutativeOperatorsInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨-, es, hes, I, -, hI⟩
  obtain ⟨⟨e, f⟩, rfl⟩ := List.length_eq_one_iff.1 (by simpa using congrArg List.length hes)
  simp only [Pairs, List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq,
    and_true] at hes
  obtain ⟨l, r, rfl, -, hr⟩ := eq_node_of_tokens e _ _ hes.1
  obtain ⟨f₁, f₂, rfl, hf₁, hf₂⟩ := eq_node_of_tokens f _ _ hes.2
  obtain ⟨a, ha, rfl⟩ := eq_const_of_tokens r 0 hr
  obtain ⟨b₁, hb₁, rfl⟩ := eq_const_of_tokens f₁ 1 hf₁
  obtain ⟨b₂, hb₂, rfl⟩ := eq_const_of_tokens f₂ 1 hf₂
  have h := hI _ (List.mem_singleton_self _)
  simp only [Term.subst] at h
  generalize Term.subst I l = x at h
  cases h with
  | refl => omega
  | node _ h => exact absurd (congrArg Fin.val (const_of_commEquiv h)) (by omega)
  | swap _ h => exact absurd (congrArg Fin.val (const_of_commEquiv h)) (by omega)

/-- The rejected instance is well formed, so the rejection comes from unsolvability. -/
example :
    WellFormed ((1, 2, [([(2, 0), (0, 0), (1, 0)], [(2, 0), (1, 1), (1, 1)])]) :
      UnificationWithCommutativeOperatorsInstance) :=
  ⟨⟨[(.node (.var 0) (.const 0), .node (.const 1) (.const 1))], rfl⟩, by decide⟩

end MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperators
