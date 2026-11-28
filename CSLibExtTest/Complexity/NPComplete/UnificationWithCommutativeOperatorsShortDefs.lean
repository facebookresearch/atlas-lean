/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShortDefs

namespace MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShort

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperators
open Cslib.Unification

private theorem accepts_encoding (i : UnificationWithCommutativeOperatorsInstance) :
    unificationWithCommutativeOperatorsShortDec (bitEncode i) = true ↔
      WellFormed i ∧ UnificationWithCommutativeOperatorsFeasible i := by
  simp [unificationWithCommutativeOperatorsShortDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : unificationWithCommutativeOperatorsShortDec [true] = false := by
  have h : bitDecode (α := UnificationWithCommutativeOperatorsInstance) [true] = none := rfl
  simp [unificationWithCommutativeOperatorsShortDec, h]

/-- `x + a ≡ a + b` holds modulo commutativity with `x := b`; both sides have at most seven
leaves. -/
example :
    unificationWithCommutativeOperatorsShortDec
      (bitEncode ((1, 2, [([(2, 0), (0, 0), (1, 0)], [(2, 0), (1, 0), (1, 1)])]) :
        UnificationWithCommutativeOperatorsInstance)) = true := by
  apply (accepts_encoding _).2
  have hes : Pairs (1, 2, [([(2, 0), (0, 0), (1, 0)], [(2, 0), (1, 0), (1, 1)])])
      [(.node (.var 0) (.const 0), .node (.const 0) (.const 1))] := rfl
  refine ⟨⟨⟨⟨_, hes⟩, by decide⟩, by decide⟩, _, hes, fun _ => .const 1, fun _ _ => rfl, ?_⟩
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp
  exact .swap (.refl _) (.refl _)

/-- The right-nested sum `x + (x + (⋯ + x))` of `n` copies of the variable `x`. -/
private def sumX : ℕ → Term (Fin 1)
  | 0 | 1 => .var 0
  | n + 2 => .node (.var 0) (sumX (n + 1))

/-- The pair `(x + ⋯ + x, x + ⋯ + x)` with eight leaves on each side. -/
private abbrev eightLeaves : UnificationWithCommutativeOperatorsInstance :=
  (1, 1, [(tokens (sumX 8), tokens (sumX 8))])

private theorem eightLeaves_pairs : Pairs eightLeaves [(sumX 8, sumX 8)] := rfl

/-- The eight-leaf pair is solvable (any ground value for `x`). -/
private theorem eightLeaves_feasible : UnificationWithCommutativeOperatorsFeasible eightLeaves :=
  ⟨_, eightLeaves_pairs, fun _ => .const 0, fun _ _ => rfl, fun p hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    exact .refl _⟩

/-- The unrestricted language accepts the eight-leaf pair. -/
example : unificationWithCommutativeOperatorsDec (bitEncode eightLeaves) = true := by
  simp only [unificationWithCommutativeOperatorsDec, bitDecode_bitEncode, decide_eq_true_eq]
  exact ⟨⟨⟨_, eightLeaves_pairs⟩, by decide⟩, eightLeaves_feasible⟩

/-- The short-expression language rejects the same solvable pair: each side has eight leaves,
one more than the bound of seven. -/
example : unificationWithCommutativeOperatorsShortDec (bitEncode eightLeaves) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨⟨-, hshort⟩, -⟩
  have := (hshort _ (List.mem_singleton_self _)).1
  revert this
  decide

end MetaMathlibExt.Complexity.NPComplete.UnificationWithCommutativeOperatorsShort
