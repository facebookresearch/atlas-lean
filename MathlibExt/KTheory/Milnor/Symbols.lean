/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.KTheory.Milnor.Relations

/-!
# Milnor symbols

For a field `F`, the multilinear `n`-ary symbol `symbolList F l` in `MilnorKRing F`
is the ordered product of degree-one symbols `symbol F x` for the units in `l`.

The empty list evaluates to `1`, the unit in degree zero. Concatenation of lists
corresponds to multiplication in the Milnor K-ring, and inserting a distinguished
unit in the middle factors as a product of the prefix symbol, the middle
degree-one symbol, and the suffix symbol. These list identities lift the
logarithmic and Steinberg relations from degree one to arbitrary degree.

## Main definitions
* `MilnorK.MilnorKRing.symbolList` : ordered product `l ↦ ∏ symbol F x`.

## Main results
* `symbolList_nil`, `symbolList_cons`, `symbolList_singleton` : evaluation at
  empty, cons, and singleton lists.
* `symbolList_append`, `symbolList_append_assoc`, `symbolList_concat_middle` :
  concatenation and insertion factorizations.
* `symbolList_mul_middle`, `symbolList_one_middle`, `symbolList_steinberg_middle` :
  list analogues of multiplicativity, vanishing at `1`, and vanishing on adjacent
  Steinberg pairs `{a, 1-a}`.
* `symbolList_pair` : binary case as product of two degree-one symbols.
-/

@[expose] public section

namespace MilnorK

variable (F : Type*) [Field F]

namespace MilnorKRing

/-- Ordered product of degree-one symbols attached to a list of units.

For `l = [x₁, …, xₙ]` this is `symbol F x₁ * … * symbol F xₙ` in
`MilnorKRing F`, with `[] ↦ 1`. It represents the `n`-ary Milnor symbol
`{x₁, …, xₙ}` in degree `n`. -/
def symbolList : List Fˣ → MilnorKRing F
  | [] => 1
  | x :: xs => symbol F x * symbolList xs

/-- The symbol of the empty list is `1`, the unit of `MilnorKRing F`. -/
@[simp]
theorem symbolList_nil : symbolList F ([] : List Fˣ) = 1 := rfl

/-- The symbol of `a :: l` is `symbol F a` times the symbol of `l`. -/
@[simp]
theorem symbolList_cons (a : Fˣ) (l : List Fˣ) :
    symbolList F (a :: l) = symbol F a * symbolList F l := rfl

/-- A singleton list evaluates to the corresponding degree-one symbol. -/
theorem symbolList_singleton (a : Fˣ) : symbolList F [a] = symbol F a := by
  simp [symbolList_cons, symbolList_nil]

/-- Concatenation of lists corresponds to multiplication of symbols. -/
theorem symbolList_append (l₁ l₂ : List Fˣ) :
    symbolList F (l₁ ++ l₂) = symbolList F l₁ * symbolList F l₂ := by
  induction l₁ with
  | nil =>
    simp [symbolList_nil, one_mul]
  | cons hd tl ih =>
    simp [List.cons_append, symbolList_cons, ih, mul_assoc]

/-- Threefold concatenation factors as a triple product of list symbols. -/
theorem symbolList_append_assoc (l₁ l₂ l₃ : List Fˣ) :
    symbolList F (l₁ ++ l₂ ++ l₃) =
      symbolList F l₁ * symbolList F l₂ * symbolList F l₃ := by
  calc
    symbolList F (l₁ ++ l₂ ++ l₃)
        = symbolList F ((l₁ ++ l₂) ++ l₃) := by rw [List.append_assoc]
    _ = symbolList F (l₁ ++ l₂) * symbolList F l₃ := symbolList_append F _ _
    _ = (symbolList F l₁ * symbolList F l₂) * symbolList F l₃ := by
        rw [symbolList_append]
    _ = symbolList F l₁ * symbolList F l₂ * symbolList F l₃ := by rw [mul_assoc]

/-- Insertion of a distinguished unit in the middle factors as prefix times
middle degree-one symbol times suffix. -/
theorem symbolList_concat_middle (pref : List Fˣ) (x : Fˣ) (suff : List Fˣ) :
    symbolList F (pref ++ [x] ++ suff) =
      symbolList F pref * symbol F x * symbolList F suff := by
  calc
    symbolList F (pref ++ [x] ++ suff)
        = symbolList F (pref ++ ([x] ++ suff)) := by rw [List.append_assoc]
    _ = symbolList F pref * symbolList F ([x] ++ suff) := symbolList_append F _ _
    _ = symbolList F pref * (symbolList F [x] * symbolList F suff) := by
        rw [symbolList_append]
    _ = symbolList F pref * (symbol F x * symbolList F suff) := by
        rw [symbolList_singleton]
    _ = symbolList F pref * symbol F x * symbolList F suff := by rw [mul_assoc]

/-- Logarithmic splitting in a slot: `a * b` at a position splits as sum of the
symbols with `a` and with `b`, reflecting `symbol (a*b) = symbol a + symbol b`. -/
theorem symbolList_mul_middle (pref suff : List Fˣ) (a b : Fˣ) :
    symbolList F (pref ++ [a * b] ++ suff) =
      symbolList F (pref ++ [a] ++ suff) + symbolList F (pref ++ [b] ++ suff) := by
  calc
    symbolList F (pref ++ [a * b] ++ suff)
        = symbolList F pref * symbol F (a * b) * symbolList F suff := by
          rw [symbolList_concat_middle]
    _ = symbolList F pref * (symbol F a + symbol F b) * symbolList F suff := by
          rw [symbol_mul]
    _ = (symbolList F pref * (symbol F a + symbol F b)) * symbolList F suff := by
          rw [mul_assoc]
    _ = (symbolList F pref * symbol F a + symbolList F pref * symbol F b) *
          symbolList F suff := by rw [mul_add]
    _ = symbolList F pref * symbol F a * symbolList F suff +
          symbolList F pref * symbol F b * symbolList F suff := by rw [add_mul]
    _ = symbolList F (pref ++ [a] ++ suff) +
          symbolList F (pref ++ [b] ++ suff) := by
        rw [symbolList_concat_middle, symbolList_concat_middle]

/-- Insertion of `1` as a unit anywhere kills the symbol, since `symbol 1 = 0`. -/
theorem symbolList_one_middle (pref suff : List Fˣ) :
    symbolList F (pref ++ [(1 : Fˣ)] ++ suff) = 0 := by
  calc
    symbolList F (pref ++ [(1 : Fˣ)] ++ suff)
        = symbolList F pref * symbol F 1 * symbolList F suff := by
          rw [symbolList_concat_middle]
    _ = symbolList F pref * 0 * symbolList F suff := by rw [symbol_one]
    _ = 0 := by rw [mul_zero, zero_mul]

/-- Insertion of an adjacent Steinberg pair `a, 1-a` anywhere kills the symbol,
lifting the relation `symbol a * symbol (1-a) = 0` to list level. -/
theorem symbolList_steinberg_middle (pref suff : List Fˣ) (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    let b : Fˣ := Units.mk0 a ha0
    let c : Fˣ := Units.mk0 (1 - a) (sub_ne_zero.mpr ha1.symm)
    symbolList F (pref ++ [b, c] ++ suff) = 0 := by
  intro b c
  calc
    symbolList F (pref ++ [b, c] ++ suff)
        = symbolList F (pref ++ ([b, c] ++ suff)) := by rw [List.append_assoc]
    _ = symbolList F pref * symbolList F ([b, c] ++ suff) := symbolList_append F _ _
    _ = symbolList F pref * (symbolList F [b, c] * symbolList F suff) := by
        rw [symbolList_append]
    _ = symbolList F pref * ((symbol F b * symbol F c) * symbolList F suff) := by
        have hpair : symbolList F [b, c] = symbol F b * symbol F c := by
          calc
            symbolList F [b, c] = symbolList F (b :: [c]) := rfl
            _ = symbol F b * symbolList F [c] := rfl
            _ = symbol F b * symbol F c := by rw [symbolList_singleton]
        rw [hpair, mul_assoc]
    _ = symbolList F pref * (0 * symbolList F suff) := by
        rw [steinberg_zero F a ha0 ha1]
    _ = 0 := by rw [zero_mul, mul_zero]

/-- The binary symbol `{a, b}` equals `symbol a * symbol b` in degree two. -/
theorem symbolList_pair (a b : Fˣ) :
    symbolList F [a, b] = symbol F a * symbol F b := by
  calc
    symbolList F [a, b] = symbolList F (a :: [b]) := rfl
    _ = symbol F a * symbolList F [b] := rfl
    _ = symbol F a * symbol F b := by rw [symbolList_singleton]

end MilnorKRing

end MilnorK
