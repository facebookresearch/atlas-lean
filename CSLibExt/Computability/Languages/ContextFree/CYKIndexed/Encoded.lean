/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Languages.ContextFree.CYKIndexed.Cost
public import CSLibExt.Computability.Languages.ContextFree.Encoded

/-!
# Indexed CYK for the canonical encoded grammar

Decode existing `EncodedCFG` data, charging symbol and rule traversal, then
use indexed CYK. No new grammar carrier or noncomputable rule enumeration.
-/

@[expose] public section

namespace Cslib.Language.CYKIndexed

open Cslib.Algorithms.Lean

variable {T : Type*}

/-- Decode symbols with a charge for each constructor test and output cons. -/
def decodeSymbols : List (ℕ ⊕ T) → TimeM ℕ (List (Symbol T ℕ))
  | [] => ⟨[], 1⟩
  | s :: ss =>
      let rest := decodeSymbols ss
      ⟨EncodedCFG.decodeSymbol s :: rest.ret, rest.time + 4⟩

/-- The charged conversion is exactly the canonical symbol decoding. -/
@[simp] theorem decodeSymbols_ret (ss : List (ℕ ⊕ T)) :
    (decodeSymbols ss).ret = ss.map EncodedCFG.decodeSymbol := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [decodeSymbols, ih]

/-- Decode every rule, charging all right-hand-side traversals. -/
def decodeRules : List (ℕ × List (ℕ ⊕ T)) →
    TimeM ℕ (List (ContextFreeRule T ℕ))
  | [] => ⟨[], 1⟩
  | r :: rs =>
      let out := decodeSymbols r.2
      let rest := decodeRules rs
      ⟨⟨r.1, out.ret⟩ :: rest.ret, out.time + rest.time + 5⟩

/-- The charged rule conversion agrees with the existing decoded grammar. -/
@[simp] theorem decodeRules_ret (rs : List (ℕ × List (ℕ ⊕ T))) :
    (decodeRules rs).ret = rs.map EncodedCFG.decodeRule := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [decodeRules, EncodedCFG.decodeRule, ih]

/-- Run indexed CYK on the existing encoded grammar, including preparation. -/
def recognizesEncoded [DecidableEq T] (tc nc : ℕ) (g : EncodedCFG T)
    (w : List T) : TimeM ℕ Bool :=
  let rules := decodeRules g.rules
  let result := recognizes tc nc g.start rules.ret w
  ⟨result.ret, rules.time + result.time + 3⟩

/-- Correctness for the canonical encoded language, including epsilon. -/
theorem recognizesEncoded_iff [DecidableEq T] (tc nc : ℕ)
    (g : EncodedCFG T) (hg : IsChomskyNormalForm g.toCFG) (w : List T) :
    (recognizesEncoded tc nc g w).ret = true ↔ w ∈ g.language := by
  simp only [recognizesEncoded, decodeRules_ret]
  exact recognizes_iff hg tc nc _
    (fun r => by simp [EncodedCFG.toCFG]) w

/-- Exact symbol-decoding traversal cost. -/
theorem decodeSymbols_time (ss : List (ℕ ⊕ T)) :
    (decodeSymbols ss).time = 1 + 4 * ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [decodeSymbols, ih]; omega

/-- Exact grammar-preparation cost, including all production symbols. -/
theorem decodeRules_time (rs : List (ℕ × List (ℕ ⊕ T))) :
    (decodeRules rs).time =
      1 + 6 * rs.length + 4 * (rs.map (fun r => r.2.length)).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [decodeRules, decodeSymbols_time, ih]; omega

/-- Cubic word-length bound including canonical grammar preparation.
All dependence on the fixed grammar and symbol-equality model is explicit. -/
theorem recognizesEncoded_time_le [DecidableEq T] (tc nc : ℕ)
    (g : EncodedCFG T) (w : List T) :
    (recognizesEncoded tc nc g w).time ≤
      (g.rules.length * (tc + nc + 2 * g.rules.length * (nc + 3) + 44) +
        4 * (g.rules.map (fun r => r.2.length)).sum + 44) *
          (w.length + 1) ^ 3 := by
  have h := recognizes_time_le tc nc g.start (decodeRules g.rules).ret w
  have hp : 1 ≤ (w.length + 1) ^ 3 := by
    nlinarith [Nat.zero_le (w.length ^ 3), Nat.zero_le (w.length ^ 2)]
  have hm := Nat.mul_le_mul_left
    (4 + 6 * g.rules.length + 4 * (g.rules.map (fun r => r.2.length)).sum) hp
  simp only [recognizesEncoded, decodeRules_time, decodeRules_ret]
  simp only [decodeRules_ret, List.length_map] at h
  nlinarith only [h, hm]

end Cslib.Language.CYKIndexed
