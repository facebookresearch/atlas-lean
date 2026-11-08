/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Kolmogorov.Basic

@[expose] public section

/-!
# Tests for Kolmogorov complexity
-/

set_option autoImplicit false

open Encodable
open Nat.Partrec (Code)
open Cslib.Kolmogorov

namespace CSLibExtTest.Computability.Kolmogorov.Basic

/-- The identity code describes every string by itself, after its self-delimiting prefix. -/
example (x : List Bool) : x ∈ U (describe Code.id x) := by
  simp [run_id]

/-- A string of `1`s describes nothing. -/
example (n : ℕ) (x : List Bool) : x ∉ U (List.replicate n true) := by
  simp [U]

/-- Complexity is bounded by the length of any description. -/
example (x : List Bool) : K x ≤ encode Code.id + 1 + x.length := by
  simpa using K_le (x := x) (p := describe Code.id x) (by simp [run_id])

/-- Optimality, applied to the description method "reverse". -/
example : ∃ c, ∀ x : List Bool, K x.reverse ≤ x.length + c := by
  obtain ⟨c, hc⟩ := exists_K_le_of_partrec (D := fun p ↦ Part.some p.reverse)
    (Primrec.list_reverse.to_comp.partrec)
  exact ⟨c, fun x ↦ hc _ x (Part.mem_some _)⟩

/-- Doubling. -/
example : ∃ c, ∀ x : List Bool, K (x ++ x) ≤ K x + c := K_append_self_le

/-- Concatenation: a pair description `1^|p| 0 p q` reads back as the concatenation. -/
example : ∃ c, ∀ x y : List Bool, K (x ++ y) ≤ 2 * K x + K y + c := K_append_le

end CSLibExtTest.Computability.Kolmogorov.Basic
