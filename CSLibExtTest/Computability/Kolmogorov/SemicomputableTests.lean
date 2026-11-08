/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Kolmogorov.Semicomputable

@[expose] public section

/-!
# Tests for upper semicomputability and the incompressible strings
-/

set_option autoImplicit false

open Cslib.Kolmogorov

namespace CSLibExtTest.Computability.Kolmogorov.Semicomputable

/-- `K x ≤ n` is recognizable, so `K x ≤ 5` is recognizable for each fixed bound. -/
example : REPred fun x : List Bool ↦ K x ≤ 5 :=
  Partrec.comp (g := fun x : List Bool ↦ (x, 5)) rePred_K_le
    (Computable.pair Computable.id (Computable.const 5))

/-- Reversal raises complexity by at most a constant. -/
example : ∃ c, ∀ x : List Bool, K x.reverse ≤ K x + c := by
  obtain ⟨c, hc⟩ := exists_K_map_le (f := fun x : List Bool ↦ Part.some x.reverse)
    Primrec.list_reverse.to_comp.partrec
  exact ⟨c, fun x ↦ hc x _ (Part.mem_some _)⟩

/-- Shortest descriptions are incompressible up to a constant. -/
example : ∃ b, ∀ x p : List Bool, p.length = K x → x ∈ U p → p.length ≤ K p + b :=
  exists_shortest_incompressible

/-- The incompressible strings are neither recognizable nor decidable. -/
example : ¬REPred fun x : List Bool ↦ x.length ≤ K x := not_rePred_incompressible

example : ¬ComputablePred fun x : List Bool ↦ x.length ≤ K x := not_computablePred_incompressible

/-- Chaitin's incompleteness theorem: a recognizable set of true lower bounds on `K` is bounded. -/
example {S : List Bool × ℕ → Prop} (hS : REPred S) (hsound : ∀ q, S q → q.2 ≤ K q.1) :
    ∃ B, ∀ q, S q → q.2 ≤ B :=
  exists_bound_of_rePred_le_K hS hsound

/-- A computable lower bound of `K` is bounded. -/
example {f : List Bool → ℕ} (hf : Computable f) (hle : ∀ x, f x ≤ K x) : ∃ B, ∀ x, f x ≤ B :=
  exists_bound_of_computable_le_K hf hle

/-- No unbounded computable function of the length is a lower bound of `K`: `|x| / 2 ≤ K x`
fails somewhere. -/
example : ¬∀ x : List Bool, x.length / 2 ≤ K x := by
  intro h
  obtain ⟨B, hB⟩ := exists_bound_of_computable_le_K
    (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2)).to_comp h
  have := hB (List.replicate (2 * B + 2) true)
  simp only [List.length_replicate] at this
  omega

/-- `K` is upper but not lower semicomputable. -/
example : ¬REPred fun q : List Bool × ℕ ↦ q.2 ≤ K q.1 := not_rePred_le_K

end CSLibExtTest.Computability.Kolmogorov.Semicomputable
