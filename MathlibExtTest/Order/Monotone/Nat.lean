/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Order.Monotone.Nat
import Mathlib.Tactic

namespace MetaMathlibExt

/-- The identity sequence on `ℕ` is increasing, via the successor-step iff. -/
example : Monotone (fun n : ℕ => n) :=
  monotone_nat_iff_le_succ.2 fun n => Nat.le_succ n

/-- The forward direction of the iff recovers the successor-step bound
from monotonicity. -/
example (hf : Monotone (fun n : ℕ => n)) : ∀ n, n ≤ n + 1 :=
  monotone_nat_iff_le_succ.1 hf

/-- The book's original `ℝ`-valued case is covered by the generalized iff. -/
example : Monotone (fun n : ℕ => (n : ℝ)) :=
  monotone_nat_iff_le_succ.2 fun n => by exact_mod_cast Nat.le_succ n

/-- Negation on `ℤ` is a genuinely decreasing (non-constant) sequence,
via the antitone successor-step iff. -/
example : Antitone (fun n : ℕ => -(n : ℤ)) :=
  antitone_nat_iff_succ_le.2 fun n => by push_cast; omega

/-- The forward direction of the antitone iff recovers the successor-step
bound from antitonicity. -/
example (hf : Antitone (fun n : ℕ => -(n : ℤ))) :
    ∀ n, -((n + 1 : ℕ) : ℤ) ≤ -(n : ℤ) :=
  antitone_nat_iff_succ_le.1 hf

/-- A constant sequence satisfies both successor-step conditions, hence is
both monotone and antitone: the boundary case where the two disjuncts of
the combined characterization overlap. -/
example : Monotone (fun _ : ℕ => (0 : ℤ)) ∧ Antitone (fun _ : ℕ => (0 : ℤ)) :=
  ⟨monotone_nat_iff_le_succ.2 fun _ => le_rfl,
    antitone_nat_iff_succ_le.2 fun _ => le_rfl⟩

/-- The identity sequence is monotone in the book sense (increasing or
decreasing), via the left disjunct of the combined iff. -/
example : Monotone (fun n : ℕ => n) ∨ Antitone (fun n : ℕ => n) :=
  monotone_or_antitone_nat_iff.2 (Or.inl fun n => Nat.le_succ n)

/-- The negated sequence is monotone in the book sense, via the right
disjunct of the combined iff. -/
example : Monotone (fun n : ℕ => -(n : ℤ)) ∨ Antitone (fun n : ℕ => -(n : ℤ)) :=
  monotone_or_antitone_nat_iff.2
    (Or.inr fun n => by push_cast; omega)

/-- The parity sequence `n % 2` is neither increasing nor decreasing:
it goes up at `n = 0` (`0 ≤ 1`) and down at `n = 1` (`1 ≤ 0` fails),
so both successor-step conditions fail. -/
example :
    ¬ (Monotone (fun n : ℕ => n % 2) ∨ Antitone (fun n : ℕ => n % 2)) := by
  intro h
  rcases monotone_or_antitone_nat_iff.1 h with hup | hdown
  · have h1 := hup 1
    norm_num at h1
  · have h0 := hdown 0
    norm_num at h0

end MetaMathlibExt
