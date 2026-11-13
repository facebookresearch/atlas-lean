/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.MaxSat
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: for one 3-clause over three variables, the
7/8 bound instantiates (in fact the all-true assignment satisfies
the clause outright here). -/
example : ∃ x : Fin 3 → Bool,
    (7 / 8 : ℝ) * ({ {(0, true), (1, true), (2, false)} } :
      Finset (Finset (Lit 3))).card ≤
      (({ {(0, true), (1, true), (2, false)} } :
        Finset (Finset (Lit 3))).filter (fun c => clauseSat x c)).card := by
  refine ⟨fun _ => true, ?_⟩
  have hsat : clauseSat (fun _ => true) ({(0, true), (1, true), (2, false)} : Finset (Lit 3)) :=
    ⟨(0, true), Finset.mem_insert_self _ _, rfl⟩
  have hfilter : ({ {(0, true), (1, true), (2, false)} } :
        Finset (Finset (Lit 3))).filter
        (fun c => clauseSat (fun _ => true) c) =
      { {(0, true), (1, true), (2, false)} } := by
    rw [Finset.filter_true_of_mem]
    intro c hc
    rw [Finset.mem_singleton] at hc
    rw [hc]
    exact hsat
  rw [hfilter, Finset.card_singleton]
  norm_num
