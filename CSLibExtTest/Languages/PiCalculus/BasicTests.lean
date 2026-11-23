/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Languages.PiCalculus.Basic

/-!
# Client tests for π-calculus substitution and reduction

These substitution, communication, scope, and guarded-choice calculations exercise
the public API through a normal client import.

Main results, all concrete calculations:

* `subst_out_var`: substitution delivers a sent channel to the input
  variable.
* `comm_example`: `ā⟨b⟩.0 | a(x).x̄.0 → 0 | b̄.0`.
* `bound_name_transmission`: a restricted name is transmitted,
  `νa.(b̄⟨a⟩.0 | b(x).x̄.0) → νa.(0 | ā.0)`, so the receiver gains the
  restricted channel.
* `scope_comm_example`: communication on a restricted channel,
  `νa.(ā⟨b⟩.0 | a(x).0) → νa.(0 | 0)`.
* `comm_after_swap`: communication after swapping the parallel
  components by structural congruence.
* `extrusion_example`: scope extrusion,
  `(νa.P) | 0 ≡ νa.(P | 0)`.
* `out_cong_example`: congruence transports under an output prefix,
  `ā⟨b⟩.(P | 0) ≡ ā⟨b⟩.P`.
* `sum_choice_example`, `input_choice_example`, `sum_sum_example`,
  `nested_sum_example`: guarded choice selects on the output side, on
  the input side, on both sides, and transitively through nested
  sums.
-/

namespace Cslib.PiCalculus.BasicTests

/-- Substitution delivers a sent channel to the input variable:
`(x̄⟨0⟩.0)[c / x] = c̄⟨0⟩.0`. -/
theorem subst_out_var (c : ℕ) :
    subst (.out (.var 0) (.const 0) .nil) (.const c) =
      .out (.const c) (.const 0) .nil := rfl

/-- Nested-binder regression: substituting for variable `1` under a
`ν` lifts the replacement `var 0` to `var 1`, so it is not captured by
the `ν`. -/
theorem substProc_nested :
    substProc (.var 0) 1 (.nu (.out (.var 2) (.const 0) .nil)) =
      .nu (.out (.var 1) (.const 0) .nil) := rfl

/-- Communication: `ā⟨b⟩.0 | a(x).x̄.0 → 0 | b̄.0`. The sent channel `b`
is substituted for the input variable. -/
theorem comm_example (a b : ℕ) :
    Step (.par (.out (.const a) (.const b) .nil)
        (.inp (.const a) (.out (.var 0) (.const 0) .nil)))
      (.par .nil (.out (.const b) (.const 0) .nil)) :=
  Step.commSelect (Select.refl _) (Select.refl _)

/-- Communication on a restricted channel:
`νa.(ā⟨b⟩.0 | a(x).0) → νa.(0 | 0)`. -/
theorem scope_comm_example (b : ℕ) :
    Step (.nu (.par (.out (.var 0) (.const b) .nil) (.inp (.var 0) .nil)))
      (.nu (.par .nil .nil)) :=
  Step.nu (Step.commSelect (Select.refl _) (Select.refl _))

/-- A restricted name is transmitted: `νa.(b̄⟨a⟩.0 | b(x).x̄.0)` reduces
to `νa.(0 | ā.0)`, where the receiver's `var 0` now denotes the
restricted channel `a` (the `ν`-binder). -/
theorem bound_name_transmission (b : ℕ) :
    Step (.nu (.par (.out (.const b) (.var 0) .nil)
        (.inp (.const b) (.out (.var 0) (.const 0) .nil))))
      (.nu (.par .nil (.out (.var 0) (.const 0) .nil))) :=
  Step.nu (Step.commSelect (Select.refl _) (Select.refl _))

/-- Communication after swapping the parallel components by structural
congruence: `a(x).0 | ā⟨b⟩.0 → 0 | 0`. -/
theorem comm_after_swap (a b : ℕ) :
    Step (.par (.inp (.const a) .nil) (.out (.const a) (.const b) .nil))
      (.par .nil .nil) :=
  Step.cong (.par_comm _ _) (Step.commSelect (Select.refl _) (Select.refl _)) (.refl _)

/-- Scope extrusion: `(νa.P) | 0 ≡ νa.(P | 0)` when the other side is
closed (here it is `nil`). -/
theorem extrusion_example (p : Proc) :
    Cong (.par (.nu p) .nil) (.nu (.par p (liftProc 0 .nil))) :=
  Cong.scope _ _

/-- Scope extrusion under an outer restriction: the outside process
`out (var 0) nil` mentions the outer `ν`'s channel, and extrusion
lifts it to `var 1` so it still denotes that channel past the fresh
inner `ν`. -/
theorem extrusion_nested :
    Cong (.nu (.par (.nu (.out (.var 1) (.const 0) .nil))
        (.out (.var 0) (.const 0) .nil)))
      (.nu (.nu (.par (.out (.var 1) (.const 0) .nil)
        (.out (.var 1) (.const 0) .nil)))) :=
  Cong.nu_cong (Cong.scope _ _)

/-- Congruence is contextual: `par_nil` transported under an output
prefix. -/
theorem out_cong_example (a b : ℕ) (p : Proc) :
    Cong (.out (.const a) (.const b) (.par p .nil))
      (.out (.const a) (.const b) p) :=
  Cong.out_cong _ _ (Cong.par_nil p)

/-- Nested restrictions commute: swapping the two `ν` binders turns the
channel `var 1` (the outer binder) into `var 0` (now the inner one). -/
theorem nu_swap_example :
    Cong (.nu (.nu (.out (.var 1) (.const 0) .nil)))
      (.nu (.nu (.out (.var 0) (.const 0) .nil))) :=
  Cong.nu_swap _

/-- Guarded choice: the left branch communicates and the right branch
is discarded. -/
theorem sum_choice_example (a b : ℕ) :
    Step (.par (.sum (.out (.const a) (.const b) .nil) .nil)
        (.inp (.const a) .nil))
      (.par .nil .nil) :=
  Step.commSelect (Select.left _ _) (Select.refl _)

/-- Guarded input choice: the receiving sum selects its `a`-branch and
the `c`-branch is discarded. -/
theorem input_choice_example (a b c : ℕ) :
    Step (.par (.out (.const a) (.const b) .nil)
        (.sum (.inp (.const a) .nil) (.inp (.const c) .nil)))
      (.par .nil .nil) :=
  Step.commSelect (Select.refl _) (Select.left _ _)

/-- Two guarded sums communicate: each selects its matching branch. -/
theorem sum_sum_example (a b : ℕ) :
    Step (.par (.sum (.out (.const a) (.const b) .nil) .nil)
        (.sum (.inp (.const a) .nil) .nil))
      (.par .nil .nil) :=
  Step.commSelect (Select.left _ _) (Select.left _ _)

/-- Nested sums: selection is transitive through the outer sum. -/
theorem nested_sum_example (a b : ℕ) :
    Step (.par (.sum (.sum (.out (.const a) (.const b) .nil) .nil) .nil)
        (.inp (.const a) .nil))
      (.par .nil .nil) :=
  Step.commSelect (Select.trans (Select.left _ _) (Select.left _ _)) (Select.refl _)

/-- Parallel composition is commutative on a concrete pair. -/
theorem par_comm_example (a b : ℕ) :
    Cong (.par (.out (.const a) (.const b) .nil) .nil)
      (.par .nil (.out (.const a) (.const b) .nil)) :=
  Cong.par_comm _ _

end Cslib.PiCalculus.BasicTests
