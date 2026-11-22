/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.ArithmeticalHierarchy
public import CSLibExt.Computability.Decidability.Degrees
public import Mathlib.Logic.Function.Iterate

@[expose] public section

set_option autoImplicit false

namespace Cslib.PostJumpCharacterisationWanted

/-- **Post's jump characterisation of the arithmetical hierarchy,
`Δ` form**: a set is in `Δₙ₊₁` iff it is Turing reducible to the `n`-th
iterate of the jump of the empty set. (The `Σ` form is relative
enumerability: `Σₙ₊₁` is RE relative to the `n`-th jump, not Turing
reducibility. At `n = 0` the `Σ` form would claim every RE set is
computable, contradicted by the halting set; Turing reducibility
characterizes `Δ`, the RE ∩ co-RE level.) Source: Soare, *Recursively
Enumerable Sets and Degrees*, Ch. I, Theorem 4.5 (Post's theorem); Rogers,
*Theory of Recursive Functions and Effective Computability*, §13.4. -/
theorem_wanted post_jump :
  ∀ {n : ℕ} {P : ℕ → Prop},
    Cslib.Decidability.IsDelta (n + 1) P ↔
      Cslib.Decidability.TuringReduciblePred P
        ((Cslib.Decidability.Jump)^[n] (fun _ ↦ False))

end Cslib.PostJumpCharacterisationWanted
