/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Distributed.AnonymousRing

@[expose] public section

/-- Boundary check: majority-transition on a 3-ring stays constant
under the constant-true start for two rounds. -/
example (δ : Bool → Bool → Bool → Bool) (k : ℕ)
    (i j : ZMod 3) :
    ringState δ (fun _ => true) k i = ringState δ (fun _ => true) k j :=
  ringState_const δ (fun _ => true) (fun a b => rfl) k i j
