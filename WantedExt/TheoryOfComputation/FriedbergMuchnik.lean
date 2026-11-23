/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.Degrees

@[expose] public section

set_option autoImplicit false

namespace Cslib.FriedbergMuchnikWanted

/-- **The Friedberg–Muchnik theorem**: there are two recursively enumerable
sets of incomparable Turing degree, by the finite-injury priority method.
Source: Friedberg, "Two recursively enumerable sets of incomparable degrees
of unsolvability", *Proceedings of the National Academy of Sciences* 43
(1957), 236–238; Muchnik, "On the unsolvability of the problem of
reducibility in the theory of algorithms", *Doklady Akademii Nauk SSSR* 108
(1956), 194–197; Soare, *Recursively Enumerable Sets and Degrees*, Ch. III,
Theorem 1.1. -/
theorem_wanted friedberg_muchnik :
  ∃ P Q : ℕ → Prop, REPred P ∧ REPred Q ∧
    ¬ Cslib.Decidability.TuringReduciblePred P Q ∧
    ¬ Cslib.Decidability.TuringReduciblePred Q P

end Cslib.FriedbergMuchnikWanted
