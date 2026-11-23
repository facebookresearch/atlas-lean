/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Decidability.Myhill

@[expose] public section

set_option autoImplicit false

namespace Cslib.MyhillBackAndForthWanted

/-- **Myhill's isomorphism theorem, hard direction**: two 1-equivalent sets
(arbitrary predicates, no recursive enumerability assumed — the effective
back-and-forth construction needs only the two 1-reductions) are recursively
isomorphic. Source: Soare, *Recursively Enumerable Sets and Degrees*,
Ch. I, Theorem 7.1; Rogers, *Theory of Recursive Functions and Effective
Computability*, §7.6. -/
theorem_wanted myhill_back_and_forth :
  ∀ {P Q : ℕ → Prop}, OneOneEquiv P Q →
    Cslib.Decidability.RecursiveIsomorphic P Q

end Cslib.MyhillBackAndForthWanted
