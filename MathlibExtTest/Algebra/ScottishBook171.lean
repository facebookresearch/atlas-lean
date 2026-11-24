/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.ScottishBook171

open MathlibExt.Algebra.ScottishBook171Wanted

-- The counterexample is available above the universe of `Bool` itself.
example :
    ¬ ∀ (A : Type 1) (U : (A → A) → (A → A) → (A → A)),
      IsAssociative A U → IsPermutationInvariant A U →
      ∀ f g : A → A, U f g = f ∘ g :=
  not_forall_eq_comp_of_associative_permutationInvariant
