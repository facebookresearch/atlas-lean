/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.AcceleratedZeckendorfGameFibonacci

open MetaMathlibExt

-- The first denomination is already terminal.
example : ∃ g, IsAccelZeckGame 1 0 g :=
  (accelZeckGame_sharp_lower_bound_fib 1 (by decide)).2

-- The second denomination needs exactly one batch of pairs of ones.
example : ∃ g, IsAccelZeckGame 2 1 g :=
  (accelZeckGame_sharp_lower_bound_fib 2 (by decide)).2

-- At F₅ = 8 the opening batch is followed by three successive combines.
example : ∃ g, IsAccelZeckGame 8 4 g :=
  (accelZeckGame_sharp_lower_bound_fib 5 (by decide)).2

example (L : ℕ) (g : ℕ → ℕ →₀ ℕ) (hg : IsAccelZeckGame 8 L g) : 4 ≤ L :=
  (accelZeckGame_sharp_lower_bound_fib 5 (by decide)).1 L g hg

-- The general bound is attained at both smallest positive inputs.
example : ∃ g, IsAccelZeckGame 1 0 g :=
  (accelZeckGame_sharp_lower_bound 1 (by decide)).2

example : ∃ g, IsAccelZeckGame 2 1 g :=
  (accelZeckGame_sharp_lower_bound 2 (by decide)).2

-- The summand F₁ stays frozen while F₃ is assembled in two batches.
example : ∃ g, IsAccelZeckGame 4 2 g :=
  (accelZeckGame_sharp_lower_bound 4 (by decide)).2

example (L : ℕ) (g : ℕ → ℕ →₀ ℕ) (hg : IsAccelZeckGame 4 L g) : 2 ≤ L :=
  (accelZeckGame_sharp_lower_bound 4 (by decide)).1 L g hg

-- Both summands of 7 = 5 + 2 contribute to the opening batch.
example : ∃ g, IsAccelZeckGame 7 3 g :=
  (accelZeckGame_sharp_lower_bound 7 (by decide)).2
