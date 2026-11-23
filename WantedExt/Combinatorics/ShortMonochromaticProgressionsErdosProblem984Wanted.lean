/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A 2-colouring whose monochromatic progressions are short (Erdős Problem 984)

Erdős Problem 984: can `ℕ` be `2`-coloured such that if `{a, a + d, …, a + (k - 1)d}` is a `k`-term
monochromatic arithmetic progression then `k ≪_ε a^ε` for all `ε > 0`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.ShortMonochromaticProgressionsErdosProblem984Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #984, https://www.erdosproblems.com/984 (status
PROVED). UnsolvedMath record UM-30007110 (`EP-984`), dataset ulamai/UnsolvedMath v1.8.0.

`ℕ` is the positive integers: progressions start at `a ≥ 1` (for `a = 0` the one-term progression
`{0}` would violate `1 ≤ C · 0^ε`) and have difference `d ≥ 1` (`d = 0` would allow arbitrarily long
constant progressions). A colouring is a function `ℕ → Fin 2` (its value at `0` is irrelevant), and
`k ≪_ε a^ε` is a constant `C_ε` with `k ≤ C_ε a^ε`. formal-conjectures has no statement of this
problem.
-/

/-- **Statement of Erdős Problem 984 on short monochromatic progressions.** The proposition that
there is a colouring of the positive integers with two colours such that for every real
$\varepsilon > 0$ there is a real constant $C_\varepsilon$ with the following property: whenever
$a \ge 1$, $d \ge 1$ and $k \ge 0$ are integers and $a, a + d, \dots, a + (k - 1)d$ all have the
same colour, $k \le C_\varepsilon a^\varepsilon$. -/
def twoColouringShortProgressions : Prop :=
  ∃ c : ℕ → Fin 2, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ a d k : ℕ, 1 ≤ a → 1 ≤ d →
    (∀ i < k, c (a + i * d) = c a) → (k : ℝ) ≤ C * (a : ℝ) ^ ε

/--
**Erdős Problem 984: a two-colouring with short monochromatic progressions exists.** There is a
colouring of the positive integers with two colours such that for every real $\varepsilon > 0$
there is a real constant $C_\varepsilon$ with the following property: whenever $a \ge 1$,
$d \ge 1$ and $k \ge 0$ are integers and $a, a + d, \dots, a + (k - 1)d$ all have the same
colour, $k \le C_\varepsilon a^\varepsilon$.

Source: T. F. Bloom, Erdős Problems,
Problem #984, https://www.erdosproblems.com/984 (status PROVED); resolution: Z. Hunter, proof in the
erdosproblems.com/984 comments, using Green's red-blue colourings for off-diagonal van der Waerden
numbers, erdosproblems.com/984: 'Zach Hunter has proved the answer is yes (see the comments)'; the
comment colours each block I_t = [100^t, 100^{t+1}) with no red 3-term progression and no blue
progression of length k_t = |I_t|^{o(1)} for odd t (colours swapped for even t),
https://www.erdosproblems.com/forum/thread/984.
-/
public theorem_wanted twoColouringShortProgressions_holds : twoColouringShortProgressions

end MathlibExt.Combinatorics.ShortMonochromaticProgressionsErdosProblem984Wanted
