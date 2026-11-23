/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lacunary essential components (Erdős Problem 37)

Erdős Problem 37: `A ⊆ ℕ` is an essential component if `d_s(A + B) > d_s(B)` for every `B ⊆ ℕ` with
`0 < d_s(B) < 1`, where `d_s` is the Schnirelmann density. Can a lacunary set be an essential
component?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Schnirelmann

@[expose] public section

namespace MathlibExt.NumberTheory.LacunaryEssentialComponentErdosProblem37Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #37, https://www.erdosproblems.com/37 (status DISPROVED
(LEAN)). UnsolvedMath record UM-30006693 (`EP-37`), dataset ulamai/UnsolvedMath v1.8.0.

Schnirelmann density is Mathlib's `schnirelmannDensity`. As in Schnirelmann's setting the sumset is
`(A ∪ {0}) + (B ∪ {0})`, which contains `A` and `B`; this is the usual notion, and a set that is not
an essential component in this sense is not one for the plain sumset either. A lacunary set is the
set of terms of a sequence of positive integers with `a (n + 1) ≥ c · a n`, `c > 1`.
formal-conjectures has no statement of this problem.
-/

open scoped Pointwise Classical in
/-- `A` is an essential component: `σ(A + B) > σ(B)` for every `B ⊆ ℕ` with `0 < σ(B) < 1`, where
`σ` is the Schnirelmann density and, as in Schnirelmann's setting, `0` is adjoined to both
summands. -/
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ, 0 < schnirelmannDensity B → schnirelmannDensity B < 1 →
    schnirelmannDensity B < schnirelmannDensity (insert 0 A + insert 0 B)

/-- `A` is the set of terms of a lacunary sequence of positive integers: `a (n + 1) ≥ c * a n` for
all `n`, for some `c > 1`. -/
def IsLacunarySet (A : Set ℕ) : Prop :=
  ∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧ (∃ c : ℝ, 1 < c ∧ ∀ n, c * a n ≤ a (n + 1)) ∧ A = Set.range a

/-- Erdős Problem 37: some lacunary set is an essential component. -/
def lacunaryEssentialComponentExists : Prop :=
  ∃ A : Set ℕ, IsLacunarySet A ∧ IsEssentialComponent A

/--
Resolved false: Ruzsa proved that every essential component `A` has `|A ∩ {1, …, N}| ≥ (log N)^{1 +
c}` for some `c > 0` and all large `N`, while a lacunary set has `O(log N)` elements up to `N`;
erdosproblems.com/37 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#37, https://www.erdosproblems.com/37 (status DISPROVED (LEAN)); resolution: I. Ruzsa, Essential
components, Proc. London Math. Soc. (1987), 38-56, every essential component A has |A ∩ [1, N]| ≥
(log N)^{1+c} for some c > 0 and all large N (erdosproblems.com/37).
-/
public theorem_wanted lacunaryEssentialComponentExists_refuted : ¬ lacunaryEssentialComponentExists

end MathlibExt.NumberTheory.LacunaryEssentialComponentErdosProblem37Wanted
