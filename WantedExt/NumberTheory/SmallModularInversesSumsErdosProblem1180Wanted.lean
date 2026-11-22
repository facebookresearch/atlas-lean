/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Residues as bounded sums of inverses of small integers (Erdős Problem 1180)

Erdős Problem 1180: let `ε > 0`. Is there `C_ε` such that, for every prime `p`, every residue modulo
`p` is a sum of at most `C_ε` elements of `{n⁻¹ : 1 ≤ n ≤ p^ε}`, where `n⁻¹` is the inverse of `n`
modulo `p`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.NumberTheory.SmallModularInversesSumsErdosProblem1180Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1180, https://www.erdosproblems.com/1180 (status
PROVED). UnsolvedMath record UM-30007221 (`EP-1180`), dataset ulamai/UnsolvedMath v1.8.0.

Summands may repeat; `n` is coprime to `p` (so `n⁻¹` exists). The constant is uniform over all
primes: the finitely many primes below the threshold of the resolving theorem are handled by sums of
copies of `1⁻¹ = 1`, so this is equivalent to the bound for large primes. Compared with the
formal-conjectures statement `ErdosProblems/1180.lean` (equivalent to `erdos_1180`; no code
imported).
-/

/-- Erdős Problem 1180: for every `ε > 0` there is `C` such that, for every prime `p`, every
residue modulo `p` is a sum of at most `C` inverses `n⁻¹ mod p` with `1 ≤ n ≤ p^ε` (`n` coprime to
`p`; repetitions allowed). -/
def boundedSumsOfSmallInverses : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
    ∃ s : Multiset ℕ, s.card ≤ C ∧ (∀ n ∈ s, 1 ≤ n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ n.Coprime p) ∧
      (s.map fun n : ℕ => (n : ZMod p)⁻¹).sum = a

/--
Resolved true: Shparlinski proved that for all sufficiently large primes `p`, every residue is a sum
of `≪ ε^{-3}` inverses `n⁻¹` with `1 ≤ n ≤ p^ε` (Glibichuk: `≪ ε^{-2}`); the remaining primes need
at most `p - 1` copies of `1`. erdosproblems.com/1180 lists the problem as proved. Source: T. F.
Bloom, Erdős Problems, Problem #1180, https://www.erdosproblems.com/1180 (status PROVED);
resolution: I. E. Shparlinski, On a question of Erdős and Graham, Arch. Math. (Basel) 78 (2002),
445-448, erdosproblems.com/1180: answered yes with C_ε ≪ ε^{-3} (for all large p); improved to
ε^{-2} by A. A. Glibichuk, Mat. Zametki (2006), 384-395.
-/
public theorem_wanted boundedSumsOfSmallInverses_holds : boundedSumsOfSmallInverses

end MathlibExt.NumberTheory.SmallModularInversesSumsErdosProblem1180Wanted
