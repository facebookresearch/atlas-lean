/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Nilpotent length of groups of exponent p^α q^β (Kourovka Notebook Problem 3.26)

Kourovka Notebook, Archive of Solved Problems, Problem 3.26 (F. Gross; V. D. Mazurov): is it true
that finite groups of exponent `p^α q^β` have nilpotent length at most `α + β`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Exponent

@[expose] public section

namespace MathlibExt.GroupTheory.ExponentNilpotentLengthKourovka3Problem26Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.26 (F. Gross;
V. D. Mazurov). UnsolvedMath record UM-00700177 (`KOU-3.26`), dataset ulamai/UnsolvedMath v1.8.0.

Nilpotent length at most `n`: a chain of `n + 1` normal subgroups from `1` to `G` with nilpotent
factors, a factor `K / L` being nilpotent when some term of the lower central series of `K`
(commutators taken in `G`) lies in `L`. Exponent dividing `p^α q^β` is used; it gives the same claim
as exponent equal to `p^α q^β`, since a smaller exponent `p^a q^b` has `a + b ≤ α + β`.
-/

/-- `G` has nilpotent (Fitting) length at most `n`: a chain `1 = N₀ ≤ N₁ ≤ ⋯ ≤ Nₙ = G` of normal
subgroups with nilpotent factors, where `Nᵢ₊₁ / Nᵢ` is nilpotent when some term of the lower
central series of `Nᵢ₊₁` (computed with commutator subgroups in `G`) lies in `Nᵢ`. -/
def NilpotentLengthLE (G : Type) [Group G] (n : ℕ) : Prop :=
  ∃ N : Fin (n + 1) → Subgroup G, N 0 = ⊥ ∧ N (Fin.last n) = ⊤ ∧ (∀ i, (N i).Normal) ∧
    ∀ i : Fin n, N i.castSucc ≤ N i.succ ∧
      ∃ c : ℕ, (fun M : Subgroup G => ⁅M, N i.succ⁆)^[c] (N i.succ) ≤ N i.castSucc

/-- Kourovka 3.26 (F. Gross; V. D. Mazurov): for all primes `p, q` and all `α, β`, a finite group
of exponent dividing `p^α q^β` has nilpotent length at most `α + β`. -/
def exponentBoundsNilpotentLength : Prop :=
  ∀ (p q α β : ℕ) (G : Type) [Group G] [Finite G], p.Prime → q.Prime →
    Monoid.exponent G ∣ p ^ α * q ^ β → NilpotentLengthLE G (α + β)

/--
Resolved false: the Kourovka Archive answers 3.26 "No, not always", citing Khukhro (Algebra and
Logic 17 (1978)): some finite group of exponent `p^α q^β` has nilpotent length greater than `α + β`.
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 3.26 (F. Gross;
V. D. Mazurov); resolution: E. I. Khukhro, Algebra and Logic 17 (1978), 473-482, Kourovka Archive,
Problem 3.26: No, not always, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted exponentBoundsNilpotentLength_refuted : ¬ exponentBoundsNilpotentLength

end MathlibExt.GroupTheory.ExponentNilpotentLengthKourovka3Problem26Wanted
