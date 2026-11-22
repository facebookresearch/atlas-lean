/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.RingTheory.PowerSeries.Binomial

namespace MetaMathlibExt

@[expose] public section

open Equiv Finset

/-- `τ` is the permutation attached to a set partition of `Fin n`: its cycles are the blocks,
each traversed in increasing order and closed by returning from the largest element to the
least one. Equivalently, whenever `τ x ≤ x`, the value `τ x` is the least element of the
cycle of `x`. Set partitions of `Fin n` correspond bijectively to such permutations, and the
paper counts partitions through this encoding.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 (the permutation `τ`
whose cycles are the parts, with their elements in increasing order). -/
def IsIncreasingCyclePerm {n : ℕ} (τ : Perm (Fin n)) : Prop :=
  ∀ x y, τ x ≤ x → τ.SameCycle x y → τ x ≤ y

instance {n : ℕ} : DecidablePred (IsIncreasingCyclePerm (n := n)) := fun τ => by
  unfold IsIncreasingCyclePerm
  infer_instance

/-- The genus of the set partition of `Fin n` encoded by `τ`: with `σ = finRotate n` the cyclic
permutation `i ↦ i + 1`, it is the `g` with `-2g = |α| - 1 - n + #cy(σ ∘ τ⁻¹)`, where `|α|` is
the number of blocks (cycles of `τ`, fixed points included) and `#cy` counts cycles including
fixed points (`Equiv.Perm.partition`). The quantity `n + 1 - |α| - #cy(σ ∘ τ⁻¹)` is a
nonnegative even number for `n ≥ 1`; the empty partition (`n = 0`) gets genus `0`.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4, equation (genus). -/
def setPartitionGenus {n : ℕ} (τ : Perm (Fin n)) : ℕ :=
  (n + 1 - τ.partition.parts.card - (finRotate n * τ⁻¹).partition.parts.card) / 2

/-- `C_{n,[α]}^{(g)}`: the number of set partitions of `Fin n` of type `[α]` (the multiset of
block sizes) and genus `g`, counted through their increasing-cycle permutations.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 (the numbers
`C_{n,[α]}^{(g)}`). -/
def partitionGenusCount (n : ℕ) (α : Multiset ℕ) (g : ℕ) : ℕ :=
  #{τ : Perm (Fin n) | IsIncreasingCyclePerm τ ∧ τ.partition.parts = α ∧
    setPartitionGenus τ = g}

/-- The partition of `Fin n` into singletons is encoded by the identity permutation.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem isIncreasingCyclePerm_one (n : ℕ) : IsIncreasingCyclePerm (1 : Perm (Fin n)) := by
  intro x y _ h
  rw [Perm.sameCycle_one] at h
  simp [h]

/-- The partition of `Fin n` into singletons has genus `0`.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem setPartitionGenus_one (n : ℕ) : setPartitionGenus (1 : Perm (Fin n)) = 0 := by
  have h : (1 : Perm (Fin n)).partition.parts.card = n := by
    simp [Perm.parts_partition]
  unfold setPartitionGenus
  rw [h]
  omega

/-- The one-block partition of `Fin n` is encoded by `finRotate n`.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4. -/
theorem isIncreasingCyclePerm_finRotate (n : ℕ) : IsIncreasingCyclePerm (finRotate n) := by
  cases n with
  | zero => intro x; exact x.elim0
  | succ m =>
    intro x y hx _
    by_cases hl : x = Fin.last m
    · subst hl
      rw [finRotate_last]
      exact Fin.zero_le y
    · exfalso
      have h1 := coe_finRotate_of_ne_last hl
      rw [Fin.le_def, h1] at hx
      omega

/-- One-part partitions have genus `0`.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Section 2.4 ("one-part partitions
(`k = 1`) necessarily have genus 0"). -/
theorem setPartitionGenus_finRotate (n : ℕ) : setPartitionGenus (finRotate n) = 0 := by
  have h : (finRotate n * (finRotate n)⁻¹).partition.parts.card = n := by
    simp [Perm.parts_partition]
  unfold setPartitionGenus
  rw [h]
  omega

/-- For `g > 0`, the generating function of the genus-`g` counts of pairings,
`Z^{(g)}(u) = ∑_k C_{2k,[2^k]}^{(g)} u^k`, equals `u^{2g} Q^{(g)}(u) / (1 - 4u)^{(6g-1)/2}`
for a rational polynomial `Q^{(g)}` of degree `g - 1` with
`Q^{(g)}(0) = (4g)! / (2^{2g} (2g+1)!)`. The half-integer power is the binomial series
`(1 + X)^r` with `r = -(6g-1)/2`, rescaled by `X ↦ -4X`.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Proposition 11
(`jis-2024-24.2.6-prop-11`). -/
public theorem_wanted pairing_genus_generatingFunction (g : ℕ) (hg : 0 < g) :
    ∃ Q : Polynomial ℚ, Q.natDegree = g - 1 ∧
      Q.eval 0 = ((4 * g).factorial : ℚ) / (2 ^ (2 * g) * ((2 * g + 1).factorial : ℚ)) ∧
      PowerSeries.mk (fun k => (partitionGenusCount (2 * k) (Multiset.replicate k 2) g : ℚ)) =
        PowerSeries.X ^ (2 * g) * (Q : PowerSeries ℚ) *
          PowerSeries.rescale (-4 : ℚ)
            (PowerSeries.binomialSeries ℚ (-((6 * (g : ℚ) - 1) / 2)))

/-- For a set partition of `Fin n` into two blocks, the permutation `σ ∘ τ⁻¹` has exactly one
cycle of length at least `2` (`f' = 1`), and for either block `B` (the cycle of `τ` through
`x₀`), with `s` the number of fixed points of `σ ∘ τ⁻¹` lying in `B`, the genus satisfies
`g = |B| - s - 1`. Taking `x₀` in each block gives both displayed formulas
`g = p - s₁ - 1 = (n - p) - s₂ - 1`.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Lemma 13
(`jis-2024-24.2.6-lem-13`). -/
public theorem_wanted twoBlock_oneFace_and_genus {n : ℕ} (τ : Perm (Fin n))
    (hτ : IsIncreasingCyclePerm τ) (h2 : τ.partition.parts.card = 2) (x₀ : Fin n) :
    (finRotate n * τ⁻¹).cycleType.card = 1 ∧
      setPartitionGenus τ + 1 + #{x | τ.SameCycle x₀ x ∧ (finRotate n * τ⁻¹) x = x} =
        #{x | τ.SameCycle x₀ x}

/-- The number of genus-`g` set partitions of `Fin n` of type `[p, n - p]` is
`n / (g + 1) * C(p - 1, g) * C(n - p - 1, g)`, halved when `n = 2p`.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Proposition 14
(`jis-2024-24.2.6-prop-14`). -/
public theorem_wanted partitionGenusCount_twoBlocks (n p g : ℕ) (hp : 2 ≤ p) (hpn : p < n) :
    (partitionGenusCount n {p, n - p} g : ℚ) =
      (if n = 2 * p then 1 / 2 else 1) *
        ((n : ℚ) / (g + 1) * ((p - 1).choose g : ℚ) * ((n - p - 1).choose g : ℚ))

end

end MetaMathlibExt
