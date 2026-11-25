/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.NatCard
public import MathlibExt.GroupTheory.IntWordMetric
public import MathlibExt.GroupTheory.HyperbolicGroup
public import MathlibExt.Topology.MetricSpace.GromovHyperbolicTriangles

/-!
# First examples of hyperbolic groups

* Finite groups are word-hyperbolic: their word metrics are bounded, and a bounded space is
  hyperbolic (Gromov, *Hyperbolic groups*, 1987, §1.2(b)).
* The word metric of the infinite cyclic group `Multiplicative ℤ` for the generator `ofAdd 1`
  (`MathlibExt.GroupTheory.IntWordMetric`) is isometric to `ℤ ⊆ ℝ`, so it is `0`-hyperbolic
  (§1.2(a)).

These are the non-degenerate test instances for the hypotheses of the main theorems on hyperbolic
groups.

## Main results

* `Group.IsHyperbolic.of_finite`: a finite group is word-hyperbolic.
* `Group.isHyperbolic_multiplicative_int`: `Multiplicative ℤ` is word-hyperbolic.
-/

@[expose] public section

open Metric

namespace Group

/-- **Finite groups are word-hyperbolic.** Every finite group is word-hyperbolic: for a finite
generating family the word metric is bounded, and a bounded metric space is hyperbolic (Gromov,
*Hyperbolic groups*, 1987, §1.2(b)). -/
theorem IsHyperbolic.of_finite (G : Type*) [Group G] [Finite G] : IsHyperbolic G := by
  classical
  let e := Finite.equivFin G
  let P : Group.Generators G (Fin (Nat.card G)) :=
    ⟨e.symm, by rw [Equiv.range_eq_univ, Subgroup.closure_univ]⟩
  have := Fintype.ofFinite G
  let M : ℕ := Finset.univ.sup fun g => P.wordLength g
  refine ⟨Fin (Nat.card G), inferInstance, P, M, ?_⟩
  let _ := P.normedGroup
  refine isDeltaHyperbolic_of_forall_dist_le (Nat.cast_nonneg M) fun g h => ?_
  rw [dist_eq_norm_inv_mul]
  change (P.wordLength (g⁻¹ * h) : ℝ) ≤ M
  exact_mod_cast Finset.le_sup (f := fun g => P.wordLength g) (Finset.mem_univ (g⁻¹ * h))

/-- **Word metrics isometric to a hyperbolic space are hyperbolic.** If `f : G → X` satisfies
`d(f g, f h) = |g⁻¹ h|_P` for all `g h` and `X` is `δ`-hyperbolic, then `G` with the word metric
of `P` is `δ`-hyperbolic. -/
theorem isDeltaHyperbolic_of_dist_eq_wordLength {G ι X : Type*} [Group G] [PseudoMetricSpace X]
    (P : Generators G ι) (f : G → X)
    (hf : ∀ g h : G, dist (f g) (f h) = (P.wordLength (g⁻¹ * h) : ℝ)) {δ : ℝ}
    (h : IsDeltaHyperbolic X δ) :
    @IsDeltaHyperbolic G P.normedGroup.toPseudoMetricSpace δ := by
  let _ := P.normedGroup
  exact h.of_isometry (Isometry.of_dist_eq fun g h => by rw [hf, dist_eq_norm_inv_mul]; rfl)

/-- **The infinite cyclic group is word-hyperbolic.** For the generator `ofAdd 1`, the word metric
of `Multiplicative ℤ` is `d(ofAdd m, ofAdd n) = |m - n|`, isometric to `ℤ ⊆ ℝ`, hence `0`-hyperbolic
(Gromov, *Hyperbolic groups*, 1987, §1.2(a)). -/
theorem isHyperbolic_multiplicative_int : IsHyperbolic (Multiplicative ℤ) := by
  refine ⟨Unit, inferInstance, Generators.intGenerators, 0,
    isDeltaHyperbolic_of_dist_eq_wordLength Generators.intGenerators
      (fun g => ((Multiplicative.toAdd g : ℤ) : ℝ)) (fun g h => ?_) isDeltaHyperbolic_real⟩
  rw [Real.dist_eq, ← ofAdd_toAdd (g⁻¹ * h), Generators.wordLength_intGenerators, toAdd_mul,
    toAdd_inv, Nat.cast_natAbs]
  push_cast
  rw [abs_sub_comm]
  ring_nf

end Group
