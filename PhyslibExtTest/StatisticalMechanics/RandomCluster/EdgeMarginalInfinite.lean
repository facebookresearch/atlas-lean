/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.EdgeMarginalInfinite

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.EdgeMarginalInfinite`

* `mass_eq_of_monotoneCoupling_of_edgeMarg_eq` on `ConfigSpace (Fin 1)` with the diagonal coupling
  of a Bernoulli mass function with itself;
* `infiniteMeasure_eq_of_edgeMarg_eq` for a Dirac measure on `ConfigSpace ℕ` compared with itself
  (`StochasticallyDominated.refl`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeMarginalInfinite

open _root_.StatMech _root_.StatMech.FK MeasureTheory

/-- The Bernoulli mass function on one coordinate: open with probability `1/4`. -/
noncomputable def bern (ω : ConfigSpace (Fin 1)) : ℝ := if ω 0 then 1 / 4 else 3 / 4

/-- The diagonal coupling of `bern` with itself. -/
noncomputable def diag (z : ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) : ℝ :=
  if z.1 = z.2 then bern z.1 else 0

-- A monotone coupling with equal edge marginals forces equal mass functions.
example : bern = bern :=
  mass_eq_of_monotoneCoupling_of_edgeMarg_eq (P := diag)
    { nonneg := fun z => by
        unfold diag bern; split_ifs <;> norm_num
      supportLE := fun z hz => by
        unfold diag; rw [ite_eq_right_iff]; intro h; exact absurd (h ▸ le_rfl) hz
      fst_marginal := fun ω => by simp [diag]
      snd_marginal := fun ω => by simp [diag] }
    (fun _ => rfl)

-- An infinite-volume measure dominated by itself with equal marginals.
example : (Measure.dirac (fun _ => true) : Measure (ConfigSpace ℕ)) =
    Measure.dirac (fun _ => true) :=
  infiniteMeasure_eq_of_edgeMarg_eq _ _ (StochasticallyDominated.refl _) (fun _ => rfl)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeMarginalInfinite
