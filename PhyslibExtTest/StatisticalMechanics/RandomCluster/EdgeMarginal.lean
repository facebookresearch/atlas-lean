/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.EdgeMarginal

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.EdgeMarginal`

On the one-coordinate space `ConfigSpace (Fin 1)`, with the Bernoulli mass functions `bern (1/4)`
and `bern (3/4)` (the coordinate is open with probability `1/4` resp. `3/4`):
* `eventMassProb` and `edgeMargProb` evaluate to `1/4` resp. `3/4` on "the coordinate is open";
* `IsMonotoneCouplingFun` holds for an explicit coupling `P` (mass `1/4, 1/2, 1/4` on the pairs
  `(0, 0)`, `(0, 1)`, `(1, 1)`), so the structure is satisfiable with distinct marginals;
* `coupling_eventMass_le` applies to `P`, and `eventMass_eq_of_edgeMarg_eq` applies to the
  diagonal coupling of `bern (1/4)` with itself.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeMarginal

open _root_.StatMech _root_.StatMech.FK

/-- A sum over configurations of one coordinate is a sum over the two values. -/
theorem sum_fin1 (f : ConfigSpace (Fin 1) → ℝ) :
    ∑ ω, f ω = f (fun _ => false) + f (fun _ => true) := by
  rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool, add_comm]
  rfl

/-- The Bernoulli mass function on one coordinate: open with probability `a`. -/
noncomputable def bern (a : ℝ) (ω : ConfigSpace (Fin 1)) : ℝ := if ω 0 then a else 1 - a

/-- The event "the coordinate is open". -/
def open0 : Set (ConfigSpace (Fin 1)) := {ω | ω 0 = true}

/-- "The coordinate is open" is increasing. -/
theorem open0_isIncreasing : IsIncreasing open0 := by
  intro x y hxy hx
  have h := hxy 0
  simp only [open0, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

-- The mass of "open" under `bern (1/4)` is `1/4`.
example : eventMassProb (bern (1 / 4)) open0 = 1 / 4 := by
  rw [eventMassProb, sum_fin1]
  norm_num [open0, bern]

-- The edge marginal of `bern (3/4)` is `3/4`.
example : edgeMargProb (bern (3 / 4)) 0 = 3 / 4 := by
  rw [edgeMargProb, sum_fin1]
  norm_num [bern]

/-- The coupling weights: `1/4` on `(0, 0)`, `1/2` on `(0, 1)`, `1/4` on `(1, 1)`. -/
noncomputable def cw : Bool → Bool → ℝ
  | false, false => 1 / 4
  | false, true => 1 / 2
  | true, true => 1 / 4
  | true, false => 0

/-- An explicit monotone coupling of `bern (1/4)` and `bern (3/4)`. -/
noncomputable def P (z : ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) : ℝ := cw (z.1 0) (z.2 0)

/-- `P` is a monotone coupling of `bern (1/4)` and `bern (3/4)`. -/
theorem P_isMonotoneCoupling : IsMonotoneCouplingFun P (bern (1 / 4)) (bern (3 / 4)) where
  nonneg z := by
    unfold P; cases z.1 0 <;> cases z.2 0 <;> norm_num [cw]
  supportLE z hz := by
    rcases z with ⟨a, b⟩
    have hab : ¬ a 0 ≤ b 0 := fun h => hz fun i => by rw [Subsingleton.elim i 0]; exact h
    unfold P
    cases ha : a 0 <;> cases hb : b 0 <;> simp_all [cw]
  fst_marginal ω := by
    rw [sum_fin1]; unfold P bern; cases h : ω 0 <;> norm_num [h, cw]
  snd_marginal ω := by
    rw [sum_fin1]; unfold P bern; cases h : ω 0 <;> norm_num [h, cw]

-- The coupling gives the stochastic comparison of the event "open".
example : eventMassProb (bern (1 / 4)) open0 ≤ eventMassProb (bern (3 / 4)) open0 :=
  coupling_eventMass_le P_isMonotoneCoupling open0_isIncreasing

/-- The diagonal coupling of a mass function with itself. -/
noncomputable def diag (μ : ConfigSpace (Fin 1) → ℝ)
    (z : ConfigSpace (Fin 1) × ConfigSpace (Fin 1)) : ℝ :=
  if z.1 = z.2 then μ z.1 else 0

-- Equal edge marginals and the diagonal coupling give equal masses of increasing events.
example : eventMassProb (bern (1 / 4)) open0 = eventMassProb (bern (1 / 4)) open0 :=
  eventMass_eq_of_edgeMarg_eq (P := diag (bern (1 / 4)))
    { nonneg := fun z => by
        unfold diag bern; split_ifs <;> norm_num
      supportLE := fun z hz => by
        unfold diag; rw [ite_eq_right_iff]; intro h; exact absurd (h ▸ le_rfl) hz
      fst_marginal := fun ω => by simp [diag]
      snd_marginal := fun ω => by simp [diag] }
    (fun _ => rfl) open0_isIncreasing

end PhyslibExtTest.StatisticalMechanics.RandomCluster.EdgeMarginal
