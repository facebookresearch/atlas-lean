/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import MathlibExt.ControlTheory.StateSpace.Coefficients

/-!
# Zone thermal RC network as a state-space plant

The lumped multizone thermal RC network, driven by the outside temperature and
the zone heating powers, as a linear state-space plant.

## i. Overview

Finitely many well-mixed zones `i : ι` with constant heat capacities `C i`,
inter-zone conductances `G i j`, boundary conductances `g0 i` to the outside,
zone temperatures `T i t`, outside temperature `Tout t` and heating powers
`P i t`. The zone equations are those of the zone-network results: the
equation of `ZoneHeatInventory.heat_inventory_deriv`
(`PhyslibExt/Engineering/ZoneHeatInventory.lean`) with boundary input
`b i t = g0 i * (Tout t - T i t)`, which is the equation of
`ZoneHeatInventory.quadratic_dissipation_deriv`
(`PhyslibExt/Engineering/ZoneQuadraticDissipation.lean`) with its constant
outside reference made a time-dependent input:
`C i * T i' = (∑ j, G i j * (T j - T i)) + g0 i * (Tout - T i) + P i`.

State: the zone temperatures `fun i => T i t` in `ι → ℝ`. Input in
`Unit ⊕ ι → ℝ`, written `Sum.elim (fun _ => Tout t) (fun i => P i t)`
(`Sum.inl ()` the outside temperature, `Sum.inr i` the heating power of zone
`i`). Output: the zone temperatures, in `ι → ℝ`. Dividing zone equation `i`
by the fixed positive capacity `C i` gives the plant row. The outside
temperature enters zone `i` with gain `+g0 i / C i`, and the same conductance
leaves through the diagonal of the state matrix with `-g0 i / C i`, so with no
heating the uniform state at a constant outside temperature is at rest;
heating power enters only its own zone, with gain `+1 / C i`.

Units (any consistent set, e.g. SI): temperatures in kelvin (only differences
enter, so degrees Celsius also work), `C i` in J/K, `G i j` and `g0 i` in W/K,
`P i` in W; the state matrix and the outside column of the input matrix are
rates (1/s), the heater block is in K/J. Physical domain `C i > 0`,
`G i j = G j i ≥ 0`, `g0 i ≥ 0`. A link of thermal resistance `R i j > 0` has
`G i j = 1 / R i j`, and `G i j = 0` means no direct link; resistances enter
only through these conductances. Only `0 < C i` is a premise; the
correspondence holds for all real `G` and `g0`, and the diagonal entries
`G i i` cancel.

Plant shape (API lock): the shape of the base-excited oscillator plant
(`PhyslibExt/ClassicalMechanics/RelativeOscillatorPlant.lean`): four
matrices, the owner record built from them, and one matrix-vector trajectory
correspondence. Trajectory semantics (API lock): the owner record is
`ControlTheory.StateSpaceCoeffs`, built from matrices by
`StateSpaceCoeffs.ofMatrix A B C D`. The owner has no continuous-time
trajectory predicate, so the trajectory condition is stated inline as in
`MathlibExt.Analysis.Control.IsControllableOn`:
`∀ t, HasDerivAt z (S.A (z t) + S.B (w t)) t`, here in matrix-vector form for
all real times `t`.

Totalized division: `1 / C i` is `0` at `C i = 0`, where row `i` of the plant
matrices vanishes and the correspondence fails; the target assumes `0 < C i`
for all `i`. Classical solutions: each side asks for `HasDerivAt` at every
time and nothing more; no continuity of `Tout` or `P` is assumed or
concluded.

The scope is the state-space form of the zone equations with its trajectory
correspondence. Excluded: a new state-space type or trajectory predicate, a
control framework, stability, decay or convergence theorems, an observer,
numerical integration, existence or uniqueness of solutions, the quadratic
functional and its dissipation identity, and any reading of a quadratic
functional as stored thermal energy.

## ii. Key results

- `ZoneHeatInventory.thermalA`, `thermalB`, `thermalC`, `thermalD`,
  `thermalPlant`: the plant matrices and the owner record built from them.
- `ZoneHeatInventory.thermal_trajectory_iff`: plant trajectories are exactly
  the solutions of the zone equations.

## iii. Table of contents

- A. The thermal plant and its trajectory correspondence

## iv. References

- `ZoneHeatInventory.heat_inventory_deriv`
  (`PhyslibExt/Engineering/ZoneHeatInventory.lean`) and
  `ZoneHeatInventory.quadratic_dissipation_deriv`
  (`PhyslibExt/Engineering/ZoneQuadraticDissipation.lean`): the zone
  equations.
- `ControlTheory.StateSpaceCoeffs`
  (`MathlibExt/ControlTheory/StateSpace/Coefficients.lean`): the owner
  coefficient record.
- `RelativeOscillator.baseExcitedPlant` and
  `RelativeOscillator.baseExcited_trajectory_iff`
  (`PhyslibExt/ClassicalMechanics/RelativeOscillatorPlant.lean`): the plant
  shape and trajectory convention.
-/

@[expose] public section

namespace ZoneHeatInventory

open Matrix

/-! ## A. The thermal plant and its trajectory correspondence -/

/-- State matrix of the zone network, acting on the vector of zone temperatures: row `i` is
zone equation `i` without its input terms, divided by `C i`, so entry `(i, j)` is
`(G i j - if i = j then (∑ k, G i k) + g0 i else 0) / C i` and the diagonal conductance
`G i i` cancels. Meaningful for `C i > 0`; at `C i = 0` the totalized division makes row `i`
zero. Without self-links the inner matrix is the negative of
`PhyslibExt.Mechanics.HarmonicMechanics.stiffnessMatrix G g0`; here `G i i`
cancels, while there it stays on the diagonal. -/
noncomputable def thermalA {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → ℝ)
    (G : ι → ι → ℝ) (g0 : ι → ℝ) : Matrix ι ι ℝ :=
  diagonal (fun i => 1 / C i) * (of G - diagonal fun i => (∑ j, G i j) + g0 i)

/-- Input matrix `diagonal (1 / C) * [g0 | 1]` for the input `(Tout, P)`: the outside
temperature (column `Sum.inl ()`) enters zone `i` with gain `g0 i / C i`, and the heating
power of zone `j` (column `Sum.inr j`) enters zone `j` alone, with gain `1 / C j`.
Meaningful for `C i > 0`. -/
noncomputable def thermalB {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → ℝ)
    (g0 : ι → ℝ) : Matrix ι (Unit ⊕ ι) ℝ :=
  diagonal (fun i => 1 / C i) * fromCols (replicateCol Unit g0) 1

/-- Output matrix `1`: the output is the vector of zone temperatures. -/
def thermalC {ι : Type*} [DecidableEq ι] : Matrix ι ι ℝ :=
  1

/-- Feedthrough matrix `0`: the input does not reach the output directly. -/
def thermalD {ι : Type*} : Matrix ι (Unit ⊕ ι) ℝ :=
  0

/-- The zone thermal network as an owner state-space record: the four matrices
assembled by `ControlTheory.StateSpaceCoeffs.ofMatrix`, with state the zone
temperatures, input the outside temperature and heating powers, and output the
zone temperatures. -/
noncomputable def thermalPlant {ι : Type*} [Fintype ι] [DecidableEq ι] (C : ι → ℝ)
    (G : ι → ι → ℝ) (g0 : ι → ℝ) :
    ControlTheory.StateSpaceCoeffs ℝ (ι → ℝ) (Unit ⊕ ι → ℝ) (ι → ℝ) :=
  ControlTheory.StateSpaceCoeffs.ofMatrix (thermalA C G g0) (thermalB C g0) thermalC
    thermalD

private lemma thermalA_mulVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ}
    {G : ι → ι → ℝ} {g0 : ι → ℝ} (x : ι → ℝ) (i : ι) :
    (thermalA C G g0 *ᵥ x) i
      = (1 / C i) * ((∑ j, G i j * x j) - ((∑ j, G i j) + g0 i) * x i) := by
  unfold thermalA
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Matrix.sub_mulVec, Pi.sub_apply,
    Matrix.mulVec_diagonal]
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.of_apply]

private lemma thermalB_mulVec_apply {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ}
    {g0 : ι → ℝ} (u : Unit → ℝ) (v : ι → ℝ) (i : ι) :
    (thermalB C g0 *ᵥ Sum.elim u v) i = (1 / C i) * (g0 i * u () + v i) := by
  unfold thermalB
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, Matrix.fromCols_mulVec_sumElim,
    Pi.add_apply, Matrix.one_mulVec]
  simp only [Matrix.mulVec_apply_eq_sum, Matrix.replicateCol_apply]
  rw [show (∑ _j : Unit, g0 i * u _j) = g0 i * u () from Fintype.sum_unique _]

/-- **State-space form of the zone thermal network** (trajectory correspondence, and the
physical-to-canonical bridge). Let `C i > 0` in every zone. The curve `s ↦ fun i => T i s` is
a trajectory of the plant `(thermalA C G g0, thermalB C g0)` driven by the input
`s ↦ Sum.elim (fun _ => Tout s) (fun i => P i s)` if and only if, at every time `t` and in
every zone `i`, `T i` has a derivative `Tv` at `t` with
`C i * Tv = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout t - T i t) + P i t`. Then `Tv` is
the derivative of `T i` at `t`, so the right side says that `T` solves the zone equations
with boundary input `g0 i * (Tout - T i)` and heating power `P i`. For the owner record `S`
that `StateSpaceCoeffs.ofMatrix` builds from the four pinned matrices, the inline trajectory
condition on the owner record (the convention of
`MathlibExt.Analysis.Control.IsControllableOn`; the record itself carries no trajectory
semantics), `∀ t, HasDerivAt z (S.A (z t) + S.B (w t)) t` for `z = fun s i => T i s` and
`w = fun s => Sum.elim (fun _ => Tout s) (fun i => P i s)`, reduces to the left side by
`simp only [ofMatrix_A_apply, ofMatrix_B_apply]`. Physical domain `C i > 0`,
`G i j = G j i ≥ 0`, `g0 i ≥ 0` (positive thermal resistances `1 / G i j` and `1 / g0 i`
where a path exists); the equivalence holds for all real `G` and `g0`. -/
theorem thermal_trajectory_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {C : ι → ℝ}
    {G : ι → ι → ℝ} {g0 : ι → ℝ} (hC : ∀ i, 0 < C i) (T : ι → ℝ → ℝ) (Tout : ℝ → ℝ)
    (P : ι → ℝ → ℝ) :
    (∀ t, HasDerivAt (fun s i => T i s)
        (thermalA C G g0 *ᵥ (fun i => T i t) +
          thermalB C g0 *ᵥ Sum.elim (fun _ => Tout t) (fun i => P i t)) t) ↔
      ∀ t i, ∃ Tv, HasDerivAt (T i) Tv t ∧
        C i * Tv = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout t - T i t) + P i t := by
  have hfield : ∀ (t : ℝ) (i : ι),
      (thermalA C G g0 *ᵥ (fun i => T i t) +
          thermalB C g0 *ᵥ Sum.elim (fun _ => Tout t) (fun i => P i t)) i
      = (1 / C i) * ((∑ j, G i j * T j t) - ((∑ j, G i j) + g0 i) * T i t
        + (g0 i * Tout t + P i t)) := by
    intro t i
    simp only [Pi.add_apply, thermalA_mulVec_apply, thermalB_mulVec_apply]
    ring
  have hsum : ∀ (t : ℝ) (i : ι), (∑ j, G i j * (T j t - T i t))
      = (∑ j, G i j * T j t) - (∑ j, G i j) * T i t := by
    intro t i
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hscalar : ∀ (t : ℝ) (i : ι), C i * ((1 / C i) *
        ((∑ j, G i j * T j t) - ((∑ j, G i j) + g0 i) * T i t
          + (g0 i * Tout t + P i t)))
      = (∑ j, G i j * (T j t - T i t)) + g0 i * (Tout t - T i t) + P i t := by
    intro t i
    have hCi : C i ≠ 0 := ne_of_gt (hC i)
    have h1 : C i * (1 / C i) = 1 := mul_one_div_cancel hCi
    rw [← mul_assoc, h1, one_mul, hsum t i]
    ring
  constructor
  · intro h t i
    have hi := (hasDerivAt_pi.mp (h t)) i
    rw [hfield t i] at hi
    exact ⟨_, hi, hscalar t i⟩
  · intro h t
    rw [hasDerivAt_pi]
    intro i
    obtain ⟨Tv, hTvd, heq⟩ := h t i
    rw [hfield t i]
    have hCi : C i ≠ 0 := ne_of_gt (hC i)
    have h2 : C i * Tv = C i * ((1 / C i) *
        ((∑ j, G i j * T j t) - ((∑ j, G i j) + g0 i) * T i t
          + (g0 i * Tout t + P i t))) := by
      rw [heq]
      exact (hscalar t i).symm
    have hTv : Tv = (1 / C i) *
        ((∑ j, G i j * T j t) - ((∑ j, G i j) + g0 i) * T i t
          + (g0 i * Tout t + P i t)) :=
      mul_left_cancel₀ hCi h2
    rw [← hTv]
    exact hTvd


end ZoneHeatInventory
