/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.C01Stoichiometry

/-!
# Stoichiometric conservation checks

Concrete consumers of `PhyslibExt.EarthScience.C01Stoichiometry`: the
public shape of the conservation theorem, a two-species one-reaction
left-null computation, and the empty system.

## i. Overview

These are elaboration and non-vacuity checks, not new results. The
two-species example has the single reaction converting species `0` into
species `1`; the vector `(1, 1)` is a left-null vector, so the total of
the two concentrations is conserved.

## ii. Key results

No new definitions or results are introduced here.

## iii. References

- `PhyslibExt.EarthScience.C01Stoichiometry`
-/

/-- The public statement shape of stoichiometric conservation. -/
example {n m : ℕ} (S : Fin n → Fin m → ℝ) (l : Fin n → ℝ)
    (c : ℝ → Fin n → ℝ) (rate : (Fin n → ℝ) → Fin m → ℝ) (t : ℝ)
    (hnull : ∀ j, ∑ i, l i * S i j = 0)
    (hode : ∀ i, HasDerivAt (fun t => c t i) (∑ j, S i j * rate (c t) j) t) :
    HasDerivAt (fun t => ∑ i, l i * c t i) 0 t :=
  EarthScience.stoichiometric_leftNull_conserved S l c rate t hnull hode

/-- Two-species, one-reaction conversion: `(1, 1)` is a left-null vector
of `S i 0 = -1` for species `0` and `1` for species `1`, i.e. the
`prod - src` coefficients for species `0` converting into species `1`. -/
example : ∀ _j : Fin 1, ∑ i : Fin 2, (1 : ℝ) * (if i = 0 then (-1 : ℝ) else 1) = 0 := by
  intro _j
  norm_num [Fin.sum_univ_two]

/-- Boundary case: the empty species system has conserved total `0`. -/
example (rate : (Fin 0 → ℝ) → Fin 1 → ℝ) (t : ℝ) :
    HasDerivAt (fun _ : ℝ => ∑ _i : Fin 0, (1 : ℝ) * (0 : ℝ)) 0 t := by
  have h := EarthScience.stoichiometric_leftNull_conserved
    (fun (_ : Fin 0) (_ : Fin 1) => (0 : ℝ)) (fun _ => (1 : ℝ))
    (fun _ _ => (0 : ℝ)) rate t (fun j => by simp) (fun i => Fin.elim0 i)
  simpa using h
