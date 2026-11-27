/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.LaxApproximation

/-! # Tests for Lax's approximation theorem -/

namespace MathlibExtTest.Dynamics.LaxApproximation

open MeasureTheory MathlibExt.Dynamics.LaxApproximationWanted.Dynamics.LaxApproximation
open scoped ENNReal

/-- The identity of the torus, as a toral dynamical system. -/
private noncomputable def idSystem (d : ℕ) : ToralDynamicalSystem d :=
  ⟨Homeomorph.refl _, MeasurePreserving.id _⟩

/-- A translation of the torus, as a toral dynamical system. -/
private noncomputable def translation {d : ℕ} (c : Torus d) : ToralDynamicalSystem d :=
  ⟨Homeomorph.addRight c, measurePreserving_add_right volume c⟩

-- Every translation of the circle is within `δ`-distance `1/10` of a cyclic cube exchange.
example (c : Torus 1) :
    ∃ (n : ℕ) (S : VolumePreservingEquiv 1),
      IsCyclicCubeExchange S n ∧ deltaDist (translation c).toVolumePreservingEquiv S < 1 / 10 :=
  lax_approximation one_pos (translation c) (by norm_num)

-- In every dimension the identity is a limit of cyclic cube exchanges.
example {d : ℕ} (hd : 0 < d) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (S : VolumePreservingEquiv d),
      IsCyclicCubeExchange S n ∧ deltaDist (idSystem d).toVolumePreservingEquiv S < ε :=
  lax_approximation hd (idSystem d) hε

-- The distance `δ` from a transformation to itself is zero.
example {d : ℕ} (S : VolumePreservingEquiv d) : deltaDist S S = 0 := by
  simp [deltaDist]

-- A toral dynamical system keeps its map when regarded as a volume-preserving transformation.
example {d : ℕ} (T : ToralDynamicalSystem d) (x : Torus d) :
    T.toVolumePreservingEquiv.toMeasurableEquiv x = T.toHomeomorph x :=
  rfl

-- The point `1/4` of the circle lies in the first of the two grid cubes of side `1/2`.
example : (fun _ => ((1 / 4 : ℝ) : AddCircle (1 : ℝ))) ∈ cube 2 (fun _ : Fin 1 => (0 : Fin 2)) :=
  fun _ => ⟨1 / 4, by norm_num, by norm_num, rfl⟩

-- Exchanging the two grid cubes of side `1/2` of the circle shifts the first one by `1/2`.
example :
    cubeShift 2 (Equiv.swap (fun _ : Fin 1 => (0 : Fin 2)) (fun _ => 1)) (fun _ => 0) 0 =
      ((1 / 2 : ℝ) : AddCircle (1 : ℝ)) := by
  simp [cubeShift]

-- With one subdivision the grid has a single cube, and no permutation of it is a cycle.
example {d : ℕ} (S : VolumePreservingEquiv d) : ¬IsCyclicCubeExchange S 1 := by
  rintro ⟨-, σ, hσ, -, -⟩
  exact hσ.ne_one (Subsingleton.elim _ _)

-- In dimension zero there is no cyclic cube exchange, which is why `0 < d` is assumed.
example (S : VolumePreservingEquiv 0) (n : ℕ) : ¬IsCyclicCubeExchange S n := by
  rintro ⟨-, σ, hσ, -, -⟩
  exact hσ.ne_one (Subsingleton.elim _ _)

end MathlibExtTest.Dynamics.LaxApproximation
