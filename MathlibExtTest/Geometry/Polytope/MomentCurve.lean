/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Polytope.MomentCurve

@[expose] public section

open MathlibExt.Geometry.Polytope

namespace MathlibExtTest.Geometry.Polytope.MomentCurve

/-- Parameters `0 < 1 < 2 < 3` on the moment curve. -/
noncomputable abbrev t4 : Fin 4 → ℝ := fun i => (i : ℝ)

theorem t4_strictMono : StrictMono t4 := fun a b h => by
  simp only [t4, Nat.cast_lt]
  exact h

/-- Three points `γ(0), γ(1), γ(2)` of the moment curve in `ℝ^2` are affinely independent. -/
example : AffineIndependent ℝ (fun i : Fin 3 => momentCurve 2 (t4 (Fin.castSucc i))) :=
  affineIndependent_momentCurve le_rfl (t4_strictMono.injective.comp (Fin.castSucc_injective 3))

/-- Gale's evenness condition on concrete index sets. -/
example : GaleEvenness ({0, 1} : Finset (Fin 4)) := by decide
example : GaleEvenness ({1, 2} : Finset (Fin 4)) := by decide
example : GaleEvenness ({0, 3} : Finset (Fin 4)) := by decide
example : ¬ GaleEvenness ({0, 2} : Finset (Fin 4)) := by decide
example : GaleEvenness ({0, 1, 3, 4} : Finset (Fin 6)) := by decide
example : ¬ GaleEvenness ({0, 2, 3, 4} : Finset (Fin 6)) := by decide

end MathlibExtTest.Geometry.Polytope.MomentCurve
