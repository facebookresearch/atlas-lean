/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Dynamics.Ergodic.BernoulliNonisomorphism

open MeasureTheory ProbabilityTheory
open MathlibExt.Dynamics.Ergodic.BernoulliShift MathlibExt.Dynamics.Ergodic.KolmogorovSinaiEntropy
open MathlibExt.Dynamics.KolmogorovSinaiWanted

-- A conjugacy in the reverse direction, with the shifts written coordinatewise, is impossible.
example : ¬ IsIsomorphicMod0
    (Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set (Fin 2)))
    (fun x n => x (n + 1))
    (Measure.infinitePi fun _ : ℕ => uniformOn (Set.univ : Set (Fin 3)))
    (fun x n => x (n + 1)) := by
  have hs (S : Type) : (fun (x : ℕ → S) n => x (n + 1)) = shift :=
    funext fun x => funext fun n => (shift_apply x n).symm
  rw [hs, hs]
  rintro ⟨π, ρ, hπ, hρ, hleft, hright, hπshift, hρshift⟩
  exact not_isomorphic_bernoulli_uniform_three_two
    ⟨ρ, π, hρ, hπ, hright, hleft, hρshift, hπshift⟩
