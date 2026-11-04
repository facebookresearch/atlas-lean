/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RussoFormula

/-!
# Tests for `MathlibExt.Probability.Percolation.RussoFormula`

* `rus_openCount` and `rus_expect_openCount` on two coordinates.
* `rus_russo_formula` applied to the event "coordinate 0 is open" at `p = 1/2` (an event that is
  increasing, so `rus_covariance_eq_sum_pivotalProb` also applies), and to a non-increasing event
  (the covariance form needs no monotonicity).
-/

@[expose] public section

open StatMech StatMech.Percolation

namespace MathlibExtTest.StatMech.Probability.Percolation.RussoFormula

example : rus_openCount (fun _ : Fin 2 => true) = 2 := by
  norm_num [rus_openCount, StatMech.Sharpness.openInd]

example : rus_expect (1 / 3) (rus_openCount (E := Fin 2)) = 2 / 3 := by
  rw [rus_expect_openCount]; norm_num

/-- The event that coordinate `0` is open. -/
def A : Set (ConfigSpace (Fin 2)) := {ω | ω 0 = true}

theorem A_increasing : IsIncreasing A := fun _ _ hle h => by
  simp only [A, Set.mem_ofPred_eq] at h ⊢
  exact (hle 0) h

example : HasDerivAt (fun p => prob p A)
    ((1 / ((1 / 2) * (1 - 1 / 2))) *
      (rus_expect (1 / 2) (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω)
        - rus_expect (1 / 2) (rus_openCount (E := Fin 2)) * prob (1 / 2) A)) (1 / 2) :=
  rus_russo_formula A (by norm_num) (by norm_num)

example : (1 / ((1 / 2 : ℝ) * (1 - 1 / 2))) *
      (rus_expect (1 / 2) (fun ω => rus_openCount ω * A.indicator (fun _ => (1 : ℝ)) ω)
        - rus_expect (1 / 2) (rus_openCount (E := Fin 2)) * prob (1 / 2) A)
      = ∑ e, pivotalProb (1 / 2) A e :=
  rus_covariance_eq_sum_pivotalProb A A_increasing (by norm_num) (by norm_num)

/-- The covariance form also holds for the decreasing event "coordinate 0 is closed". -/
example : HasDerivAt (fun p => prob p {ω : ConfigSpace (Fin 2) | ω 0 = false})
    ((1 / ((1 / 3) * (1 - 1 / 3))) *
      (rus_expect (1 / 3) (fun ω => rus_openCount ω *
          ({ω : ConfigSpace (Fin 2) | ω 0 = false}).indicator (fun _ => (1 : ℝ)) ω)
        - rus_expect (1 / 3) (rus_openCount (E := Fin 2)) *
          prob (1 / 3) {ω : ConfigSpace (Fin 2) | ω 0 = false})) (1 / 3) :=
  rus_russo_formula _ (by norm_num) (by norm_num)

end MathlibExtTest.StatMech.Probability.Percolation.RussoFormula
