/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RoulettePathLaw
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open RussianRoulette

/-- `listPathWeight` on `[]` is `0`. -/
example (q : Unit → ℝ) (Q : Unit → Unit → ℝ) (i : Unit) :
    listPathWeight q Q i [] = 0 :=
  rfl

/-- `listPathWeight` on a wrong-start singleton is `0`. -/
example (q : Bool → ℝ) (Q : Bool → Bool → ℝ) (i j : Bool) (hne : j ≠ i) :
    listPathWeight q Q i [j] = 0 := by
  have h : listPathWeight q Q i [j]
      = (if j = i then ENNReal.ofReal (q j) else 0) := rfl
  rw [h, ite_eq_right hne]

/-- One-state `q = 1 / 2`: `[x]` has weight `1 / 2`. -/
example : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) () [()]
    = ENNReal.ofReal (1 / 2 : ℝ) := by
  have h : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
        (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) ()
        [()]
      = (if () = () then ENNReal.ofReal (1 / 2 : ℝ) else 0) := rfl
  rw [h, ite_eq_left rfl]

/-- One-state `q = 1 / 2`: `[x, x]` has weight `1 / 4`. -/
example : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) ()
      [(), ()]
    = ENNReal.ofReal (1 / 4 : ℝ) := by
  have h : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
        (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) ()
        [(), ()]
      = (if () = () then ENNReal.ofReal (((1 : ℝ) - 1 / 2) * 1 * (1 / 2))
        else 0) := rfl
  rw [h, ite_eq_left rfl]
  congr 1
  norm_num

/-- `listCompletedWeight_ofFn` at `n = 1` with concrete values. -/
example : listCompletedWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ)))
      (List.ofFn (fun _ : Fin (1 + 1) => ())) = 1 / 4 := by
  rw [listCompletedWeight_ofFn]
  simp only [completedWeight, survivalWeight, stepKernel, Fin.prod_univ_one]
  norm_num

/-- One-state `q = 1`: `[x]` has probability `1`. -/
example : pathPMF (fun _ : Unit => (1 : ℝ)) (fun _ _ => (0 : ℝ)) (1 / 2 : ℝ)
      (by norm_num) (fun _ _ => by norm_num)
      (by intro _; simp) (by intro _; simp) () [()] = 1 := by
  rw [pathPMF_apply]
  have h : listPathWeight (fun _ : Unit => (1 : ℝ)) (fun _ _ => (0 : ℝ)) () [()]
      = (if () = () then ENNReal.ofReal (1 : ℝ) else 0) := rfl
  rw [h, ite_eq_left rfl, ENNReal.ofReal_one]

/-- One-state `q = 1`: `[x, x]` has probability `0`. -/
example : pathPMF (fun _ : Unit => (1 : ℝ)) (fun _ _ => (0 : ℝ)) (1 / 2 : ℝ)
      (by norm_num) (fun _ _ => by norm_num)
      (by intro _; simp) (by intro _; simp) () [(), ()] = 0 := by
  rw [pathPMF_apply]
  have h : listPathWeight (fun _ : Unit => (1 : ℝ)) (fun _ _ => (0 : ℝ)) ()
      [(), ()]
      = (if () = () then ENNReal.ofReal ((0 : ℝ) * 1) else 0) := rfl
  rw [h, ite_eq_left rfl]
  have h0 : ((0 : ℝ) * 1) = 0 := by norm_num
  rw [h0, ENNReal.ofReal_zero]

/-- One-state `q = 1 / 2` via `stepKernel`: `[x]` has probability `1 / 2`. -/
example : pathPMF (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) (1 / 2 : ℝ)
      (by norm_num)
      (by intro a b; unfold stepKernel; norm_num)
      (by intro j; simp [stepKernel])
      (by intro a; simp [stepKernel]; norm_num) () [()]
    = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [pathPMF_apply]
  have h : listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
        (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) () [()]
      = (if () = () then ENNReal.ofReal (1 / 2 : ℝ) else 0) := rfl
  rw [h, ite_eq_left rfl]

/-- Total mass one at `c = 1 / 2`, restated as a `∑'` equality. -/
example : (∑' l : List Unit, listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) () l) = 1 :=
  (hasSum_listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
    (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) (1 / 2 : ℝ)
    (by norm_num)
    (by intro a b; unfold stepKernel; norm_num)
    (by intro j; simp [stepKernel])
    (by intro a; simp [stepKernel]; norm_num) ()).tsum_eq

/-- One-state `q = 1 / 2`: tail at `n = 0` is `1`. -/
example : (∑' l : List Unit, (if 0 < l.length then
      listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) () l
      else 0)) = 1 := by
  rw [tsum_listPathWeight_length_gt (fun _ : Unit => (1 / 2 : ℝ))
    (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) (1 / 2 : ℝ)
    (by norm_num)
    (by intro a b; unfold stepKernel; norm_num)
    (by intro j; simp [stepKernel])
    (by intro a; simp [stepKernel]; norm_num) () 0,
    survivalMass_zero, ENNReal.ofReal_one]

/-- One-state `q = 1 / 2`: tail at `n = 1` is `1 / 2`. -/
example : (∑' l : List Unit, (if 1 < l.length then
      listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) () l
      else 0)) = ENNReal.ofReal (1 / 2 : ℝ) := by
  rw [tsum_listPathWeight_length_gt (fun _ : Unit => (1 / 2 : ℝ))
    (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) (1 / 2 : ℝ)
    (by norm_num)
    (by intro a b; unfold stepKernel; norm_num)
    (by intro j; simp [stepKernel])
    (by intro a; simp [stepKernel]; norm_num) () 1]
  congr 1
  have hsw : ∀ x : Fin (1 + 1) → Unit, survivalWeight
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) x
      = 1 / 2 := by
    intro x
    simp only [survivalWeight, stepKernel, Fin.prod_univ_one]
    norm_num
  unfold survivalMass
  have h : ∀ x : Fin (1 + 1) → Unit, x ≠ (fun _ => ()) →
      (if x 0 = () then (1 / 2 : ℝ) else 0) = 0 := by
    intro x hx
    exfalso
    apply hx
    funext j
    exact Subsingleton.elim _ _
  trans ∑ x : Fin (1 + 1) → Unit, (if x 0 = () then (1 / 2 : ℝ) else 0)
  · apply Finset.sum_congr rfl
    intro x _
    rw [hsw x]
  · rw [Fintype.sum_eq_single _ h]
    simp

/-- One-state `q = 1 / 2`: expected transitions `≤ 1`. -/
example : (∑' l : List Unit, (listPathWeight (fun _ : Unit => (1 / 2 : ℝ)) (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) () l).toReal * ((l.length : ℝ) - 1)) ≤ 1 := by
  have h := tsum_listPathWeight_toReal_length_sub_le (fun _ : Unit => (1 / 2 : ℝ))
    (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) (1 / 2 : ℝ)
    (by norm_num)
    (by intro a b; unfold stepKernel; norm_num)
    (by intro j; simp [stepKernel])
    (by intro a; simp [stepKernel]; norm_num) ()
  have h2 : (1 / 2 : ℝ) / (1 - 1 / 2) = 1 := by norm_num
  rw [h2] at h
  exact h

/-- One-state `q = 1 / 2`: expected trials `≤ 2`. -/
example : (∑' l : List Unit, (listPathWeight (fun _ : Unit => (1 / 2 : ℝ))
      (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) () l).toReal
      * (l.length : ℝ)) ≤ 2 := by
  have h := tsum_listPathWeight_toReal_length_le (fun _ : Unit => (1 / 2 : ℝ))
    (stepKernel (fun _ : Unit => (1 / 2 : ℝ)) (fun _ _ => (1 : ℝ))) (1 / 2 : ℝ)
    (by norm_num)
    (by intro a b; unfold stepKernel; norm_num)
    (by intro j; simp [stepKernel])
    (by intro a; simp [stepKernel]; norm_num) ()
  have h2 : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
  rw [h2] at h
  exact h

end
public section
