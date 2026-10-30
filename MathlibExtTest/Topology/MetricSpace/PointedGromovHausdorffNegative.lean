/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import MathlibExt.Topology.MetricSpace.PointedGromovHausdorff
/-! Negative tests for pointed Gromov–Hausdorff convergence. -/
namespace PointedGromovHausdorffNegativeTests
def twoPt (a : ℝ) : Set ℝ := {0, a}
def pt0 (a : ℝ) : ↥(twoPt a) := ⟨0, by simp [twoPt]⟩
def ptA (a : ℝ) : ↥(twoPt a) := ⟨a, by simp [twoPt]⟩
def threePt : Set ℝ := {0, 1, 3}
def q0 : ↥threePt := ⟨0, by simp [threePt]⟩
def q1 : ↥threePt := ⟨1, by simp [threePt]⟩
def q3 : ↥threePt := ⟨3, by simp [threePt]⟩
theorem coe_pt0 (a : ℝ) : ((pt0 a) : ℝ) = 0 := rfl
theorem coe_ptA (a : ℝ) : ((ptA a) : ℝ) = a := rfl
theorem coe_q0 : ((q0) : ℝ) = 0 := rfl
theorem coe_q1 : ((q1) : ℝ) = 1 := rfl
theorem coe_q3 : ((q3) : ℝ) = 3 := rfl
theorem mem_twoPt_iff (a : ℝ) (x : ↥(twoPt a)) :
    (x : ℝ) = 0 ∨ (x : ℝ) = a := by
  simpa [twoPt] using x.2
theorem mem_threePt_iff (x : ↥threePt) :
    (x : ℝ) = 0 ∨ (x : ℝ) = 1 ∨ (x : ℝ) = 3 := by
  simpa [threePt] using x.2
theorem dist_pts {a x y : ℝ} {u v : ↥(twoPt a)} (hx : (u : ℝ) = x)
    (hy : (v : ℝ) = y) : dist u v = |x - y| := by
  rw [Subtype.dist_eq, Real.dist_eq, hx, hy]
theorem dist_pts3 {x y : ℝ} {u v : ↥threePt} (hx : (u : ℝ) = x)
    (hy : (v : ℝ) = y) : dist u v = |x - y| := by
  rw [Subtype.dist_eq, Real.dist_eq, hx, hy]
theorem pt0_mem_ball {a R : ℝ} (h : 0 < R) :
    pt0 a ∈ Metric.ball (pt0 a) R := by
  rw [Metric.mem_ball, dist_pts (coe_pt0 a) (coe_pt0 a), sub_self, abs_zero]
  exact h
theorem pt0_mem_closedBall {a R : ℝ} (h : 0 ≤ R) :
    pt0 a ∈ Metric.closedBall (pt0 a) R := by
  rw [Metric.mem_closedBall, dist_pts (coe_pt0 a) (coe_pt0 a), sub_self, abs_zero]
  exact h
theorem ptA_mem_closedBall {a R : ℝ} (h : |a| ≤ R) :
    ptA a ∈ Metric.closedBall (pt0 a) R := by
  rw [Metric.mem_closedBall, dist_pts (coe_ptA a) (coe_pt0 a), sub_zero]
  exact h
theorem pair_cover_fails {a r : ℝ} (h : r ≤ |a|) {D : Type} {F : D → ↥(twoPt a)}
    {d : ↥(twoPt a)} (hsingle : ∀ x, F x = d) {C : Set ↥(twoPt a)}
    (h0 : pt0 a ∈ C) (h1 : ptA a ∈ C) :
    ¬ (C ⊆ Metric.thickening r (Set.range F)) := by
  intro hsub
  rcases mem_twoPt_iff a d with hd | hd
  · obtain ⟨z, hz, hlt⟩ := Metric.mem_thickening_iff.mp (hsub h1)
    obtain ⟨x, rfl⟩ := hz
    rw [hsingle x, dist_pts (coe_ptA a) hd, sub_zero] at hlt
    linarith
  · obtain ⟨z, hz, hlt⟩ := Metric.mem_thickening_iff.mp (hsub h0)
    obtain ⟨x, rfl⟩ := hz
    rw [hsingle x, dist_pts (coe_pt0 a) hd, zero_sub, abs_neg] at hlt
    linarith
theorem T3_closedBall_criterion_fails {R : ℝ} (hR : 0 < R) (k : ℕ)
    (g : ↥(Metric.closedBall (pt0 (R + 1 / ((k : ℝ) + 1))) R) → ↥(Metric.closedBall (pt0 R) R)) :
    ¬ (Metric.closedBall (pt0 R) R ⊆
      Metric.thickening (R / 2) (Set.range fun x => ((g x : ↥(twoPt R))))) := by
  have hdom : ∀ x : ↥(Metric.closedBall (pt0 (R + 1 / ((k : ℝ) + 1))) R),
      ((x : ↥(twoPt (R + 1 / ((k : ℝ) + 1)))) : ℝ) = 0 := by
    intro x
    rcases mem_twoPt_iff _ (x : ↥(twoPt (R + 1 / ((k : ℝ) + 1)))) with h | h
    · exact h
    · exfalso
      have hm : (x : ↥(twoPt (R + 1 / ((k : ℝ) + 1)))) ∈
          Metric.closedBall (pt0 (R + 1 / ((k : ℝ) + 1))) R := x.2
      rw [Metric.mem_closedBall, dist_pts h (coe_pt0 _)] at hm
      have ht : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      rw [sub_zero, abs_of_pos (by linarith)] at hm
      linarith
  have hmemD : pt0 (R + 1 / ((k : ℝ) + 1)) ∈
      Metric.closedBall (pt0 (R + 1 / ((k : ℝ) + 1))) R :=
    pt0_mem_closedBall (le_of_lt hR)
  have hxeq : ∀ x : ↥(Metric.closedBall (pt0 (R + 1 / ((k : ℝ) + 1))) R),
      x = ⟨pt0 (R + 1 / ((k : ℝ) + 1)), hmemD⟩ :=
    fun x => Subtype.ext (Subtype.ext (hdom x))
  have hsingle : ∀ x : ↥(Metric.closedBall (pt0 (R + 1 / ((k : ℝ) + 1))) R),
      ((g x : ↥(twoPt R))) =
        ((g ⟨pt0 (R + 1 / ((k : ℝ) + 1)), hmemD⟩ : ↥(twoPt R))) := fun x => by
    rw [hxeq x]
  have h0 : pt0 R ∈ Metric.closedBall (pt0 R) R :=
    pt0_mem_closedBall (le_of_lt hR)
  have h1 : ptA R ∈ Metric.closedBall (pt0 R) R :=
    ptA_mem_closedBall (by rw [abs_of_pos hR])
  intro hsub
  have hr : R / 2 ≤ |R| := by rw [abs_of_pos hR]; linarith
  exact pair_cover_fails hr hsingle h0 h1 hsub
theorem T4_distortion :
    ¬ GromovHausdorff.PointedGHConverges (X := fun _ => ↥(twoPt 1))
      (fun _ => pt0 1) (pt0 0) := by
  intro h
  obtain ⟨n, hn⟩ := (h 2 (by norm_num) (1 / 2) (by norm_num)).exists
  obtain ⟨f, hbase, hdist, _⟩ := hn
  have m0 : pt0 (1 : ℝ) ∈ Metric.ball (pt0 1) 2 := pt0_mem_ball (by norm_num)
  have m1 : ptA (1 : ℝ) ∈ Metric.ball (pt0 1) 2 := by
    rw [Metric.mem_ball, dist_pts (coe_ptA 1) (coe_pt0 1), sub_zero]
    norm_num
  have hfx0 : f ⟨pt0 1, m0⟩ = pt0 (0 : ℝ) := hbase
  have hfx1 : f ⟨ptA 1, m1⟩ = pt0 (0 : ℝ) := Subtype.ext (by
    rcases mem_twoPt_iff 0 (f ⟨ptA 1, m1⟩) with h | h <;> exact h)
  have hkey : |dist (f ⟨pt0 1, m0⟩) (f ⟨ptA 1, m1⟩) - dist (pt0 1) (ptA 1)| ≤
    (1 / 2 : ℝ) := hdist _ _
  rw [hfx0, hfx1, dist_pts (coe_pt0 0) (coe_pt0 0), sub_self, abs_zero,
    dist_pts (coe_pt0 1) (coe_ptA 1)] at hkey
  norm_num at hkey
theorem T5_coverage :
    ¬ GromovHausdorff.PointedGHConverges (X := fun _ => ↥(twoPt 0))
      (fun _ => pt0 0) (pt0 1) := by
  intro h
  obtain ⟨n, hn⟩ := (h 2 (by norm_num) (1 / 2) (by norm_num)).exists
  obtain ⟨f, _, _, hcov⟩ := hn
  have hmemD : pt0 (0 : ℝ) ∈ Metric.ball (pt0 0) 2 := pt0_mem_ball (by norm_num)
  have hdom0 : ∀ x : ↥(Metric.ball (pt0 (0 : ℝ)) 2), ((x : ↥(twoPt 0)) : ℝ) = 0 := by
    intro x
    rcases mem_twoPt_iff 0 (x : ↥(twoPt 0)) with h | h <;> exact h
  have hxeq : ∀ x : ↥(Metric.ball (pt0 (0 : ℝ)) 2), x = ⟨pt0 0, hmemD⟩ :=
    fun x => Subtype.ext (Subtype.ext (hdom0 x))
  have hsingle : ∀ x : ↥(Metric.ball (pt0 (0 : ℝ)) 2), f x = f ⟨pt0 0, hmemD⟩ :=
    fun x => by rw [hxeq x]
  have m0 : pt0 (1 : ℝ) ∈ Metric.ball (pt0 1) (2 - 1 / 2) := by
    rw [Metric.mem_ball, dist_pts (coe_pt0 1) (coe_pt0 1), sub_self, abs_zero]
    norm_num
  have m1 : ptA (1 : ℝ) ∈ Metric.ball (pt0 1) (2 - 1 / 2) := by
    rw [Metric.mem_ball, dist_pts (coe_ptA 1) (coe_pt0 1), sub_zero]
    norm_num
  exact pair_cover_fails (by norm_num) hsingle m0 m1 hcov
theorem T6_basepoint :
    ¬ GromovHausdorff.PointedGHConverges (X := fun _ => ↥threePt)
      (fun _ => q0) q3 := by
  intro h
  obtain ⟨n, hn⟩ := (h 2 (by norm_num) (1 / 2) (by norm_num)).exists
  obtain ⟨f, hbase, hdist, _⟩ := hn
  have m0 : q0 ∈ Metric.ball q0 2 := by
    rw [Metric.mem_ball, dist_pts3 coe_q0 coe_q0, sub_self, abs_zero]
    norm_num
  have m1 : q1 ∈ Metric.ball q0 2 := by
    rw [Metric.mem_ball, dist_pts3 coe_q1 coe_q0, sub_zero]
    norm_num
  have hfb : f ⟨q0, m0⟩ = q3 := hbase
  have hkey : |dist (f ⟨q0, m0⟩) (f ⟨q1, m1⟩) - dist q0 q1| ≤ (1 / 2 : ℝ) :=
    hdist _ _
  rw [hfb, dist_pts3 coe_q0 coe_q1] at hkey
  rcases mem_threePt_iff (f ⟨q1, m1⟩) with hw | hw | hw <;>
    rw [dist_pts3 coe_q3 hw] at hkey <;> norm_num at hkey
theorem T7_limit_distance {R : ℝ} (hR : 0 < R) :
    ¬ GromovHausdorff.PointedGHConverges
      (X := fun n : ℕ => ↥(twoPt (R + 1 / ((n : ℝ) + 1))))
      (fun n => pt0 (R + 1 / ((n : ℝ) + 1))) (pt0 (R + 1)) := by
  intro h
  have hRd : (0 : ℝ) < R + 2 := by linarith
  have heps : (0 : ℝ) < min R (1 / 2) / 2 := by
    linarith [lt_min hR (show (0 : ℝ) < 1 / 2 by norm_num)]
  have hev := h (R + 2) hRd (min R (1 / 2) / 2) heps
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N1, hN1⟩ := hev
  have hfrac : 1 / (((N1 + 1 : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
    have hcast : (1 : ℝ) ≤ ((N1 + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le N1)
    rw [div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨f, hbase, hdist, _⟩ := hN1 (N1 + 1) (Nat.le_succ N1)
  set aN : ℝ := R + 1 / (((N1 + 1 : ℕ) : ℝ) + 1) with haNdef
  have ht : (0 : ℝ) < 1 / (((N1 + 1 : ℕ) : ℝ) + 1) := by positivity
  have haNpos : (0 : ℝ) < aN := by linarith
  have m0 : pt0 aN ∈ Metric.ball (pt0 aN) (R + 2) := pt0_mem_ball hRd
  have m1 : ptA aN ∈ Metric.ball (pt0 aN) (R + 2) := by
    rw [Metric.mem_ball, dist_pts (coe_ptA aN) (coe_pt0 aN), sub_zero, abs_of_pos haNpos]
    linarith
  have hfb : f ⟨pt0 aN, m0⟩ = pt0 (R + 1) := hbase
  have edom : dist (ptA aN) (pt0 aN) = aN := by
    rw [dist_pts (coe_ptA aN) (coe_pt0 aN), sub_zero, abs_of_pos haNpos]
  have hkey : |dist (f ⟨ptA aN, m1⟩) (f ⟨pt0 aN, m0⟩) - dist (ptA aN) (pt0 aN)| ≤
    min R (1 / 2) / 2 := hdist _ _
  rw [hfb, edom] at hkey
  rcases mem_twoPt_iff (R + 1) (f ⟨ptA aN, m1⟩) with hd | hd
  · have eimg : dist (f ⟨ptA aN, m1⟩) (pt0 (R + 1)) = 0 := by
      rw [dist_pts hd (coe_pt0 _), sub_self, abs_zero]
    rw [eimg, zero_sub, abs_neg, abs_of_pos haNpos] at hkey
    have hmin : min R (1 / 2) ≤ R := min_le_left R (1 / 2)
    linarith
  · have eimg : dist (f ⟨ptA aN, m1⟩) (pt0 (R + 1)) = R + 1 := by
      rw [dist_pts hd (coe_pt0 _), sub_zero, abs_of_pos (by linarith)]
    rw [eimg, show (R + 1) - aN = 1 - 1 / (((N1 + 1 : ℕ) : ℝ) + 1) by rw [haNdef]; ring,
      abs_of_pos (by linarith)] at hkey
    have hmin : min R (1 / 2) ≤ 1 / 2 := min_le_right R (1 / 2)
    linarith
end PointedGromovHausdorffNegativeTests
