/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.ContinuousRectangleCrossing
import Code.FK.PeriodicPlanarSheffieldHalfPlaneCage












open Set SimpleGraph Topology
open scoped unitInterval

namespace StatMech

namespace Lattice

open ContinuousRectangleCrossing



def halfPlaneReturnPath (alpha c d : Int) (hcd : c <= d) :
    (hypercubicLattice 2).Walk ![alpha, d] ![alpha, c] :=
  let top : (hypercubicLattice 2).Walk ![alpha, d] ![alpha - 1, d] :=
    ((jec_hsegRight d (alpha - 1) 1).copy rfl
      (by ext i; fin_cases i <;> simp)).reverse
  let side : (hypercubicLattice 2).Walk ![alpha - 1, d] ![alpha - 1, c] :=
    ((jec_vsegUp (alpha - 1) c (d - c).toNat).copy rfl
      (by ext i; fin_cases i <;> (simp; try omega))).reverse
  let bottom : (hypercubicLattice 2).Walk ![alpha - 1, c] ![alpha, c] :=
    (jec_hsegRight c (alpha - 1) 1).copy rfl
      (by ext i; fin_cases i <;> simp)
  top.append (side.append bottom)



theorem jec_rayCount_halfPlaneReturnPath
    (alpha c d e : Int) (hcd : c <= d) (hce : c < e) (hed : e < d) :
    jec_rayCount ![alpha, e] (halfPlaneReturnPath alpha c d hcd) = 1 := by
  unfold halfPlaneReturnPath
  simp only [jec_rayCount_append, jec_rayCount_copy, jec_rayCount_reverse,
    jec_rayCount_hsegRight, jec_rayCount_vsegUp,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (((d - c).toNat : Nat) : Int) = d - c by omega]
  rw [if_pos (by omega)]



theorem mem_halfPlaneReturnPath_of_coord_ge
    (alpha c d : Int) (hcd : c <= d) {z : Site 2}
    (hz : z ∈ (halfPlaneReturnPath alpha c d hcd).support)
    (hz0 : alpha <= z 0) : z = ![alpha, d] ∨ z = ![alpha, c] := by
  unfold halfPlaneReturnPath at hz
  simp only [Walk.mem_support_append_iff, Walk.support_copy,
    Walk.support_reverse, List.mem_reverse] at hz
  rcases hz with hz | hz | hz
  · obtain ⟨h1, h0lo, h0hi⟩ := jec_hsegRight_support d (alpha - 1) 1 hz
    have h0 : z 0 = alpha := by omega
    left
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  · obtain ⟨h0, _, _⟩ := jec_vsegUp_support (alpha - 1) c _ hz
    omega
  · obtain ⟨h1, h0lo, h0hi⟩ := jec_hsegRight_support c (alpha - 1) 1 hz
    have h0 : z 0 = alpha := by omega
    right
    ext i
    fin_cases i
    · simpa using h0
    · simpa using h1



theorem halfPlaneReturnPath_coord_le
    (alpha c d : Int) (hcd : c <= d) {z : Site 2}
    (hz : z ∈ (halfPlaneReturnPath alpha c d hcd).support) :
    z 0 <= alpha := by
  unfold halfPlaneReturnPath at hz
  simp only [Walk.mem_support_append_iff, Walk.support_copy,
    Walk.support_reverse, List.mem_reverse] at hz
  rcases hz with hz | hz | hz
  · simpa using (jec_hsegRight_support d (alpha - 1) 1 hz).2.2
  · have h0 := (jec_vsegUp_support (alpha - 1) c _ hz).1
    omega
  · simpa using (jec_hsegRight_support c (alpha - 1) 1 hz).2.2



theorem halfPlaneReturnPath_vertical_bounds
    (alpha c d : Int) (hcd : c <= d) {z : Site 2}
    (hz : z ∈ (halfPlaneReturnPath alpha c d hcd).support) :
    c <= z 1 ∧ z 1 <= d := by
  unfold halfPlaneReturnPath at hz
  simp only [Walk.mem_support_append_iff, Walk.support_copy,
    Walk.support_reverse, List.mem_reverse] at hz
  rcases hz with hz | hz | hz
  · have h1 := (jec_hsegRight_support d (alpha - 1) 1 hz).1
    omega
  · have h := (jec_vsegUp_support (alpha - 1) c (d - c).toNat hz).2
    rw [show (((d - c).toNat : Nat) : Int) = d - c by omega] at h
    simpa using h
  · have h1 := (jec_hsegRight_support c (alpha - 1) 1 hz).1
    omega


theorem jec_rayCount_eq_zero_of_support_below
    (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (h : ∀ p ∈ w.support, p 1 < z 1) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro edge hedge
  obtain ⟨u, v⟩ := edge
  have hu := h u (w.fst_mem_support_of_mem_edges hedge)
  have hv := h v (w.snd_mem_support_of_mem_edges hedge)
  simp only [decide_eq_true_eq]
  change ¬jec_rayEdge z s(u, v)
  rw [jec_rayEdge_mk]
  omega


theorem jec_rayCount_eq_zero_of_support_above
    (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (h : ∀ p ∈ w.support, z 1 < p 1) :
    jec_rayCount z w = 0 := by
  classical
  rw [jec_rayCount, List.countP_eq_zero]
  intro edge hedge
  obtain ⟨u, v⟩ := edge
  have hu := h u (w.fst_mem_support_of_mem_edges hedge)
  have hv := h v (w.snd_mem_support_of_mem_edges hedge)
  simp only [decide_eq_true_eq]
  change ¬jec_rayEdge z s(u, v)
  rw [jec_rayEdge_mk]
  omega



theorem jec_rayParity_eq_along_walk {a x y : Site 2}
    (loop : (hypercubicLattice 2).Walk a a)
    (p : (hypercubicLattice 2).Walk x y)
    (hdisj : ∀ z, z ∈ p.support -> z ∉ loop.support) :
    (Even (jec_rayCount x loop) <-> Even (jec_rayCount y loop)) := by
  induction p with
  | nil => rfl
  | @cons x y z hxy p ih =>
      have hx : x ∉ loop.support :=
        hdisj x (by simp)
      have hy : y ∉ loop.support :=
        hdisj y (by simp)
      exact (jec_localConstancy loop hxy hx hy).trans
        (ih (fun w hw => hdisj w (by simp [hw])))





theorem halfPlane_walks_intersect
    (alpha c d e beta f : Int) (hce : c < e) (hed : e < d)
    (crosscut : (hypercubicLattice 2).Walk ![alpha, c] ![alpha, d])
    (escape : (hypercubicLattice 2).Walk ![alpha, e] ![beta, f])
    (hcrossLeft : ∀ z, z ∈ crosscut.support -> alpha <= z 0)
    (hcrossRight : ∀ z, z ∈ crosscut.support -> z 0 < beta)
    (hescapeLeft : ∀ z, z ∈ escape.support -> alpha <= z 0) :
    ∃ z, z ∈ crosscut.support ∧ z ∈ escape.support := by
  by_contra hnone
  push Not at hnone
  have hcd : c <= d := (hce.trans hed).le
  let ret := halfPlaneReturnPath alpha c d hcd
  let loop : (hypercubicLattice 2).Walk ![alpha, c] ![alpha, c] :=
    crosscut.append ret
  have hescapeCross : ∀ z, z ∈ escape.support ->
      z ∉ crosscut.support := by
    intro z hzE hzC
    exact hnone z hzC hzE
  have hescapeRet : ∀ z, z ∈ escape.support -> z ∉ ret.support := by
    intro z hzE hzR
    rcases mem_halfPlaneReturnPath_of_coord_ge alpha c d hcd hzR
        (hescapeLeft z hzE) with rfl | rfl
    · exact hnone _ crosscut.end_mem_support hzE
    · exact hnone _ crosscut.start_mem_support hzE
  have hescapeLoop : ∀ z, z ∈ escape.support -> z ∉ loop.support := by
    intro z hzE
    change z ∉ (crosscut.append ret).support
    rw [Walk.mem_support_append_iff]
    push Not
    exact ⟨hescapeCross z hzE, hescapeRet z hzE⟩
  have hstartOdd : ¬ Even (jec_rayCount ![alpha, e] loop) := by
    change ¬ Even (jec_rayCount ![alpha, e] (crosscut.append ret))
    rw [jec_rayCount_append]
    have hcrossZero : jec_rayCount ![alpha, e] crosscut = 0 := by
      apply jec_rayCount_eq_zero_of_right
      intro z hz
      simpa using hcrossLeft z hz
    rw [hcrossZero, jec_rayCount_halfPlaneReturnPath alpha c d e hcd hce hed]
    decide
  have halphaBeta : alpha < beta := by
    have := hcrossRight _ crosscut.start_mem_support
    simpa using this
  have hendEven : Even (jec_rayCount ![beta, f] loop) := by
    change Even (jec_rayCount ![beta, f] (crosscut.append ret))
    apply jec_ray_even_far
    intro z hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · have := hcrossRight z hz
      simpa using this
    · have := halfPlaneReturnPath_coord_le alpha c d hcd hz
      simp only [Matrix.cons_val_zero]
      omega
  exact hstartOdd ((jec_rayParity_eq_along_walk loop escape hescapeLoop).2 hendEven)



theorem halfPlane_walks_intersect_of_endpoint_outside
    (alpha c d e beta f : Int) (hce : c < e) (hed : e < d)
    (crosscut : (hypercubicLattice 2).Walk ![alpha, c] ![alpha, d])
    (escape : (hypercubicLattice 2).Walk ![alpha, e] ![beta, f])
    (hcrossLeft : ∀ z, z ∈ crosscut.support -> alpha <= z 0)
    (hescapeLeft : ∀ z, z ∈ escape.support -> alpha <= z 0)
    (houtside :
      (∀ z, z ∈ crosscut.support -> z 0 < beta) ∨
      (∀ z, z ∈ crosscut.support -> z 1 < f) ∨
      (∀ z, z ∈ crosscut.support -> f < z 1)) :
    ∃ z, z ∈ crosscut.support ∧ z ∈ escape.support := by
  by_contra hnone
  push Not at hnone
  have hcd : c <= d := (hce.trans hed).le
  let ret := halfPlaneReturnPath alpha c d hcd
  let loop : (hypercubicLattice 2).Walk ![alpha, c] ![alpha, c] :=
    crosscut.append ret
  have hescapeCross : ∀ z, z ∈ escape.support ->
      z ∉ crosscut.support := by
    intro z hzE hzC
    exact hnone z hzC hzE
  have hescapeRet : ∀ z, z ∈ escape.support -> z ∉ ret.support := by
    intro z hzE hzR
    rcases mem_halfPlaneReturnPath_of_coord_ge alpha c d hcd hzR
        (hescapeLeft z hzE) with rfl | rfl
    · exact hnone _ crosscut.end_mem_support hzE
    · exact hnone _ crosscut.start_mem_support hzE
  have hescapeLoop : ∀ z, z ∈ escape.support -> z ∉ loop.support := by
    intro z hzE
    change z ∉ (crosscut.append ret).support
    rw [Walk.mem_support_append_iff]
    push Not
    exact ⟨hescapeCross z hzE, hescapeRet z hzE⟩
  have hstartOdd : ¬Even (jec_rayCount ![alpha, e] loop) := by
    change ¬Even (jec_rayCount ![alpha, e] (crosscut.append ret))
    rw [jec_rayCount_append]
    have hcrossZero : jec_rayCount ![alpha, e] crosscut = 0 := by
      apply jec_rayCount_eq_zero_of_right
      intro z hz
      simpa using hcrossLeft z hz
    rw [hcrossZero, jec_rayCount_halfPlaneReturnPath alpha c d e hcd hce hed]
    decide
  have hendEven : Even (jec_rayCount ![beta, f] loop) := by
    change Even (jec_rayCount ![beta, f] (crosscut.append ret))
    rcases houtside with hright | habove | hbelow
    · apply jec_ray_even_far
      intro z hz
      rw [Walk.mem_support_append_iff] at hz
      rcases hz with hz | hz
      · simpa using hright z hz
      · have halphaBeta : alpha < beta := by
          simpa using hright _ crosscut.start_mem_support
        have := halfPlaneReturnPath_coord_le alpha c d hcd hz
        simp only [Matrix.cons_val_zero]
        omega
    · have hzero : jec_rayCount ![beta, f]
          (crosscut.append ret) = 0 := by
        apply jec_rayCount_eq_zero_of_support_below
        intro z hz
        rw [Walk.mem_support_append_iff] at hz
        rcases hz with hz | hz
        · simpa using habove z hz
        · have hdf : d < f := by
            simpa using habove _ crosscut.end_mem_support
          exact (halfPlaneReturnPath_vertical_bounds alpha c d hcd hz).2.trans_lt hdf
      rw [hzero]
      exact ⟨0, by norm_num⟩
    · have hzero : jec_rayCount ![beta, f]
          (crosscut.append ret) = 0 := by
        apply jec_rayCount_eq_zero_of_support_above
        intro z hz
        rw [Walk.mem_support_append_iff] at hz
        rcases hz with hz | hz
        · simpa using hbelow z hz
        · have hfc : f < c := by
            simpa using hbelow _ crosscut.start_mem_support
          exact hfc.trans_le
            (halfPlaneReturnPath_vertical_bounds alpha c d hcd hz).1
      rw [hzero]
      exact ⟨0, by norm_num⟩
  exact hstartOdd
    ((jec_rayParity_eq_along_walk loop escape hescapeLoop).2 hendEven)

end Lattice

namespace ContinuousHalfPlaneCrosscut

open Lattice ContinuousRectangleCrossing



theorem gridConnector_coord_ge {alpha : Int} {x y z : Site 2}
    (hx : alpha <= x 0) (hy : alpha <= y 0)
    (hz : z ∈ (gridConnector x y).support) : alpha <= z 0 := by
  rw [gridConnector_mem_support] at hz
  rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hat : alpha <= t := by
      rw [Set.mem_uIcc] at ht
      rcases ht with ht | ht <;> omega
    simpa using hat
  · simpa using hy


theorem gridWalk_coord_ge {alpha : Int} {g : Nat -> Site 2} {N : Nat}
    (hg : ∀ k, k <= N -> alpha <= g k 0) {z : Site 2}
    (hz : z ∈ (gridWalk g N).support) : alpha <= z 0 := by
  rcases gridWalk_mem_support_cases g N z hz with rfl | ⟨k, hk, hzk⟩
  · exact hg 0 (Nat.zero_le _)
  · exact gridConnector_coord_ge (hg k hk.le) (hg (k + 1) hk) hzk



theorem sampledGrid_walk_coord_ge_source
    {p q : Fin 2 -> Real} (gamma : Path p q)
    (hgamma : ∀ t : unitInterval, p 0 <= gamma t 0)
    {n N : Nat} (hN : 0 < N) {z : Site 2}
    (hz : z ∈ (gridWalk (sampledGrid n N hN gamma) N).support) :
    gridFloor n p 0 <= z 0 := by
  apply gridWalk_coord_ge (N := N) (g := sampledGrid n N hN gamma) _ hz
  intro k hk
  rw [sampledGrid_eq n N hN gamma hk]
  apply Int.floor_mono
  exact mul_le_mul_of_nonneg_left (hgamma _) (Nat.cast_nonneg n)



theorem gridFloor_coord_lt_of_two_mesh_lt
    {n : Nat} (hn : 0 < n) {p q : Fin 2 -> Real} {i : Fin 2}
    (hgap : 2 / (n : Real) < q i - p i) :
    gridFloor n p i < gridFloor n q i := by
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hp := gridFloor_error hn p i
  have hq := gridFloor_error hn q i
  rw [abs_lt] at hp hq
  have hembed : gridEmbed n (gridFloor n p) i <
      gridEmbed n (gridFloor n q) i := by
    rw [div_eq_mul_inv] at hgap hp hq
    linarith
  simp only [gridEmbed] at hembed
  rw [div_lt_div_iff_of_pos_right hnR] at hembed
  exact_mod_cast hembed






theorem wholeArc_intersects_escape_of_margin_outside
    {lo hi root far : Fin 2 -> Real}
    (crosscut : Path lo hi) (escape : Path root far)
    (hloRootX : lo 0 = root 0) (hhiRootX : hi 0 = root 0)
    (hloRootY : lo 1 < root 1) (hrootHiY : root 1 < hi 1)
    (hcrossLeft : ∀ t : unitInterval, lo 0 <= crosscut t 0)
    (hescapeLeft : ∀ t : unitInterval, root 0 <= escape t 0)
    {margin : Real} (hmargin : 0 < margin)
    (houtside :
      (∀ t : unitInterval, crosscut t 0 + margin < far 0) ∨
      (∀ t : unitInterval, crosscut t 1 + margin < far 1) ∨
      (∀ t : unitInterval, far 1 + margin < crosscut t 1)) :
    ∃ t s : unitInterval, crosscut t = escape s := by
  by_contra hnone
  have hcrossCompact : IsCompact (Set.range crosscut) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image crosscut.continuous)
  have hescapeCompact : IsCompact (Set.range escape) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image escape.continuous)
  have hrangeDisj : Disjoint (Set.range crosscut) (Set.range escape) := by
    rw [Set.disjoint_left]
    intro x hx hy
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨s, hs⟩ := hy
    exact hnone ⟨t, s, hs.symm⟩
  obtain ⟨rho, hrho, hsep⟩ := Metric.exists_pos_forall_lt_edist
    hcrossCompact hescapeCompact.isClosed hrangeDisj
  have hrhoR : (0 : Real) < (rho : Real) := by exact_mod_cast hrho
  let delta : Real := min ((rho : Real) / 6)
    (min ((root 1 - lo 1) / 2)
      (min ((hi 1 - root 1) / 2) (margin / 4)))
  have hdelta : 0 < delta := by
    dsimp only [delta]
    rw [lt_min_iff, lt_min_iff, lt_min_iff]
    constructor
    · positivity
    constructor
    · linarith
    constructor <;> linarith
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hdelta
  let n := m + 1
  have hn : 0 < n := by simp [n]
  have hmesh : 1 / (n : Real) < delta := by
    simpa [n] using hm
  have hrhoMesh : 6 / (n : Real) < (rho : Real) := by
    have := hmesh.trans_le (min_le_left _ _)
    rw [div_eq_mul_inv] at this ⊢
    norm_num at this ⊢
    linarith
  have hloMesh : 2 / (n : Real) < root 1 - lo 1 := by
    have := hmesh.trans_le
      ((min_le_right _ _).trans (min_le_left _ _))
    rw [div_eq_mul_inv] at this ⊢
    norm_num at this ⊢
    linarith
  have hhiMesh : 2 / (n : Real) < hi 1 - root 1 := by
    have := hmesh.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [div_eq_mul_inv] at this ⊢
    norm_num at this ⊢
    linarith
  have hmarginMesh : 4 / (n : Real) < margin := by
    have := hmesh.trans_le
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [div_eq_mul_inv] at this ⊢
    norm_num at this ⊢
    linarith
  obtain ⟨NC, hNC, hfineC⟩ := exists_fine_sampling crosscut hn
  obtain ⟨NE, hNE, hfineE⟩ := exists_fine_sampling escape hn
  let C0 := gridWalk (sampledGrid n NC hNC crosscut) NC
  let E0 := gridWalk (sampledGrid n NE hNE escape) NE
  let alpha := gridFloor n lo 0
  let c := gridFloor n lo 1
  let d := gridFloor n hi 1
  let e := gridFloor n root 1
  let beta := gridFloor n far 0
  let f := gridFloor n far 1
  have hCsrc : sampledGrid n NC hNC crosscut 0 = ![alpha, c] := by
    rw [sampledGrid_zero]
    funext i
    fin_cases i <;> rfl
  have hCtgt : sampledGrid n NC hNC crosscut NC = ![alpha, d] := by
    rw [sampledGrid_self]
    funext i
    fin_cases i
    · simp [alpha, gridFloor, hhiRootX, hloRootX]
    · rfl
  have hEsrc : sampledGrid n NE hNE escape 0 = ![alpha, e] := by
    rw [sampledGrid_zero]
    funext i
    fin_cases i
    · simp [alpha, gridFloor, hloRootX]
    · rfl
  have hEtgt : sampledGrid n NE hNE escape NE = ![beta, f] := by
    rw [sampledGrid_self]
    funext i
    fin_cases i <;> rfl
  let C : (hypercubicLattice 2).Walk ![alpha, c] ![alpha, d] :=
    C0.copy hCsrc hCtgt
  let E : (hypercubicLattice 2).Walk ![alpha, e] ![beta, f] :=
    E0.copy hEsrc hEtgt
  have hce : c < e := by
    exact gridFloor_coord_lt_of_two_mesh_lt hn hloMesh
  have hed : e < d := by
    exact gridFloor_coord_lt_of_two_mesh_lt hn hhiMesh
  have hCLeft : ∀ z, z ∈ C.support -> alpha <= z 0 := by
    intro z hz
    apply sampledGrid_walk_coord_ge_source crosscut hcrossLeft hNC
    simpa [C, C0] using hz
  have hELeft : ∀ z, z ∈ E.support -> alpha <= z 0 := by
    intro z hz
    have hrootSource : ∀ t : unitInterval, root 0 <= escape t 0 := hescapeLeft
    have := sampledGrid_walk_coord_ge_source escape hrootSource hNE
      (by simpa [E, E0] using hz)
    change ⌊(n : Real) * lo 0⌋ <= z 0
    change ⌊(n : Real) * root 0⌋ <= z 0 at this
    rw [hloRootX]
    exact this
  have hCOutside :
      (∀ z, z ∈ C.support -> z 0 < beta) ∨
      (∀ z, z ∈ C.support -> z 1 < f) ∨
      (∀ z, z ∈ C.support -> f < z 1) := by
    rcases houtside with hright | habove | hbelow
    · left
      intro z hz
      have hz0 : z ∈ C0.support := by simpa [C] using hz
      obtain ⟨t, ht⟩ := sampledGrid_walk_near crosscut hn hNC hfineC
        (by simpa [C0] using hz0)
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      have ht0 : |gridEmbed n z 0 - crosscut t 0| < 3 / (n : Real) := by
        rw [dist_pi_lt_iff (by positivity)] at ht
        simpa [Real.dist_eq] using ht 0
      have hfarErr := gridFloor_error hn far 0
      rw [abs_lt] at ht0 hfarErr
      have hreal : gridEmbed n z 0 < gridEmbed n (gridFloor n far) 0 := by
        have := hright t
        rw [div_eq_mul_inv] at ht0 hfarErr hmarginMesh
        linarith
      simp only [gridEmbed] at hreal
      rw [div_lt_div_iff_of_pos_right hnR] at hreal
      exact_mod_cast hreal
    · right; left
      intro z hz
      have hz0 : z ∈ C0.support := by simpa [C] using hz
      obtain ⟨t, ht⟩ := sampledGrid_walk_near crosscut hn hNC hfineC
        (by simpa [C0] using hz0)
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      have ht1 : |gridEmbed n z 1 - crosscut t 1| < 3 / (n : Real) := by
        rw [dist_pi_lt_iff (by positivity)] at ht
        simpa [Real.dist_eq] using ht 1
      have hfarErr := gridFloor_error hn far 1
      rw [abs_lt] at ht1 hfarErr
      have hreal : gridEmbed n z 1 < gridEmbed n (gridFloor n far) 1 := by
        have := habove t
        rw [div_eq_mul_inv] at ht1 hfarErr hmarginMesh
        linarith
      simp only [gridEmbed] at hreal
      rw [div_lt_div_iff_of_pos_right hnR] at hreal
      exact_mod_cast hreal
    · right; right
      intro z hz
      have hz0 : z ∈ C0.support := by simpa [C] using hz
      obtain ⟨t, ht⟩ := sampledGrid_walk_near crosscut hn hNC hfineC
        (by simpa [C0] using hz0)
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      have ht1 : |gridEmbed n z 1 - crosscut t 1| < 3 / (n : Real) := by
        rw [dist_pi_lt_iff (by positivity)] at ht
        simpa [Real.dist_eq] using ht 1
      have hfarErr := gridFloor_error hn far 1
      rw [abs_lt] at ht1 hfarErr
      have hreal : gridEmbed n (gridFloor n far) 1 < gridEmbed n z 1 := by
        have := hbelow t
        rw [div_eq_mul_inv] at ht1 hfarErr hmarginMesh
        linarith
      simp only [gridEmbed] at hreal
      rw [div_lt_div_iff_of_pos_right hnR] at hreal
      exact_mod_cast hreal
  obtain ⟨z, hzC, hzE⟩ := halfPlane_walks_intersect_of_endpoint_outside
    alpha c d e beta f hce hed C E hCLeft hELeft hCOutside
  have hzC0 : z ∈ C0.support := by simpa [C] using hzC
  have hzE0 : z ∈ E0.support := by simpa [E] using hzE
  obtain ⟨t, ht⟩ := sampledGrid_walk_near crosscut hn hNC hfineC
    (by simpa [C0] using hzC0)
  obtain ⟨s, hs⟩ := sampledGrid_walk_near escape hn hNE hfineE
    (by simpa [E0] using hzE0)
  have hsepTS : (rho : Real) < dist (crosscut t) (escape s) := by
    have hsepE : (rho : ENNReal) < edist (crosscut t) (escape s) :=
      hsep (crosscut t) ⟨t, rfl⟩ (escape s) ⟨s, rfl⟩
    have h := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top
      (edist_ne_top (crosscut t) (escape s))).2 hsepE
    simpa [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
  have hclose : dist (crosscut t) (escape s) < 6 / (n : Real) := by
    calc
      dist (crosscut t) (escape s) <=
          dist (crosscut t) (gridEmbed n z) +
            dist (gridEmbed n z) (escape s) := dist_triangle _ _ _
      _ < 3 / (n : Real) + 3 / (n : Real) :=
        add_lt_add (by simpa [_root_.dist_comm] using ht) hs
      _ = 6 / (n : Real) := by ring
  linarith



theorem wholeArc_intersects_escape
    {lo hi root far : Fin 2 -> Real}
    (crosscut : Path lo hi) (escape : Path root far)
    (hloRootX : lo 0 = root 0) (hhiRootX : hi 0 = root 0)
    (hloRootY : lo 1 < root 1) (hrootHiY : root 1 < hi 1)
    (hcrossLeft : ∀ t : unitInterval, lo 0 <= crosscut t 0)
    (hescapeLeft : ∀ t : unitInterval, root 0 <= escape t 0)
    {margin : Real} (hmargin : 0 < margin)
    (hfar : ∀ t : unitInterval, crosscut t 0 + margin < far 0) :
    ∃ t s : unitInterval, crosscut t = escape s := by
  exact wholeArc_intersects_escape_of_margin_outside crosscut escape
    hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft
      hmargin (Or.inl hfar)



theorem wholeArc_intersects_escape_of_far
    {lo hi root far : Fin 2 -> Real}
    (crosscut : Path lo hi) (escape : Path root far)
    (hloRootX : lo 0 = root 0) (hhiRootX : hi 0 = root 0)
    (hloRootY : lo 1 < root 1) (hrootHiY : root 1 < hi 1)
    (hcrossLeft : ∀ t : unitInterval, lo 0 <= crosscut t 0)
    (hescapeLeft : ∀ t : unitInterval, root 0 <= escape t 0)
    (hfar : ∀ t : unitInterval, crosscut t 0 < far 0) :
    ∃ t s : unitInterval, crosscut t = escape s := by
  obtain ⟨tmax, _htmax, hmax⟩ := isCompact_univ.exists_isMaxOn
    Set.univ_nonempty
    (show Continuous (fun t : unitInterval => crosscut t 0) by fun_prop).continuousOn
  let margin := (far 0 - crosscut tmax 0) / 2
  have hmargin : 0 < margin := by
    dsimp only [margin]
    linarith [hfar tmax]
  apply wholeArc_intersects_escape crosscut escape
    hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft hmargin
  intro t
  have hle := hmax (Set.mem_univ t)
  change crosscut t 0 <= crosscut tmax 0 at hle
  dsimp only [margin]
  linarith [hfar tmax]



theorem wholeArc_intersects_escape_of_outside
    {lo hi root far : Fin 2 -> Real}
    (crosscut : Path lo hi) (escape : Path root far)
    (hloRootX : lo 0 = root 0) (hhiRootX : hi 0 = root 0)
    (hloRootY : lo 1 < root 1) (hrootHiY : root 1 < hi 1)
    (hcrossLeft : ∀ t : unitInterval, lo 0 <= crosscut t 0)
    (hescapeLeft : ∀ t : unitInterval, root 0 <= escape t 0)
    (houtside :
      (∀ t : unitInterval, crosscut t 0 < far 0) ∨
      (∀ t : unitInterval, crosscut t 1 < far 1) ∨
      (∀ t : unitInterval, far 1 < crosscut t 1)) :
    ∃ t s : unitInterval, crosscut t = escape s := by
  rcases houtside with hright | habove | hbelow
  · exact wholeArc_intersects_escape_of_far crosscut escape
      hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft hright
  · obtain ⟨tmax, _htmax, hmax⟩ := isCompact_univ.exists_isMaxOn
      Set.univ_nonempty
      (show Continuous (fun t : unitInterval => crosscut t 1) by fun_prop).continuousOn
    let margin := (far 1 - crosscut tmax 1) / 2
    have hmargin : 0 < margin := by
      dsimp only [margin]
      linarith [habove tmax]
    apply wholeArc_intersects_escape_of_margin_outside crosscut escape
      hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft hmargin
    right; left
    intro t
    have hle := hmax (Set.mem_univ t)
    change crosscut t 1 <= crosscut tmax 1 at hle
    dsimp only [margin]
    linarith [habove tmax]
  · obtain ⟨tmin, _htmin, hmin⟩ := isCompact_univ.exists_isMinOn
      Set.univ_nonempty
      (show Continuous (fun t : unitInterval => crosscut t 1) by fun_prop).continuousOn
    let margin := (crosscut tmin 1 - far 1) / 2
    have hmargin : 0 < margin := by
      dsimp only [margin]
      linarith [hbelow tmin]
    apply wholeArc_intersects_escape_of_margin_outside crosscut escape
      hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft hmargin
    right; right
    intro t
    have hle := hmin (Set.mem_univ t)
    change crosscut tmin 1 <= crosscut t 1 at hle
    dsimp only [margin]
    linarith [hbelow tmin]

end ContinuousHalfPlaneCrosscut

namespace FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair





theorem exists_open_graphWalk_to_exposedRectExit
    (D : PeriodicPlanarDualPair P Pdual)
    (eta : ConfigSpace (Sym2 W))
    {r right bottom top : Real} {x : W}
    (hxRect : x ∈ D.dualEmbedding.rectVertices r right bottom top)
    (hinfinite : (Pdual.clusterWithinSet eta
      (D.dualEmbedding.rightHalfPlaneVertices r) x).Infinite) :
    ∃ z : W, ∃ q : Pdual.graph.Walk x z,
      ¬q.Nil ∧
      (∀ v ∈ q.support,
        v ∈ D.dualEmbedding.rightHalfPlaneVertices r) ∧
      (∀ {u v : W}, s(u, v) ∈ q.edges -> eta s(u, v) = true) ∧
      (right < D.dualEmbedding.vertexCoord z 0 ∨
        D.dualEmbedding.vertexCoord z 1 < bottom ∨
        top < D.dualEmbedding.vertexCoord z 1) := by
  obtain ⟨v, _hvRect, z, hvz, hzHalfPlane, hzOutside, q, hq⟩ :=
    D.dualEmbedding.exists_open_exposedRectExit_of_rightHalfPlane_cluster
      eta hxRect hinfinite
  let last : (Pdual.openSubgraph eta).Walk v z :=
    (SimpleGraph.Walk.nil : (Pdual.openSubgraph eta).Walk z z).cons hvz
  let qOpen : (Pdual.openSubgraph eta).Walk x z := q.append last
  obtain ⟨qG, hsupport, hopen⟩ :=
    Pdual.openSubgraphWalk_exists_graphWalk eta qOpen
  have hxz : x ≠ z := by
    intro hxz
    subst z
    rcases hzOutside with hright | hbottom | htop
    · exact (not_lt_of_ge hxRect.2.1) hright
    · exact (not_lt_of_ge hxRect.2.2.1) hbottom
    · exact (not_lt_of_ge hxRect.2.2.2) htop
  refine ⟨z, qG, SimpleGraph.Walk.not_nil_of_ne hxz, ?_, hopen, hzOutside⟩
  intro w hw
  have hwOpen : w ∈ qOpen.support := by rwa [← hsupport]
  change w ∈ (q.append last).support at hwOpen
  rw [SimpleGraph.Walk.mem_support_append_iff] at hwOpen
  rcases hwOpen with hw | hw
  · exact (hq w hw).1
  · dsimp only [last] at hw
    rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at hw
    have hvHalfPlane := (hq v q.end_mem_support).1
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hvHalfPlane
    · have hwz : w = z := by simpa using hw
      exact hwz.symm ▸ hzHalfPlane




structure WholeArcBoundaryPlacement
    (D : PeriodicPlanarDualPair P Pdual)
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b) : Prop where
  lower_boundary : D.primalEmbedding.vertexCoord x 0 =
    D.dualEmbedding.vertexCoord a 0
  upper_boundary : D.primalEmbedding.vertexCoord y 0 =
    D.dualEmbedding.vertexCoord a 0
  root_above_lower : D.primalEmbedding.vertexCoord x 1 <
    D.dualEmbedding.vertexCoord a 1
  root_below_upper : D.dualEmbedding.vertexCoord a 1 <
    D.primalEmbedding.vertexCoord y 1
  primal_in_halfPlane : ∀ t : unitInterval,
    D.primalEmbedding.vertexCoord x 0 <=
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p t) 0
  dual_in_halfPlane : ∀ t : unitInterval,
    D.dualEmbedding.vertexCoord a 0 <=
      D.dualEmbedding.coordinates
        (D.dualEmbedding.simpleWalkArc q t) 0



structure WholeArcBoundaryIncidence
    (D : PeriodicPlanarDualPair P Pdual)
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b) : Prop
    extends WholeArcBoundaryPlacement D p q where
  dual_endpoint_outside :
    (∀ t : unitInterval,
      D.primalEmbedding.coordinates
          (D.primalEmbedding.simpleWalkArc p t) 0 <
        D.dualEmbedding.vertexCoord b 0) ∨
    (∀ t : unitInterval,
      D.primalEmbedding.coordinates
          (D.primalEmbedding.simpleWalkArc p t) 1 <
        D.dualEmbedding.vertexCoord b 1) ∨
    (∀ t : unitInterval,
      D.dualEmbedding.vertexCoord b 1 <
        D.primalEmbedding.coordinates
          (D.primalEmbedding.simpleWalkArc p t) 1)



theorem WholeArcBoundaryPlacement.toIncidence_of_exposedEndpoint
    (D : PeriodicPlanarDualPair P Pdual)
    {x y : V} {a b : W}
    {p : P.graph.Walk x y} {q : Pdual.graph.Walk a b}
    (hplace : WholeArcBoundaryPlacement D p q)
    {right bottom top : Real}
    (hcrossRight : ∀ t : unitInterval,
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p t) 0 < right)
    (hcrossBottom : ∀ t : unitInterval, bottom <
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p t) 1)
    (hcrossTop : ∀ t : unitInterval,
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p t) 1 < top)
    (hexit : right < D.dualEmbedding.vertexCoord b 0 ∨
      D.dualEmbedding.vertexCoord b 1 < bottom ∨
      top < D.dualEmbedding.vertexCoord b 1) :
    WholeArcBoundaryIncidence D p q := by
  refine { toWholeArcBoundaryPlacement := hplace
           dual_endpoint_outside := ?_ }
  rcases hexit with hright | hbottom | htop
  · left
    intro t
    exact (hcrossRight t).trans hright
  · right; right
    intro t
    exact hbottom.trans (hcrossBottom t)
  · right; left
    intro t
    exact (hcrossTop t).trans htop




theorem no_open_primal_dual_of_wholeArcBoundaryIncidence
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b)
    (hp : ¬p.Nil) (hq : ¬q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges ->
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges ->
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    (hinc : WholeArcBoundaryIncidence D p q) : False := by
  let pcross := (D.primalEmbedding.simpleWalkArc p).map
    D.primalEmbedding.coordinates.continuous
  let descape := (D.dualEmbedding.simpleWalkArc q).map
    D.dualEmbedding.coordinates.continuous
  obtain ⟨t, s, hts⟩ :=
    ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_outside
      pcross descape hinc.lower_boundary hinc.upper_boundary
        hinc.root_above_lower hinc.root_below_upper
        hinc.primal_in_halfPlane hinc.dual_in_halfPlane
        hinc.dual_endpoint_outside
  have hcoord : D.primalEmbedding.coordinates
      (D.primalEmbedding.simpleWalkArc p t) =
      D.dualEmbedding.coordinates
        (D.dualEmbedding.simpleWalkArc q s) := by
    simpa only [pcross, descape] using hts
  have hphysical : D.primalEmbedding.simpleWalkArc p t =
      D.dualEmbedding.simpleWalkArc q s := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨t, rfl⟩ ⟨s, hphysical.symm⟩





structure WholeArcTraceIncidence
    (D : PeriodicPlanarDualPair P Pdual)
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b) where
  lo : Fin 2 -> Real
  hi : Fin 2 -> Real
  root : Fin 2 -> Real
  far : Fin 2 -> Real
  primalTrace : Path lo hi
  dualTrace : Path root far
  primal_range : Set.range primalTrace ⊆ Set.range
    ((D.primalEmbedding.simpleWalkArc p).map
      D.primalEmbedding.coordinates.continuous)
  dual_range : Set.range dualTrace ⊆ Set.range
    ((D.dualEmbedding.simpleWalkArc q).map
      D.dualEmbedding.coordinates.continuous)
  lower_boundary : lo 0 = root 0
  upper_boundary : hi 0 = root 0
  root_above_lower : lo 1 < root 1
  root_below_upper : root 1 < hi 1
  primal_in_halfPlane : ∀ t : unitInterval,
    lo 0 <= primalTrace t 0
  dual_in_halfPlane : ∀ t : unitInterval,
    root 0 <= dualTrace t 0
  dual_endpoint_outside :
    (∀ t : unitInterval, primalTrace t 0 < far 0) ∨
    (∀ t : unitInterval, primalTrace t 1 < far 1) ∨
    (∀ t : unitInterval, far 1 < primalTrace t 1)



theorem no_open_primal_dual_of_wholeArcTraceIncidence
    (D : PeriodicPlanarDualPair P Pdual)
    (omega : ConfigSpace (Sym2 V))
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b)
    (hp : ¬p.Nil) (hq : ¬q.Nil)
    (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges ->
      omega s(u, v) = true)
    (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges ->
      dualConfigEquiv D.edgeDual omega s(u, v) = true)
    (hinc : WholeArcTraceIncidence D p q) : False := by
  obtain ⟨t, s, hts⟩ :=
    ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_outside
      hinc.primalTrace hinc.dualTrace
        hinc.lower_boundary hinc.upper_boundary
        hinc.root_above_lower hinc.root_below_upper
        hinc.primal_in_halfPlane hinc.dual_in_halfPlane
        hinc.dual_endpoint_outside
  have hpMem := hinc.primal_range ⟨t, rfl⟩
  have hqMem := hinc.dual_range ⟨s, rfl⟩
  obtain ⟨tp, htp⟩ := hpMem
  obtain ⟨tq, htq⟩ := hqMem
  have hcoord : D.primalEmbedding.coordinates
      (D.primalEmbedding.simpleWalkArc p tp) =
      D.dualEmbedding.coordinates
        (D.dualEmbedding.simpleWalkArc q tq) := by
    exact htp.trans (hts.trans htq.symm)
  have hphysical : D.primalEmbedding.simpleWalkArc p tp =
      D.dualEmbedding.simpleWalkArc q tq := by
    rw [← D.coordinates_eq] at hcoord
    exact D.primalEmbedding.coordinates.injective hcoord
  have hdisjoint := D.no_open_primal_dual_simpleWalkArc_crossing
    omega p q hp hq hpopen hqopen
  exact Set.disjoint_left.1 hdisjoint
    ⟨tp, rfl⟩ ⟨tq, hphysical.symm⟩

end PeriodicPlanarDualPair

end FK.PeriodicPlanar

end StatMech
