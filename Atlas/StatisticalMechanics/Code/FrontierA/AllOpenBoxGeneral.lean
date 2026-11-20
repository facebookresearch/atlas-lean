/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Walls.bgf2faithcontract

open Set SimpleGraph Finset

namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation
open StatMech.Walls

variable {d : ℕ}


def bgfdInBox (L : ℕ) (c x : Site d) : Prop :=
  ∀ i, (x i - c i).natAbs ≤ L

theorem bgfd_update_inBox {L : ℕ} {c x : Site d}
    (hx : bgfdInBox L c x) (j : Fin d) {v : ℤ}
    (hv : (v - c j).natAbs ≤ L) :
    bgfdInBox L c (Function.update x j v) := by
  intro i
  by_cases hij : i = j
  · subst i
    rw [Function.update_self]
    exact hv
  · rw [Function.update_of_ne hij]
    exact hx i

theorem bgfd_mix_inBox {L : ℕ} {c x y : Site d}
    (hx : bgfdInBox L c x) (hy : bgfdInBox L c y) (k : ℕ) :
    bgfdInBox L c (mixSite x y k) := by
  intro i
  simp only [mixSite]
  by_cases h : (i : ℕ) < k
  · rw [if_pos h]
    exact hy i
  · rw [if_neg h]
    exact hx i


theorem bgfd_ascend {L : ℕ} {c : Site d}
    {omega : ConfigSpace (Sym2 (Site d))}
    (hopen : ∀ x y : Site d, bgfdInBox L c x → bgfdInBox L c y →
      (hypercubicLattice d).Adj x y → omega s(x, y) = true)
    {x : Site d} (hx : bgfdInBox L c x) (j : Fin d) :
    ∀ (k : ℕ) (a : ℤ),
      (a - c j).natAbs ≤ L →
      (a + (k : ℤ) - c j).natAbs ≤ L →
      Connected d omega (Function.update x j a)
        (Function.update x j (a + (k : ℤ))) := by
  intro k
  induction k with
  | zero =>
      intro a _ _
      simpa using (connected_rfl : Connected d omega
        (Function.update x j a) (Function.update x j a))
  | succ m ih =>
      intro a ha hak
      have hint : (a + (m : ℤ) - c j).natAbs ≤ L := by
        push_cast at hak ⊢
        omega
      have hstep : Connected d omega
          (Function.update x j (a + (m : ℤ)))
          (Function.update x j (a + (m : ℤ) + 1)) := by
        have hin1 : bgfdInBox L c
            (Function.update x j (a + (m : ℤ))) :=
          bgfd_update_inBox hx j hint
        have hin2 : bgfdInBox L c
            (Function.update x j (a + (m : ℤ) + 1)) := by
          refine bgfd_update_inBox hx j ?_
          push_cast at hak ⊢
          omega
        have hadj := adj_update_succ x j (a + (m : ℤ))
        exact SimpleGraph.Adj.reachable (G := openSubgraph d omega)
          (by
            rw [openSubgraph_adj]
            exact ⟨hadj, hopen _ _ hin1 hin2 hadj⟩)
      have hrec := (ih a ha hint).trans hstep
      have he : a + (m : ℤ) + 1 = a + ((m + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rwa [he] at hrec

theorem bgfd_update_conn {L : ℕ} {c : Site d}
    {omega : ConfigSpace (Sym2 (Site d))}
    (hopen : ∀ x y : Site d, bgfdInBox L c x → bgfdInBox L c y →
      (hypercubicLattice d).Adj x y → omega s(x, y) = true)
    {x : Site d} (hx : bgfdInBox L c x) (j : Fin d) {a : ℤ}
    (ha : (a - c j).natAbs ≤ L) :
    Connected d omega x (Function.update x j a) := by
  have hxj : (x j - c j).natAbs ≤ L := hx j
  have hxupd : Function.update x j (x j) = x :=
    Function.update_eq_self j x
  rcases le_total (x j) a with hle | hle
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    have h := bgfd_ascend hopen hx j k (x j) hxj (by rw [hk]; exact ha)
    rwa [hxupd, hk] at h
  · obtain ⟨k, hk⟩ := Int.le.dest hle
    have h := bgfd_ascend hopen hx j k a ha (by rw [hk]; exact hxj)
    rw [hk, hxupd] at h
    exact h.symm

theorem bgfd_mix_conn {L : ℕ} {c : Site d}
    {omega : ConfigSpace (Sym2 (Site d))}
    (hopen : ∀ x y : Site d, bgfdInBox L c x → bgfdInBox L c y →
      (hypercubicLattice d).Adj x y → omega s(x, y) = true)
    {x y : Site d} (hx : bgfdInBox L c x) (hy : bgfdInBox L c y) :
    ∀ k, k ≤ d → Connected d omega x (mixSite x y k) := by
  intro k
  induction k with
  | zero =>
      intro _
      rw [mixSite_zero]
  | succ m ih =>
      intro hsucc
      have hm : m < d := by omega
      have h1 := ih (by omega)
      have hstep : Connected d omega (mixSite x y m)
          (mixSite x y (m + 1)) := by
        rw [mixSite_succ hm]
        exact bgfd_update_conn hopen (bgfd_mix_inBox hx hy m)
          ⟨m, hm⟩ (hy ⟨m, hm⟩)
      exact h1.trans hstep


theorem bgfd_box_connected {L : ℕ} {c : Site d}
    {omega : ConfigSpace (Sym2 (Site d))}
    (hopen : ∀ x y : Site d, bgfdInBox L c x → bgfdInBox L c y →
      (hypercubicLattice d).Adj x y → omega s(x, y) = true)
    {x y : Site d} (hx : bgfdInBox L c x) (hy : bgfdInBox L c y) :
    Connected d omega x y := by
  have h := bgfd_mix_conn hopen hx hy d le_rfl
  rwa [mixSite_full] at h


def bgfdCentre (L : ℕ) (j : Site d) : Site d :=
  fun i => (2 * (L : ℤ) + 1) * j i


theorem bgfd_idx_iff_inBox {L : ℕ} {j x : Site d} :
    bgn_idx L x = j ↔ bgfdInBox L (bgfdCentre L j) x := by
  constructor
  · intro h i
    have hxi : (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = j i := by
      rw [← h]
      rfl
    have hdiv := (bsc_ediv_eq_iff).mp hxi
    simpa [bgfdCentre] using hdiv
  · intro h
    funext i
    show (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) = j i
    refine (bsc_ediv_eq_iff).mpr ?_
    simpa [bgfdCentre] using h i

theorem bgfd_idx_centre (L : ℕ) (j : Site d) :
    bgn_idx L (bgfdCentre L j) = j :=
  bgfd_idx_iff_inBox.mpr (by intro i; simp [bgfdCentre])

theorem bgfd_centre_injective (L : ℕ) :
    Function.Injective (bgfdCentre (d := d) L) := by
  intro j k h
  funext i
  have hi := congrFun h i
  simp only [bgfdCentre] at hi
  have hfactor : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
  exact mul_left_cancel₀ hfactor hi



theorem bgfd_lat_shift (c x y : Site d) :
    (hypercubicLattice d).Adj (x + c) (y + c) ↔
      (hypercubicLattice d).Adj x y := by
  rw [hypercubicLattice_adj, hypercubicLattice_adj]
  refine Iff.of_eq (congrArg (· = 1) ?_)
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.add_apply]
  congr 1
  ring



theorem bgfd_idx_shift (L : ℕ) (j x : Site d) :
    bgn_idx L (x + bgfdCentre L j) = bgn_idx L x + j := by
  funext i
  have hb : (2 * (L : ℤ) + 1) ≠ 0 := by positivity
  show ((x + bgfdCentre L j) i + (L : ℤ)) / (2 * (L : ℤ) + 1) =
    bgn_idx L x i + j i
  rw [Pi.add_apply]
  show (x i + bgfdCentre L j i + (L : ℤ)) /
      (2 * (L : ℤ) + 1) =
    (x i + (L : ℤ)) / (2 * (L : ℤ) + 1) + j i
  have hc : bgfdCentre L j i = (2 * (L : ℤ) + 1) * j i := rfl
  rw [hc]
  have hrw : x i + (2 * (L : ℤ) + 1) * j i + (L : ℤ) =
      (x i + (L : ℤ)) + j i * (2 * (L : ℤ) + 1) := by ring
  rw [hrw, Int.add_mul_ediv_right _ _ hb]

@[simp] theorem bgfd_centre_zero (L : ℕ) :
    bgfdCentre (d := d) L 0 = 0 := by
  funext i
  simp [bgfdCentre]


def BgfdIndexAllOpen (omega : ConfigSpace (Sym2 (Site d)))
    (L : ℕ) (j : Site d) : Prop :=
  ∀ x y : Site d, bgn_idx L x = j → bgn_idx L y = j →
    (hypercubicLattice d).Adj x y → omega s(x, y) = true


theorem bgfd_indexAllOpen_connected
    {omega : ConfigSpace (Sym2 (Site d))} {L : ℕ} {j : Site d}
    (hopen : BgfdIndexAllOpen omega L j) {x y : Site d}
    (hx : bgn_idx L x = j) (hy : bgn_idx L y = j) :
    Connected d omega x y := by
  refine bgfd_box_connected ?_
    (bgfd_idx_iff_inBox.mp hx) (bgfd_idx_iff_inBox.mp hy)
  intro a b ha hb hadj
  exact hopen a b (bgfd_idx_iff_inBox.mpr ha)
    (bgfd_idx_iff_inBox.mpr hb) hadj

end StatMech.FrontierA
