/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicPhysicalCompactVariation



namespace StatMech.Universality

open Finset SimpleGraph
open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

private theorem primal_adj_coord_bounds
    {n m : Nat} {hm : m ≤ n}
    {p q : FKIsingSquareRadialPatchPrimalNode m}
    (hpq : (fkIsingSquareRadialPatchPrimalGraph n m hm).Adj p q) :
    p.1.1.1 ≤ q.1.1.1 + 1 ∧ q.1.1.1 ≤ p.1.1.1 + 1 ∧
      p.1.2.1 ≤ q.1.2.1 + 1 ∧ q.1.2.1 ≤ p.1.2.1 + 1 := by
  change (hypercubicLattice 2).Adj
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1 at hpq
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq
  let dx : Int :=
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1 0 -
      (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1 0
  let dy : Int :=
    (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1 1 -
      (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1 1
  have hdx : dx ≤ (dx.natAbs : Int) := Int.le_natAbs
  have hndx : -dx ≤ (dx.natAbs : Int) := by
    simpa [Int.natAbs_neg] using (Int.le_natAbs (a := -dx))
  have hdy : dy ≤ (dy.natAbs : Int) := Int.le_natAbs
  have hndy : -dy ≤ (dy.natAbs : Int) := by
    simpa [Int.natAbs_neg] using (Int.le_natAbs (a := -dy))
  have hsum : dx.natAbs + dy.natAbs = 1 := by
    simpa [dx, dy] using hpq
  have hpI :
      (p.1.1.1 : Int) =
        (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1 0 +
          (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1 1 := by
    simp [fkIsingSquareRadialPatchPrimalNodeVertex,
      fkIsingSquareRadialPatchVertex]
  have hqI :
      (q.1.1.1 : Int) =
        (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1 0 +
          (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1 1 := by
    simp [fkIsingSquareRadialPatchPrimalNodeVertex,
      fkIsingSquareRadialPatchVertex]
  have hpHalf :
      2 * (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1 0 =
        (p.1.1.1 : Int) + p.1.2.1 := by
    change 2 * ((((p.1.1.1 + p.1.2.1 + 1) / 2 : Nat)) : Int) = _
    norm_cast
    have hmod := Nat.even_iff.mp p.2
    omega
  have hqHalf :
      2 * (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1 0 =
        (q.1.1.1 : Int) + q.1.2.1 := by
    change 2 * ((((q.1.1.1 + q.1.2.1 + 1) / 2 : Nat)) : Int) = _
    norm_cast
    have hmod := Nat.even_iff.mp q.2
    omega
  have hpJ :
      (p.1.2.1 : Int) =
        (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1 0 -
          (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1 1 := by
    omega
  have hqJ :
      (q.1.2.1 : Int) =
        (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1 0 -
          (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1 1 := by
    omega
  constructor
  · exact_mod_cast (show (p.1.1.1 : Int) ≤ q.1.1.1 + 1 by omega)
  constructor
  · exact_mod_cast (show (q.1.1.1 : Int) ≤ p.1.1.1 + 1 by omega)
  constructor
  · exact_mod_cast (show (p.1.2.1 : Int) ≤ q.1.2.1 + 1 by omega)
  · exact_mod_cast (show (q.1.2.1 : Int) ≤ p.1.2.1 + 1 by omega)

private theorem dual_adj_coord_bounds
    {m : Nat} {p q : FKIsingSquareRadialPatchDualNode m}
    (hpq : (fkIsingSquareRadialPatchDualGraph m).Adj p q) :
    p.1.1.1 ≤ q.1.1.1 + 1 ∧ q.1.1.1 ≤ p.1.1.1 + 1 ∧
      p.1.2.1 ≤ q.1.2.1 + 1 ∧ q.1.2.1 ≤ p.1.2.1 + 1 := by
  change
    (p.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = p.1.1.1) ∧
      (p.1.2.1 + 1 = q.1.2.1 ∨ q.1.2.1 + 1 = p.1.2.1) at hpq
  rcases hpq with ⟨hpq0 | hpq0, hpq1 | hpq1⟩ <;> omega

private theorem walk_coord_bounds
    {V : Type*} {G : SimpleGraph V} (coord : V → Nat)
    (hadj : ∀ {p q}, G.Adj p q →
      coord p ≤ coord q + 1 ∧ coord q ≤ coord p + 1)
    {p q : V} (w : G.Walk p q) :
    coord p ≤ coord q + w.length ∧ coord q ≤ coord p + w.length := by
  induction w with
  | nil => simp
  | cons h w ih =>
      have hs := hadj h
      simp only [Walk.length_cons]
      omega

private theorem primal_reachable_anchor
    (n m : Nat) (hm : m ≤ n) (hmpos : 0 < m) :
    ∀ p : FKIsingSquareRadialPatchPrimalNode m,
      (fkIsingSquareRadialPatchPrimalGraph n m hm).Reachable p
        ⟨(⟨0, hmpos⟩, ⟨0, hmpos⟩), by simp⟩ := by
  let anchor : FKIsingSquareRadialPatchPrimalNode m :=
    ⟨(⟨0, hmpos⟩, ⟨0, hmpos⟩), by simp⟩
  let P : Nat → Prop := fun k ↦
    ∀ p : FKIsingSquareRadialPatchPrimalNode m,
      p.1.1.1 + p.1.2.1 = k →
        (fkIsingSquareRadialPatchPrimalGraph n m hm).Reachable p anchor
  suffices ∀ k, P k by
    intro p
    exact this (p.1.1.1 + p.1.2.1) p rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      dsimp only [P]
      intro p hsum
      by_cases hi0 : p.1.1.1 = 0
      · by_cases hj0 : p.1.2.1 = 0
        · have hp : p = anchor := by
            apply Subtype.ext
            apply Prod.ext <;> apply Fin.ext <;> simp [anchor, hi0, hj0]
          rw [hp]
        · have hj2 : 2 ≤ p.1.2.1 := by
            have hmod := Nat.even_iff.mp p.2
            omega
          let mid : FKIsingSquareRadialPatchPrimalNode m :=
            ⟨(⟨1, by omega⟩, ⟨p.1.2.1 - 1, by omega⟩), by
              change Even (1 + (p.1.2.1 - 1))
              rw [Nat.even_iff]
              have hmod := Nat.even_iff.mp p.2
              omega⟩
          let q : FKIsingSquareRadialPatchPrimalNode m :=
            ⟨(⟨0, hmpos⟩, ⟨p.1.2.1 - 2, by omega⟩), by
              change Even (0 + (p.1.2.1 - 2))
              rw [Nat.even_iff]
              have hmod := Nat.even_iff.mp p.2
              omega⟩
          have hpm :
              (fkIsingSquareRadialPatchPrimalGraph n m hm).Adj p mid := by
            change (hypercubicLattice 2).Adj
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm mid).1
            rw [hypercubicLattice_adj, Fin.sum_univ_two]
            simp [mid, hi0, fkIsingSquareRadialPatchPrimalNodeVertex,
              fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
            have hmod := Nat.even_iff.mp p.2
            omega
          have hmq :
              (fkIsingSquareRadialPatchPrimalGraph n m hm).Adj mid q := by
            change (hypercubicLattice 2).Adj
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm mid).1
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1
            rw [hypercubicLattice_adj, Fin.sum_univ_two]
            simp [mid, q, fkIsingSquareRadialPatchPrimalNodeVertex,
              fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
            have hmod := Nat.even_iff.mp p.2
            omega
          have hqsum : q.1.1.1 + q.1.2.1 < k := by
            simp [q]
            omega
          exact hpm.reachable.trans (hmq.reachable.trans (ih _ hqsum q rfl))
      · by_cases hj0 : p.1.2.1 = 0
        · have hi2 : 2 ≤ p.1.1.1 := by
            have hmod := Nat.even_iff.mp p.2
            omega
          let mid : FKIsingSquareRadialPatchPrimalNode m :=
            ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨1, by omega⟩), by
              change Even ((p.1.1.1 - 1) + 1)
              rw [Nat.even_iff]
              have hmod := Nat.even_iff.mp p.2
              omega⟩
          let q : FKIsingSquareRadialPatchPrimalNode m :=
            ⟨(⟨p.1.1.1 - 2, by omega⟩, ⟨0, hmpos⟩), by
              change Even ((p.1.1.1 - 2) + 0)
              rw [Nat.even_iff]
              have hmod := Nat.even_iff.mp p.2
              omega⟩
          have hpm :
              (fkIsingSquareRadialPatchPrimalGraph n m hm).Adj p mid := by
            change (hypercubicLattice 2).Adj
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm mid).1
            rw [hypercubicLattice_adj, Fin.sum_univ_two]
            simp [mid, hj0, fkIsingSquareRadialPatchPrimalNodeVertex,
              fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
            have hmod := Nat.even_iff.mp p.2
            omega
          have hmq :
              (fkIsingSquareRadialPatchPrimalGraph n m hm).Adj mid q := by
            change (hypercubicLattice 2).Adj
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm mid).1
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1
            rw [hypercubicLattice_adj, Fin.sum_univ_two]
            simp [mid, q, fkIsingSquareRadialPatchPrimalNodeVertex,
              fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
            have hmod := Nat.even_iff.mp p.2
            omega
          have hqsum : q.1.1.1 + q.1.2.1 < k := by
            simp [q]
            omega
          exact hpm.reachable.trans (hmq.reachable.trans (ih _ hqsum q rfl))
        · let q : FKIsingSquareRadialPatchPrimalNode m :=
            ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨p.1.2.1 - 1, by omega⟩), by
              change Even ((p.1.1.1 - 1) + (p.1.2.1 - 1))
              rw [Nat.even_iff]
              have hmod := Nat.even_iff.mp p.2
              omega⟩
          have hpq :
              (fkIsingSquareRadialPatchPrimalGraph n m hm).Adj p q := by
            change (hypercubicLattice 2).Adj
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p).1
              (fkIsingSquareRadialPatchPrimalNodeVertex n m hm q).1
            rw [hypercubicLattice_adj, Fin.sum_univ_two]
            simp [q, fkIsingSquareRadialPatchPrimalNodeVertex,
              fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf_eq]
            have hmod := Nat.even_iff.mp p.2
            omega
          have hqsum : q.1.1.1 + q.1.2.1 < k := by
            simp [q]
            omega
          exact hpq.reachable.trans (ih _ hqsum q rfl)

private theorem dual_reachable_anchor
    (m : Nat) (hm2 : 2 ≤ m) :
    ∀ p : FKIsingSquareRadialPatchDualNode m,
      (fkIsingSquareRadialPatchDualGraph m).Reachable p
        ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by norm_num⟩ := by
  let anchor : FKIsingSquareRadialPatchDualNode m :=
    ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by norm_num⟩
  let P : Nat → Prop := fun k ↦
    ∀ p : FKIsingSquareRadialPatchDualNode m,
      p.1.1.1 + p.1.2.1 = k →
        (fkIsingSquareRadialPatchDualGraph m).Reachable p anchor
  suffices ∀ k, P k by
    intro p
    exact this (p.1.1.1 + p.1.2.1) p rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      dsimp only [P]
      intro p hsum
      by_cases hi0 : p.1.1.1 = 0
      · by_cases hj1 : p.1.2.1 = 1
        · have hp : p = anchor := by
            apply Subtype.ext
            apply Prod.ext <;> apply Fin.ext <;> simp [anchor, hi0, hj1]
          rw [hp]
        · have hj3 : 3 ≤ p.1.2.1 := by
            have hmod := Nat.not_even_iff.mp p.2
            omega
          let mid : FKIsingSquareRadialPatchDualNode m :=
            ⟨(⟨1, by omega⟩, ⟨p.1.2.1 - 1, by omega⟩), by
              change ¬ Even (1 + (p.1.2.1 - 1))
              rw [Nat.not_even_iff]
              have hmod := Nat.not_even_iff.mp p.2
              omega⟩
          let q : FKIsingSquareRadialPatchDualNode m :=
            ⟨(⟨0, by omega⟩, ⟨p.1.2.1 - 2, by omega⟩), by
              change ¬ Even (0 + (p.1.2.1 - 2))
              rw [Nat.not_even_iff]
              have hmod := Nat.not_even_iff.mp p.2
              omega⟩
          have hpm : (fkIsingSquareRadialPatchDualGraph m).Adj p mid := by
            change
              (p.1.1.1 + 1 = mid.1.1.1 ∨ mid.1.1.1 + 1 = p.1.1.1) ∧
                (p.1.2.1 + 1 = mid.1.2.1 ∨ mid.1.2.1 + 1 = p.1.2.1)
            simp [mid, hi0]
            omega
          have hmq : (fkIsingSquareRadialPatchDualGraph m).Adj mid q := by
            change
              (mid.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = mid.1.1.1) ∧
                (mid.1.2.1 + 1 = q.1.2.1 ∨ q.1.2.1 + 1 = mid.1.2.1)
            simp [mid, q]
            omega
          have hqsum : q.1.1.1 + q.1.2.1 < k := by
            simp [q]
            omega
          exact hpm.reachable.trans (hmq.reachable.trans (ih _ hqsum q rfl))
      · by_cases hj0 : p.1.2.1 = 0
        · by_cases hi1 : p.1.1.1 = 1
          · have hpq : (fkIsingSquareRadialPatchDualGraph m).Adj p anchor := by
              change
                (p.1.1.1 + 1 = anchor.1.1.1 ∨
                    anchor.1.1.1 + 1 = p.1.1.1) ∧
                  (p.1.2.1 + 1 = anchor.1.2.1 ∨
                    anchor.1.2.1 + 1 = p.1.2.1)
              simp [anchor, hi1, hj0]
            exact hpq.reachable
          · have hi3 : 3 ≤ p.1.1.1 := by
              have hmod := Nat.not_even_iff.mp p.2
              omega
            let mid : FKIsingSquareRadialPatchDualNode m :=
              ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨1, by omega⟩), by
                change ¬ Even ((p.1.1.1 - 1) + 1)
                rw [Nat.not_even_iff]
                have hmod := Nat.not_even_iff.mp p.2
                omega⟩
            let q : FKIsingSquareRadialPatchDualNode m :=
              ⟨(⟨p.1.1.1 - 2, by omega⟩, ⟨0, by omega⟩), by
                change ¬ Even ((p.1.1.1 - 2) + 0)
                rw [Nat.not_even_iff]
                have hmod := Nat.not_even_iff.mp p.2
                omega⟩
            have hpm : (fkIsingSquareRadialPatchDualGraph m).Adj p mid := by
              change
                (p.1.1.1 + 1 = mid.1.1.1 ∨ mid.1.1.1 + 1 = p.1.1.1) ∧
                  (p.1.2.1 + 1 = mid.1.2.1 ∨ mid.1.2.1 + 1 = p.1.2.1)
              simp [mid, hj0]
              omega
            have hmq : (fkIsingSquareRadialPatchDualGraph m).Adj mid q := by
              change
                (mid.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = mid.1.1.1) ∧
                  (mid.1.2.1 + 1 = q.1.2.1 ∨ q.1.2.1 + 1 = mid.1.2.1)
              simp [mid, q]
              omega
            have hqsum : q.1.1.1 + q.1.2.1 < k := by
              simp [q]
              omega
            exact hpm.reachable.trans (hmq.reachable.trans (ih _ hqsum q rfl))
        · let q : FKIsingSquareRadialPatchDualNode m :=
            ⟨(⟨p.1.1.1 - 1, by omega⟩, ⟨p.1.2.1 - 1, by omega⟩), by
              change ¬ Even ((p.1.1.1 - 1) + (p.1.2.1 - 1))
              rw [Nat.not_even_iff]
              have hmod := Nat.not_even_iff.mp p.2
              omega⟩
          have hpq : (fkIsingSquareRadialPatchDualGraph m).Adj p q := by
            change
              (p.1.1.1 + 1 = q.1.1.1 ∨ q.1.1.1 + 1 = p.1.1.1) ∧
                (p.1.2.1 + 1 = q.1.2.1 ∨ q.1.2.1 + 1 = p.1.2.1)
            simp [q]
            omega
          have hqsum : q.1.1.1 + q.1.2.1 < k := by
            simp [q]
            omega
          exact hpq.reachable.trans (ih _ hqsum q rfl)

theorem fkIsingSquareRadialPatchPrimalBoundaryDistance_ge_of_coordinate_margin
    (n m r : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (p : FKIsingSquareRadialPatchPrimalNode m)
    (hi0 : r ≤ p.1.1.1) (hi1 : p.1.1.1 + r < m)
    (hj0 : r ≤ p.1.2.1) (hj1 : p.1.2.1 + r < m) :
    r ≤ fkIsingSquareRadialPatchPrimalBoundaryDistance
      n m hm (by omega) p := by
  obtain ⟨b, hb, hdist⟩ :=
    isingFiniteGraphDistanceToBoundary_exists_eq_dist
      (fkIsingSquareRadialPatchPrimalGraph n m hm)
      (fkIsingSquareRadialPatchPrimalBoundary m)
      (fkIsingSquareRadialPatchPrimalBoundary_nonempty m (by omega)) p
  have hreach : (fkIsingSquareRadialPatchPrimalGraph n m hm).Reachable p b :=
    (primal_reachable_anchor n m hm (by omega) p).trans
      (primal_reachable_anchor n m hm (by omega) b).symm
  obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
  have hi := walk_coord_bounds
    (fun q : FKIsingSquareRadialPatchPrimalNode m ↦ q.1.1.1)
    (fun {_ _} h ↦
      ⟨(primal_adj_coord_bounds h).1,
        (primal_adj_coord_bounds h).2.1⟩) w
  have hj := walk_coord_bounds
    (fun q : FKIsingSquareRadialPatchPrimalNode m ↦ q.1.2.1)
    (fun {_ _} h ↦
      ⟨(primal_adj_coord_bounds h).2.2.1,
        (primal_adj_coord_bounds h).2.2.2⟩) w
  change r ≤ isingFiniteGraphDistanceToBoundary
    (fkIsingSquareRadialPatchPrimalGraph n m hm)
    (fkIsingSquareRadialPatchPrimalBoundary m)
    (fkIsingSquareRadialPatchPrimalBoundary_nonempty m (by omega)) p
  rw [hdist, ← hw]
  rcases hb with hb | hb | hb | hb <;> omega

theorem fkIsingSquareRadialPatchDualBoundaryDistance_ge_of_coordinate_margin
    (m r : Nat) (hm2 : 2 ≤ m)
    (p : FKIsingSquareRadialPatchDualNode m)
    (hi0 : r ≤ p.1.1.1) (hi1 : p.1.1.1 + r < m)
    (hj0 : r ≤ p.1.2.1) (hj1 : p.1.2.1 + r < m) :
    r ≤ fkIsingSquareRadialPatchDualBoundaryDistance m hm2 p := by
  obtain ⟨b, hb, hdist⟩ :=
    isingFiniteGraphDistanceToBoundary_exists_eq_dist
      (fkIsingSquareRadialPatchDualGraph m)
      (fkIsingSquareRadialPatchDualBoundary m)
      (fkIsingSquareRadialPatchDualBoundary_nonempty m hm2) p
  have hreach : (fkIsingSquareRadialPatchDualGraph m).Reachable p b :=
    (dual_reachable_anchor m hm2 p).trans
      (dual_reachable_anchor m hm2 b).symm
  obtain ⟨w, hw⟩ := hreach.exists_walk_length_eq_dist
  have hi := walk_coord_bounds
    (fun q : FKIsingSquareRadialPatchDualNode m ↦ q.1.1.1)
    (fun {_ _} h ↦
      ⟨(dual_adj_coord_bounds h).1,
        (dual_adj_coord_bounds h).2.1⟩) w
  have hj := walk_coord_bounds
    (fun q : FKIsingSquareRadialPatchDualNode m ↦ q.1.2.1)
    (fun {_ _} h ↦
      ⟨(dual_adj_coord_bounds h).2.2.1,
        (dual_adj_coord_bounds h).2.2.2⟩) w
  change r ≤ isingFiniteGraphDistanceToBoundary
    (fkIsingSquareRadialPatchDualGraph m)
    (fkIsingSquareRadialPatchDualBoundary m)
    (fkIsingSquareRadialPatchDualBoundary_nonempty m hm2) p
  rw [hdist, ← hw]
  rcases hb with hb | hb | hb | hb <;> omega

end

end StatMech.Universality
