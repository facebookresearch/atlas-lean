/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.ABClusterCondition
import Code.Sharpness.ABPhysicalDeriv

open Finset Set SimpleGraph

namespace StatMech
namespace Sharpness

open ConfigSpace

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

private noncomputable def mtrLaw (p : Sym2 W -> Real)
    (e : Sym2 W) (b : Bool) : Real :=
  if b then p e else 1 - p e

private theorem mtrLaw_sum_one (p : Sym2 W -> Real) (e : Sym2 W) :
    mtrLaw p e false + mtrLaw p e true = 1 := by
  simp [mtrLaw]

private theorem mtr_probV_eq_wprob (p : Sym2 W -> Real)
    (A : Set (ConfigSpace (Sym2 W))) :
    probV p A = wprob (mtrLaw p) A := by
  unfold probV wprob configWeightV pweight edgeWeightV mtrLaw
  rfl



noncomputable def mtrPhi (p : Sym2 W -> Real) (D : Finset (Sym2 W))
    (o : W) (S : Finset W) : Real :=
  ∑ q ∈ shk_boundaryPairs H S,
    if s(q.1, q.2) ∈ D then
      p s(q.1, q.2) *
        probV p (connEvent H (S : Set W) o {q.1})
    else 0



theorem mtr_probV_compl (p : Sym2 W -> Real)
    (A : Set (ConfigSpace (Sym2 W))) :
    probV p Aᶜ = 1 - probV p A := by
  rw [mtr_probV_eq_wprob, mtr_probV_eq_wprob]
  exact mpi_wprob_compl (mtrLaw p) (mtrLaw_sum_one p) A


theorem mtr_crossing_compl_eq_sum_surfaces (p : Sym2 W -> Real)
    (o : W) (B : Set W) :
    1 - probV p (mpiCrossingEvent H o B) =
      ∑ S ∈ (Finset.univ.filter fun S : Finset W => o ∈ S),
        probV p (mpiSurfaceEvent H B S) := by
  rw [← mtr_probV_compl p (mpiCrossingEvent H o B), mtr_probV_eq_wprob]
  exact mpi_wprob_crossing_compl_eq_sum_surfaces H
    (mtrLaw p) (mtrLaw_sum_one p) o B


theorem mtr_probV_eq_sum_inter_surfaces (p : Sym2 W -> Real)
    (o : W) (B : Set W) (C : Set (ConfigSpace (Sym2 W)))
    (hC : C ⊆ (mpiCrossingEvent H o B)ᶜ) :
    probV p C =
      ∑ S ∈ (Finset.univ.filter fun S : Finset W => o ∈ S),
        probV p (C ∩ mpiSurfaceEvent H B S) := by
  rw [mtr_probV_eq_wprob]
  exact mpi_wprob_eq_sum_inter_surfaces H (mtrLaw p) o B C hC


theorem mtr_surface_phi_factor (p : Sym2 W -> Real)
    (D : Finset (Sym2 W)) (o : W) (B : Set W) (S : Finset W) :
    mtrPhi H p D o S * probV p (mpiSurfaceEvent H B S) =
      ∑ q ∈ shk_boundaryPairs H S,
        if s(q.1, q.2) ∈ D then
          p s(q.1, q.2) *
            probV p
              (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S)
        else 0 := by
  unfold mtrPhi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hD : s(q.1, q.2) ∈ D
  · simp only [hD, if_true]
    rw [abcc_conn_surface_factor H p B S o q.1]
    ring
  · simp [hD]



theorem mtr_boundary_le_closedPivotal_surface
    (p c : Sym2 W -> Real) (hp : ∀ e, 0 <= p e ∧ p e <= 1)
    (D : Finset (Sym2 W)) (beta : Real) (hbeta : 0 <= beta)
    (hc : ∀ e ∈ D, 0 <= c e)
    (hpc : ∀ e ∈ D, p e <= beta * c e)
    (o : W) (B : Set W) (S : Finset W) (ho : o ∈ S) :
    (∑ q ∈ shk_boundaryPairs H S,
        if s(q.1, q.2) ∈ D then
          p s(q.1, q.2) *
            probV p
              (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S)
        else 0) <=
      beta * ∑ e ∈ D, c e *
        probV p (abgiClosedPivotal e (mpiCrossingEvent H o B) ∩
          mpiSurfaceEvent H B S) := by
  let f : Sym2 W -> Real := fun e => c e *
    probV p (abgiClosedPivotal e (mpiCrossingEvent H o B) ∩
      mpiSurfaceEvent H B S)
  have hinj : Set.InjOn (fun q : W × W => s(q.1, q.2))
      (shk_boundaryPairs H S : Set (W × W)) := by
    intro q hq r hr hqr
    obtain ⟨qx, qy, _⟩ := (shk_mem_boundaryPairs H S).mp hq
    obtain ⟨rx, ry, _⟩ := (shk_mem_boundaryPairs H S).mp hr
    rw [Sym2.eq_iff] at hqr
    rcases hqr with h | h
    · exact Prod.ext h.1 h.2
    · have : q.2 ∈ S := by rw [h.2]; exact rx
      exact False.elim (qy this)
  calc
    (∑ q ∈ shk_boundaryPairs H S,
        if s(q.1, q.2) ∈ D then
          p s(q.1, q.2) *
            probV p
              (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S)
        else 0) <=
      ∑ q ∈ shk_boundaryPairs H S,
        if hD : s(q.1, q.2) ∈ D then beta * f s(q.1, q.2) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hD : s(q.1, q.2) ∈ D
      · simp only [hD, if_true]
        have hsub :
            connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S ⊆
              abgiClosedPivotal s(q.1, q.2) (mpiCrossingEvent H o B) ∩
                mpiSurfaceEvent H B S := by
          intro omega hw
          exact ⟨mpi_conn_surface_subset_pivotalClosed H o B S ho hq hw, hw.2⟩
        have hprob := abgi_probV_mono p hp hsub
        have hprob0 := abgi_probV_nonneg p hp
          (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S)
        have hcoef0 : 0 <= beta * c s(q.1, q.2) :=
          mul_nonneg hbeta (hc _ hD)
        calc
          p s(q.1, q.2) * probV p
              (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S) <=
            (beta * c s(q.1, q.2)) * probV p
              (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S) :=
                mul_le_mul_of_nonneg_right (hpc _ hD) hprob0
          _ <= (beta * c s(q.1, q.2)) * probV p
              (abgiClosedPivotal s(q.1, q.2) (mpiCrossingEvent H o B) ∩
                mpiSurfaceEvent H B S) :=
                mul_le_mul_of_nonneg_left hprob hcoef0
          _ = beta * f s(q.1, q.2) := by ring
      · simp [hD]
    _ = beta * ∑ e ∈
        (shk_boundaryPairs H S).image (fun q => s(q.1, q.2)),
        if e ∈ D then f e else 0 := by
      rw [Finset.mul_sum, Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hD : s(q.1, q.2) ∈ D <;> simp [hD]
    _ <= beta * ∑ e ∈ D, f e := by
      apply mul_le_mul_of_nonneg_left _ hbeta
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro e he
        exact (Finset.mem_filter.mp he).2
      · intro e he _
        exact mul_nonneg (hc e he) (abgi_probV_nonneg p hp _)
    _ = beta * ∑ e ∈ D, c e *
        probV p (abgiClosedPivotal e (mpiCrossingEvent H o B) ∩
          mpiSurfaceEvent H B S) := rfl




theorem mtr_meanfield_reassembly
    (p c : Sym2 W -> Real) (hp : ∀ e, 0 <= p e ∧ p e <= 1)
    (D : Finset (Sym2 W)) (beta m : Real) (hbeta : 0 <= beta)
    (hc : ∀ e ∈ D, 0 <= c e)
    (hpc : ∀ e ∈ D, p e <= beta * c e)
    (o : W) (B : Set W)
    (hm : ∀ S : Finset W, o ∈ S ->
      (mpiSurfaceEvent H B S).Nonempty -> m <= mtrPhi H p D o S) :
    m * (1 - probV p (mpiCrossingEvent H o B)) <=
      beta * ∑ e ∈ D, c e *
        probV p (abgiClosedPivotal e (mpiCrossingEvent H o B)) := by
  let P : Finset (Finset W) := Finset.univ.filter fun S => o ∈ S
  have hmass : 1 - probV p (mpiCrossingEvent H o B) =
      ∑ S ∈ P, probV p (mpiSurfaceEvent H B S) :=
    mtr_crossing_compl_eq_sum_surfaces H p o B
  calc
    m * (1 - probV p (mpiCrossingEvent H o B)) =
        ∑ S ∈ P, m * probV p (mpiSurfaceEvent H B S) := by
      rw [hmass, Finset.mul_sum]
    _ <= ∑ S ∈ P, beta * ∑ e ∈ D, c e *
        probV p (abgiClosedPivotal e (mpiCrossingEvent H o B) ∩
          mpiSurfaceEvent H B S) := by
      apply Finset.sum_le_sum
      intro S hS
      have hoS : o ∈ S := (Finset.mem_filter.mp hS).2
      by_cases hocc : (mpiSurfaceEvent H B S).Nonempty
      · have hsurf0 : 0 <= probV p (mpiSurfaceEvent H B S) :=
          abgi_probV_nonneg p hp _
        calc
          m * probV p (mpiSurfaceEvent H B S) <=
              mtrPhi H p D o S * probV p (mpiSurfaceEvent H B S) :=
            mul_le_mul_of_nonneg_right (hm S hoS hocc) hsurf0
          _ = ∑ q ∈ shk_boundaryPairs H S,
              if s(q.1, q.2) ∈ D then
                p s(q.1, q.2) * probV p
                  (connEvent H (S : Set W) o {q.1} ∩ mpiSurfaceEvent H B S)
              else 0 := mtr_surface_phi_factor H p D o B S
          _ <= beta * ∑ e ∈ D, c e *
              probV p (abgiClosedPivotal e (mpiCrossingEvent H o B) ∩
                mpiSurfaceEvent H B S) :=
            mtr_boundary_le_closedPivotal_surface H p c hp D beta hbeta hc hpc
              o B S hoS
      · have hempty : mpiSurfaceEvent H B S = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hocc
        rw [hempty]
        simp [probV]
    _ = beta * ∑ e ∈ D, c e *
        probV p (abgiClosedPivotal e (mpiCrossingEvent H o B)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e heD
      rw [← Finset.mul_sum]
      congr 1
      symm
      exact mtr_probV_eq_sum_inter_surfaces H p o B
        (abgiClosedPivotal e (mpiCrossingEvent H o B))
        (mpi_pivotalClosed_subset_compl
          (isIncreasing_connEvent H Set.univ o B))

end Sharpness
end StatMech
