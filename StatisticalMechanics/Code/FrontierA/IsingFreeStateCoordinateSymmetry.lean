/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingDiagonalReflectionInfinite

open Filter MeasureTheory Set Topology

namespace StatMech.FrontierA

open StatMech Ising Lattice StatMech.FrontierB

variable {d : Nat}

noncomputable def freeBoxAutomorphismEquiv
    (e : Site d ≃ Site d)
    (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
    (n : Nat) :
    freeDomainVertices (boxFinset d n) ≃
      freeDomainVertices (boxFinset d n) where
  toFun x := ⟨e x.1, (hbox n x.1).1 x.2⟩
  invFun x := ⟨e.symm x.1, by
    apply (hbox n (e.symm x.1)).2
    simpa using x.2⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp

@[simp] theorem freeBoxAutomorphismEquiv_val
    (e : Site d ≃ Site d)
    (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
    (n : Nat) (x : freeDomainVertices (boxFinset d n)) :
    (freeBoxAutomorphismEquiv e hbox n x).1 = e x.1 := rfl

theorem freeDomainSpinSupport_map_freeBoxAutomorphism
    (e : Site d ≃ Site d)
    (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
    (n : Nat) (A : Finset (Site d)) :
    (freeDomainSpinSupport (boxFinset d n) A).map
        (freeBoxAutomorphismEquiv e hbox n).toEmbedding =
      freeDomainSpinSupport (boxFinset d n) (A.map e.toEmbedding) := by
  ext z
  simp only [Finset.mem_map, freeDomainSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, hx, rfl⟩
  · rintro ⟨a, ha, haz⟩
    let x : freeDomainVertices (boxFinset d n) :=
      ⟨a, by
        apply (hbox n a).2
        have haz' : e a = z.1 := haz
        rw [haz']
        exact z.2⟩
    refine ⟨x, ha, ?_⟩
    apply Subtype.ext
    exact haz



theorem integral_freeState_spinProd_boxAutomorphism
    (e : Site d ≃ Site d)
    (hadj : ∀ x y, (hypercubicLattice d).Adj x y ↔
      (hypercubicLattice d).Adj (e x) (e y))
    (hbox : ∀ n x, x ∈ boxFinset d n ↔ e x ∈ boxFinset d n)
    (beta : Real) (hbeta : 0 <= beta) (A : Finset (Site d)) :
    (∫ omega, spinProd (A.map e.toEmbedding) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  let eA := A.map e.toEmbedding
  let S := A ∪ eA
  obtain ⟨N, hSN⟩ := Lattice.finite_subset_box
    (↑S : Set (Site d)) S.finite_toSet
  have hAbox (n : Nat) (hn : N <= n) : A ⊆ boxFinset d n := by
    intro x hx
    rw [mem_boxFinset]
    exact box_mono d hn (hSN (Finset.mem_union_left eA hx))
  have heAbox (n : Nat) (hn : N <= n) : eA ⊆ boxFinset d n := by
    intro x hx
    rw [mem_boxFinset]
    exact box_mono d hn (hSN (Finset.mem_union_right A hx))
  have hfinite (n : Nat) (hn : N <= n) :
      (∫ omega, spinProd eA omega
          ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) =
        ∫ omega, spinProd A omega
          ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d))) := by
    rw [integral_freeMeasure_spinProd_eq_freeDomain
        d n beta eA (heAbox n hn),
      integral_freeMeasure_spinProd_eq_freeDomain
        d n beta A (hAbox n hn)]
    let eb := freeBoxAutomorphismEquiv e hbox n
    have hebAdj (x y : freeDomainVertices (boxFinset d n)) :
        (freeDomainGraph (boxFinset d n)).Adj x y ↔
          (freeDomainGraph (boxFinset d n)).Adj (eb x) (eb y) := by
      exact hadj x.1 y.1
    have hrel := isingExpectation_spinProd_relabel
      (freeDomainGraph (boxFinset d n))
      (freeDomainGraph (boxFinset d n)) eb hebAdj beta 0
      (freeDomainSpinSupport (boxFinset d n) A)
    rw [freeDomainSpinSupport_map_freeBoxAutomorphism e hbox n A] at hrel
    exact hrel.symm
  have hlimA := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta A
  have hlimeA := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta eA
  apply le_antisymm
  · exact le_of_tendsto_of_tendsto hlimeA hlimA (by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hfinite n hn).le)
  · exact le_of_tendsto_of_tendsto hlimA hlimeA (by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact (hfinite n hn).ge)



def isingCoordinateNegate (i : Fin d) (x : Site d) : Site d :=
  fun a => if a = i then -x a else x a

@[simp] theorem isingCoordinateNegate_apply_same
    (i : Fin d) (x : Site d) : isingCoordinateNegate i x i = -x i := by
  simp [isingCoordinateNegate]

theorem isingCoordinateNegate_apply_of_ne
    (i a : Fin d) (hai : a ≠ i) (x : Site d) :
    isingCoordinateNegate i x a = x a := by
  simp [isingCoordinateNegate, hai]

@[simp] theorem isingCoordinateNegate_involutive
    (i : Fin d) (x : Site d) :
    isingCoordinateNegate i (isingCoordinateNegate i x) = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp
  · simp [isingCoordinateNegate_apply_of_ne i a hai]

def isingCoordinateNegateEquiv (i : Fin d) : Site d ≃ Site d where
  toFun := isingCoordinateNegate i
  invFun := isingCoordinateNegate i
  left_inv := isingCoordinateNegate_involutive i
  right_inv := isingCoordinateNegate_involutive i

theorem hypercubicLattice_adj_coordinateNegate
    (i : Fin d) (x y : Site d) :
    (hypercubicLattice d).Adj x y ↔
      (hypercubicLattice d).Adj
        (isingCoordinateNegate i x) (isingCoordinateNegate i y) := by
  change (∑ a, (x a - y a).natAbs) = 1 ↔
    (∑ a, (isingCoordinateNegate i x a -
      isingCoordinateNegate i y a).natAbs) = 1
  have hsum :
      (∑ a, (isingCoordinateNegate i x a -
        isingCoordinateNegate i y a).natAbs) =
        ∑ a, (x a - y a).natAbs := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases hai : a = i
    · subst a
      simp only [isingCoordinateNegate_apply_same]
      rw [show -x i - -y i = -(x i - y i) by ring, Int.natAbs_neg]
    · simp [isingCoordinateNegate_apply_of_ne i a hai]
  rw [hsum]

theorem mem_boxFinset_coordinateNegate_iff
    (i : Fin d) (n : Nat) (x : Site d) :
    x ∈ boxFinset d n ↔ isingCoordinateNegate i x ∈ boxFinset d n := by
  simp only [mem_boxFinset, mem_box]
  constructor <;> intro hx a
  · by_cases hai : a = i
    · subst a
      simpa using hx i
    · simpa [isingCoordinateNegate_apply_of_ne i a hai] using hx a
  · have h := hx a
    by_cases hai : a = i
    · subst a
      simpa using h
    · simpa [isingCoordinateNegate_apply_of_ne i a hai] using h

theorem integral_freeState_spinProd_coordinateNegate
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta)
    (A : Finset (Site d)) :
    (∫ omega, spinProd
        (A.map (isingCoordinateNegateEquiv i).toEmbedding) omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, spinProd A omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) :=
  integral_freeState_spinProd_boxAutomorphism
    (isingCoordinateNegateEquiv i)
    (hypercubicLattice_adj_coordinateNegate i)
    (mem_boxFinset_coordinateNegate_iff i) beta hbeta A

theorem currentContinuityFreeTwoPoint_coordinateNegate
    (i : Fin d) (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (isingCoordinateNegate i x) =
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  have h := integral_freeState_spinProd_coordinateNegate
    i beta hbeta ({Percolation.origin d, x} : Finset (Site d))
  have ho : isingCoordinateNegate i (Percolation.origin d) =
      Percolation.origin d := by
    funext a
    by_cases hai : a = i <;>
      simp [isingCoordinateNegate, Percolation.origin, hai]
  simp [isingCoordinateNegateEquiv] at h
  rw [ho] at h
  simpa [currentContinuityFreeTwoPoint] using h



theorem mem_boxFinset_diagonalReflect_zero_iff
    (i j : Fin d) (hij : i ≠ j) (n : Nat) (x : Site d) :
    x ∈ boxFinset d n ↔
      isingDiagonalReflect i j 0 x ∈ boxFinset d n := by
  simp only [mem_boxFinset, mem_box]
  constructor
  · intro hx a
    by_cases hai : a = i
    · subst a
      simpa [hij] using hx j
    · by_cases haj : a = j
      · subst a
        simpa [hij, Ne.symm hij] using hx i
      · simpa [isingDiagonalReflect_apply_of_ne i j a hai haj] using hx a
  · intro hx a
    have h := hx (Equiv.swap i j a)
    have hR := congrFun (isingDiagonalReflect_involutive i j hij 0 x) a
    rw [← hR]
    by_cases hai : a = i
    · subst a
      simpa [hij] using hx j
    · by_cases haj : a = j
      · subst a
        simpa [hij, Ne.symm hij] using hx i
      · simpa [isingDiagonalReflect_apply_of_ne i j a hai haj] using hx a

theorem currentContinuityFreeTwoPoint_coordinateSwap
    (i j : Fin d) (hij : i ≠ j)
    (beta : Real) (hbeta : 0 <= beta) (x : Site d) :
    currentContinuityFreeTwoPoint d beta (Percolation.origin d)
        (isingDiagonalReflect i j 0 x) =
      currentContinuityFreeTwoPoint d beta (Percolation.origin d) x := by
  have h := integral_freeState_spinProd_boxAutomorphism
    (isingDiagonalReflectEquiv i j hij 0)
    (hypercubicLattice_adj_diagonalReflect i j hij 0)
    (mem_boxFinset_diagonalReflect_zero_iff i j hij)
    beta hbeta ({Percolation.origin d, x} : Finset (Site d))
  have ho : isingDiagonalReflect i j 0 (Percolation.origin d) =
      Percolation.origin d := by
    funext a
    simp [isingDiagonalReflect, isingDiagonalShift, Percolation.origin]
  simp [isingDiagonalReflectEquiv] at h
  rw [ho] at h
  simpa [currentContinuityFreeTwoPoint] using h

end StatMech.FrontierA
