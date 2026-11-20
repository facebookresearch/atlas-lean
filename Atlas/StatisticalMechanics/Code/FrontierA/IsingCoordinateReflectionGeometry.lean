/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingFreeStateCoordinateMerge

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}



def isingCoordinateReflect (i : Fin d) (m : Int) (x : Site d) : Site d :=
  fun a => if a = i then m - x a else x a

@[simp] theorem isingCoordinateReflect_apply_same
    (i : Fin d) (m : Int) (x : Site d) :
    isingCoordinateReflect i m x i = m - x i := by
  simp [isingCoordinateReflect]

theorem isingCoordinateReflect_apply_of_ne
    (i a : Fin d) (hai : a ≠ i) (m : Int) (x : Site d) :
    isingCoordinateReflect i m x a = x a := by
  simp [isingCoordinateReflect, hai]

@[simp] theorem isingCoordinateReflect_involutive
    (i : Fin d) (m : Int) (x : Site d) :
    isingCoordinateReflect i m (isingCoordinateReflect i m x) = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp
  · simp [isingCoordinateReflect_apply_of_ne i a hai]

def isingCoordinateReflectEquiv
    (i : Fin d) (m : Int) : Site d ≃ Site d where
  toFun := isingCoordinateReflect i m
  invFun := isingCoordinateReflect i m
  left_inv := isingCoordinateReflect_involutive i m
  right_inv := isingCoordinateReflect_involutive i m

theorem hypercubicLattice_adj_coordinateReflect
    (i : Fin d) (m : Int) (x y : Site d) :
    (hypercubicLattice d).Adj x y ↔
      (hypercubicLattice d).Adj
        (isingCoordinateReflect i m x) (isingCoordinateReflect i m y) := by
  change (∑ a, (x a - y a).natAbs) = 1 ↔
    (∑ a, (isingCoordinateReflect i m x a -
      isingCoordinateReflect i m y a).natAbs) = 1
  have hsum :
      (∑ a, (isingCoordinateReflect i m x a -
        isingCoordinateReflect i m y a).natAbs) =
        ∑ a, (x a - y a).natAbs := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases hai : a = i
    · subst a
      simp only [isingCoordinateReflect_apply_same]
      rw [show (m - x i) - (m - y i) = -(x i - y i) by ring,
        Int.natAbs_neg]
    · simp [isingCoordinateReflect_apply_of_ne i a hai]
  rw [hsum]

def isingCoordinatePlane (i : Fin d) (m : Int) (x : Site d) : Prop :=
  2 * x i = m

def isingCoordinateLower (i : Fin d) (m : Int) (x : Site d) : Prop :=
  2 * x i < m

theorem isingCoordinateReflect_fixed
    (i : Fin d) (m : Int) (x : Site d)
    (hx : isingCoordinatePlane i m x) :
    isingCoordinateReflect i m x = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [isingCoordinatePlane] at hx ⊢
    omega
  · exact isingCoordinateReflect_apply_of_ne i a hai m x

theorem isingCoordinateReflect_centered
    (i : Fin d) (m : Int) (x : Site d) :
    2 * isingCoordinateReflect i m x i - m = -(2 * x i - m) := by
  simp
  ring

theorem isingCoordinateReflect_lower_of_upper
    (i : Fin d) (m : Int) (x : Site d)
    (hp : ¬ isingCoordinatePlane i m x)
    (hl : ¬ isingCoordinateLower i m x) :
    isingCoordinateLower i m (isingCoordinateReflect i m x) := by
  unfold isingCoordinatePlane at hp
  unfold isingCoordinateLower at hl ⊢
  simp only [isingCoordinateReflect_apply_same]
  omega

theorem isingCoordinateReflect_not_plane
    (i : Fin d) (m : Int) (x : Site d)
    (hp : ¬ isingCoordinatePlane i m x) :
    ¬ isingCoordinatePlane i m (isingCoordinateReflect i m x) := by
  intro hr
  apply hp
  unfold isingCoordinatePlane at hr ⊢
  simp only [isingCoordinateReflect_apply_same] at hr
  omega

theorem isingCoordinateReflect_not_lower_of_lower
    (i : Fin d) (m : Int) (x : Site d)
    (hl : isingCoordinateLower i m x) :
    ¬ isingCoordinateLower i m (isingCoordinateReflect i m x) := by
  unfold isingCoordinateLower at hl ⊢
  simp only [isingCoordinateReflect_apply_same]
  omega




theorem coordinateReflect_eq_of_adj_crossing
    (i : Fin d) (m : Int) {x y : Site d}
    (hxy : (hypercubicLattice d).Adj x y)
    (hxl : isingCoordinateLower i m x)
    (hyp : ¬ isingCoordinatePlane i m y)
    (hyl : ¬ isingCoordinateLower i m y) :
    isingCoordinateReflect i m x = y := by
  obtain ⟨a, b, rfl⟩ := adj_exists_dir hxy
  by_cases hai : a = i
  · subst a
    cases b with
    | false =>
        exfalso
        apply hyl
        unfold isingCoordinateLower at hxl ⊢
        simp [coordShift, stepSign]
        omega
    | true =>
        have hm : m = 2 * x i + 1 := by
          unfold isingCoordinateLower at hxl hyl
          unfold isingCoordinatePlane at hyp
          simp [coordShift, stepSign] at hyp hyl
          omega
        funext q
        by_cases hqi : q = i
        · subst q
          simp [coordShift, stepSign, hm]
          omega
        · rw [isingCoordinateReflect_apply_of_ne i q hqi]
          simp [coordShift, Function.update_of_ne hqi]
  · have hiUpdate : coordShift x a (stepSign b) i = x i := by
      simp [coordShift, Function.update_of_ne (Ne.symm hai)]
    rw [isingCoordinateLower, hiUpdate] at hyl
    exact absurd hxl hyl

theorem coordinateReflect_eq_of_adj_crossing_symm
    (i : Fin d) (m : Int) {x y : Site d}
    (hxy : (hypercubicLattice d).Adj x y)
    (hyl : isingCoordinateLower i m y)
    (hxp : ¬ isingCoordinatePlane i m x)
    (hxl : ¬ isingCoordinateLower i m x) :
    isingCoordinateReflect i m y = x :=
  coordinateReflect_eq_of_adj_crossing i m hxy.symm hyl hxp hxl



noncomputable def isingCoordinateSymmetricHull
    (K : Finset (Site d)) (i : Fin d) (m : Int) : Finset (Site d) :=
  K ∪ K.image (isingCoordinateReflect i m)

theorem subset_isingCoordinateSymmetricHull
    (K : Finset (Site d)) (i : Fin d) (m : Int) :
    K ⊆ isingCoordinateSymmetricHull K i m := by
  intro x hx
  exact Finset.mem_union_left _ hx

theorem mem_isingCoordinateSymmetricHull_reflect_iff
    (K : Finset (Site d)) (i : Fin d) (m : Int) (x : Site d) :
    x ∈ isingCoordinateSymmetricHull K i m ↔
      isingCoordinateReflect i m x ∈
        isingCoordinateSymmetricHull K i m := by
  classical
  unfold isingCoordinateSymmetricHull
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      apply Finset.mem_union_left
      rw [← hyx, isingCoordinateReflect_involutive]
      exact hy
  · intro hx
    have hr := (show isingCoordinateReflect i m
        (isingCoordinateReflect i m x) ∈
          K ∪ K.image (isingCoordinateReflect i m) by
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨isingCoordinateReflect i m x, hx, rfl⟩)
      · obtain ⟨y, hy, hyr⟩ := Finset.mem_image.mp hx
        apply Finset.mem_union_left
        rw [← hyr, isingCoordinateReflect_involutive]
        exact hy)
    simpa using hr

end StatMech.FrontierA
