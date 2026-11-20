/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.IsingMarkovReflectionFold
import Code.Lattice.PathVisitsRow
import Code.Percolation.PcNontrivial

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation

variable {d : Nat}



def isingDiagonalShift (i j : Fin d) (c : Int) : Site d :=
  fun a => if a = i then c else if a = j then -c else 0



def isingDiagonalReflect (i j : Fin d) (c : Int) (x : Site d) : Site d :=
  fun a => x (Equiv.swap i j a) + isingDiagonalShift i j c a

@[simp] theorem isingDiagonalReflect_apply_i
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x : Site d) :
    isingDiagonalReflect i j c x i = x j + c := by
  simp [isingDiagonalReflect, isingDiagonalShift, hij]

@[simp] theorem isingDiagonalReflect_apply_j
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x : Site d) :
    isingDiagonalReflect i j c x j = x i - c := by
  simp [isingDiagonalReflect, isingDiagonalShift, Ne.symm hij, sub_eq_add_neg]

theorem isingDiagonalReflect_apply_of_ne
    (i j a : Fin d) (hai : a ≠ i) (haj : a ≠ j)
    (c : Int) (x : Site d) :
    isingDiagonalReflect i j c x a = x a := by
  simp [isingDiagonalReflect, isingDiagonalShift, hai, haj,
    Equiv.swap_apply_of_ne_of_ne]

@[simp] theorem isingDiagonalReflect_involutive
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x : Site d) :
    isingDiagonalReflect i j c (isingDiagonalReflect i j c x) = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [hij]
  · by_cases haj : a = j
    · subst a
      simp [hij, Ne.symm hij]
    · rw [isingDiagonalReflect_apply_of_ne i j a hai haj]
      rw [isingDiagonalReflect_apply_of_ne i j a hai haj]


def isingDiagonalReflectEquiv
    (i j : Fin d) (hij : i ≠ j) (c : Int) : Site d ≃ Site d where
  toFun := isingDiagonalReflect i j c
  invFun := isingDiagonalReflect i j c
  left_inv := isingDiagonalReflect_involutive i j hij c
  right_inv := isingDiagonalReflect_involutive i j hij c

theorem isingDiagonalReflect_sub
    (i j : Fin d) (c : Int) (x y : Site d) (a : Fin d) :
    isingDiagonalReflect i j c x a - isingDiagonalReflect i j c y a =
      x (Equiv.swap i j a) - y (Equiv.swap i j a) := by
  simp only [isingDiagonalReflect]
  ring


theorem hypercubicLattice_adj_diagonalReflect
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x y : Site d) :
    (hypercubicLattice d).Adj x y <->
      (hypercubicLattice d).Adj
        (isingDiagonalReflect i j c x) (isingDiagonalReflect i j c y) := by
  change (∑ a, (x a - y a).natAbs) = 1 ↔
    (∑ a, (isingDiagonalReflect i j c x a -
      isingDiagonalReflect i j c y a).natAbs) = 1
  have hsum :
      (∑ a : Fin d,
          (isingDiagonalReflect i j c x a -
            isingDiagonalReflect i j c y a).natAbs) =
        ∑ a : Fin d, (x a - y a).natAbs := by
    simp_rw [isingDiagonalReflect_sub]
    exact Equiv.sum_comp (Equiv.swap i j) (fun a => (x a - y a).natAbs)
  rw [hsum]

theorem isingDiagonalReflect_fixed
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x : Site d)
    (hx : x i - x j = c) :
    isingDiagonalReflect i j c x = x := by
  funext a
  by_cases hai : a = i
  · subst a
    simp [hij]
    omega
  · by_cases haj : a = j
    · subst a
      simp [hij, Ne.symm hij]
      omega
    · exact isingDiagonalReflect_apply_of_ne i j a hai haj c x

theorem isingDiagonalReflect_difference
    (i j : Fin d) (hij : i ≠ j) (c : Int) (x : Site d) :
    isingDiagonalReflect i j c x i - isingDiagonalReflect i j c x j =
      2 * c - (x i - x j) := by
  simp [hij]
  ring



theorem diagonalDifference_adj_le_one
    (i j : Fin d) (hij : i ≠ j) {x y : Site d}
    (hxy : (hypercubicLattice d).Adj x y) :
    (y i - y j - (x i - x j)).natAbs <= 1 := by
  obtain ⟨a, b, rfl⟩ := adj_exists_dir hxy
  by_cases hai : a = i
  · subst a
    by_cases hji : j = i
    · exact absurd hji (Ne.symm hij)
    · cases b <;> simp [coordShift, stepSign, hji]
  · by_cases haj : a = j
    · subst a
      cases b <;> simp [coordShift, stepSign, hij]
    · cases b <;>
        simp [coordShift, stepSign, Ne.symm hai, Ne.symm haj]



theorem diagonalPlane_separates_adjacent
    (i j : Fin d) (hij : i ≠ j) (c : Int) {x y : Site d}
    (hxy : (hypercubicLattice d).Adj x y)
    (hx : x i - x j < c) (hy : c < y i - y j) : False := by
  have hstep := diagonalDifference_adj_le_one i j hij hxy
  omega

end StatMech.FrontierA
