/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABHypercubic

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABLatticeUnconditional`

The nearest-neighbour coupling `J_e = 1` on lattice edges (and `0` elsewhere) on `ℤ^d` satisfies
every hypothesis of `abl_aizenmanBarsky_hypercubic_neighbourSum`: it is nonnegative, supported on
lattice edges, translation invariant, and its row at the origin is finitely supported (inside the
box `Λ_1`), hence summable. The theorem then gives the Aizenman–Barsky inequality
`∂_β M ≤ |J| M ∂_h M` for this coupling, used here at `β = 1`, `h = 1` on `ℤ²`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABLatticeUnconditional

open _root_.StatMech _root_.StatMech.Sharpness _root_.StatMech.Lattice

open scoped Classical in
/-- The nearest-neighbour coupling: `1` on lattice edges, `0` elsewhere. -/
noncomputable def nnCoupling (d : ℕ) : Sym2 (Site d) → ℝ :=
  fun e => if e ∈ (hypercubicLattice d).edgeSet then 1 else 0

lemma nnCoupling_nonneg (d : ℕ) (e : Sym2 (Site d)) : 0 ≤ nnCoupling d e := by
  unfold nnCoupling; split_ifs <;> norm_num

lemma nnCoupling_support (d : ℕ) (x y : Site d) (h : ¬ (hypercubicLattice d).Adj x y) :
    nnCoupling d s(x, y) = 0 := by
  simp only [nnCoupling, SimpleGraph.mem_edgeSet]
  exact ite_eq_right h

lemma nnCoupling_translate (d : ℕ) (x u v : Site d) :
    nnCoupling d s(FK.fktc_translate x u, FK.fktc_translate x v) = nnCoupling d s(u, v) := by
  simp only [nnCoupling, SimpleGraph.mem_edgeSet, FK.fktc_translate_adj]

/-- The row of the nearest-neighbour coupling at the origin is supported in the box `Λ_1`, so it is
summable. -/
lemma nnCoupling_row_summable (d : ℕ) : Summable (fun y =>
    if (hypercubicLattice d).Adj (0 : Site d) y then nnCoupling d s(0, y) else 0) := by
  apply summable_of_ne_finset_zero (s := (box_finite d 1).toFinset)
  intro y hy
  have hyb : y ∉ box d 1 := by simpa using hy
  have hadj : ¬ (hypercubicLattice d).Adj (0 : Site d) y := by
    intro hadj
    apply hyb
    rw [hypercubicLattice_adj] at hadj
    intro i
    have hle := Finset.single_le_sum (f := fun i => ((0 : Site d) i - y i).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg] at hle hadj
    omega
  exact ite_eq_right hadj

-- The Aizenman–Barsky inequality for nearest-neighbour bond percolation on `ℤ^d`.
example (d : ℕ) : AizenmanBarskyInequalityPhysical
    (abigMag (hypercubicLattice d) (nnCoupling d) (0 : Site d))
    (∑' y, if (hypercubicLattice d).Adj (0 : Site d) y then nnCoupling d s(0, y) else 0) :=
  abl_aizenmanBarsky_hypercubic_neighbourSum (nnCoupling d) (nnCoupling_nonneg d)
    (nnCoupling_support d) (nnCoupling_translate d) (nnCoupling_row_summable d)

-- The inequality at `β = 1`, `h = 1` on `ℤ²`.
example : deriv (fun b => abigMag (hypercubicLattice 2) (nnCoupling 2) 0 b 1) 1 ≤
    (∑' y, if (hypercubicLattice 2).Adj (0 : Site 2) y then nnCoupling 2 s(0, y) else 0) *
      (abigMag (hypercubicLattice 2) (nnCoupling 2) 0 1 1 *
        deriv (fun t => abigMag (hypercubicLattice 2) (nnCoupling 2) 0 1 t) 1) :=
  abl_aizenmanBarsky_hypercubic_neighbourSum (nnCoupling 2) (nnCoupling_nonneg 2)
    (nnCoupling_support 2) (nnCoupling_translate 2) (nnCoupling_row_summable 2) 1 zero_le_one 1
    one_pos

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABLatticeUnconditional
