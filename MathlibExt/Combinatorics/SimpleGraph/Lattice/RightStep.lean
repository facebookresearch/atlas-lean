/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerFaces
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InsideConnected

/-!
# Moving right off a closed walk

For a closed walk `Vc` in the square lattice `ℤ²`, the right-step property `ecc_RightStep Vc R`
says that every outside site off `Vc` in a column at most `R` is joined, avoiding `Vc`, to a site
strictly further right. Iterating it, every such site reaches column `R + 1`. The property follows
from its restriction `ecc_RightDodge` to sites whose right neighbour is on `Vc`, and holds outright
when no right neighbour of such a site is on `Vc`.

The right-step property can fail: `StatMech.Lattice.edc_rightStep_refuted` gives a closed walk with
an outside site walled in on all four sides.

## Main definitions

* `StatMech.Lattice.ecc_RightStep Vc R`: outside off-walk sites in columns `≤ R` can move right.
* `StatMech.Lattice.ecc_RightDodge Vc R`: the same, for sites whose right neighbour is on `Vc`.

## Main results

* `StatMech.Lattice.ecc_reaches_right_band`: under the right-step property, outside off-walk sites
  reach column `R + 1` avoiding `Vc`.
* `StatMech.Lattice.ecc_rightStep_of_rightDodge`: the dodge property implies the right-step
  property.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}

/-- Every site outside `Vc` (even ray count), off `Vc`, and in a column at most `R` is joined by a
lattice path avoiding `Vc` to a site in a column strictly further right. -/
def ecc_RightStep (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w

/-- Under the right-step property, every outside site off `Vc` reaches a site in a column at least
`R + 1` by a lattice path avoiding `Vc` (induction on the distance to column `R + 1`). -/
theorem ecc_reaches_right_band (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hstep : ecc_RightStep Vc R)
    (z : Site 2) (hzout : z ∉ jec_leftRegion Vc) (hzoff : z ∉ Vc.support) :
    ∃ w : Site 2, (R : ℤ) + 1 ≤ w 0 ∧ (offSupport Vc).Reachable z w := by
  generalize hm : ((R : ℤ) + 1 - z 0).toNat = m
  induction m using Nat.strong_induction_on generalizing z with
  | _ m ih =>
    rcases le_or_gt ((R : ℤ) + 1) (z 0) with hge | hlt
    · exact ⟨z, hge, SimpleGraph.Reachable.refl _⟩
    · have hzR : z 0 ≤ (R : ℤ) := by omega
      obtain ⟨w, hprog, hreach⟩ := hstep z hzout hzoff hzR
      have hwoff : w ∉ Vc.support := offSupportComponent_offSupport Vc hzoff hreach
      have hwout : w ∉ jec_leftRegion Vc :=
        offSupport_component_monochromatic_out Vc hzout hreach hzoff
      have hmw : ((R : ℤ) + 1 - w 0).toNat < m := by rw [← hm]; omega
      obtain ⟨u, hu, hwu⟩ := ih _ hmw w hwout hwoff rfl
      exact ⟨u, hu, hreach.trans hwu⟩

/-- An off-walk site whose right neighbour is off `Vc` reaches that neighbour avoiding `Vc`. -/
theorem ecc_rightNeighbor_step (Vc : (hypercubicLattice 2).Walk a a) {z : Site 2}
    (hzoff : z ∉ Vc.support) (hnbOff : (![z 0 + 1, z 1] : Site 2) ∉ Vc.support) :
    (offSupport Vc).Reachable z ![z 0 + 1, z 1] := by
  have hadj : (hypercubicLattice 2).Adj z ![z 0 + 1, z 1] := by
    have h := hadj_step (z 0) (z 1)
    have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
    rw [hzeq]; exact h
  exact (Adj.reachable ⟨hadj, hzoff, hnbOff⟩ : (offSupport Vc).Reachable _ _)

/-- The right-step property restricted to sites whose right neighbour is on `Vc`: such a site
still reaches a site further right avoiding `Vc`. -/
def ecc_RightDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
    (![z 0 + 1, z 1] : Site 2) ∈ Vc.support →
    ∃ w : Site 2, z 0 < w 0 ∧ (offSupport Vc).Reachable z w

/-- The dodge property implies the right-step property: sites with a free right neighbour step
right directly. -/
theorem ecc_rightStep_of_rightDodge (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hdodge : ecc_RightDodge Vc R) : ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  by_cases hnb : (![z 0 + 1, z 1] : Site 2) ∈ Vc.support
  · exact hdodge z hzout hzoff hzR hnb
  · exact ⟨![z 0 + 1, z 1], by simp, ecc_rightNeighbor_step Vc hzoff hnb⟩

theorem ecc_rightStep_of_rightNeighbor_offSupport (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hnb : ∀ z : Site 2, z ∉ jec_leftRegion Vc → z ∉ Vc.support → z 0 ≤ (R : ℤ) →
        (![z 0 + 1, z 1] : Site 2) ∉ Vc.support) :
    ecc_RightStep Vc R := by
  intro z hzout hzoff hzR
  exact ⟨![z 0 + 1, z 1], by simp,
    ecc_rightNeighbor_step Vc hzoff (hnb z hzout hzoff hzR)⟩

end Lattice

end StatMech
