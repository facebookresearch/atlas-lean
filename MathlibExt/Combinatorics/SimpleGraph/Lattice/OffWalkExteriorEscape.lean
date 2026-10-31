/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.ReachesExteriorConnected

/-!
# Escaping to the exterior of a box avoiding a closed walk

Let `Vc` be a closed walk in the square lattice `ℤ²` whose vertices lie in the box `[-R, R]²`.
Sites of the exterior of the box are connected to each other by lattice paths avoiding `Vc`
(`arcxc_exterior_reachable_offSupport`), so a site reaches every exterior site off `Vc` as soon as
it reaches one of them. Straight vertical or
horizontal segments from a site to the exterior that miss `Vc` give such escapes, and every site off
`Vc` in a row at height at least `R` escapes upward.

The file also records which off-walk connectivity hypotheses about the even–odd inside
`jec_leftRegion Vc` can never hold. The inside and outside are defined for every site, including the
vertices of `Vc` (a site `z` is labeled by the unit face with upper right corner `z`). A vertex of
`Vc` in its leftmost column is always outside, and the inside, when nonempty, always contains a
vertex of `Vc` (`oc_exists_support_not_leftRegion`, `oc_leftRegion_meets_support`, proved in
`JordanExteriorClosure`). Hence the predicates `oc_OutsideReachesExterior` (for a walk inside the
box) and `oc_OutsideReachesTop` of this file are unsatisfiable.

## Main definitions

* `StatMech.Lattice.oc_supportSet Vc`: the set of vertices of `Vc`.
* `StatMech.Lattice.oc_OutsideReachesExterior Vc R`: every site outside `Vc` reaches the exterior of
  the box avoiding `Vc`.
* `StatMech.Lattice.oc_OutsideReachesTop Vc R`: every site outside `Vc` reaches a row at height at
  least `R` by a lattice path avoiding `Vc`.

## Main results

* `StatMech.Lattice.oc_reachesExterior_of_vertUpClear` and its three siblings: a clear straight
  segment to the exterior gives an escape.
* `StatMech.Lattice.oc_reachesExterior_of_row_ge_R`: sites off `Vc` at height at least `R` escape.
* `StatMech.Lattice.oc_not_outsideReachesExterior`, `StatMech.Lattice.oc_not_outsideReachesTop`:
  the two predicates above are unsatisfiable.
-/

@[expose] public section

open Set SimpleGraph Function

namespace StatMech

namespace Lattice

variable {a : Site 2}

/-- The set of vertices visited by the closed walk `Vc`. -/
def oc_supportSet (Vc : (hypercubicLattice 2).Walk a a) : Set (Site 2) :=
  {z | z ∈ Vc.support}

@[simp] theorem oc_mem_supportSet (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2) :
    z ∈ oc_supportSet Vc ↔ z ∈ Vc.support := Iff.rfl

/-- Every site outside the closed walk `Vc` (even ray count) reaches some site of the exterior of
the box `[-R, R]²` in the lattice with the vertices of `Vc` removed.

When `Vc` lies in the box this never holds: a vertex of `Vc` in its leftmost column is outside, is
isolated once the vertices of `Vc` are removed, and is not exterior
(`StatMech.Lattice.oc_not_outsideReachesExterior`). -/
def oc_OutsideReachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z, z ∉ jec_leftRegion Vc →
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e

theorem oc_exterior_reachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2} (hz : z ∈ exterior 2 R) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e :=
  ⟨z, hz, SimpleGraph.Reachable.refl _⟩

theorem oc_reachesExterior_of_offSupport_walk (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z e : Site 2} (heExt : e ∈ exterior 2 R)
    (p : (hypercubicLattice 2).Walk z e) (hp : ∀ w ∈ p.support, w ∉ Vc.support) :
    ∃ e' : Site 2, e' ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e' := by
  have hzoff : z ∉ Vc.support := hp z p.start_mem_support
  refine ⟨e, heExt, ?_⟩
  rw [ffc_reachable_iff_offSupportWalk (B := oc_supportSet Vc) hzoff]
  exact ⟨p, hp⟩

/-- If the vertical segment from `z` up to row `R + 1` misses `Vc`, it is a path from `z` to the
exterior of the box avoiding `Vc`. -/
theorem oc_vertUpEscape (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      ∃ p : (hypercubicLattice 2).Walk z e, ∀ w ∈ p.support, w ∉ Vc.support := by
  set e : Site 2 := ![z 0, (R : ℤ) + 1] with he
  have heExt : e ∈ exterior 2 R := arcxc_mem_exterior_of_row_high R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).copy hzeq.symm rfl with hp
  refine ⟨e, heExt, p, ?_⟩
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact hclear w hw

theorem oc_reachesExterior_of_vertUpClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2}
    (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  obtain ⟨e, heExt, p, hp⟩ := oc_vertUpEscape Vc R hclear
  exact oc_reachesExterior_of_offSupport_walk Vc R heExt p hp

/-- If the horizontal segment from `z` right to column `R + 1` misses `Vc`, it is a path from `z`
to the exterior of the box avoiding `Vc`. -/
theorem oc_horizRightEscape (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      ∃ p : (hypercubicLattice 2).Walk z e, ∀ w ∈ p.support, w ∉ Vc.support := by
  set e : Site 2 := ![(R : ℤ) + 1, z 1] with he
  have heExt : e ∈ exterior 2 R := arcxc_mem_exterior_of_col_high R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).copy hzeq.symm rfl with hp
  refine ⟨e, heExt, p, ?_⟩
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact hclear w hw

theorem oc_reachesExterior_of_horizRightClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2}
    (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) ((R : ℤ) + 1)).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  obtain ⟨e, heExt, p, hp⟩ := oc_horizRightEscape Vc R hclear
  exact oc_reachesExterior_of_offSupport_walk Vc R heExt p hp

theorem oc_mem_exterior_of_row_low (R : ℕ) {z : Site 2} (hz : z 1 ≤ -((R : ℤ) + 1)) :
    z ∈ exterior 2 R := by
  refine ⟨1, ?_⟩
  have h2 : (R : ℤ) < |z 1| := by
    have : z 1 < -(R : ℤ) := by omega
    calc (R : ℤ) = -(-(R : ℤ)) := by ring
      _ < -(z 1) := by omega
      _ ≤ |z 1| := neg_le_abs _
  rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2

theorem oc_mem_exterior_of_col_low (R : ℕ) {z : Site 2} (hz : z 0 ≤ -((R : ℤ) + 1)) :
    z ∈ exterior 2 R := by
  refine ⟨0, ?_⟩
  have h2 : (R : ℤ) < |z 0| := by
    have : z 0 < -(R : ℤ) := by omega
    calc (R : ℤ) = -(-(R : ℤ)) := by ring
      _ < -(z 0) := by omega
      _ ≤ |z 0| := neg_le_abs _
  rw [Int.abs_eq_natAbs] at h2; exact_mod_cast h2

theorem oc_reachesExterior_of_vertDownClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2}
    (hclear : ∀ w ∈ (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  set e : Site 2 := ![z 0, -((R : ℤ) + 1)] with he
  have heExt : e ∈ exterior 2 R := oc_mem_exterior_of_row_low R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_vertSeg (z 0) (z 1) (-((R : ℤ) + 1))).copy hzeq.symm rfl with hp
  apply oc_reachesExterior_of_offSupport_walk Vc R heExt p
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact hclear w hw

theorem oc_reachesExterior_of_horizLeftClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    {z : Site 2}
    (hclear : ∀ w ∈ (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).support, w ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  set e : Site 2 := ![-((R : ℤ) + 1), z 1] with he
  have heExt : e ∈ exterior 2 R := oc_mem_exterior_of_col_low R (by rw [he]; simp)
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_horizSeg (z 1) (z 0) (-((R : ℤ) + 1))).copy hzeq.symm rfl with hp
  apply oc_reachesExterior_of_offSupport_walk Vc R heExt p
  intro w hw
  rw [hp, SimpleGraph.Walk.support_copy] at hw
  exact hclear w hw

theorem oc_vertUp_support_col {z : Site 2} {R : ℕ} {w : Site 2}
    (hw : w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support) :
    ∃ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) ∧ w = ![z 0, t] :=
  (sw_vertSeg_mem_support (z 0) (z 1) ((R : ℤ) + 1) w).mp hw

theorem oc_vertUp_clear_of_colClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    ∀ w ∈ (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).support, w ∉ Vc.support := by
  intro w hw
  obtain ⟨t, ht, rfl⟩ := oc_vertUp_support_col hw
  exact hcol t ht

theorem oc_reachesExterior_of_colClear (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e :=
  oc_reachesExterior_of_vertUpClear Vc R (oc_vertUp_clear_of_colClear Vc R hcol)

/-- A site off `Vc` at height at least `R`, with `Vc` in the box `[-R, R]²`, reaches the exterior
avoiding `Vc`: at height `R` the segment up to row `R + 1` can only meet `Vc` at the site itself. -/
theorem oc_reachesExterior_of_row_ge_R (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) {z : Site 2}
    (hzrow : (R : ℤ) ≤ z 1) (hzoff : z ∉ Vc.support) :
    ∃ e : Site 2, e ∈ exterior 2 R ∧
      (ffc_offSupportLattice (oc_supportSet Vc)).Reachable z e := by
  rcases lt_or_ge (R : ℤ) (z 1) with hlt | hge
  · exact oc_exterior_reachesExterior Vc R (arcxc_mem_exterior_of_row_high R (by omega))
  · have hzR : z 1 = R := le_antisymm hge hzrow
    apply oc_reachesExterior_of_colClear Vc R
    intro t ht hmem
    rw [Set.mem_uIcc] at ht
    have htbox : (![z 0, t] : Site 2) ∈ box 2 R := hsupp hmem
    have htabs : (t).natAbs ≤ R := by have := htbox 1; simpa using this
    have htle : t ≤ (R : ℤ) := by
      have : |t| ≤ (R : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast htabs
      exact (abs_le.mp this).2
    have htR : t = (R : ℤ) := by omega
    subst htR
    have hzeq : (![z 0, (R : ℤ)] : Site 2) = z := by
      ext i; fin_cases i
      · simp
      · change (R : ℤ) = z 1; rw [hzR]
    rw [hzeq] at hmem
    exact hzoff hmem

/-- Every site outside the closed walk `Vc` is joined to a site at height at least `R` by a lattice
path avoiding `Vc`.

This never holds: it forces every outside site off `Vc`, while some vertex of `Vc` is outside
(`StatMech.Lattice.oc_not_outsideReachesTop`). -/
def oc_OutsideReachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) : Prop :=
  ∀ z, z ∉ jec_leftRegion Vc →
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support

theorem oc_top_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hzrow : (R : ℤ) ≤ z 1) (hzoff : z ∉ Vc.support) :
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
  refine ⟨z, hzrow, SimpleGraph.Walk.nil, ?_⟩
  intro u hu
  rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hu
  exact hu ▸ hzoff

theorem oc_colClear_reachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) {z : Site 2}
    (hcol : ∀ t : ℤ, t ∈ Set.uIcc (z 1) ((R : ℤ) + 1) → (![z 0, t] : Site 2) ∉ Vc.support) :
    ∃ w : Site 2, (R : ℤ) ≤ w 1 ∧
      ∃ p : (hypercubicLattice 2).Walk z w, ∀ u ∈ p.support, u ∉ Vc.support := by
  set e : Site 2 := ![z 0, (R : ℤ) + 1] with he
  have hzeq : z = ![z 0, z 1] := by ext i; fin_cases i <;> simp
  set p : (hypercubicLattice 2).Walk z e :=
    (sw_vertSeg (z 0) (z 1) ((R : ℤ) + 1)).copy hzeq.symm rfl with hp
  refine ⟨e, by rw [he]; simp, p, ?_⟩
  intro u hu
  rw [hp, SimpleGraph.Walk.support_copy] at hu
  exact oc_vertUp_clear_of_colClear Vc R hcol u hu

/-! ### Unsatisfiable off-walk hypotheses

The refutations of the off-walk connectivity hypotheses for `jec_leftRegion`
(`oc_exists_support_not_leftRegion`, `oc_leftRegion_meets_support`, `oc_not_hInOff`,
`oc_not_hOutOff`, ...) live in `JordanExteriorClosure`, and `oc_ffc_reachable_eq_of_mem` in
`FloodFillConnected`; this section applies them to the predicates of this file. -/

/-- `StatMech.Lattice.oc_OutsideReachesExterior` never holds for a closed walk in the box. -/
theorem oc_not_outsideReachesExterior (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ)
    (hsupp : oc_supportSet Vc ⊆ box 2 R) : ¬ oc_OutsideReachesExterior Vc R := by
  intro h
  obtain ⟨v, hv, hout, -⟩ := oc_exists_support_not_leftRegion Vc
  obtain ⟨e, he, hve⟩ := h v hout
  have := oc_ffc_reachable_eq_of_mem (B := oc_supportSet Vc) hv hve
  subst this
  exact arcxc_exterior_offSupport hsupp he hv

/-- `StatMech.Lattice.oc_OutsideReachesTop` never holds. -/
theorem oc_not_outsideReachesTop (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ) :
    ¬ oc_OutsideReachesTop Vc R := by
  intro h
  refine oc_not_forall_outside_offSupport Vc fun s hs => ?_
  obtain ⟨w, -, pw, hpw⟩ := h s hs
  exact hpw s pw.start_mem_support

end Lattice

end StatMech
