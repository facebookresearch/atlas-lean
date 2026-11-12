/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































import Mathlib
import Code.Foundations.ConfigSpace
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Lattice.PlanarDual
import Code.Lattice.BoundaryConditions

open SimpleGraph Real

namespace StatMech

namespace RSW

open StatMech.Lattice












def dualParam (p q pStar : ℝ) : Prop := p * pStar / ((1 - p) * (1 - pStar)) = q



noncomputable def selfDualPoint (q : ℝ) : ℝ := Real.sqrt q / (1 + Real.sqrt q)


theorem selfDualPoint_mem_Ioo {q : ℝ} (hq : 0 < q) :
    selfDualPoint q ∈ Set.Ioo (0 : ℝ) 1 := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have h1s : (0 : ℝ) < 1 + Real.sqrt q := by linarith
  refine ⟨?_, ?_⟩
  · rw [selfDualPoint]; positivity
  · rw [selfDualPoint, div_lt_one h1s]; linarith

theorem selfDualPoint_pos {q : ℝ} (hq : 0 < q) : 0 < selfDualPoint q :=
  (selfDualPoint_mem_Ioo hq).1

theorem selfDualPoint_lt_one {q : ℝ} (hq : 0 < q) : selfDualPoint q < 1 :=
  (selfDualPoint_mem_Ioo hq).2




theorem dualParam_selfDualPoint {q : ℝ} (hq : 0 < q) :
    dualParam (selfDualPoint q) q (selfDualPoint q) := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  set s := Real.sqrt q with hsdef
  have h1s : (0 : ℝ) < 1 + s := by linarith
  have hp : selfDualPoint q = s / (1 + s) := rfl
  rw [dualParam, hp]
  have h1p : 1 - s / (1 + s) = 1 / (1 + s) := by field_simp; ring
  rw [h1p, div_mul_div_comm, div_mul_div_comm, div_div_div_cancel_right₀]
  · rw [mul_one]; nlinarith [hsq]
  · positivity





theorem dualParam_self_iff {q : ℝ} (hq : 0 < q) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    dualParam p q p ↔ p = selfDualPoint q := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have h1p : (0 : ℝ) < 1 - p := by linarith
  set s := Real.sqrt q with hsdef
  have h1s : (0 : ℝ) < 1 + s := by linarith
  rw [dualParam, selfDualPoint, ← hsdef]
  constructor
  · intro h
    have hmul : p * p = q * ((1 - p) * (1 - p)) := by field_simp at h; linarith [h]
    
    have hpe : p = s * (1 - p) := by
      have hpos : 0 < s * (1 - p) := mul_pos hs h1p
      nlinarith [hmul, hsq, hp0, hpos, mul_pos hp0 hp0]
    field_simp
    nlinarith [hpe]
  · intro h; subst h
    have h1pe : 1 - s / (1 + s) = 1 / (1 + s) := by field_simp; ring
    rw [div_mul_div_comm, h1pe, div_mul_div_comm, div_div_div_cancel_right₀]
    · rw [mul_one]; nlinarith [hsq]
    · positivity










def dualBC : BoundaryCondition → BoundaryCondition
  | .free => .wired
  | .wired => .free
  | .periodic => .periodic

@[simp] theorem dualBC_free : dualBC .free = .wired := rfl
@[simp] theorem dualBC_wired : dualBC .wired = .free := rfl
@[simp] theorem dualBC_periodic : dualBC .periodic = .periodic := rfl




@[simp] theorem dualBC_dualBC (bc : BoundaryCondition) : dualBC (dualBC bc) = bc := by
  cases bc <;> rfl












theorem isOpen_iff_not_dualCross_open (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : ω e = true ↔ ¬ dualConfig ω (crossEdge e) = true := by
  rw [Lattice.isOpen_iff_dual_isClosed]; simp [Bool.not_eq_true]




theorem dualCross_open_iff_closed (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : dualConfig ω (crossEdge e) = true ↔ ω e = false := by
  rw [Lattice.dual_isOpen_iff_isClosed, Equiv.symm_apply_apply]





theorem crossingPair_incompatible (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) := by
  rintro ⟨h1, h2⟩
  rw [isOpen_iff_not_dualCross_open] at h1
  exact h1 h2



theorem ConfigSpace.edge_of_mem_openWalk {ω : ConfigSpace (Sym2 (Site 2))}
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y) {e : Sym2 (Site 2)}
    (he : e ∈ w.edges) : ω e = true := by
  have hmem : e ∈ (openSubgraph 2 ω).edgeSet := w.edges_subset_edgeSet he
  revert hmem
  refine Sym2.ind (fun a b hmem => ?_) e
  rw [SimpleGraph.mem_edgeSet] at hmem
  exact hmem.2















theorem openWalk_blocks_dualWalk (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  crossingPair_incompatible ω e
    ⟨ConfigSpace.edge_of_mem_openWalk w he,
     ConfigSpace.edge_of_mem_openWalk w' he'⟩






theorem dualConfig_involutive (ω : ConfigSpace (Sym2 (Site 2))) (e : Sym2 (Site 2)) :
    dualConfig (dualConfig ω) e = ω (crossEdge.symm (crossEdge.symm e)) :=
  Lattice.dualConfig_dualConfig ω e

end RSW

end StatMech
