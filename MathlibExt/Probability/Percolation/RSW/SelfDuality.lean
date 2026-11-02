/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoundaryConditions
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual

/-!
# Self-duality on `ℤ²`: the self-dual point and primal/dual blocking

Two ingredients of planar duality for percolation-type models on `ℤ²`:

* the random-cluster duality relation `p p* / ((1 - p)(1 - p*)) = q` and its fixed point, the
  self-dual point `p_sd(q) = √q / (1 + √q)` (equal to `1/2` for Bernoulli percolation, `q = 1`),
  together with the exchange of free and wired boundary conditions under duality;
* the fact that a primal edge and its crossing dual edge are never both open, so an open primal
  path and an open dual path cannot cross.

## Main definitions

* `StatMech.RSW.dualParam`: the relation `p p* / ((1 - p)(1 - p*)) = q`.
* `StatMech.RSW.selfDualPoint`: `√q / (1 + √q)`.
* `StatMech.RSW.dualBC`: free ↔ wired, periodic ↦ periodic.

## Main results

* `StatMech.RSW.dualParam_self_iff`: `p ∈ (0, 1)` is self-dual iff `p = selfDualPoint q`.
* `StatMech.RSW.crossingPair_incompatible`, `StatMech.RSW.openWalk_blocks_dualWalk`: a primal open
  path and a dual open path never use a crossing pair of edges.

See also `StatMech.BeffaraDC.selfDualPoint` and `StatMech.BeffaraDC.dualParam` in PhyslibExt
(`RandomCluster/CriticalPoint/SelfDualValue`), which define the same self-dual point and the dual
parameter as a function of `p`.

## References

* G. Grimmett, *The Random-Cluster Model*, Springer, 2006, Chapter 6.
* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model
  is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012), 511–542.
-/

@[expose] public section

open SimpleGraph Real

namespace StatMech

namespace RSW

open StatMech.Lattice

/-- The random-cluster duality relation between `p` and `p*` at cluster weight `q`:
`p p* / ((1 - p)(1 - p*)) = q`. -/
def dualParam (p q pStar : ℝ) : Prop := p * pStar / ((1 - p) * (1 - pStar)) = q

/-- The self-dual point `p_sd(q) = √q / (1 + √q)` of the random-cluster model on `ℤ²`. -/
noncomputable def selfDualPoint (q : ℝ) : ℝ := Real.sqrt q / (1 + Real.sqrt q)

/-- `selfDualPoint q ∈ (0, 1)` for `q > 0`. -/
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

/-- `selfDualPoint q` is dual to itself. -/
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

/-- For `p ∈ (0, 1)` and `q > 0`, `p` is self-dual iff `p = selfDualPoint q`. -/
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

/-- Boundary conditions under planar duality: free and wired are exchanged, periodic is fixed. -/
def dualBC : BoundaryCondition → BoundaryCondition
  | .free => .wired
  | .wired => .free
  | .periodic => .periodic

@[simp] theorem dualBC_free : dualBC .free = .wired := rfl
@[simp] theorem dualBC_wired : dualBC .wired = .free := rfl
@[simp] theorem dualBC_periodic : dualBC .periodic = .periodic := rfl

@[simp] theorem dualBC_dualBC (bc : BoundaryCondition) : dualBC (dualBC bc) = bc := by
  cases bc <;> rfl

/-- A primal edge is open iff its crossing dual edge is not open.

See also `StatMech.Lattice.isOpen_iff_dual_isClosed`. -/
theorem isOpen_iff_not_dualCross_open (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : ω e = true ↔ ¬ dualConfig ω (crossEdge e) = true := by
  rw [Lattice.isOpen_iff_dual_isClosed]; simp [Bool.not_eq_true]

/-- The crossing dual edge of `e` is open iff `e` is closed.

See also `StatMech.Lattice.dual_isOpen_iff_isClosed`. -/
theorem dualCross_open_iff_closed (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : dualConfig ω (crossEdge e) = true ↔ ω e = false := by
  rw [Lattice.dual_isOpen_iff_isClosed, Equiv.symm_apply_apply]

/-- A primal edge and its crossing dual edge are never both open. -/
theorem crossingPair_incompatible (ω : ConfigSpace (Sym2 (Site 2)))
    (e : Sym2 (Site 2)) : ¬ (ω e = true ∧ dualConfig ω (crossEdge e) = true) := by
  rintro ⟨h1, h2⟩
  rw [isOpen_iff_not_dualCross_open] at h1
  exact h1 h2

/-- Every edge of a walk in the open subgraph is open. -/
theorem ConfigSpace.edge_of_mem_openWalk {ω : ConfigSpace (Sym2 (Site 2))}
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y) {e : Sym2 (Site 2)}
    (he : e ∈ w.edges) : ω e = true := by
  have hmem : e ∈ (openSubgraph 2 ω).edgeSet := w.edges_subset_edgeSet he
  revert hmem
  refine Sym2.ind (fun a b hmem => ?_) e
  rw [SimpleGraph.mem_edgeSet] at hmem
  exact hmem.2

/-- An open primal walk and an open dual walk never use a crossing pair of edges. -/
theorem openWalk_blocks_dualWalk (ω : ConfigSpace (Sym2 (Site 2)))
    {x y : Site 2} (w : (openSubgraph 2 ω).Walk x y)
    {x' y' : Site 2} (w' : (openSubgraph 2 (dualConfig ω)).Walk x' y')
    (e : Sym2 (Site 2)) (he : e ∈ w.edges) (he' : crossEdge e ∈ w'.edges) :
    False :=
  crossingPair_incompatible ω e
    ⟨ConfigSpace.edge_of_mem_openWalk w he,
     ConfigSpace.edge_of_mem_openWalk w' he'⟩

end RSW

end StatMech
