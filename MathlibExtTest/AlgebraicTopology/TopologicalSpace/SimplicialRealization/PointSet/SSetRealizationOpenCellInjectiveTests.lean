/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationOpenCellInjective

/-!
# Open-cell carrier uniqueness regression

Direct symbolic-universe client of
`SSet.carrier_eq_of_sigmaToTop_eq_of_interior`: the two distinct
zero-dimensional vertex carriers of `Δ[1]` share the unique positive point of
`Convexity.StdSimplex ℝ (Fin 1)`, yet their `SSet.sigmaToTop` images differ.
The test also pins dimension zero and demonstrates that carrier data alone do
not determine barycentric coordinates.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory.SSetRealizationOpenCellInjectiveTests

/-- The two vertices of `Δ[1]`, at fixed degree `0`. -/
def vertex : Fin 2 → (Δ[1] : SSet.{u}) _⦋0⦌ :=
  fun i => SSet.stdSimplex.const 1 i _

/-- Unique point of the topological `0`-simplex. -/
noncomputable def pt0 : Convexity.StdSimplex ℝ (Fin 1) :=
  Convexity.StdSimplex.single 0

private theorem pt0_pos : ∀ i, 0 < pt0.weights i := by
  intro i
  rw [Convexity.StdSimplex.weights_apply_eq_one pt0 i]
  norm_num

/-- The two vertex carriers have distinct `sigmaToTop` images. -/
theorem vertex_sigmaToTop_ne :
    SSet.sigmaToTop (Δ[1] : SSet.{u})
        ⟨SSet.N.mk (vertex 0) (by simp [SSet.nonDegenerate_zero, vertex]), pt0⟩ ≠
      SSet.sigmaToTop (Δ[1] : SSet.{u})
        ⟨SSet.N.mk (vertex 1) (by simp [SSet.nonDegenerate_zero, vertex]), pt0⟩ := by
  intro h
  have hcar := SSet.carrier_eq_of_sigmaToTop_eq_of_interior
    (Δ[1] : SSet.{u}) _ _ _ _ pt0_pos pt0_pos h
  have hToS := congrArg SSet.N.toS hcar
  have hVert : vertex.{u} 0 = vertex.{u} 1 := (SSet.S.ext_iff _ _).mp hToS
  have h0 : SSet.stdSimplex.obj₀Equiv (vertex.{u} 0) = (0 : Fin 2) := by
    simp [vertex, SSet.stdSimplex.const]
  have h1 : SSet.stdSimplex.obj₀Equiv (vertex.{u} 1) = (1 : Fin 2) := by
    simp [vertex, SSet.stdSimplex.const]
  rw [hVert] at h0
  exact absurd (h1.symm.trans h0) (by decide)

private noncomputable def pQuarter : Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.duple (0 : Fin 2) (1 : Fin 2)
    (s := (1 / 4 : ℝ)) (t := (3 / 4 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)

private noncomputable def pHalf : Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.barycenter

private theorem pQuarter_pos : ∀ i, 0 < pQuarter.weights i := by
  intro i
  fin_cases i <;> simp [pQuarter, Convexity.StdSimplex.weights_duple]

private theorem pHalf_pos : ∀ i, 0 < pHalf.weights i := by
  intro i
  simp [pHalf, Convexity.StdSimplex.weights_barycenter_apply]

private theorem pQuarter_ne_pHalf : pQuarter ≠ pHalf := by
  intro h
  have hQuarter : pQuarter.weights 0 = (1 / 4 : ℝ) := by
    simp [pQuarter, Convexity.StdSimplex.weights_duple]
  have hHalf : pHalf.weights 0 = (1 / 2 : ℝ) := by
    simp [pHalf, Convexity.StdSimplex.weights_barycenter_apply]
  rw [h, hHalf] at hQuarter
  norm_num at hQuarter

/-- Equal carrier data alone do not identify distinct interior coordinates. -/
theorem equal_carrier_different_coordinates :
    ∃ (s : (Δ[1] : SSet.{u}).N)
      (p q : Convexity.StdSimplex ℝ (Fin (s.dim + 1))),
      (∀ i, 0 < p.weights i) ∧ (∀ i, 0 < q.weights i) ∧ p ≠ q := by
  let s : (Δ[1] : SSet.{u}).N :=
    SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))
      (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate 1)
  exact ⟨s, pQuarter, pHalf, pQuarter_pos, pHalf_pos, pQuarter_ne_pHalf⟩

/-- The carrier theorem applies uniformly in dimension zero. -/
theorem dimension_zero_self_carrier :
    SSet.N.mk (vertex.{u} 0)
        (by simp [SSet.nonDegenerate_zero, vertex]) =
      SSet.N.mk (vertex.{u} 0)
        (by simp [SSet.nonDegenerate_zero, vertex]) := by
  apply SSet.carrier_eq_of_sigmaToTop_eq_of_interior
    (Δ[1] : SSet.{u}) _ _ pt0 pt0 pt0_pos pt0_pos
  rfl

/-- Concrete universe-one specialization. -/
theorem vertex_sigmaToTop_ne_universeOne :
    SSet.sigmaToTop (Δ[1] : SSet.{1})
        ⟨SSet.N.mk (vertex 0) (by simp [SSet.nonDegenerate_zero, vertex]), pt0⟩ ≠
      SSet.sigmaToTop (Δ[1] : SSet.{1})
        ⟨SSet.N.mk (vertex 1) (by simp [SSet.nonDegenerate_zero, vertex]), pt0⟩ :=
  vertex_sigmaToTop_ne

/-- Original universe-zero specialization. -/
theorem vertex_sigmaToTop_ne_universeZero :
    SSet.sigmaToTop (Δ[1] : SSet.{0})
        ⟨SSet.N.mk (vertex 0) (by simp [SSet.nonDegenerate_zero, vertex]), pt0⟩ ≠
      SSet.sigmaToTop (Δ[1] : SSet.{0})
        ⟨SSet.N.mk (vertex 1) (by simp [SSet.nonDegenerate_zero, vertex]), pt0⟩ :=
  vertex_sigmaToTop_ne

/-- Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.HasNormCarrier

#print axioms SSet.carrier_eq_of_sigmaToTop_eq_of_interior
#print axioms vertex_sigmaToTop_ne
#print axioms equal_carrier_different_coordinates
#print axioms dimension_zero_self_carrier
#print axioms vertex_sigmaToTop_ne_universeOne
#print axioms vertex_sigmaToTop_ne_universeZero

end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory.SSetRealizationOpenCellInjectiveTests
