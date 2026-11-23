/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationVertexWeight

/-!
# Tests for realization vertex weights

These public-only consumers cover symbolic and concrete universes, exact
sigma evaluation, the finite positive-star cover, carrier positions, and a
boundary point of `Delta[2]` whose third coordinate is zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory
namespace SSetRealizationVertexWeightTests

#synth (Δ[0] : SSet.{u}).Finite
#synth (Δ[1] : SSet.{u}).Finite
#synth (Δ[2] : SSet.{u}).Finite
#synth (Δ[0] : SSet.{u}).Nonsingular
#synth (Δ[1] : SSet.{u}).Nonsingular
#synth (Δ[2] : SSet.{u}).Nonsingular

/-- Symbolic-universe weight client. -/
noncomputable example (p : (Δ[0] : SSet.{u}) _⦋0⦌) :
    C(SSet.toTop.obj (Δ[0] : SSet.{u}), ℝ) :=
  SSet.realizationVertexWeight (Δ[0] : SSet.{u}) p

/-- Universe-one star client. -/
noncomputable example (p : (Δ[1] : SSet.{1}) _⦋0⦌) :
    TopologicalSpace.Opens (SSet.toTop.obj (Δ[1] : SSet.{1})) :=
  SSet.nonsingularVertexStar (Δ[1] : SSet.{1}) p

/-- Universe-zero carrier-position client. -/
noncomputable example (p : (Δ[2] : SSet.{0}) _⦋0⦌)
    (z : SSet.toTop.obj (Δ[2] : SSet.{0}))
    (hz : z ∈ SSet.nonsingularVertexStar (Δ[2] : SSet.{0}) p) :
    Fin ((SSet.realizationInteriorCarrier (Δ[2] : SSet.{0}) z).carrier.dim + 1) :=
  SSet.nonsingularVertexStarPosition (Δ[2] : SSet.{0}) p z hz

/-- The public sigma formula is exact at arbitrary universe. -/
example (K : SSet.{u}) [K.Finite] [K.Nonsingular]
    (p : K _⦋0⦌) (s : K.N)
    (q : Convexity.StdSimplex ℝ (Fin (s.dim + 1))) :
    SSet.realizationVertexWeight K p (SSet.sigmaToTop K ⟨s, q⟩) =
      (q.map (SSet.simplexVertex K s)).weights p :=
  SSet.realizationVertexWeight_sigma K p s q

/-- A realized vertex is in its positive star. -/
example (K : SSet.{u}) [K.Finite] [K.Nonsingular] (p : K _⦋0⦌) :
    SSet.realizedVertex p ∈ SSet.nonsingularVertexStar K p :=
  SSet.realizedVertex_mem_nonsingularVertexStar K p

/-- The finite vertex-indexed star family covers the realization. -/
example (K : SSet.{u}) [K.Finite] [K.Nonsingular]
    (z : SSet.toTop.obj K) :
    ∃ p : K _⦋0⦌, z ∈ SSet.nonsingularVertexStar K p :=
  SSet.exists_mem_nonsingularVertexStar K z

/-- The selected carrier position has the requested vertex label. -/
example (K : SSet.{u}) [K.Finite] [K.Nonsingular]
    (p : K _⦋0⦌) (z : SSet.toTop.obj K)
    (hz : z ∈ SSet.nonsingularVertexStar K p) :
    SSet.simplexVertex K (SSet.realizationInteriorCarrier K z).carrier
        (SSet.nonsingularVertexStarPosition K p z hz) = p :=
  SSet.nonsingularVertexStarPosition_vertex K p z hz

/-- Carrier positions identify their vertex labels exactly. -/
example (K : SSet.{u}) [K.Finite] [K.Nonsingular]
    (p q : K _⦋0⦌) (z : SSet.toTop.obj K)
    (hp : z ∈ SSet.nonsingularVertexStar K p)
    (hq : z ∈ SSet.nonsingularVertexStar K q) :
    SSet.nonsingularVertexStarPosition K p z hp =
        SSet.nonsingularVertexStarPosition K q z hq ↔ p = q :=
  SSet.nonsingularVertexStarPosition_eq_iff K p q z hp hq

/-- Vertices of `Delta[2]`. -/
private noncomputable def deltaTwoVertex (i : Fin 3) :
    (Δ[2] : SSet.{u}) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm i

/-- The nondegenerate `0 -> 1` edge of `Delta[2]`. -/
private noncomputable def deltaTwoEdgeZeroOne : (Δ[2] : SSet.{u}).N :=
  SSet.N.mk
    (SSet.stdSimplex.edge 2 (0 : Fin 3) (1 : Fin 3) (by decide)) (by
      rw [SSet.stdSimplex.mem_nonDegenerate_iff_mono,
        SimplexCategory.mono_iff_injective]
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp_all [SSet.stdSimplex.edge])

/-- The midpoint of that edge, with both carrier coordinates positive. -/
private noncomputable def edgeMidpoint :
    Convexity.StdSimplex ℝ (Fin (deltaTwoEdgeZeroOne.{u}.dim + 1)) :=
  Convexity.StdSimplex.duple 0 1
    (s := (1 / 2 : ℝ)) (t := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)

/-- The corresponding boundary point of the realized two-simplex. -/
private noncomputable def deltaTwoBoundaryPoint :
    SSet.toTop.obj (Δ[2] : SSet.{u}) :=
  SSet.sigmaToTop (Δ[2] : SSet.{u})
    ⟨deltaTwoEdgeZeroOne.{u}, edgeMidpoint.{u}⟩

private theorem edgeLabel_ne_two
    (i : Fin (deltaTwoEdgeZeroOne.{u}.dim + 1)) :
    SSet.simplexVertex (Δ[2] : SSet.{u}) deltaTwoEdgeZeroOne i ≠
      deltaTwoVertex 2 := by
  fin_cases i <;> decide

/-- The boundary point has zero third-vertex weight, hence is outside the
third positive star. -/
private theorem deltaTwoBoundaryPoint_not_mem_thirdStar :
    deltaTwoBoundaryPoint.{u} ∉
      SSet.nonsingularVertexStar (Δ[2] : SSet.{u}) (deltaTwoVertex 2) := by
  intro hz
  rw [SSet.mem_nonsingularVertexStar_iff] at hz
  change 0 < SSet.realizationVertexWeight (Δ[2] : SSet.{u})
    (deltaTwoVertex 2)
    (SSet.sigmaToTop (Δ[2] : SSet.{u})
      ⟨deltaTwoEdgeZeroOne.{u}, edgeMidpoint.{u}⟩) at hz
  rw [SSet.realizationVertexWeight_sigma,
    Convexity.StdSimplex.weights_map_apply] at hz
  have he : Finset.univ.filter
      (fun i => SSet.simplexVertex (Δ[2] : SSet.{u})
        deltaTwoEdgeZeroOne i = deltaTwoVertex 2) = ∅ := by
    ext i
    simp [edgeLabel_ne_two]
  rw [he] at hz
  simp at hz

/-- Boundary-correct carrier membership: the chosen interior carrier has no
position labelled by the absent third vertex. -/
private theorem deltaTwoBoundaryCarrier_has_no_thirdPosition :
    ¬ ∃ i : Fin ((SSet.realizationInteriorCarrier
        (Δ[2] : SSet.{u}) deltaTwoBoundaryPoint).carrier.dim + 1),
      SSet.simplexVertex (Δ[2] : SSet.{u})
        (SSet.realizationInteriorCarrier
          (Δ[2] : SSet.{u}) deltaTwoBoundaryPoint).carrier i =
        deltaTwoVertex 2 := by
  intro h
  exact deltaTwoBoundaryPoint_not_mem_thirdStar
    ((SSet.mem_nonsingularVertexStar_iff_exists_position
      (Δ[2] : SSet.{u}) (deltaTwoVertex 2) deltaTwoBoundaryPoint).mpr h)

#print axioms SSet.sigmaVertexWeight_factorsThrough
#print axioms SSet.realizationVertexWeight
#print axioms SSet.exists_mem_nonsingularVertexStar
#print axioms SSet.mem_nonsingularVertexStar_iff_exists_position
#print axioms SSet.nonsingularVertexStarPosition_eq_iff

end SSetRealizationVertexWeightTests
end MathlibExtTest.AlgebraicTopology.TopologicalSpace.ModelCategory

end
