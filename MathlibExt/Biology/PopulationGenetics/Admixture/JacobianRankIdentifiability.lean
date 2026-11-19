/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.LocalInverseBridge
public import MathlibExt.Analysis.Calculus.Jacobian
public import MathlibExt.Biology.PopulationGenetics.Admixture.LinearIdentifiability
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Jacobian-rank identifiability for a three-population admixture graph

Populations are `A = 0`, `B = 1`, `C = 2`; the four drift edges are the shared
stem above the `A`/`B` split, the `A` edge, the `B` edge, and `C`'s private
edge after admixture. The five parameters are `p = (α, s, a, b, c)`: the
admixture proportion `α` of `C` from the `A` lineage and the four edge lengths
`s, a, b, c`. The parametrization
`threePopF2 p = (f2 A B, f2 A C, f2 B C) = (a + b, (1 - α)² (a + b) + c, α² (a + b) + c)`
is identified with the `f2` vector of the drift model with weights
`threePopWeights α`. Its Jacobian has rank exactly `3` whenever `a + b ≠ 0`,
so no parameter point with `a + b ≠ 0` is locally identifiable from `f2`
statistics: the map does not see the stem length `s` nor the split of
`a + b` between `a` and `b`, as `threePopF2_eq_shift` shows globally. The
general criterion used for the converse direction (an injective derivative
implies local injectivity) is
`LocalInverseBridge.exists_mem_nhds_injOn_of_contDiffAt_injective`, and the
three-leaf star tree is the positive example: its length-to-`f2` map is
globally, hence locally, injective with everywhere injective derivative.

## Main results

* `threePopWeights`, `threePopF2`, `threePopF2_eq_f2`: the parametrization and
  its identification with drift-model `f2` statistics.
* `threePopF2_jacobian_rank`, `threePopF2_not_injective_fderiv`: rank `3 < 5`
  and failure of local identifiability.
* `threePopF2_eq_shift`: the unidentified directions.
* `starTreeF2_injective`, `starTreeF2_injective_fderiv`: the tree example.

## References

* N. Patterson et al., "Ancient admixture in human history", *Genetics* 192
  (2012), 1065–1093 (admixture graphs and f-statistics).
* S. Sankararaman et al. / qpGraph literature on graph parameter
  identifiability from f-statistics.
-/

@[expose] public section

open Filter Set Matrix MeasureTheory
  MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped Topology

namespace MathlibExt.Biology.PopulationGenetics.Admixture

/-- Lineage weights of the three-population admixture model on four edges
(shared stem, `A` edge, `B` edge, `C` private edge): populations `A = 0` and
`B = 1` have binary weights on the stem and their own edge; `C = 2` is the
`α : 1 - α` mixture of the `A` and `B` lineages followed by private drift. -/
def threePopWeights (α : ℝ) : Fin 3 → Fin 4 → ℝ :=
  !![1, 1, 0, 0; 1, 0, 1, 0; 1, α, 1 - α, 1]

/-- The parametrization `(α, s, a, b, c) ↦ (f2 A B, f2 A C, f2 B C)` of the
three-population admixture graph, as an explicit polynomial map. -/
def threePopF2 (p : Fin 5 → ℝ) : Fin 3 → ℝ :=
  ![p 2 + p 3, (1 - p 0) ^ 2 * (p 2 + p 3) + p 4, (p 0) ^ 2 * (p 2 + p 3) + p 4]

/-- The polynomial map is the `f2` vector of the drift model with weights
`threePopWeights α` and edge lengths `(s, a, b, c)`; such a model
exists for nonnegative lengths by the drift-model realization of arbitrary
weights and nonnegative lengths already on main. -/
theorem threePopF2_eq_f2 {α s a b c : ℝ}
    (M : DriftModel (Measure.count : Measure (Fin 4)) (Fin 4) (Fin 3))
    (hw : M.weight = threePopWeights α) (hl : M.len = ![s, a, b, c]) :
    threePopF2 ![α, s, a, b, c] =
      ![f2 Measure.count M.freq 0 1, f2 Measure.count M.freq 0 2,
        f2 Measure.count M.freq 1 2] := by
  funext i
  have h2 : ∀ X Y : Fin 3, f2 Measure.count M.freq X Y =
      ∑ e, (M.weight X e - M.weight Y e) ^ 2 * M.len e := fun X Y => M.f2_freq X Y
  fin_cases i <;>
    simp [threePopF2, h2, hw, hl, threePopWeights, Fin.sum_univ_four] <;> ring

/-! Private Jacobian computation for `threePopF2`. -/

private noncomputable def coordProj (i : Fin 5) : (Fin 5 → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 5 => ℝ) i

private theorem threePopF2_comp1_hasFDerivAt (p : Fin 5 → ℝ) :
    HasFDerivAt (fun p : Fin 5 → ℝ => (1 - p 0) ^ 2 * (p 2 + p 3) + p 4)
      (((1 - p 0) ^ 2) • (coordProj 2 + coordProj 3)
        + (-2 * (1 - p 0) * (p 2 + p 3)) • coordProj 0 + coordProj 4) p := by
  have h0 : HasFDerivAt (fun p : Fin 5 → ℝ => p 0) (coordProj 0) p :=
    (coordProj 0).hasFDerivAt
  have h1 : HasFDerivAt (fun p : Fin 5 → ℝ => 1 - p 0) (-coordProj 0) p :=
    h0.const_sub 1
  have hsq := h1.pow 2
  have hS : HasFDerivAt (fun p : Fin 5 → ℝ => p 2 + p 3) (coordProj 2 + coordProj 3) p :=
    (coordProj 2).hasFDerivAt.add (coordProj 3).hasFDerivAt
  have hprod := hsq.mul hS
  have hsum := hprod.add (coordProj 4).hasFDerivAt
  convert hsum using 1
  all_goals first | module | (funext q; simp [coordProj])

private theorem threePopF2_comp2_hasFDerivAt (p : Fin 5 → ℝ) :
    HasFDerivAt (fun p : Fin 5 → ℝ => (p 0) ^ 2 * (p 2 + p 3) + p 4)
      (((p 0) ^ 2) • (coordProj 2 + coordProj 3)
        + (2 * p 0 * (p 2 + p 3)) • coordProj 0 + coordProj 4) p := by
  have h0 : HasFDerivAt (fun p : Fin 5 → ℝ => p 0) (coordProj 0) p :=
    (coordProj 0).hasFDerivAt
  have hsq := h0.pow 2
  have hS : HasFDerivAt (fun p : Fin 5 → ℝ => p 2 + p 3) (coordProj 2 + coordProj 3) p :=
    (coordProj 2).hasFDerivAt.add (coordProj 3).hasFDerivAt
  have hprod := hsq.mul hS
  have hsum := hprod.add (coordProj 4).hasFDerivAt
  convert hsum using 1
  all_goals first | module | (funext q; simp [coordProj])

private noncomputable def threePopJacCLM (p : Fin 5 → ℝ) : (Fin 5 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![
    coordProj 2 + coordProj 3,
    ((1 - p 0) ^ 2) • (coordProj 2 + coordProj 3)
      + (-2 * (1 - p 0) * (p 2 + p 3)) • coordProj 0 + coordProj 4,
    ((p 0) ^ 2) • (coordProj 2 + coordProj 3)
      + (2 * p 0 * (p 2 + p 3)) • coordProj 0 + coordProj 4]

private theorem threePopF2_hasFDerivAt (p : Fin 5 → ℝ) :
    HasFDerivAt threePopF2 (threePopJacCLM p) p := by
  rw [threePopJacCLM, hasFDerivAt_pi]
  intro i
  fin_cases i
  · exact ((coordProj 2).hasFDerivAt.add (coordProj 3).hasFDerivAt :
      HasFDerivAt (fun p : Fin 5 → ℝ => p 2 + p 3) (coordProj 2 + coordProj 3) p)
  · exact threePopF2_comp1_hasFDerivAt p
  · exact threePopF2_comp2_hasFDerivAt p

private theorem threePopF2_fderiv (p : Fin 5 → ℝ) :
    fderiv ℝ threePopF2 p = threePopJacCLM p :=
  (threePopF2_hasFDerivAt p).fderiv

private def threePopJac (p : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 5) ℝ :=
  !![0, 0, 1, 1, 0;
     -2 * (1 - p 0) * (p 2 + p 3), 0, (1 - p 0) ^ 2, (1 - p 0) ^ 2, 1;
     2 * p 0 * (p 2 + p 3), 0, (p 0) ^ 2, (p 0) ^ 2, 1]

private theorem threePopJac_eq_toMatrix (p : Fin 5 → ℝ) :
    LinearMap.toMatrix' (threePopJacCLM p).toLinearMap = threePopJac p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix'_apply, threePopJacCLM, threePopJac, coordProj]

private theorem threePopJac_rank {p : Fin 5 → ℝ} (hp : p 2 + p 3 ≠ 0) :
    (threePopJac p).rank = 3 := by
  have hsurj : Function.Surjective (threePopJac p).mulVec := by
    intro y
    refine ⟨![(y 2 - y 1 - (2 * p 0 - 1) * y 0) / (2 * (p 2 + p 3)), 0, y 0, 0,
      y 2 - 2 * p 0 * (p 2 + p 3) * ((y 2 - y 1 - (2 * p 0 - 1) * y 0) / (2 * (p 2 + p 3)))
        - (p 0) ^ 2 * y 0], ?_⟩
    funext i
    fin_cases i <;> simp [threePopJac, Matrix.mulVec]; field_simp [hp]; ring
  have h := Matrix.mulVec_surjective_iff_rank_eq_card.mp hsurj
  simpa using h

/-- **Jacobian rank of the three-population admixture parametrization.**
At every parameter point with `a + b ≠ 0` the Jacobian has rank exactly `3`
(less than the `5` parameters). -/
theorem threePopF2_jacobian_rank {p : Fin 5 → ℝ} (hp : p 2 + p 3 ≠ 0) :
    (MetaMathlibExt.jacobianMatrix threePopF2 p).rank = 3 := by
  have hd : DifferentiableAt ℝ threePopF2 p := (threePopF2_hasFDerivAt p).differentiableAt
  rw [MetaMathlibExt.jacobianMatrix_eq_toMatrix'_fderiv threePopF2 p hd,
    threePopF2_fderiv p, threePopJac_eq_toMatrix p]
  exact threePopJac_rank hp

/-- The derivative is nowhere injective at such points: the five parameters are
not locally identifiable from the three `f2` values. -/
theorem threePopF2_not_injective_fderiv {p : Fin 5 → ℝ} (hp : p 2 + p 3 ≠ 0) :
    ¬ Function.Injective (fderiv ℝ threePopF2 p) := by
  intro hinj
  have hd : DifferentiableAt ℝ threePopF2 p := (threePopF2_hasFDerivAt p).differentiableAt
  have hmul : Function.Injective (MetaMathlibExt.jacobianMatrix threePopF2 p).mulVec := by
    intro x y hxy
    apply hinj
    rw [← MetaMathlibExt.jacobianMatrix_mulVec_eq_fderiv threePopF2 p hd x,
      ← MetaMathlibExt.jacobianMatrix_mulVec_eq_fderiv threePopF2 p hd y]
    exact hxy
  have hrank5 : (MetaMathlibExt.jacobianMatrix threePopF2 p).rank = 5 := by
    have hiff : Function.Injective (MetaMathlibExt.jacobianMatrix threePopF2 p).mulVec ↔
        (MetaMathlibExt.jacobianMatrix threePopF2 p).rank = Fintype.card (Fin 5) := by
      rw [Matrix.mulVec_injective_iff, Matrix.rank_eq_finrank_span_cols,
        linearIndependent_iff_card_eq_finrank_span, Set.finrank]
      exact eq_comm
    have := hiff.mp hmul
    simpa using this
  have hrank3 := threePopF2_jacobian_rank hp
  rw [hrank3] at hrank5
  exact absurd hrank5 (by norm_num)

/-- Unidentified directions, exhibited globally: the shared stem length and the
split of `a + b` between the two source edges are invisible to `f2`. -/
theorem threePopF2_eq_shift {α s s' a b c t : ℝ} :
    threePopF2 ![α, s', a + t, b - t, c] = threePopF2 ![α, s, a, b, c] := by
  funext i
  fin_cases i <;> simp [threePopF2]

/-- The length-to-`f2` map of the three-leaf star tree,
`(x, y, z) ↦ (x + y, x + z, y + z)`. -/
def starTreeF2 (l : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![l 0 + l 1, l 0 + l 2, l 1 + l 2]

/-- **Tree acceptance example.** The star-tree parametrization is globally
injective, hence its edge lengths are locally (indeed globally) identifiable
from `f2`. -/
theorem starTreeF2_injective : Function.Injective starTreeF2 := by
  intro l l' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [starTreeF2] at h0 h1 h2
  funext i
  fin_cases i
  · change l 0 = l' 0
    linarith
  · change l 1 = l' 1
    linarith
  · change l 2 = l' 2
    linarith

/-- Its derivative is everywhere injective, so the general criterion applies. -/
theorem starTreeF2_injective_fderiv (p : Fin 3 → ℝ) :
    Function.Injective (fderiv ℝ starTreeF2 p) := by
  have hF : starTreeF2 = fun l => Matrix.mulVecLin !![1, 1, 0; 1, 0, 1; 0, 1, 1] l := by
    funext l i
    fin_cases i <;> simp [starTreeF2, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  set L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
    ⟨Matrix.mulVecLin !![1, 1, 0; 1, 0, 1; 0, 1, 1],
      LinearMap.continuous_of_finiteDimensional _⟩ with hL
  have hEq : starTreeF2 = ⇑L := hF
  have hfder : fderiv ℝ starTreeF2 p = L := by
    rw [hEq, ContinuousLinearMap.fderiv]
  rw [hfder]
  intro x y hxy
  apply starTreeF2_injective
  rw [hEq]
  exact hxy

end MathlibExt.Biology.PopulationGenetics.Admixture
