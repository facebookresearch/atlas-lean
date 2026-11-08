/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.CeaLemma

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for Céa's lemma

* On `ℝ` with `B = mul` and `L = (· * 3)`: the variational solution is `3`,
  the Galerkin solution in `⊥` is `0`, Galerkin orthogonality holds,
  and Céa's lemma holds in pointwise and infimum form.
* On `EuclideanSpace ℝ (Fin 2)` with `B` the inner product and `L` the inner
  product with `(1, 2)`: the Galerkin solution in the span of the first
  coordinate axis is `(1, 0)`, and Céa's lemma holds with `(1, 0)` as the
  comparison vector.
-/

open InnerProductSpace

namespace MathlibExtTest.Analysis.InnerProductSpace.CeaLemmaTests

open MathlibExt.Analysis.InnerProductSpace.CeaLemma

/-- Coercivity of multiplication on `ℝ`, with constant `1`. -/
private theorem isCoercive_mul : IsCoercive (ContinuousLinearMap.mul ℝ ℝ) := by
  refine ⟨1, one_pos, fun u => ?_⟩
  simp [Real.norm_eq_abs]

/-- The variational solution for `B = mul`, `L = (· * 3)` is `3`. -/
example : variationalSolution (E := ℝ) isCoercive_mul
    ((ContinuousLinearMap.mul ℝ ℝ) 3) = 3 := by
  symm
  apply variationalSolution_eq_of_forall isCoercive_mul
  intro w
  simp [ContinuousLinearMap.mul]

/-- The Galerkin solution in `⊥` is `0`. -/
example : galerkinSolution (B := ContinuousLinearMap.mul ℝ ℝ) isCoercive_mul
    (W := (⊥ : Submodule ℝ ℝ))
    (Submodule.closed_of_finiteDimensional (⊥ : Submodule ℝ ℝ)).isComplete
    ((ContinuousLinearMap.mul ℝ ℝ) 3) = 0 := by
  symm
  apply galerkinSolution_eq_of_forall isCoercive_mul _
  intro w
  have hw : (w : ℝ) = 0 := (Submodule.mem_bot ℝ).mp w.2
  simp [hw]

/-- Galerkin orthogonality on `ℝ` with `W = ⊥`. -/
example (w : (⊥ : Submodule ℝ ℝ)) :
    (ContinuousLinearMap.mul ℝ ℝ)
      (variationalSolution (E := ℝ) isCoercive_mul ((ContinuousLinearMap.mul ℝ ℝ) 3)
        - ((galerkinSolution (B := ContinuousLinearMap.mul ℝ ℝ) isCoercive_mul
            (W := (⊥ : Submodule ℝ ℝ))
            (Submodule.closed_of_finiteDimensional (⊥ : Submodule ℝ ℝ)).isComplete
            ((ContinuousLinearMap.mul ℝ ℝ) 3) : ℝ))) (w : ℝ) = 0 :=
  galerkin_orthogonality isCoercive_mul
    (Submodule.closed_of_finiteDimensional (⊥ : Submodule ℝ ℝ)).isComplete _ w

/-- Céa's lemma on `ℝ` with `W = ⊥`. -/
example :
    ‖variationalSolution (E := ℝ) isCoercive_mul ((ContinuousLinearMap.mul ℝ ℝ) 3)
      - ((galerkinSolution (B := ContinuousLinearMap.mul ℝ ℝ) isCoercive_mul
          (W := (⊥ : Submodule ℝ ℝ))
          (Submodule.closed_of_finiteDimensional (⊥ : Submodule ℝ ℝ)).isComplete
          ((ContinuousLinearMap.mul ℝ ℝ) 3) : ℝ))‖
      ≤ (‖ContinuousLinearMap.mul ℝ ℝ‖ / 1) *
        ‖variationalSolution (E := ℝ) isCoercive_mul ((ContinuousLinearMap.mul ℝ ℝ) 3)
          - (0 : ℝ)‖ := by
  apply norm_sub_galerkinSolution_le isCoercive_mul _ _ one_pos
  · intro v
    simp [Real.norm_eq_abs]
  · exact (Submodule.mem_bot ℝ).mpr rfl

/-- Céa's lemma in infimum form on `ℝ` with `W = ⊥`. -/
example :
    ‖variationalSolution (E := ℝ) isCoercive_mul ((ContinuousLinearMap.mul ℝ ℝ) 3)
      - ((galerkinSolution (B := ContinuousLinearMap.mul ℝ ℝ) isCoercive_mul
          (W := (⊥ : Submodule ℝ ℝ))
          (Submodule.closed_of_finiteDimensional (⊥ : Submodule ℝ ℝ)).isComplete
          ((ContinuousLinearMap.mul ℝ ℝ) 3) : ℝ))‖
      ≤ (‖ContinuousLinearMap.mul ℝ ℝ‖ / 1) *
        ⨅ v : (⊥ : Submodule ℝ ℝ),
          ‖variationalSolution (E := ℝ) isCoercive_mul ((ContinuousLinearMap.mul ℝ ℝ) 3)
            - (v : ℝ)‖ := by
  apply norm_sub_galerkinSolution_le_iInf isCoercive_mul _ _ one_pos
  intro v
  simp [Real.norm_eq_abs]

/-- The inner product on `EuclideanSpace ℝ (Fin 2)` as a plain (non-`⋆`)
bounded bilinear form. -/
noncomputable def euclidBilin :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ where
  toFun x := innerSL ℝ x
  map_add' x y := by
    ext z
    simp [map_add]
  map_smul' c x := by
    ext z
    simp [map_smul]
  cont := (innerSL ℝ).continuous

@[simp]
theorem euclidBilin_apply (x y : EuclideanSpace ℝ (Fin 2)) :
    euclidBilin x y = ⟪x, y⟫_ℝ :=
  innerSL_apply_apply ℝ x y

/-- The inner product on `EuclideanSpace ℝ (Fin 2)` is coercive with constant `1`. -/
private theorem isCoercive_euclidBilin : IsCoercive euclidBilin := by
  refine ⟨1, one_pos, fun u => ?_⟩
  simp [pow_two]

/-- The Galerkin solution in the span of the first coordinate axis is the
first-coordinate projection of `(1, 2)`. -/
example :
    galerkinSolution (B := euclidBilin) isCoercive_euclidBilin
      (W := Submodule.span ℝ {(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :
        EuclideanSpace ℝ (Fin 2))})
      (Submodule.closed_of_finiteDimensional
        (Submodule.span ℝ {(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :
          EuclideanSpace ℝ (Fin 2))})).isComplete
      (euclidBilin (WithLp.toLp 2 ![1, 2] : EuclideanSpace ℝ (Fin 2)))
      = ⟨EuclideanSpace.single (0 : Fin 2) (1 : ℝ),
          Submodule.subset_span (Set.mem_singleton _)⟩ := by
  symm
  apply galerkinSolution_eq_of_forall isCoercive_euclidBilin _
  intro w
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp w.2
  have hwin : (w : EuclideanSpace ℝ (Fin 2))
      = c • (EuclideanSpace.single (0 : Fin 2) (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) := hc.symm
  rw [hwin]
  simp [EuclideanSpace.inner_single_right]

/-- Céa's estimate on the Euclidean example, with `(1, 0)` as comparison vector. -/
example :
    ‖variationalSolution (E := EuclideanSpace ℝ (Fin 2)) isCoercive_euclidBilin
        (euclidBilin (WithLp.toLp 2 ![1, 2] : EuclideanSpace ℝ (Fin 2)))
      - ((galerkinSolution (B := euclidBilin) isCoercive_euclidBilin
          (W := Submodule.span ℝ {(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :
            EuclideanSpace ℝ (Fin 2))})
          (Submodule.closed_of_finiteDimensional
            (Submodule.span ℝ {(EuclideanSpace.single (0 : Fin 2) (1 : ℝ) :
              EuclideanSpace ℝ (Fin 2))})).isComplete
          (euclidBilin (WithLp.toLp 2 ![1, 2] : EuclideanSpace ℝ (Fin 2))) :
          EuclideanSpace ℝ (Fin 2)))‖
      ≤ (‖euclidBilin‖ / 1) *
        ‖variationalSolution (E := EuclideanSpace ℝ (Fin 2)) isCoercive_euclidBilin
            (euclidBilin (WithLp.toLp 2 ![1, 2] : EuclideanSpace ℝ (Fin 2)))
          - (WithLp.toLp 2 ![1, 0] : EuclideanSpace ℝ (Fin 2))‖ := by
  apply norm_sub_galerkinSolution_le isCoercive_euclidBilin _ _ one_pos
  · intro v
    simp [pow_two]
  · rw [Submodule.mem_span_singleton]
    exact ⟨1, by ext i; fin_cases i <;> simp⟩

end MathlibExtTest.Analysis.InnerProductSpace.CeaLemmaTests


namespace MathlibExtTest.Analysis.InnerProductSpace.CeaLemmaTests

/-- Coercivity gives uniqueness without a completeness instance on the ambient space. -/
theorem uniqueness_without_completeSpace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : IsCoercive B) {L : E →L[ℝ] ℝ} {x y : E}
    (hx : ∀ w, B x w = L w) (hy : ∀ w, B y w = L w) : x = y := by
  exact MathlibExt.Analysis.InnerProductSpace.CeaLemma.eq_of_forall_bilin hB hx hy

end MathlibExtTest.Analysis.InnerProductSpace.CeaLemmaTests
