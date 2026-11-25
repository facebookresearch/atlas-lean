/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.Path
public import MathlibExt.Analysis.CStarAlgebra.Pullback

/-!
# Nonunital interval evaluation and matching-path gluing

The matching pair is the literal closed pullback of endpoint evaluations.
Stock path concatenation supplies the continuous half-interval gluing.
The resulting nonunital star hom is norm-decreasing in the actual supremum
norm; neither an output path nor a uniform bound is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra

noncomputable section

namespace ContinuousMap.IntervalGluing

universe uB

variable (B : Type uB) [NonUnitalCStarAlgebra B]

/-- Let `B` be a possibly nonunital complex C*-algebra. The functions are continuous `B`-valued
paths on the closed real interval `[0,1]`.

nonunital evaluation at an interval point. -/
def evalAt (s : unitInterval) : C(unitInterval, B) →⋆ₙₐ[ℂ] B where
  toFun f := f s
  map_zero' := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem evalAt_apply (s : unitInterval) (f : C(unitInterval, B)) :
    evalAt B s f = f s := by
  rfl

/-- Let `B` be a possibly nonunital complex C*-algebra. The functions are continuous `B`-valued
paths on the closed real interval `[0,1]`.

Constant paths, without a unit in the coefficient algebra. -/
def constantHom : B →⋆ₙₐ[ℂ] C(unitInterval, B) where
  toFun b := ContinuousMap.const unitInterval b
  map_zero' := by ext s; rfl
  map_add' _ _ := by ext s; rfl
  map_smul' _ _ := by ext s; rfl
  map_mul' _ _ := by ext s; rfl
  map_star' _ := by ext s; rfl

@[simp]
theorem constantHom_apply (b : B) (s : unitInterval) :
    constantHom B b s = b := by
  rfl

/-- Let `B` be a possibly nonunital complex C*-algebra. The functions are continuous `B`-valued
paths on the closed real interval `[0,1]`.

Precomposition by the interval reversal. -/
def reverseHom : C(unitInterval, B) →⋆ₙₐ[ℂ] C(unitInterval, B) where
  toFun f := f.comp ⟨unitInterval.symm, unitInterval.continuous_symm⟩
  map_zero' := by ext s; rfl
  map_add' _ _ := by ext s; rfl
  map_smul' _ _ := by ext s; rfl
  map_mul' _ _ := by ext s; rfl
  map_star' _ := by ext s; rfl

@[simp]
theorem reverseHom_apply (f : C(unitInterval, B)) (s : unitInterval) :
    reverseHom B f s = f (unitInterval.symm s) := by
  rfl

theorem reverseHom_zero (f : C(unitInterval, B)) :
    reverseHom B f 0 = f 1 := by
  rw [reverseHom_apply, unitInterval.symm_zero]

theorem reverseHom_one (f : C(unitInterval, B)) :
    reverseHom B f 1 = f 0 := by
  rw [reverseHom_apply, unitInterval.symm_one]

/-- Let `B` be a possibly nonunital complex C*-algebra. The paths take values in `B` on the closed
interval `[0,1]`; a matching pair has equal meeting endpoints.

The closed matching-endpoint pullback, with its inherited norm. -/
abbrev MatchingPaths :=
  NonUnitalCStarPullback.Pullback (evalAt B 1) (evalAt B 0)

variable {B}

/-- Let `B` be a possibly nonunital complex C*-algebra. The paths take values in `B` on the closed
interval `[0,1]`; a matching pair has equal meeting endpoints.

Concatenate the two coordinates of a matching pair. -/
def glue (p : MatchingPaths B) : C(unitInterval, B) :=
  let first : Path (p.1.1 0) (p.1.1 1) :=
    { toContinuousMap := p.1.1
      source' := rfl
      target' := rfl }
  let second : Path (p.1.1 1) (p.1.2 1) :=
    { toContinuousMap := p.1.2
      source' := p.property.symm
      target' := rfl }
  (first.trans second).toContinuousMap

/-- **Half-interval concatenation of matching paths.** Let `B` be a nonunital
complex C*-algebra and let `p = (f, g)` be continuous paths on `[0, 1]` with
`f(1) = g(0)`. For `s ∈ [0, 1]`, the glued path has value `f(2s)` when
`s ≤ 1/2`, and `g(2s - 1)` when `s > 1/2`. Both arguments belong to `[0, 1]`;
the matching condition makes the two endpoint values agree at `s = 1/2`. -/
theorem glue_apply (p : MatchingPaths B) (s : unitInterval) :
    glue p s =
      if h : (s : ℝ) ≤ 1 / 2 then
        p.1.1 ⟨2 * (s : ℝ),
          (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩
      else
        p.1.2 ⟨2 * (s : ℝ) - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, s.2.2⟩⟩ := by
  dsimp only [glue]
  exact Path.trans_apply _ _ s

@[simp]
theorem glue_zero (p : MatchingPaths B) : glue p 0 = p.1.1 0 := by
  dsimp only [glue]
  exact Path.source _

@[simp]
theorem glue_one (p : MatchingPaths B) : glue p 1 = p.1.2 1 := by
  dsimp only [glue]
  exact Path.target _

/-- Let `B` be a possibly nonunital complex C*-algebra. The paths take values in `B` on the closed
interval `[0,1]`; a matching pair has equal meeting endpoints.

Half-interval gluing is a nonunital star homomorphism. Its standard C-star contractivity is the
required supremum-norm bound. -/
def glueHom : MatchingPaths B →⋆ₙₐ[ℂ] C(unitInterval, B) where
  toFun := glue
  map_zero' := by
    ext s
    rw [glue_apply]
    split_ifs <;> rfl
  map_add' := by
    intro p q
    ext s
    simp only [glue_apply, ContinuousMap.add_apply]
    split_ifs <;> rfl
  map_smul' := by
    intro z p
    ext s
    simp only [glue_apply, ContinuousMap.smul_apply]
    split_ifs <;> rfl
  map_mul' := by
    intro p q
    ext s
    simp only [glue_apply, ContinuousMap.mul_apply]
    split_ifs <;> rfl
  map_star' := by
    intro p
    ext s
    simp only [glue_apply, ContinuousMap.star_apply]
    split_ifs <;> rfl

@[simp]
theorem glueHom_apply (p : MatchingPaths B) : glueHom p = glue p := by
  rfl

theorem glueHom_zero (p : MatchingPaths B) : glueHom p 0 = p.1.1 0 := by
  rw [glueHom_apply, glue_zero]

theorem glueHom_one (p : MatchingPaths B) : glueHom p 1 = p.1.2 1 := by
  rw [glueHom_apply, glue_one]

end ContinuousMap.IntervalGluing
