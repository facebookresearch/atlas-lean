/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageMiddleSection

/-!
# Boundary cycles for the adjacent-column connecting map

A cycle in column `p+1` lifts degreewise to the middle adjacent quotient.
Its differential lies in the image of column `p`; exactness therefore gives
a canonical lift to column `p`.  This file constructs that boundary lift and
proves both its factorization equation and its cycle equation.  Identifying
the resulting homology class with the connecting homomorphism is separate.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The boundary in column `p` of a cycle lifted from column `p+1`, together
with its defining factorization through the left map of the adjacent short
exact sequence. -/
noncomputable def horizontalFirstPageAdjacentBoundaryLift (p q : ℕ) :
    { x₁ : (horizontalDirectColumnCochain K (p + 1)).cycles
          (-((p + 1 : ℕ) : ℤ) - q) ⟶
        (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) //
      x₁ ≫ (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
          (-(p : ℤ) - q) =
        (horizontalDirectColumnCochain K (p + 1)).iCycles
            (-((p + 1 : ℕ) : ℤ) - q) ≫
          horizontalFirstPageAdjacentMiddleSection K p q ≫
          (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.d
            (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) } := by
  let S := horizontalFirstPageAdjacentDirectShortComplex K p
  let hS := horizontalFirstPageAdjacentDirectShortExact K p
  let n : ℤ := -((p + 1 : ℕ) : ℤ) - q
  let j : ℤ := -(p : ℤ) - q
  have hij : (ComplexShape.up ℤ).Rel n j := by
    dsimp [n, j]
    simp only [ComplexShape.up_Rel]
    omega
  let F := HomologicalComplex.eval C (ComplexShape.up ℤ) j
  let Sj := S.map F
  let hSj := hS.map_of_exact F
  let _ := hSj.mono_f
  let x₂ : (horizontalDirectColumnCochain K (p + 1)).cycles n ⟶ S.X₂.X n :=
    (horizontalDirectColumnCochain K (p + 1)).iCycles n ≫
      horizontalFirstPageAdjacentMiddleSection K p q
  have hx₂g : x₂ ≫ S.g.f n =
      (horizontalDirectColumnCochain K (p + 1)).iCycles n := by
    dsimp [x₂]
    rw [Category.assoc, horizontalFirstPageAdjacentMiddleSection_g,
      Category.comp_id]
  have hx₂d : (x₂ ≫ S.X₂.d n j) ≫ Sj.g = 0 := by
    change (x₂ ≫ S.X₂.d n j) ≫ S.g.f j = 0
    rw [Category.assoc, ← S.g.comm n j, ← Category.assoc, hx₂g]
    change (horizontalDirectColumnCochain K (p + 1)).iCycles n ≫
      (horizontalDirectColumnCochain K (p + 1)).d n j = 0
    simp
  refine ⟨hSj.exact.lift (x₂ ≫ S.X₂.d n j) hx₂d, ?_⟩
  simpa [S, F, Sj, x₂, n, j] using
    hSj.exact.lift_f (x₂ ≫ S.X₂.d n j) hx₂d

/-- Underlying boundary-cycle morphism. -/
noncomputable def horizontalFirstPageAdjacentBoundaryCycles (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).cycles
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) :=
  (horizontalFirstPageAdjacentBoundaryLift K p q).1

/-- The boundary-cycle morphism maps through the left term to the
differential of the chosen middle lift. -/
theorem horizontalFirstPageAdjacentBoundaryCycles_f (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
          (-(p : ℤ) - q) =
      (horizontalDirectColumnCochain K (p + 1)).iCycles
          (-((p + 1 : ℕ) : ℤ) - q) ≫
        horizontalFirstPageAdjacentMiddleSection K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.d
          (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) :=
  (horizontalFirstPageAdjacentBoundaryLift K p q).2

/-- The lifted boundary is a cycle in column `p`. -/
theorem horizontalFirstPageAdjacentBoundaryCycles_d (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q ≫
      (horizontalDirectColumnCochain K p).d
        (-(p : ℤ) - q) (-(p : ℤ) - q + 1) = 0 := by
  let S := horizontalFirstPageAdjacentDirectShortComplex K p
  let hS := horizontalFirstPageAdjacentDirectShortExact K p
  let _ := hS.mono_f
  let k : ℤ := -(p : ℤ) - q + 1
  have hij : (ComplexShape.up ℤ).Rel
      (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) := by
    simp only [ComplexShape.up_Rel]
    push_cast
    omega
  have hjk : (ComplexShape.up ℤ).Rel (-(p : ℤ) - q) k := by
    dsimp [k]
    simp only [ComplexShape.up_Rel]
  have hm : Mono (S.f.f k) := by infer_instance
  let _ := hm
  have hcomm := S.f.comm (-(p : ℤ) - q) k
  change S.f.f (-(p : ℤ) - q) ≫ S.X₂.d (-(p : ℤ) - q) k =
    (horizontalDirectColumnCochain K p).d (-(p : ℤ) - q) k ≫
      S.f.f k at hcomm
  apply (cancel_mono (S.f.f k)).1
  simp only [zero_comp]
  rw [Category.assoc, ← hcomm, ← Category.assoc,
    horizontalFirstPageAdjacentBoundaryCycles_f]
  simp only [Category.assoc]
  rw [S.X₂.d_comp_d, comp_zero, comp_zero]

end HomologicalComplex₂

end
