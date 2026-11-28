/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageBoundaryCycles

/-!
# Cycle representatives of adjacent-column connecting maps

Let `K` be a first-quadrant bicomplex in an abelian category. The adjacent-column connecting
map starts from direct-column cycles in column `p+1` at cochain degree `-(p+1)-q`.

Lift such a cycle to the middle term of the adjacent short exact sequence and take its
boundary. The resulting cycle in column `p` at degree `-p-q` represents the connecting
homology class. The formula retains the specified middle section and boundary-cycle map.
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

private noncomputable def horizontalFirstPageAdjacentMiddleSectionRaw
    (p q : ℕ) :
    (horizontalFirstPageAdjacentDirectShortComplex K p).X₃.X
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.X
        (-((p + 1 : ℕ) : ℤ) - q) := by
  change (horizontalDirectColumnCochain K (p + 1)).X
      (-((p + 1 : ℕ) : ℤ) - q) ⟶ _
  exact horizontalFirstPageAdjacentMiddleSection K p q

private theorem horizontalFirstPageAdjacentMiddleSectionRaw_g (p q : ℕ) :
    horizontalFirstPageAdjacentMiddleSectionRaw K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).g.f
          (-((p + 1 : ℕ) : ℤ) - q) =
      𝟙 _ := by
  change horizontalFirstPageAdjacentMiddleSection K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).g.f
        (-((p + 1 : ℕ) : ℤ) - q) = 𝟙 _
  exact horizontalFirstPageAdjacentMiddleSection_g K p q

private noncomputable def horizontalFirstPageAdjacentBoundaryCyclesRaw
    (p q : ℕ) :
    (horizontalFirstPageAdjacentDirectShortComplex K p).X₃.cycles
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₁.X
        (-(p : ℤ) - q) := by
  change (horizontalDirectColumnCochain K (p + 1)).cycles
      (-((p + 1 : ℕ) : ℤ) - q) ⟶
    (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q)
  exact horizontalFirstPageAdjacentBoundaryCycles K p q

private theorem horizontalFirstPageAdjacentBoundaryCyclesRaw_f (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCyclesRaw K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
          (-(p : ℤ) - q) =
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₃.iCycles
          (-((p + 1 : ℕ) : ℤ) - q) ≫
        horizontalFirstPageAdjacentMiddleSectionRaw K p q ≫
        (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.d
          (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) := by
  change horizontalFirstPageAdjacentBoundaryCycles K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q) =
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalFirstPageAdjacentMiddleSection K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.d
        (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
  exact horizontalFirstPageAdjacentBoundaryCycles_f K p q

private theorem horizontalFirstPageAdjacentBoundaryCyclesRaw_d (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCyclesRaw K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₁.d
        (-(p : ℤ) - q) (-(p : ℤ) - q + 1) = 0 := by
  change horizontalFirstPageAdjacentBoundaryCycles K p q ≫
    (horizontalDirectColumnCochain K p).d
      (-(p : ℤ) - q) (-(p : ℤ) - q + 1) = 0
  exact horizontalFirstPageAdjacentBoundaryCycles_d K p q

private theorem
    horizontalFirstPageAdjacentConnectingMap_eq_boundaryCyclesRaw
    (p q : ℕ) :
    (horizontalFirstPageAdjacentDirectShortComplex K p).X₃.homologyπ
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalFirstPageAdjacentDirectShortExact K p).δ
        (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
        (by simp only [ComplexShape.up_Rel]; push_cast; omega) =
    (horizontalFirstPageAdjacentDirectShortComplex K p).X₁.liftCycles
        (horizontalFirstPageAdjacentBoundaryCyclesRaw K p q)
        (-(p : ℤ) - q + 1) (by simp)
        (horizontalFirstPageAdjacentBoundaryCyclesRaw_d K p q) ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₁.homologyπ
        (-(p : ℤ) - q) := by
  let S := horizontalFirstPageAdjacentDirectShortComplex K p
  let hS := horizontalFirstPageAdjacentDirectShortExact K p
  let n : ℤ := -((p + 1 : ℕ) : ℤ) - q
  let j : ℤ := -(p : ℤ) - q
  have hij : (ComplexShape.up ℤ).Rel n j := by
    dsimp [n, j]
    simp only [ComplexShape.up_Rel]
    omega
  let x₃ := S.X₃.iCycles n
  let x₂ := x₃ ≫ horizontalFirstPageAdjacentMiddleSectionRaw K p q
  have hx₃ : x₃ ≫ S.X₃.d n j = 0 := by
    dsimp [x₃]
    simp
  have hx₂ : x₂ ≫ S.g.f n = x₃ := by
    dsimp [x₂]
    rw [Category.assoc, horizontalFirstPageAdjacentMiddleSectionRaw_g,
      Category.comp_id]
  have hx₁ := horizontalFirstPageAdjacentBoundaryCyclesRaw_f K p q
  have hx₁' : horizontalFirstPageAdjacentBoundaryCyclesRaw K p q ≫
      S.f.f j = x₂ ≫ S.X₂.d n j := by
    simpa [x₂, x₃, n, j] using hx₁
  have hδ := hS.δ_eq n j hij x₃ (by simpa [x₃]) x₂ hx₂
    (horizontalFirstPageAdjacentBoundaryCyclesRaw K p q) hx₁'
    (j + 1) (by simp)
  have hnext : (ComplexShape.up ℤ).next n = j :=
    (ComplexShape.up ℤ).next_eq' hij
  have hlift : S.X₃.liftCycles x₃ j hnext (by simp [x₃]) = 𝟙 _ := by
    apply (cancel_mono (S.X₃.iCycles n)).1
    rw [S.X₃.liftCycles_i, Category.id_comp]
  rw [hlift, Category.id_comp] at hδ
  simpa [S, hS, n, j, x₃, x₂] using hδ

/-- The boundary-cycle formula for an adjacent-column connecting map.

The source homology projection followed by the adjacent connecting morphism equals the
canonical boundary-cycle lift followed by the target homology projection, at cochain degrees
`-(p+1)-q` and `-p-q`. -/
theorem horizontalFirstPageAdjacentConnectingMap_eq_boundaryCycles
    (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).homologyπ
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalFirstPageAdjacentConnectingMap K p q =
    (horizontalDirectColumnCochain K p).liftCycles
        (horizontalFirstPageAdjacentBoundaryCycles K p q)
        (-(p : ℤ) - q + 1) (by simp)
        (horizontalFirstPageAdjacentBoundaryCycles_d K p q) ≫
      (horizontalDirectColumnCochain K p).homologyπ (-(p : ℤ) - q) := by
  change (horizontalFirstPageAdjacentDirectShortComplex K p).X₃.homologyπ
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalFirstPageAdjacentDirectShortExact K p).δ
        (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
        (by simp only [ComplexShape.up_Rel]; push_cast; omega) =
    (horizontalFirstPageAdjacentDirectShortComplex K p).X₁.liftCycles
        (horizontalFirstPageAdjacentBoundaryCyclesRaw K p q)
        (-(p : ℤ) - q + 1) (by simp)
        (horizontalFirstPageAdjacentBoundaryCyclesRaw_d K p q) ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₁.homologyπ
        (-(p : ℤ) - q)
  exact horizontalFirstPageAdjacentConnectingMap_eq_boundaryCyclesRaw K p q

end HomologicalComplex₂

end
