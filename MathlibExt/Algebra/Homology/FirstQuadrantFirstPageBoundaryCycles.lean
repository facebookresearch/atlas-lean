/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageMiddleSection

/-!
# Boundary representatives from the adjacent direct-column sequence

Let K be a nonnegative homological bicomplex in an abelian category C.
For each p, write its adjacent direct-column short exact sequence as
0 → D_p → M_p → D_(p+1) → 0, where
M_p = coker(F_(p−1) → F_(p+1)).

Set n=−(p+1)−q, so n+1=−p−q. The supported degreewise section
D_(p+1)^n → M_p^n lifts the cycle inclusion from Z^n(D_(p+1)).
Its differential lands in the image of D_p^(n+1), and exactness
gives a representative b : Z^n(D_(p+1)) → D_p^(n+1) satisfying
a ∘ b = d_M ∘ s ∘ i_Z.

This representative is a target cycle: d_(D_p) ∘ b = 0.
The construction supplies the boundary map and its factorization
equation for arbitrary p,q ≥ 0.
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

/-- For a nonnegative homological bicomplex K in an abelian
category, let 0 → D_p → M_p → D_(p+1) → 0 be its adjacent sequence,
n=−(p+1)−q and s : D_(p+1)^n → M_p^n the supported section.
The boundary lift consists of a map b : Z^n(D_(p+1)) → D_p^(n+1)
with a^(n+1) ∘ b = d_M^(n,n+1) ∘ s ∘ i_Z.
Exactness of the constructed sequence gives this lift. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q ≥ 0, the boundary representative is
b : Z^(−(p+1)−q)(D_(p+1)) → D_p^(−p−q).
It is the morphism whose composite with the left adjacent-sequence
map is the differential of the supported middle lift of source cycles. -/
noncomputable def horizontalFirstPageAdjacentBoundaryCycles (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).cycles
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) :=
  (horizontalFirstPageAdjacentBoundaryLift K p q).1

/-- For the adjacent sequence 0 → D_p → M_p → D_(p+1) → 0
of a nonnegative homological bicomplex in an abelian category,
the boundary representative satisfies
a ∘ b = d_M ∘ s ∘ i_Z in degrees n=−(p+1)−q and n+1=−p−q.
Here s is the supported degreewise middle section. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category, the boundary representative
b : Z^(−(p+1)−q)(D_(p+1)) → D_p^(−p−q)
satisfies d_(D_p) ∘ b = 0.
It therefore factors through the target cycles in cochain degree −p−q. -/
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
