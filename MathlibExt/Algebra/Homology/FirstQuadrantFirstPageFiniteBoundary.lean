/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageCokernelSections

/-!
# The finite-stage horizontal boundary on cycles

Inside filtration stage `p+1`, the total differential of a vertical cycle in
the top column has no surviving vertical component.  It is exactly the
previous-column inclusion of the horizontal bicomplex differential.  This is
the transparent finite-stage calculation underlying the first-page boundary.
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

/-- Inclusion of column `p` into filtration stage `p+1` in total degree
`p+q`. -/
noncomputable def horizontalFilteredPreviousColumnInclusion (p q : ℕ) :
    (K.X p).X q ⟶ horizontalFilteredTotalObj K (p + 1) (p + q) :=
  horizontalFilteredTotalι K (p + 1) (p + q)
    ⟨⟨(p, q), by simp⟩, by change p ≤ p + 1; omega⟩

/-- On vertical cycles, the filtered total differential from the top column
is precisely the previous-column inclusion of the horizontal differential. -/
theorem horizontalFilteredTopInclusion_d_eq_previous (p q : ℕ) :
    (K.X (p + 1)).iCycles q ≫
        horizontalFilteredTopInclusion K (p + 1) q ≫
        horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) =
      (K.X (p + 1)).iCycles q ≫ (K.d (p + 1) p).f q ≫
        horizontalFilteredPreviousColumnInclusion K p q := by
  have hD :
      horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) ≫
          horizontalFilteredTotalToTotal K (p + 1) (p + q) =
        horizontalFilteredTotalToTotal K (p + 1) (p + 1 + q) ≫
          (K.total (ComplexShape.down ℕ)).d (p + 1 + q) (p + q) := by
    rw [show p + 1 + q = p + q + 1 by omega]
    exact horizontalFilteredTotalD_toTotal K (p + 1) (p + q)
  apply (cancel_mono
    (horizontalFilteredTotalToTotal K (p + 1) (p + q))).1
  simp only [Category.assoc]
  rw [hD]
  have htop := horizontalFilteredTotalι_toTotal K (p + 1) (p + 1 + q)
    (horizontalFilteredTopIndex (p + 1) q)
  change horizontalFilteredTopInclusion K (p + 1) q ≫
      horizontalFilteredTotalToTotal K (p + 1) (p + 1 + q) =
    K.ιTotal (ComplexShape.down ℕ) (p + 1) q (p + 1 + q) (by simp) at htop
  rw [reassoc_of% htop]
  have hprev := horizontalFilteredTotalι_toTotal K (p + 1) (p + q)
    ⟨⟨(p, q), by simp⟩, by change p ≤ p + 1; omega⟩
  change horizontalFilteredPreviousColumnInclusion K p q ≫
      horizontalFilteredTotalToTotal K (p + 1) (p + q) =
    K.ιTotal (ComplexShape.down ℕ) p q (p + q) (by simp) at hprev
  rw [hprev]
  change (K.X (p + 1)).iCycles q ≫
      K.ιTotal (ComplexShape.down ℕ) (p + 1) q (p + 1 + q) (by simp) ≫
      (K.D₁ (ComplexShape.down ℕ) (p + 1 + q) (p + q) +
        K.D₂ (ComplexShape.down ℕ) (p + 1 + q) (p + q)) = _
  simp only [Preadditive.comp_add, ← Category.assoc, K.ι_D₁, K.ι_D₂]
  rw [K.d₁_eq (ComplexShape.down ℕ)
    (ComplexShape.down_mk (p + 1) p rfl) q (p + q) (by simp)]
  simp only [Category.assoc, ComplexShape.ε₁_def, one_smul]
  have hvertical : (K.X (p + 1)).iCycles q ≫
      K.d₂ (ComplexShape.down ℕ) (p + 1) q (p + q) = 0 := by
    cases q with
    | zero =>
        rw [K.d₂_eq_zero (ComplexShape.down ℕ) (p + 1) 0 (p + 0) (by simp),
          comp_zero]
    | succ q =>
        rw [K.d₂_eq (ComplexShape.down ℕ) (p + 1)
          (ComplexShape.down_mk (q + 1) q rfl) (p + (q + 1)) (by simp; omega)]
        rw [Linear.comp_units_smul, ← Category.assoc,
          (K.X (p + 1)).iCycles_d, zero_comp, smul_zero]
  rw [hvertical, add_zero]

/-- The same finite-stage boundary formula with the source cycle written in
the direct-column presentation. -/
theorem horizontalDirectColumnTopInclusion_d_eq_previous (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      horizontalFilteredTopInclusion K (p + 1) q ≫
      horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q) =
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      (K.d (p + 1) p).f q ≫
      horizontalFilteredPreviousColumnInclusion K p q := by
  let e := horizontalDirectColumnVerticalCyclesIso K (p + 1) q
  have he := horizontalDirectColumnVerticalCyclesIso_hom_iCycles K (p + 1) q
  calc
    _ = e.hom ≫ ((K.X (p + 1)).iCycles q ≫
        horizontalFilteredTopInclusion K (p + 1) q ≫
        horizontalFilteredTotalD K (p + 1) (p + 1 + q) (p + q)) := by
      rw [← reassoc_of% he]
    _ = e.hom ≫ ((K.X (p + 1)).iCycles q ≫
        (K.d (p + 1) p).f q ≫
        horizontalFilteredPreviousColumnInclusion K p q) :=
      congrArg (fun z => e.hom ≫ z)
        (horizontalFilteredTopInclusion_d_eq_previous K p q)
    _ = _ := by
      rw [reassoc_of% he]

end HomologicalComplex₂

end
