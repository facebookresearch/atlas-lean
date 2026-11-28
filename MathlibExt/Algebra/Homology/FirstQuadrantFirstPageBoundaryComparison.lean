/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageZeroBoundary

/-!
# The adjacent boundary is the signed horizontal homology map

Let K be a nonnegative homological bicomplex in an abelian category C.
Write D_p for its signed direct cochain column, with K_(p,q) in degree
−p−q, and 0 → D_p → M_p → D_(p+1) → 0 for the adjacent quotient
short exact sequence.

The supported section of column p+1 into F_(p+1) sends a source cycle
to a lift whose total differential is its raw horizontal differential
in column p. This identifies the exactness-defined adjacent boundary
representative with the map obtained from (K.d_(p+1,p))_q.

After transporting through the column sign-removing comparisons, the
boundary-cycle lift is (−1)^(q+1) times the horizontal cycles map.
Consequently the adjacent connecting homomorphism, identified with a
map H_q(K_(p+1)) → H_q(K_p), is
δ_adj = (−1)^(q+1) H_q(d_h).
The formulas include p=0, the edge from column one to column zero.
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
category and p,q ≥ 0, the supported section is
s_(p,q) : D_p^(−p−q) → F_p^(−p−q).
At p=0 it is the direct complete zero-stage section, and at
positive p it is the finite top-column section transported to the
complete-stage presentation. -/
noncomputable def horizontalCompleteDirectColumnSupportedSection :
    (p q : ℕ) →
      (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) ⟶
        ((horizontalCompleteFiltrationCochainDiagram K).obj
          (horizontalFirstPageUpperIndex p)).X (-(p : ℤ) - q)
  | 0, q => horizontalCompleteDirectColumnSectionComponent K 0 q
  | p + 1, q => horizontalCompleteSuccDirectColumnSection K p q

/-- For a nonnegative homological bicomplex K in an abelian
category, the inverse of coker(F_(p−1) → F_p) ≅ D_p has component
in degree i=−p−q equal to π_i ∘ s_(p,q).
Here s is the supported top-column section into F_p and π is
the consecutive-stage cokernel projection. -/
theorem horizontalFirstPageCokernelIso_inv_f_supported (p q : ℕ) :
    (horizontalFirstPageCokernelIso K p).inv.f (-(p : ℤ) - q) =
      horizontalCompleteDirectColumnSupportedSection K p q ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K p)).f
          (-(p : ℤ) - q) := by
  cases p with
  | zero =>
      exact horizontalFirstPageCokernelIso_inv_f_zero K q
  | succ p =>
      exact horizontalFirstPageCokernelIso_inv_f_succ K p q

/-- For a nonnegative homological bicomplex K in an abelian
category, put i=−(p+1)−q and j=i+1=−p−q.
On Z^i(D_(p+1)), taking the differential after the section into
F_(p+1) equals applying the raw horizontal component
(K.d_(p+1,p))_q, taking the supported target section into F_p,
and including F_p into F_(p+1).
This holds for all p,q≥0, including the one-to-zero edge. -/
theorem horizontalCompleteDirectColumnSupportedSection_d (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1))).d
          (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) =
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
      (K.d (p + 1) p).f q ≫
      (horizontalDirectColumnCochainXIso K p q).inv ≫
      horizontalCompleteDirectColumnSupportedSection K p q ≫
      (horizontalFirstPageNextFiltrationMap K p).f (-(p : ℤ) - q) := by
  cases p with
  | zero =>
      exact horizontalCompleteOneToZeroDirectColumnSection_d K q
  | succ p =>
      exact horizontalCompleteSuccDirectColumnSection_d K p q

/-- For a nonnegative homological bicomplex K in an abelian
category and j=−p−q, the left map a : D_p → M_p of the
adjacent quotient sequence has component
a^j = π_M^j ∘ (F_p → F_(p+1))^j ∘ s_(p,q).
The middle quotient is M_p=coker(F_(p−1) → F_(p+1)). -/
theorem horizontalCompleteDirectColumnSupportedSection_adjacent_f
    (p q : ℕ) :
    horizontalCompleteDirectColumnSupportedSection K p q ≫
        (horizontalFirstPageNextFiltrationMap K p).f (-(p : ℤ) - q) ≫
        (cokernel.π (horizontalFirstPageFiltrationMap K p ≫
          horizontalFirstPageNextFiltrationMap K p)).f (-(p : ℤ) - q) =
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q) := by
  dsimp [horizontalFirstPageAdjacentDirectShortComplex,
    horizontalFirstPageAdjacentLeftIso,
    horizontalFirstPageAdjacentCokernelShortComplex,
    CategoryTheory.cokernelCompShortComplex]
  rw [horizontalFirstPageCokernelIso_inv_f_supported K p q]
  simp only [Category.assoc]
  rw [← HomologicalComplex.comp_f]
  rw [← HomologicalComplex.comp_f, cokernel.π_desc]

/-- For a nonnegative homological bicomplex K in an abelian
category, let α_(p,q) : D_p^(−p−q) ≅ K_(p,q).
The raw representative from Z^(−(p+1)−q)(D_(p+1)) to
D_p^(−p−q) is
α_(p,q)⁻¹ ∘ (K.d_(p+1,p))_q ∘ α_(p+1,q) ∘ i_Z.
It uses the horizontal bicomplex component before sign transport. -/
noncomputable def horizontalDirectColumnRawHorizontalRepresentative
    (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).cycles
        (-((p + 1 : ℕ) : ℤ) - q) ⟶
      (horizontalDirectColumnCochain K p).X (-(p : ℤ) - q) :=
  (horizontalDirectColumnCochain K (p + 1)).iCycles
      (-((p + 1 : ℕ) : ℤ) - q) ≫
    (horizontalDirectColumnCochainXIso K (p + 1) q).hom ≫
    (K.d (p + 1) p).f q ≫
    (horizontalDirectColumnCochainXIso K p q).inv

/-- For a nonnegative homological bicomplex K in an abelian
category, let s_M lift D_(p+1) into the middle quotient M_p and
R_(p,q) be the raw horizontal representative on source cycles.
Then d_M ∘ s_M ∘ i_Z = a ∘ R_(p,q), in degrees
−(p+1)−q and −p−q, where a : D_p → M_p is the left adjacent arrow. -/
theorem horizontalFirstPageAdjacentMiddleSection_d_eq_raw (p q : ℕ) :
    (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalFirstPageAdjacentMiddleSection K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).X₂.d
        (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) =
    horizontalDirectColumnRawHorizontalRepresentative K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q) := by
  dsimp [horizontalFirstPageAdjacentMiddleSection]
  simp only [Category.assoc]
  change (horizontalDirectColumnCochain K (p + 1)).iCycles
        (-((p + 1 : ℕ) : ℤ) - q) ≫
      horizontalCompleteSuccDirectColumnSection K p q ≫
      (cokernel.π (horizontalFirstPageFiltrationMap K p ≫
        horizontalFirstPageNextFiltrationMap K p)).f
          (-((p + 1 : ℕ) : ℤ) - q) ≫
      (cokernel (horizontalFirstPageFiltrationMap K p ≫
        horizontalFirstPageNextFiltrationMap K p)).d
          (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q) = _
  have hπ := (cokernel.π (horizontalFirstPageFiltrationMap K p ≫
    horizontalFirstPageNextFiltrationMap K p)).comm
      (-((p + 1 : ℕ) : ℤ) - q) (-(p : ℤ) - q)
  rw [hπ]
  rw [reassoc_of% horizontalCompleteDirectColumnSupportedSection_d K p q]
  dsimp [horizontalDirectColumnRawHorizontalRepresentative]
  rw [horizontalCompleteDirectColumnSupportedSection_adjacent_f K p q]
  simp only [Category.assoc]

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q≥0, the boundary representative obtained from
exactness of D_p → M_p → D_(p+1) equals R_(p,q), the raw
horizontal component conjugated by the direct-column object
identifications on source cycles. -/
theorem horizontalFirstPageAdjacentBoundaryCycles_eq_raw (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q =
      horizontalDirectColumnRawHorizontalRepresentative K p q := by
  let S := horizontalFirstPageAdjacentDirectShortComplex K p
  let hS := horizontalFirstPageAdjacentDirectShortExact K p
  let _ := hS.mono_f
  have hm : Mono (S.f.f (-(p : ℤ) - q)) := by infer_instance
  let _ := hm
  apply (cancel_mono (S.f.f (-(p : ℤ) - q))).1
  change horizontalFirstPageAdjacentBoundaryCycles K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q) =
    horizontalDirectColumnRawHorizontalRepresentative K p q ≫
      (horizontalFirstPageAdjacentDirectShortComplex K p).f.f
        (-(p : ℤ) - q)
  rw [horizontalFirstPageAdjacentBoundaryCycles_f]
  exact horizontalFirstPageAdjacentMiddleSection_d_eq_raw K p q

/-- For a nonnegative homological bicomplex K in an abelian
category, let C_(p,q) be the horizontal cycles map transported
through the sign-removing column identifications.
The adjacent boundary representative satisfies
b_(p,q) = (−1)^(q+1) i_Z ∘ C_(p,q),
as a map from the column-p+1 source cycles to the column-p term
in cochain degree −p−q. -/
theorem horizontalFirstPageAdjacentBoundaryCycles_eq_horizontal (p q : ℕ) :
    horizontalFirstPageAdjacentBoundaryCycles K p q =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        (horizontalDirectColumnHorizontalCyclesMap K p q ≫
          (horizontalDirectColumnCochain K p).iCycles (-(p : ℤ) - q)) := by
  rw [horizontalFirstPageAdjacentBoundaryCycles_eq_raw K p q]
  rw [horizontalDirectColumnHorizontalCyclesMap_iCycles K p q]
  simp only [smul_smul, Int.units_mul_self, one_smul]
  rfl

/-- For a nonnegative homological bicomplex K in an abelian
category, the canonical target-cycle lift of the adjacent
boundary representative equals (−1)^(q+1) C_(p,q).
Here C_(p,q) is the horizontal cycles map conjugated by the
direct-column sign and extension comparisons. -/
theorem horizontalFirstPageAdjacentBoundaryLiftCycles_eq_horizontal
    (p q : ℕ) :
    (horizontalDirectColumnCochain K p).liftCycles
        (horizontalFirstPageAdjacentBoundaryCycles K p q)
        (-(p : ℤ) - q + 1) (by simp)
        (horizontalFirstPageAdjacentBoundaryCycles_d K p q) =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        horizontalDirectColumnHorizontalCyclesMap K p q := by
  apply (cancel_mono
    ((horizontalDirectColumnCochain K p).iCycles (-(p : ℤ) - q))).1
  rw [(horizontalDirectColumnCochain K p).liftCycles_i]
  simp only [Linear.units_smul_comp]
  exact horizontalFirstPageAdjacentBoundaryCycles_eq_horizontal K p q

/-- For a nonnegative homological bicomplex K in an abelian
category, let χ_(p,q) : H_(−p−q)(D_p) ≅ H_q(K_p).
The adjacent connecting map satisfies
δ = (−1)^(q+1) χ_(p,q)⁻¹ ∘ H_q(d_h) ∘ χ_(p+1,q).
Its source degree is −(p+1)−q and its target degree is −p−q. -/
theorem horizontalFirstPageAdjacentConnectingMap_eq_horizontal
    (p q : ℕ) :
    horizontalFirstPageAdjacentConnectingMap K p q =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        ((horizontalDirectColumnHomologyIso K (p + 1) q).hom ≫
          HomologicalComplex.homologyMap (K.d (p + 1) p) q ≫
          (horizontalDirectColumnHomologyIso K p q).inv) := by
  apply (cancel_epi ((horizontalDirectColumnCochain K (p + 1)).homologyπ
    (-((p + 1 : ℕ) : ℤ) - q))).1
  rw [horizontalFirstPageAdjacentConnectingMap_eq_boundaryCycles K p q]
  rw [horizontalFirstPageAdjacentBoundaryLiftCycles_eq_horizontal K p q]
  simp only [Linear.units_smul_comp, Linear.comp_units_smul]
  rw [horizontalDirectColumnHorizontalCyclesMap_homologyπ K p q]

/-- For a nonnegative homological bicomplex K in an abelian
category and p,q≥0, identifying the adjacent quotient homologies
with ordinary vertical homology gives
δ_adj : H_q(K_(p+1)) → H_q(K_p),
δ_adj = (−1)^(q+1) H_q(K.d_(p+1,p)).
This is the connecting morphism of the adjacent-column short
exact sequence after the column sign-removing comparisons. -/
theorem horizontalFirstPageAdjacentVerticalConnectingMap_eq_horizontal
    (p q : ℕ) :
    horizontalFirstPageAdjacentVerticalConnectingMap K p q =
      ((q + 1 : ℕ) : ℤ).negOnePow •
        horizontalFirstPageHorizontalHomologyMap K p q := by
  dsimp [horizontalFirstPageAdjacentVerticalConnectingMap,
    horizontalFirstPageHorizontalHomologyMap]
  rw [horizontalFirstPageAdjacentConnectingMap_eq_horizontal K p q]
  simp only [Linear.comp_units_smul, Linear.units_smul_comp,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  push_cast
  rfl

end HomologicalComplex₂

end
