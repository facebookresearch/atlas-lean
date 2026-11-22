/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.OriginalTwoBeadOrdinalCharts

/-!
# The original two-standard-simplex pushout

The full first and second bead charts identify the original union with
the pushout along the same original endpoint maps. The filler retains
both original whole simplex maps, in every arity.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.OriginalTwoBead.OrdinalCharts

/-- The native chart of the original overlap vertex. -/
noncomputable def overlapIso (p q : ℕ) :
    (Δ[0] : SSet.{u}) ≅ (left (pivot p q) ⊓ right (pivot p q)).toSSet :=
  stdSimplex.faceSingletonIso (pivot p q) ≪≫
    Subcomplex.eqToIso (intersection (pivot p q)).symm

/-- The original endpoint inclusion into the first standard bead. -/
def lastVertex (p : ℕ) : (Δ[0] : SSet.{u}) ⟶ (Δ[p] : SSet.{u}) :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋p⦌ (Fin.last p))

/-- The original endpoint inclusion into the second standard bead. -/
def firstVertex (q : ℕ) : (Δ[0] : SSet.{u}) ⟶ (Δ[q] : SSet.{u}) :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋q⦌ 0)

/-- The native overlap chart reads the original total pivot map. -/
theorem overlapIso_inclusion (p q : ℕ) :
    (overlapIso.{u} p q).hom ≫
      (left (pivot p q) ⊓ right (pivot p q)).ι =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋p + q⦌ (pivot p q)) := by
  rw [overlapIso, Iso.trans_hom, Category.assoc]
  change (stdSimplex.faceSingletonIso (pivot p q)).hom ≫
    (stdSimplex.face {pivot p q}).ι = _
  ext d x
  rfl

/-- The first whole chart sends its original terminal vertex to the original overlap. -/
theorem overlapLeft_chart (p q : ℕ) :
    (overlapIso.{u} p q).hom ≫ overlapLeft (pivot p q) =
      lastVertex p ≫ (leftIso p q).hom := by
  apply (cancel_mono (left (pivot p q)).ι).1
  simp only [Category.assoc]
  rw [leftIso_inclusion]
  change (overlapIso p q).hom ≫
      (left (pivot p q) ⊓ right (pivot p q)).ι = _
  rw [overlapIso_inclusion, lastVertex, ← SSet.stdSimplex.map_comp]
  rfl

/-- The second whole chart sends its original initial vertex to the same overlap. -/
theorem overlapRight_chart (p q : ℕ) :
    (overlapIso.{u} p q).hom ≫ overlapRight (pivot p q) =
      firstVertex q ≫ (rightIso p q).hom := by
  apply (cancel_mono (right (pivot p q)).ι).1
  simp only [Category.assoc]
  rw [rightIso_inclusion]
  change (overlapIso p q).hom ≫
      (left (pivot p q) ⊓ right (pivot p q)).ι = _
  rw [overlapIso_inclusion, firstVertex, ← SSet.stdSimplex.map_comp]
  congr 1

/-- The original first standard bead into the full union. -/
def leftInto (p q : ℕ) :
    (Δ[p] : SSet.{u}) ⟶ (union (pivot p q) : SSet.{u}) :=
  (leftIso p q).hom ≫ leftIntoUnion (pivot p q)

/-- The original second standard bead into the full union. -/
def rightInto (p q : ℕ) :
    (Δ[q] : SSet.{u}) ⟶ (union (pivot p q) : SSet.{u}) :=
  (rightIso p q).hom ≫ rightIntoUnion (pivot p q)

/-- The two standard beads form the same original genuine pushout. -/
theorem standardIsPushout (p q : ℕ) :
    IsPushout (lastVertex.{u} p) (firstVertex q) (leftInto p q) (rightInto p q) := by
  apply (isPushout (pivot p q)).of_iso
    (overlapIso p q).symm (leftIso p q).symm (rightIso p q).symm (Iso.refl _)
  · apply (cancel_epi (overlapIso p q).hom).1
    simp only [Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, overlapLeft_chart, Category.assoc,
      Iso.hom_inv_id,
      Category.comp_id]
  · apply (cancel_epi (overlapIso p q).hom).1
    simp only [Iso.symm_hom]
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, overlapRight_chart, Category.assoc,
      Iso.hom_inv_id,
      Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, leftInto,
      Iso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, rightInto,
      Iso.inv_hom_id_assoc]

/-- Both original standard-simplex maps extend with their exact endpoint identification. -/
theorem exists_standard_extension (p q : ℕ) {K : SSet.{u}} [Quasicategory K]
    (l : (Δ[p] : SSet.{u}) ⟶ K) (r : (Δ[q] : SSet.{u}) ⟶ K)
    (h : lastVertex p ≫ l = firstVertex q ≫ r) :
    ∃ τ : (Δ[p + q] : SSet.{u}) ⟶ K,
      SSet.stdSimplex.map (prefixOperator p q) ≫ τ = l ∧
        SSet.stdSimplex.map (suffixOperator p q) ≫ τ = r := by
  let σ := (standardIsPushout p q).desc l r h
  obtain ⟨τ, hτ⟩ := exists_original_extension (pivot p q) σ
  refine ⟨τ, ?_, ?_⟩
  · calc
      SSet.stdSimplex.map (prefixOperator p q) ≫ τ =
          leftInto p q ≫ (union (pivot p q)).ι ≫ τ := by
        rw [leftInto, Category.assoc]
        change _ = (leftIso p q).hom ≫ (left (pivot p q)).ι ≫ τ
        rw [← Category.assoc, leftIso_inclusion]
      _ = l := by rw [hτ]; exact (standardIsPushout p q).inl_desc _ _ _
  · calc
      SSet.stdSimplex.map (suffixOperator p q) ≫ τ =
          rightInto p q ≫ (union (pivot p q)).ι ≫ τ := by
        rw [rightInto, Category.assoc]
        change _ = (rightIso p q).hom ≫ (right (pivot p q)).ι ≫ τ
        rw [← Category.assoc, rightIso_inclusion]
      _ = r := by rw [hτ]; exact (standardIsPushout p q).inr_desc _ _ _

end SSet.OriginalTwoBead.OrdinalCharts
