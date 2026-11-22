/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativePrisms
import MathlibExt.AlgebraicTopology.SimplicialSet.PullbackSimplex

/-!
# Original zero simplices of fixed-base marked mapping complexes

The original pullback projections and the already proved zero-parameter
unit identify its vertices with marked maps satisfying their literal base
equation. Reconstruction uses the existing native pullback-simplex lift.
Both original projections are characterized, with no fibrancy or marked
model assumption.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

private theorem zero_prism_over (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (t : (relativeMappingComplex k r p) _⦋0⦌) :
    mappingComplexZeroEquiv k X Y
        ((pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app (op ⦋0⦌) t) ≫ p = r := by
  let f : prod ((simplexParameter k).obj ⦋0⦌) X ⟶ Y :=
    (pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app (op ⦋0⦌) t
  have hf : f ≫ p = (zeroParameterUnitIso k X).hom ≫ r :=
    Hom.ext (relativeMapping_prism_over k r p (op ⦋0⦌) t)
  change ((zeroParameterUnitIso k X).inv ≫ f) ≫ p = r
  rw [Category.assoc, hf, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private theorem zero_map_over (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (f : X ⟶ Y) (hf : f ≫ p = r) :
    (mappingComplexPost k X p).app (op ⦋0⦌) ((mappingComplexZeroEquiv k X Y).symm f) =
      (mappingBasePoint k r).app (op ⦋0⦌) (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) := by
  rw [mappingBasePoint, SSet.yonedaEquiv_symm_app_id]
  apply (mappingComplexZeroEquiv k X Z).injective
  rw [mappingComplexZeroEquiv_post, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hf

/-- Original fixed-base mapping vertices are precisely the original marked maps over that same base. -/
def relativeMappingZeroEquiv (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) :
    (relativeMappingComplex k r p) _⦋0⦌ ≃ {f : X ⟶ Y // f ≫ p = r} where
  toFun t := ⟨mappingComplexZeroEquiv k X Y
    ((pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app (op ⦋0⦌) t),
      zero_prism_over k r p t⟩
  invFun f := PullbackSimplex.lift
    (IsPullback.of_hasPullback (mappingComplexPost k X p) (mappingBasePoint k r)) 0
      ((mappingComplexZeroEquiv k X Y).symm f.val)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) (zero_map_over k r p f.val f.property)
  left_inv t := by
    apply PullbackSimplex.hom_ext
      (IsPullback.of_hasPullback (mappingComplexPost k X p) (mappingBasePoint k r))
    · rw [PullbackSimplex.lift_fst]
      exact Equiv.symm_apply_apply _ _
    · rw [PullbackSimplex.lift_snd]
      apply SSet.stdSimplex.obj₀Equiv.injective
      apply Fin.ext
      omega
  right_inv f := by
    apply Subtype.ext
    let z : (pullback (mappingComplexPost k X p) (mappingBasePoint k r) : SSet.{u}) _⦋0⦌ :=
      PullbackSimplex.lift
        (IsPullback.of_hasPullback (mappingComplexPost k X p) (mappingBasePoint k r)) 0
          ((mappingComplexZeroEquiv k X Y).symm f.val)
          (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) (zero_map_over k r p f.val f.property)
    change mappingComplexZeroEquiv k X Y
      ((pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app (op ⦋0⦌) z) = f.val
    have hz : (pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app (op ⦋0⦌) z =
        (mappingComplexZeroEquiv k X Y).symm f.val :=
      PullbackSimplex.lift_fst _ 0 _ _ (zero_map_over k r p f.val f.property)
    rw [hz]
    exact Equiv.apply_symm_apply _ _

/-- Zero evaluation is the original product-unit restriction of the original first projection. -/
theorem relativeMappingZeroEquiv_val (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (t : (relativeMappingComplex k r p) _⦋0⦌) :
    (relativeMappingZeroEquiv k r p t).val = mappingComplexZeroEquiv k X Y
      ((pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app (op ⦋0⦌) t) := rfl

/-- Reconstruction retains the same entire original zero-prism. -/
theorem relativeMappingZeroEquiv_symm_fst (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (f : {f : X ⟶ Y // f ≫ p = r}) :
    (pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r)).app (op ⦋0⦌)
      ((relativeMappingZeroEquiv k r p).symm f) = (mappingComplexZeroEquiv k X Y).symm f.val :=
  PullbackSimplex.lift_fst
    (IsPullback.of_hasPullback (mappingComplexPost k X p) (mappingBasePoint k r)) 0
      ((mappingComplexZeroEquiv k X Y).symm f.val)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) (zero_map_over k r p f.val f.property)

/-- Reconstruction retains the canonical original zero-parameter point. -/
theorem relativeMappingZeroEquiv_symm_snd (k : ParameterMarking) {X Y Z : Marked.{u}}
    (r : X ⟶ Z) (p : Y ⟶ Z) (f : {f : X ⟶ Y // f ≫ p = r}) :
    (pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r)).app (op ⦋0⦌)
      ((relativeMappingZeroEquiv k r p).symm f) = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) :=
  PullbackSimplex.lift_snd
    (IsPullback.of_hasPullback (mappingComplexPost k X p) (mappingBasePoint k r)) 0
      ((mappingComplexZeroEquiv k X Y).symm f.val)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) (zero_map_over k r p f.val f.property)

end SSet.Marked
