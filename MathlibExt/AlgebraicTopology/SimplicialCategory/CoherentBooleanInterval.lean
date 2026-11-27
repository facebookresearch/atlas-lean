/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomObjects

/-!
# Actual parallel arrows and a noninvertible coherent cell

The original coherent two-simplex has two distinct arrows from vertex
zero to vertex two: the direct endpoint path and the path through the
middle vertex. Inclusion supplies an actual noninvertible arrow in their
ordinary Hom poset, hence an original enriched Hom one-simplex. The
proved realization Hom isomorphism transports and reads back that exact
cell and both original boundaries.

This fixture supplies no locally Kan or Bergner-model hypothesis and
makes no quasicategory assertion for its coherent nerve.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.BooleanInterval

/-- The actual endpoint-path carrier in the original coherent two-simplex. -/
abbrev Path02 := SimplicialThickening.Path (ULift.up.{u} (0 : Fin 3)) (ULift.up.{u} (2 : Fin 3))

/-- The original direct path between the two supplied endpoint vertices. -/
def direct : Path02.{u} where
  I := {ULift.up 0, ULift.up 2}
  left := by simp
  right := by simp
  left_le k _ := by change (0 : Fin 3) ≤ k.down; exact Fin.zero_le _
  le_right k _ := by change k.down ≤ (2 : Fin 3); exact Fin.le_last _

/-- The original path containing the middle vertex as well as both endpoints. -/
def through : Path02.{u} where
  I := Set.univ
  left_le k _ := by change (0 : Fin 3) ≤ k.down; exact Fin.zero_le _
  le_right k _ := by change k.down ≤ (2 : Fin 3); exact Fin.le_last _

/-- The supplied parallel original arrows are distinct. -/
theorem direct_ne_through : direct.{u} ≠ through := by
  intro h
  have hm : ULift.up (1 : Fin 3) ∈ direct.{u}.I := by rw [h]; trivial
  simp [direct] at hm

/-- The actual nonidentity inclusion arrow in the original coherent Hom poset. -/
def alpha : direct.{u} ⟶ through := ⟨⟨⟨Set.subset_univ _⟩⟩⟩

/-- This supplied original Hom-category arrow is not invertible. -/
theorem alpha_not_isIso : ¬ IsIso alpha.{u} := by
  intro h
  let _ : IsIso alpha.{u} := h
  have hm : ULift.up (1 : Fin 3) ∈ direct.{u}.I :=
    (inv alpha).hom.down.down (Set.mem_univ _)
  simp [direct] at hm

/-- The original direct-arrow vertex of the enriched Hom simplicial set. -/
def directVertex : (nerve Path02.{u}) _⦋0⦌ := ComposableArrows.mk₀ direct

/-- The original composite-arrow vertex of the same enriched Hom, at the same object endpoints. -/
def throughVertex : (nerve Path02.{u}) _⦋0⦌ := ComposableArrows.mk₀ through

/-- The actual original noninvertible Hom-category arrow as an enriched Hom one-simplex. -/
def alphaCell : (nerve Path02.{u}) _⦋1⦌ := ComposableArrows.mk₁ alpha

/-- These are still two different individual parallel original Hom vertices. -/
theorem directVertex_ne_throughVertex : directVertex.{u} ≠ throughVertex := by
  intro h
  exact direct_ne_through (congrArg (fun p : ComposableArrows Path02.{u} 0 => p.obj 0) h)

/-- The actual source face of the specified enriched cell is the original direct-arrow vertex. -/
theorem alphaCell_source : (nerve Path02.{u}).δ 1 alphaCell = directVertex :=
  ComposableArrows.ext₀ rfl

/-- The actual target face of the same specified enriched cell is the original
composite-arrow vertex. -/
theorem alphaCell_target : (nerve Path02.{u}).δ 0 alphaCell = throughVertex :=
  ComposableArrows.ext₀ rfl

/-- The actual original realization Hom at the supplied two endpoint vertices. -/
abbrev realizedHom :=
  hom (SSet.stdSimplex.{u}.obj ⦋2⦌)
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋2⦌ 0))
    (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋2⦌ 2))

/-- The transported individual direct-arrow vertex in actual coherent realization. -/
def realizedDirect : realizedHom.{u} _⦋0⦌ := (simplexHomIso ⦋2⦌ 0 2).inv.app (op ⦋0⦌) directVertex

/-- The transported individual composite-arrow vertex with the same original object endpoints. -/
def realizedThrough : realizedHom.{u} _⦋0⦌ := (simplexHomIso ⦋2⦌ 0 2).inv.app (op ⦋0⦌) throughVertex

/-- The transported actual enriched cell, rather than a supplied comparison witness. -/
def realizedAlpha : realizedHom.{u} _⦋1⦌ := (simplexHomIso ⦋2⦌ 0 2).inv.app (op ⦋1⦌) alphaCell

/-- The transported actual direct arrow reads back exactly the original direct-arrow vertex. -/
theorem read_realizedDirect : (simplexHomIso.{u} ⦋2⦌ 0 2).hom.app (op ⦋0⦌)
  realizedDirect = directVertex :=
  congr($((simplexHomIso ⦋2⦌ 0 2).inv_hom_id).app (op ⦋0⦌) directVertex)

/-- The transported actual composite arrow reads back exactly the original composite-arrow
vertex. -/
theorem read_realizedThrough : (simplexHomIso.{u} ⦋2⦌ 0 2).hom.app (op ⦋0⦌)
  realizedThrough = throughVertex :=
  congr($((simplexHomIso ⦋2⦌ 0 2).inv_hom_id).app (op ⦋0⦌) throughVertex)

/-- The transported actual cell reads back the whole specified original enriched one-simplex. -/
theorem read_realizedAlpha : (simplexHomIso.{u} ⦋2⦌ 0 2).hom.app (op ⦋1⦌)
  realizedAlpha = alphaCell :=
  congr($((simplexHomIso ⦋2⦌ 0 2).inv_hom_id).app (op ⦋1⦌) alphaCell)

/-- The transported parallel original arrows remain distinct. -/
theorem realizedDirect_ne_realizedThrough : realizedDirect.{u} ≠ realizedThrough := by
  intro h
  exact directVertex_ne_throughVertex (read_realizedDirect.symm.trans
    ((congrArg (fun a => (simplexHomIso.{u} ⦋2⦌ 0 2).hom.app (op ⦋0⦌) a) h).trans
      read_realizedThrough))

/-- The actual transported cell retains the original source face exactly. -/
theorem realizedAlpha_source : realizedHom.{u}.δ 1 realizedAlpha = realizedDirect := by
  have h := congr($((simplexHomIso.{u} ⦋2⦌ 0 2).inv.naturality (SimplexCategory.δ 1).op) alphaCell)
  exact h.symm.trans (congrArg (fun a => (simplexHomIso.{u} ⦋2⦌ 0 2).inv.app (op
    ⦋0⦌) a) alphaCell_source)

/-- The same transported cell retains the original target face exactly. -/
theorem realizedAlpha_target : realizedHom.{u}.δ 0 realizedAlpha = realizedThrough := by
  have h := congr($((simplexHomIso.{u} ⦋2⦌ 0 2).inv.naturality (SimplexCategory.δ 0).op) alphaCell)
  exact h.symm.trans (congrArg (fun a => (simplexHomIso.{u} ⦋2⦌ 0 2).inv.app (op
    ⦋0⦌) a) alphaCell_target)

end CategoryTheory.CoherentRealization.BooleanInterval
