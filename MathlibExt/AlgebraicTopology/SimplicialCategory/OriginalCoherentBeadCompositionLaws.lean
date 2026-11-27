/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBead

/-!
# Original bead identity and composition laws

The endpoint maps and complete Hom factors are the original maps.
These laws are the genuine original identity, composition and outer
operator relations in the coherent realization presentation.
-/

noncomputable section

universe u

open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead

open SimplicialEnrichment SimplicialQuiver

/-- The original initial vertex reads the original whole first-endpoint map. -/
theorem Bead.first_map {K : SSet.{u}} {x y : K _⦋0⦌}
    {q : SimplexCategoryᵒᵖ} (b : Bead K x y q) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋b.dimension⦌ 0) ≫
      SSet.yonedaEquiv.symm b.simplex = SSet.yonedaEquiv.symm x := by
  rw [SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg SSet.yonedaEquiv.symm b.source_eq

/-- The original terminal vertex reads the original whole last-endpoint map. -/
theorem Bead.last_map {K : SSet.{u}} {x y : K _⦋0⦌}
    {q : SimplexCategoryᵒᵖ} (b : Bead K x y q) :
    SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋b.dimension⦌ (Fin.last b.dimension)) ≫
      SSet.yonedaEquiv.symm b.simplex = SSet.yonedaEquiv.symm y := by
  rw [SSet.yonedaEquiv_symm_naturality_left]
  exact congrArg SSet.yonedaEquiv.symm b.target_eq

private theorem original_vertex_zero (K : SSet.{u}) (x : K _⦋0⦌) :
    vertex K x (initial 0) = x := by
  have hc : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  change K.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x = x
  rw [hc]
  exact ConcreteCategory.congr_hom (K.map_id (op ⦋0⦌)) x

/-- The zero-length original bead, with its whole original identity coefficient. -/
def identity (K : SSet.{u}) (x : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    Bead K x x q :=
  ⟨0, x, original_vertex_zero K x, original_vertex_zero K x,
    (eId SSet.{u} (initial 0)).app q PUnit.unit⟩

/-- The original zero-length bead evaluates to the original presented identity. -/
theorem evaluation_identity (K : SSet.{u}) (x : K _⦋0⦌) (q : SimplexCategoryᵒᵖ) :
    (identity K x q).evaluation =
      _root_.Quotient.mk (congruence (relations K) q x x)
        (@Quiver.Path.nil (K _⦋0⦌) (quiverAt (generatingQuiver K) q) x) :=
  _root_.Quotient.sound
    (Closure.relation (Equations.identity q x (initial 0) (original_vertex_zero K x)))

/-- The complete original composition law at the actual original endpoint equations. -/
theorem simplexHom_composition {K : SSet.{u}} {n : SimplexCategory}
    (σ : K.obj (op n)) (i j k : coherentSimplex.{u} n)
    {x y z : K _⦋0⦌} (hx : vertex K σ i = x) (hy : vertex K σ j = y)
    (hz : vertex K σ k = z) :
    eComp SSet.{u} i j k ≫ simplexHom K σ i k hx hz =
      (simplexHom K σ i j hx hy ⊗ₘ simplexHom K σ j k hy hz) ≫
        eComp SSet.{u} (C := realization K) x y z := by
  ext q a
  obtain ⟨a, b⟩ := a
  exact _root_.Quotient.sound
    (Closure.relation (Equations.composition q σ i j k hx hy hz a b))

/-- A genuine original outer operator factors the same whole bead insertion,
with the exact original source-object transports. -/
theorem source_operator_factor {K : SSet.{u}} {n m : SimplexCategory}
    (f : n ⟶ m) (σ : K.obj (op m)) (α : K.obj (op n))
    (hα : K.map f.op σ = α) (i j : coherentSimplex.{u} n)
    (i' j' : coherentSimplex.{u} m)
    (hi : (coherentSimplexMap f).obj i = i')
    (hj : (coherentSimplexMap f).obj j = j')
    {x y : K _⦋0⦌} (hx : vertex K α i = x) (hy : vertex K α j = y)
    (hx' : vertex K σ i' = x) (hy' : vertex K σ j' = y) :
    (coherentSimplexMap f).map i j ≫
      eqToHom (congrArg₂ (fun a b : coherentSimplex.{u} m => a ⟶[SSet.{u}] b) hi hj) ≫
        simplexHom K σ i' j' hx' hy' =
      simplexHom K α i j hx hy := by
  subst α
  have hs := simplexHom_source_transport σ hi hj
    ((vertex_operator K f σ i).symm.trans hx)
    ((vertex_operator K f σ j).symm.trans hy) hx' hy'
  exact (congrArg (fun g => (coherentSimplexMap f).map i j ≫ g) hs).trans
    (simplexHom_operator f σ i j hx hy).symm

end CategoryTheory.CoherentRealization.OriginalBead
