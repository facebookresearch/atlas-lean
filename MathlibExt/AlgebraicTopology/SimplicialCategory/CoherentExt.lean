/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentUnit
import MathlibExt.AlgebraicTopology.SimplicialCategory.PresentationUniversalProperty

/-!
# Whole original generator determination for coherent realization

An enriched map from the actual realization is determined by its original
object map and its maps on the actual coherent generators. Equality is
of whole enriched functors, without choosing representatives of objects.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization
open SimplicialEnrichment SimplicialQuiver

/-- Equality on individual original objects and actual generating Homs determines the whole
enriched map. -/
theorem hom_ext {K : SSet.{u}} {C : Carrier.{u}} {F G : realization K ⟶ C}
    (hobj : F.obj = G.obj)
    (hgen : ∀ x y, (generator (generatingQuiver K) x y ≫ quotientHom (relations K) x y
      ≫ F.map x y) ≫
      eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y) (congrFun hobj x) (congrFun hobj y)) =
        generator (generatingQuiver K) x y ≫ quotientHom (relations K) x y ≫
          G.map x y) : F = G := by
  apply (presentedInterpretationEquiv (C := C) (relations K)).injective
  apply Subtype.ext
  cases F with
  | mk objF mapF idF compF =>
      cases G with
      | mk objG mapG idG compG =>
          change objF = objG at hobj
          subst objG
          change Interpretation.mk objF
            (fun x y => generator (generatingQuiver K) x y ≫ quotientHom (relations K) x y
              ≫ mapF x y) =
              Interpretation.mk objF
                (fun x y => generator (generatingQuiver K) x y ≫
                  quotientHom (relations K) x y ≫ mapG x y)
          congr 1
          funext x y
          have h := hgen x y
          change (generator (generatingQuiver K) x y ≫ quotientHom (relations K) x y ≫
            mapF x y) ≫ 𝟙 _ =
            generator (generatingQuiver K) x y ≫ quotientHom (relations K) x y ≫ mapG x y at h
          exact (Category.comp_id _).symm.trans h

/-- Relabeling through a second pair of original endpoint equations is literal equality
transport composition. -/
theorem simplexHom_reindex_comp (K : SSet.{u}) {n : SimplexCategory} (σ : K.obj (op n))
    (i j : coherentSimplex.{u} n) {x y x' y' : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y) (hxx : x = x') (hyy : y = y') :
    simplexHom K σ i j hx hy ≫ eqToHom (congrArg₂ (hom K) hxx hyy) =
      simplexHom K σ i j (hx.trans hxx) (hy.trans hyy) := by
  subst x'
  subst y'
  change simplexHom K σ i j hx hy ≫ 𝟙 _ = simplexHom K σ i j hx hy
  exact Category.comp_id _

/-- Equal original outer simplices determine equal actual generating paths with the same
endpoint labels. -/
theorem arrowPath_simplex_congr (K : SSet.{u}) {n : SimplexCategory} {σ τ : K.obj (op n)}
    (h : σ = τ) (i j : coherentSimplex.{u} n) {x y : K _⦋0⦌}
    (hx : vertex K σ i = x) (hy : vertex K σ j = y)
    (hx' : vertex K τ i = x) (hy' : vertex K τ j = y) {q : SimplexCategoryᵒᵖ}
    (a : (i ⟶[SSet.{u}] j).obj q) :
    arrowPath K σ i j hx hy a = arrowPath K τ i j hx' hy' a := by
  subst τ
  rfl

end CategoryTheory.CoherentRealization
