/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentComponentSimplexReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingEdges
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFlagEvaluation

/-!
# The actual coherent nerve maps to the nerve of its original component category

Every actual coherent simplex gives an ordinary functor on its same
ordinal-labelled objects and original represented Hom components.
The direct-to-through relation proves composition. All faces,
degeneracies and strict enriched maps preserve the complete map.
No locally Kan or equivalence hypothesis enters this construction.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.ComponentNerve
open SimplicialEnrichment ComponentSimplexReadback

variable {C : Carrier.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- Every ordered original endpoint triple satisfies the actual component composition relation, including
  coincident endpoints. -/
theorem representative_composition {n : SimplexCategory} (σ : CoherentSimplexIn C n)
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    ComponentCategory.arrowOf C (representative σ i j hij) ≫
        ComponentCategory.arrowOf C (representative σ j k hjk) =
      ComponentCategory.arrowOf C (representative σ i k (hij.trans hjk)) := by
  let θ : ⦋2⦌ ⟶ n := SimplexCategory.mkOfLeComp i j k hij hjk
  have h01 := representative_operator θ σ (0 : Fin 3) 1 (by decide)
  have h12 := representative_operator θ σ (1 : Fin 3) 2 (by decide)
  have h02 := representative_operator θ σ (0 : Fin 3) 2 (by decide)
  have h := triangle_composition ((coherentNerveFunctor.obj C).map θ.op σ)
  rw [h01, h12, h02] at h
  exact h

/-- The supplied whole coherent simplex determines an ordinary functor with its same individual original
  vertices and component arrows. -/
def simplexFunctor {n : SimplexCategory} (σ : CoherentSimplexIn C n) :
    Fin (n.len + 1) ⥤ ComponentCategory.objects.{u} C where
  obj i := ComponentCategory.objectOf.{u} C (σ.obj (point n i))
  map {i j} f := ComponentCategory.arrowOf C (representative σ i j (leOfHom f))
  map_id i := by
    rw [representative_identity]
    exact ComponentCategory.arrowOf_identity C _
  map_comp {i j k} f g := (representative_composition σ i j k (leOfHom f) (leOfHom g)).symm

/-- All genuine simplex operators preserve the entire ordinary functor, with the same original endpoint labels. -/
theorem simplexFunctor_operator {n m : SimplexCategory} (θ : n ⟶ m)
    (σ : CoherentSimplexIn C m) :
    simplexFunctor ((coherentNerveFunctor.obj C).map θ.op σ) =
      (SimplexCategory.toCat.map θ).toFunctor ⋙ simplexFunctor σ := by
  refine Functor.hext (fun _ => rfl) ?_
  intro i j f
  apply heq_of_eq
  exact congrArg (ComponentCategory.arrowOf C) (representative_operator θ σ i j (leOfHom f))

/-- The actual whole coherent nerve comparison to the ordinary nerve of the same original component category. -/
def map (C : Carrier.{u}) : coherentNerveFunctor.obj C ⟶ nerve (ComponentCategory.objects.{u} C) where
  app _ := ↾fun σ => simplexFunctor σ
  naturality q r θ := by
    apply ConcreteCategory.hom_ext
    intro σ
    exact simplexFunctor_operator θ.unop σ

/-- Each actual individual original object is retained by the whole nerve comparison. -/
theorem map_vertex (C : Carrier.{u}) (x : C) :
    (map C).app (op ⦋0⦌) (constantSimplex C ⦋0⦌ x) =
      ComposableArrows.mk₀ (ComponentCategory.objectOf.{u} C x) :=
  ComposableArrows.ext₀ rfl

/-- The direct endpoint representative of the constructed original edge is exactly its supplied Hom vertex. -/
theorem representative_originalEdge (x y : C) (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    representative (HomSimplex.simplex x y (SSet.yonedaEquiv.symm τ)) 0 1 (by decide) = τ := by
  let z : (Δ[0] : SSet.{u}) _⦋0⦌ := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hFlag : (HomFlagEvaluation.flagMap.{u} (n := 0)).app (op ⦋0⦌) z =
      endpointVertex.{u} ⦋1⦌ 0 1 (by decide) := by
    apply ComposableArrows.ext₀ (C := SimplicialThickening.Path
      (ULift.up.{u} (0 : Fin 2)) (ULift.up.{u} (1 : Fin 2)))
    exact AdjacentHom.path_eq _ _ (by decide)
      (fun k _ _ => AdjacentHom.finTwo_vertices k) _
  have h := HomFlagEvaluation.evaluate_constructed_apply x y
    (SSet.yonedaEquiv.symm τ) (op ⦋0⦌) z
  change ((HomSimplex.simplex x y (SSet.yonedaEquiv.symm τ)).map
      (point ⦋1⦌ 0) (point ⦋1⦌ 1)).app (op ⦋0⦌)
        ((HomFlagEvaluation.flagMap.{u} (n := 0)).app (op ⦋0⦌) z) =
      (SSet.yonedaEquiv.symm τ).app (op ⦋0⦌) z at h
  rw [hFlag] at h
  have hτ : (SSet.yonedaEquiv.symm τ).app (op ⦋0⦌) z = τ := by
    simpa only [Category.id_comp, Equiv.apply_symm_apply] using
      (SSet.yonedaEquiv_comp (𝟙 (Δ[0] : SSet.{u})) (SSet.yonedaEquiv.symm τ)).symm
  exact h.trans hτ

/-- The entire actual original edge maps to its same represented ordinary component arrow. -/
theorem map_originalEdge (x y : C) (τ : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    (map C).app (op ⦋1⦌) (HomSimplex.simplex x y (SSet.yonedaEquiv.symm τ)) =
      ComposableArrows.mk₁ (ComponentCategory.arrowOf C τ) := by
  refine ComposableArrows.ext₁ (F := (map C).app (op ⦋1⦌)
    (HomSimplex.simplex x y (SSet.yonedaEquiv.symm τ)))
    (G := ComposableArrows.mk₁ (ComponentCategory.arrowOf C τ)) rfl rfl ?_
  change ComponentCategory.arrowOf C
      (representative (HomSimplex.simplex x y (SSet.yonedaEquiv.symm τ)) 0 1 (by decide)) =
    𝟙 _ ≫ ComponentCategory.arrowOf C τ ≫ 𝟙 _
  rw [representative_originalEdge, Category.id_comp, Category.comp_id]
  rfl

/-- Whole nerve comparison naturality follows the same strict enriched map on every original vertex and
  represented arrow. -/
theorem naturality {D : Carrier.{u}} (F : C ⟶ D) :
    map C ≫ nerveMap (ComponentCategory.mapFunctor F) =
      coherentNerveFunctor.map F ≫ map D := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro σ
  refine Functor.hext (fun _ => rfl) ?_
  intro i j f
  apply heq_of_eq
  exact SSet.mapπ₀_mk (F.map (σ.obj (point q.unop i)) (σ.obj (point q.unop j)))
    (representative σ i j (leOfHom f))

end CategoryTheory.CoherentRealization.ComponentNerve
