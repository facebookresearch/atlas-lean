/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.MappingFibre

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.MappingFibreTest

variable {W V U : SimplicialSpace.{u}}

/- The whole raw API elaborates with no model or fibrancy instance. -/
example (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre.fst W x y ≫ W.diagram.δ (1 : Fin 2) =
      mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm x :=
  mappingFibre.source_eq W x y

example (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre.fst W x y ≫ W.diagram.δ (0 : Fin 2) =
      mappingFibre.snd W x y ≫ SSet.yonedaEquiv.symm y :=
  mappingFibre.target_eq W x y

example (f : W ⟶ V) (g : V ⟶ U)
    {x y : (W.diagram _⦋0⦌) _⦋0⦌} {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    {x'' y'' : (U.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y')
    (hx' : mappingVertexMap g x' = x'') (hy' : mappingVertexMap g y' = y'') :
    mappingFibre.map f hx hy ≫ mappingFibre.map g hx' hy' =
      mappingFibre.map (f ≫ g) (x' := x'') (y' := y'')
        ((congrArg (mappingVertexMap g) hx).trans hx')
        ((congrArg (mappingVertexMap g) hy).trans hy') :=
  mappingFibre.map_comp f g hx hy hx' hy'

example (f : W ⟶ V) {x y : (W.diagram _⦋0⦌) _⦋0⦌}
    {x' y' : (V.diagram _⦋0⦌) _⦋0⦌}
    (hx : mappingVertexMap f x = x') (hy : mappingVertexMap f y = y') :
    mappingFibre.map f hx hy ≫ mappingFibre.snd V x' y' = mappingFibre.snd W x y :=
  mappingFibre.map_snd f hx hy

/- A nonconstant outer simplex, made discrete in the inner direction using
the native constant-simplicial-object functor. -/
private abbrev discreteSpace (A : SSet.{u}) : SimplicialSpace.{u} :=
  ⟨A ⋙ SimplicialObject.const (Type u)⟩

private def discreteMap {A B : SSet.{u}} (f : A ⟶ B) :
    discreteSpace A ⟶ discreteSpace B :=
  InducedCategory.homMk (whiskerRight f (SimplicialObject.const (Type u)))

private def vertex (n : ℕ) (i : Fin (n + 1)) :
    ((discreteSpace (Δ[n] : SSet.{u})).diagram _⦋0⦌) _⦋0⦌ :=
  SSet.stdSimplex.obj₀Equiv.symm i

/- On the actual identity edge, d1 is vertex0 and d0 is vertex1. -/
example :
    (mappingEndpoint (discreteSpace (Δ[1] : SSet.{0})) ≫ prod.fst).app (op ⦋0⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
      vertex 1 0 := by
  rw [mappingEndpoint_fst]
  change (Δ[1] : SSet.{0}).δ (1 : Fin 2) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = _
  simp only [SSet.stdSimplex.δ_objEquiv_symm_apply, Category.comp_id]
  calc
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ 1) =
        SSet.yonedaEquiv (SSet.stdSimplex.δ (1 : Fin 2)) :=
      (SSet.yonedaEquiv_map (SimplexCategory.δ 1)).symm
    _ = SSet.yonedaEquiv (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
      rw [SSet.stdSimplex.δ_one_eq_const]
    _ = vertex 1 0 := SSet.yonedaEquiv_const _

example :
    (mappingEndpoint (discreteSpace (Δ[1] : SSet.{0})) ≫ prod.snd).app (op ⦋0⦌)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) =
      vertex 1 1 := by
  rw [mappingEndpoint_snd]
  change (Δ[1] : SSet.{0}).δ (0 : Fin 2) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) = _
  simp only [SSet.stdSimplex.δ_objEquiv_symm_apply, Category.comp_id]
  calc
    SSet.stdSimplex.objEquiv.symm (SimplexCategory.δ 0) =
        SSet.yonedaEquiv (SSet.stdSimplex.δ (0 : Fin 2)) :=
      (SSet.yonedaEquiv_map (SimplexCategory.δ 0)).symm
    _ = SSet.yonedaEquiv (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
      rw [SSet.stdSimplex.δ_zero_eq_const]
    _ = vertex 1 1 := SSet.yonedaEquiv_const _

example : vertex.{0} 1 0 ≠ vertex 1 1 := by
  intro h
  have h' : (0 : Fin 2) = 1 := congrArg SSet.stdSimplex.obj₀Equiv h
  exact Fin.zero_ne_one h'

private def shift :
    discreteSpace (Δ[1] : SSet.{0}) ⟶ discreteSpace (Δ[2] : SSet.{0}) :=
  discreteMap (SSet.stdSimplex.δ (0 : Fin 3))

private def collapse :
    discreteSpace (Δ[2] : SSet.{0}) ⟶ discreteSpace (Δ[0] : SSet.{0}) :=
  discreteMap (SSet.const (X := (Δ[2] : SSet.{0})) (SSet.stdSimplex.obj₀Equiv.symm 0))

example : mappingVertexMap shift (vertex 1 0) = vertex 2 1 := rfl
example : mappingVertexMap shift (vertex 1 1) = vertex 2 2 := rfl
example : mappingVertexMap collapse (vertex 2 1) = vertex 0 0 := rfl
example : mappingVertexMap collapse (vertex 2 2) = vertex 0 0 := rfl

/- Both objects and both prescribed vertices move; the second map collapses
distinct vertices, so no monicity premise can be hidden in this client. -/
example :
    mappingFibre.map shift (x := vertex 1 0) (y := vertex 1 1)
        (x' := vertex 2 1) (y' := vertex 2 2) rfl rfl ≫
      mappingFibre.map collapse (x := vertex 2 1) (y := vertex 2 2)
        (x' := vertex 0 0) (y' := vertex 0 0) rfl rfl =
    mappingFibre.map (shift ≫ collapse) (x := vertex 1 0) (y := vertex 1 1)
      (x' := vertex 0 0) (y' := vertex 0 0) rfl rfl :=
  mappingFibre.map_comp shift collapse rfl rfl rfl rfl

/- An explicit higher value universe, with the literal chosen pullback legs. -/
example (A : SimplicialSpace.{u + 1}) (x y : (A.diagram _⦋0⦌) _⦋0⦌) :
    mappingFibre.map (𝟙 A) (x := x) (y := y) (x' := x) (y' := y) rfl rfl =
      𝟙 (mappingFibre A x y) :=
  mappingFibre.map_id A x y

example {A : SimplicialSpace.{u}} {x y x' y' : (A.diagram _⦋0⦌) _⦋0⦌}
    (hx : x = x') (hy : y = y') :
    mappingFibre.map (𝟙 A) hx hy = eqToHom (by cases hx; cases hy; rfl) :=
  mappingFibre.map_id_eqToHom hx hy

end SimplicialSpace.MappingFibreTest
