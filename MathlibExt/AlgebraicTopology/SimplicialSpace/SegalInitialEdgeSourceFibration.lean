/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialEdgeSourceFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyMappingFibre
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpFibrations
import MathlibExt.AlgebraicTopology.SimplicialSpace.ReedyLevelFibrancy

/-!
# The whole leading-edge/tail source map retains the original endpoint fibration

The actual leading-edge target is the pullback of the original endpoint
map along the same original source object and first tail vertex. The
original row source is its first product projection. Thus Reedy fibrancy
gives the source-map fibration required for genuine weak base change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.InitialEdgeTailMapping

/-- The original row source and full tail simplex form the same actual product-base map. -/
def sourceTailMap (W : SimplicialSpace.{u}) (n : ℕ) : rowTarget W n ⟶ W.diagram _⦋0⦌ ⨯ W.diagram _⦋n⦌ :=
  prod.lift (rowSource W n) (pullback.fst _ _)

/-- The actual source and original tail vertex form the whole original endpoint-base comparison. -/
def sourceTailEndpoint (W : SimplicialSpace.{u}) (n : ℕ) :
    W.diagram _⦋0⦌ ⨯ W.diagram _⦋n⦌ ⟶ W.diagram _⦋0⦌ ⨯ W.diagram _⦋0⦌ :=
  prod.map (𝟙 _) (tailFirstVertex W n)

set_option backward.isDefEq.respectTransparency false in
/-- The whole original leading-edge/tail target is the endpoint pullback with both original legs. -/
theorem endpoint_isPullback (W : SimplicialSpace.{u}) (n : ℕ) :
    IsPullback (pullback.snd (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2)))
      (sourceTailMap W n) (mappingEndpoint W) (sourceTailEndpoint W n) := by
  have hw : pullback.snd (tailFirstVertex W n) (W.diagram.δ (0 : Fin 2)) ≫ mappingEndpoint W =
      sourceTailMap W n ≫ sourceTailEndpoint W n := by
    apply prod.hom_ext
    · simp only [sourceTailMap, sourceTailEndpoint, rowSource, Category.assoc,
        mappingEndpoint_fst, prod.map_fst, prod.lift_fst, Category.comp_id]
    · simp only [sourceTailMap, sourceTailEndpoint, Category.assoc,
        mappingEndpoint_snd, prod.map_snd]
      rw [← Category.assoc, prod.lift_snd]
      exact (pullback.condition (f := tailFirstVertex W n) (g := W.diagram.δ (0 : Fin 2))).symm
  apply IsPullback.of_isLimit' (CommSq.mk hw)
  refine PullbackCone.IsLimit.mk hw
    (fun s => pullback.lift (s.snd ≫ prod.snd) s.fst ?_)
    (fun s => pullback.lift_snd _ _ _)
    (fun s => ?_)
    (fun s m hm hn => ?_)
  · have h := congrArg (fun q => q ≫ prod.snd) s.condition
    simpa only [Category.assoc, mappingEndpoint_snd, sourceTailEndpoint, prod.map_snd] using h.symm
  · apply prod.hom_ext
    · simp only [Category.assoc]
      rw [sourceTailMap, prod.lift_fst, rowSource, ← Category.assoc, pullback.lift_snd]
      have h := congrArg (fun q => q ≫ prod.fst) s.condition
      simpa only [Category.assoc, mappingEndpoint_fst, sourceTailEndpoint,
        prod.map_fst, Category.comp_id] using h
    · simp only [Category.assoc]
      rw [sourceTailMap, prod.lift_snd, pullback.lift_fst]
  · apply pullback.hom_ext
    · have h := congrArg (fun q => q ≫ prod.snd) hn
      simpa only [Category.assoc, sourceTailMap, prod.lift_snd, pullback.lift_fst] using h
    · exact hm.trans (pullback.lift_snd _ _ _).symm

/-- The actual original endpoint pullback gives a Kan fibration to the source-and-tail product. -/
theorem sourceTailMap_fibration (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, Fibration (sourceTailMap W n) := by
  intro hW n
  let _ := ReedyModel.mappingEndpoint_fibration W hW
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  exact (fibrations SSet.{u}).of_isPullback (endpoint_isPullback W n)
    ((HomotopicalAlgebra.fibration_iff _).mp (inferInstanceAs (Fibration (mappingEndpoint W))))

/-- The whole leading-edge target's source projection is a Kan fibration at original Reedy fibrancy. -/
theorem rowSource_fibration (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, Fibration (rowSource W n) := by
  intro hW n
  let _ : SSet.KanComplex (W.diagram _⦋n⦌) := ReedyModel.level_kanComplex W hW n
  let _ := sourceTailMap_fibration W hW n
  let _ : Fibration (prod.fst : W.diagram _⦋0⦌ ⨯ W.diagram _⦋n⦌ ⟶ W.diagram _⦋0⦌) := by
    apply (HomotopicalAlgebra.fibration_iff _).mpr
    exact (fibrations SSet.{u}).of_isPullback
      (IsPullback.of_hasBinaryProduct' (W.diagram _⦋0⦌) (W.diagram _⦋n⦌)).flip
      ((HomotopicalAlgebra.fibration_iff _).mp
        (inferInstanceAs (Fibration (terminal.from (W.diagram _⦋n⦌)))))
  have he : sourceTailMap W n ≫ prod.fst = rowSource W n := prod.lift_fst _ _
  rw [← he]
  infer_instance

/-- The original leading-edge source map is sharp at actual Reedy fibrancy. -/
theorem rowSource_sharp (W : SimplicialSpace.{u}) :
    letI : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
    IsFibrant W → ∀ n : ℕ, SSet.SharpComparisonDraft.Sharp (rowSource W n) := by
  intro hW n
  let _ := rowSource_fibration W hW n
  exact SSet.SharpComparisonDraft.sharp_of_fibration _

end SimplicialSpace.InitialEdgeTailMapping
