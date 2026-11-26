/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontVertices
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFunctor
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomRetargetAlgebra

/-!
# The actual cosimplicial original right-Hom resolution

The fixed-front quotient resolving simplex has its two original
structural endpoint labels. Realizing its actual quotient operators and
retargeting by the proved endpoint equations gives whole right-Hom maps.
These preserve identities and composition; no weak-resolution or frame
property is assumed.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightHomResolution
open FixedFrontCollapse FixedFrontVertices
variable {n m k : ℕ}

/-- The entire actual source-to-target Hom of the realized fixed-front quotient. -/
abbrev object (n : ℕ) : SSet.{u} := FixedFrontCollapse.rightHom n

/-- The whole actual quotient operator on the source-to-target realization Hom, retaining its original
  structural endpoints. -/
def map (θ : ⦋n⦌ ⟶ ⦋m⦌) : object.{u} n ⟶ object.{u} m :=
  (realizationMap (FixedFrontOperators.map θ)).map (source n) (target n) ≫
    eqToHom (congrArg₂ (CoherentRealization.hom (FixedFrontCollapse.object m)) (map_source θ) (map_target θ))

/-- The actual Hom map is precisely the original realization map followed by the two proved original
  endpoint equalities. -/
theorem map_readback (θ : ⦋n⦌ ⟶ ⦋m⦌) :
    map.{u} θ = (realizationMap (FixedFrontOperators.map θ)).map (source n) (target n) ≫
      eqToHom (congrArg₂ (CoherentRealization.hom (FixedFrontCollapse.object m)) (map_source θ) (map_target θ)) := rfl

/-- The whole actual right-resolution identity map fixes every original represented Hom cell. -/
theorem map_id (n : ℕ) : map.{u} (𝟙 ⦋n⦌) = 𝟙 (object n) := by
  have hF := FixedFrontOperators.map_id.{u} n
  have hR : realizationMap (FixedFrontOperators.map (𝟙 ⦋n⦌)) = 𝟙 (realization (FixedFrontCollapse.object n)) :=
    (congrArg realizationMap hF).trans (realizationMap_id _)
  have h := HornHomFaces.retargetMap_eq hR (source n) (target n)
    (map_source (𝟙 ⦋n⦌)) (map_target (𝟙 ⦋n⦌)) rfl rfl
  exact h.trans (Category.comp_id _)

/-- The actual whole right-resolution map retains composition at the same original structural source and
  target labels. -/
theorem map_comp (θ : ⦋n⦌ ⟶ ⦋m⦌) (ψ : ⦋m⦌ ⟶ ⦋k⦌) : map.{u} (θ ≫ ψ) = map θ ≫ map ψ := by
  let f := FixedFrontOperators.map.{u} θ
  let g := FixedFrontOperators.map.{u} ψ
  let F := realizationMap f
  let G := realizationMap g
  have hQ := FixedFrontOperators.map_comp.{u} θ ψ
  have hR : realizationMap (FixedFrontOperators.map (θ ≫ ψ)) = F ≫ G :=
    (congrArg realizationMap hQ).trans (realizationMap_comp f g)
  have h := HornHomFaces.retargetMap_eq hR (source n) (target n)
    (map_source (θ ≫ ψ)) (map_target (θ ≫ ψ))
    ((congrArg (fun a => g.app (op ⦋0⦌) a) (map_source θ)).trans (map_source ψ))
    ((congrArg (fun a => g.app (op ⦋0⦌) a) (map_target θ)).trans (map_target ψ))
  have hT := HomRetargetAlgebra.restriction_reindex F G (source n) (target n)
    (map_source θ) (map_target θ) (map_source ψ) (map_target ψ)
  exact h.trans hT.symm

end CategoryTheory.CoherentRealization.RightHomResolution
