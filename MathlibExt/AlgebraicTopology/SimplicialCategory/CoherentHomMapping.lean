/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSimplexEndpoints
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomWholeOperators

/-!
# The actual original Hom-to-right-mapping-space map

The maximum construction gives a genuine simplicial map from the entire
original enriched Hom to the existing right mapping space of the actual
coherent nerve. Every face and degeneracy uses the proved whole enriched
simplex-operator equation and the actual join transport. The supplied
individual original objects are retained.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomMapping
open SimplicialEnrichment HomSimplex HomSimplexEndpoints HomWholeOperators PathMaximumOperators
variable {C : Carrier.{u}} (x y : C)

/-- The genuine standard-simplex map of the supplied original enriched coherent simplex. -/
def simplexMap {k : ℕ} (σ : coherentSimplex.{u} ⦋k⦌ ⟶ C) :
    (Δ[k] : SSet.{u}) ⟶ coherentNerveFunctor.obj C :=
  (SSet.yonedaEquiv (X := coherentNerveFunctor.obj C) (n := ⦋k⦌)).symm σ

/-- The actual enriched-simplex readback of an original Hom simplex follows every supplied simplex operator. -/
theorem simplex_map_operator {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (τ : (x ⟶[SSet.{u}] y) _⦋m⦌) :
    SSet.stdSimplex.map (extension θ) ≫ simplexMap (simplex x y (SSet.yonedaEquiv.symm τ)) =
      simplexMap (simplex x y (SSet.yonedaEquiv.symm ((x ⟶[SSet.{u}] y).map θ.op τ))) := by
  have hY := SSet.yonedaEquiv_symm_naturality_left (X := coherentNerveFunctor.obj C)
    (extension θ) (simplex x y (SSet.yonedaEquiv.symm τ))
  have hS := simplex_operator x y θ (SSet.yonedaEquiv.symm τ)
  have hτ := SSet.yonedaEquiv_symm_naturality_left (X := (x ⟶[SSet.{u}] y)) θ τ
  have hE : coherentSimplexMap (extension θ) ≫ simplex x y (SSet.yonedaEquiv.symm τ) =
      simplex x y (SSet.yonedaEquiv.symm ((x ⟶[SSet.{u}] y).map θ.op τ)) :=
    hS.trans (congrArg (fun t => simplex x y t) hτ)
  exact hY.trans (congrArg (fun σ => simplexMap σ) hE)

private theorem mappingSimplex_operator {n m : ℕ} (θ : ⦋n⦌ ⟶ ⦋m⦌)
    (τ : (x ⟶[SSet.{u}] y) _⦋m⦌) :
    (SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y)).map θ.op
      (mappingSimplex x y (SSet.yonedaEquiv.symm τ)) =
      mappingSimplex x y (SSet.yonedaEquiv.symm ((x ⟶[SSet.{u}] y).map θ.op τ)) := by
  apply Subtype.ext
  let A := (SSet.join.map (SSet.stdSimplex.map θ)).app (Δ[0] : SSet.{u})
  let B := (SSet.joinStdSimplexIso.{u} m 0).hom
  let D := (SSet.joinStdSimplexIso.{u} n 0).hom
  let E := SSet.stdSimplex.map (extension θ)
  let T := simplexMap (simplex x y (SSet.yonedaEquiv.symm τ))
  let U := simplexMap (simplex x y (SSet.yonedaEquiv.symm ((x ⟶[SSet.{u}] y).map θ.op τ)))
  have hJ : A ≫ B = D ≫ E := SSet.joinStdSimplexIso_natural_left θ
  have hT : E ≫ T = U := simplex_map_operator x y θ τ
  change A ≫ (B ≫ T) = D ≫ U
  exact (Category.assoc A B T).symm.trans
    ((congrArg (fun f => f ≫ T) hJ).trans
      ((Category.assoc D E T).trans (congrArg (fun f => D ≫ f) hT)))

/-- The genuine whole original Hom comparison with the existing right mapping space at the supplied original
  source and target. -/
def map : (x ⟶[SSet.{u}] y) ⟶
    SSet.mappingSpaceRight (coherentNerveFunctor.obj C) (vertex x) (vertex y) where
  app q := ↾fun τ => mappingSimplex x y (SSet.yonedaEquiv.symm τ)
  naturality q r θ := by
    apply ConcreteCategory.hom_ext
    intro τ
    induction q using Opposite.rec with
    | _ q =>
      induction q using SimplexCategory.rec with
      | _ m =>
        induction r using Opposite.rec with
        | _ r =>
          induction r using SimplexCategory.rec with
          | _ n => exact (mappingSimplex_operator x y θ.unop τ).symm

/-- The actual comparison reads the entire original enriched simplex after the genuine join transport in
  every degree. -/
theorem map_readback {n : ℕ} (τ : (x ⟶[SSet.{u}] y) _⦋n⦌) :
    ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) ((map x y).app (op ⦋n⦌) τ)).val =
      simplexMap (simplex x y (SSet.yonedaEquiv.symm τ)) :=
  mappingSimplex_readback x y (SSet.yonedaEquiv.symm τ)

/-- The supplied individual source is exactly the front endpoint of every actual mapping-space simplex. -/
theorem map_front {n : ℕ} (τ : (x ⟶[SSet.{u}] y) _⦋n⦌) :
    SSet.frontInclusion n ≫ ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) ((map x y).app (op ⦋n⦌) τ)).val =
      SSet.toDeltaZero (Δ[n] : SSet.{u}) ≫ vertex x := by
  exact (congrArg (fun t => SSet.frontInclusion n ≫ t) (map_readback x y τ)).trans
    (front_map x y (SSet.yonedaEquiv.symm τ))

/-- The supplied individual target is exactly the last endpoint of every actual mapping-space simplex. -/
theorem map_last {n : ℕ} (τ : (x ⟶[SSet.{u}] y) _⦋n⦌) :
    SSet.rightVertex n ≫ ((SSet.mappingSpaceRight.simplexEquivSucc _ _ _ n) ((map x y).app (op ⦋n⦌) τ)).val
      = vertex y := by
  exact (congrArg (fun t => SSet.rightVertex n ≫ t) (map_readback x y τ)).trans
    (right_map x y (SSet.yonedaEquiv.symm τ))

end CategoryTheory.CoherentRealization.HomMapping
