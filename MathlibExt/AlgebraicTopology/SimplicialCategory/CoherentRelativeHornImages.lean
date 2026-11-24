/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRelativeHornData
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornOrderedMaps

/-!
# Whole target Hom images in the actual relative coherent horn square

The supplied target simplex and original commutative square identify
every original Hom map, including the outer lift and both endpoint
transports. The nonexceptional maps use the proved whole supplied-face
naturality, without an enriched-filler outcome as an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.RelativeHornImages
open SimplicialEnrichment

variable {C D : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (F : C ⟶ D) (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (σ : coherentSimplex.{u} ⦋n + 2⦌ ⟶ D)
  (sq : CommSq f (Λ[n + 2, i]).ι (coherentNerveFunctor.map F) (SSet.yonedaEquiv.symm σ))

/-- The exact original Hom equality isomorphism at any two supplied individual vertex labels. -/
def homIso (a b : Fin (n + 3)) :
    (F.obj (HornFaces.object f a) ⟶[SSet.{u}] F.obj (HornFaces.object f b)) ≅
      (σ.obj (.mk (ULift.up a)) ⟶[SSet.{u}] σ.obj (.mk (ULift.up b))) :=
  eqToIso (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
    (RelativeHornData.object_image F f σ sq a) (RelativeHornData.object_image F f σ sq b))

/-- The outer endpoint equality isomorphism is exactly the one already derived from the original square. -/
theorem homIso_outer : homIso F f σ sq 0 (Fin.last (n + 2)) = RelativeHornData.endpointIso F f σ sq := rfl

private theorem ordered_congr
    {f₁ f₂ : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj D}
    (hEq : f₁ = f₂) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))
    (a b : Fin (n + 3)) (hab : a ≤ b) (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    HornOutsideIntervals.homMap f₁ hi₀ hiₙ a b hab h ≫
        eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
          (congrArg (fun f' => HornFaces.object f' a) hEq)
          (congrArg (fun f' => HornFaces.object f' b) hEq)) =
      HornOutsideIntervals.homMap f₂ hi₀ hiₙ a b hab h := by
  subst f₂
  change HornOutsideIntervals.homMap f₁ hi₀ hiₙ a b hab h ≫ 𝟙 _ =
    HornOutsideIntervals.homMap f₁ hi₀ hiₙ a b hab h
  exact Category.comp_id _

variable (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

/-- Every nonexceptional original ordered Hom maps to the whole specified target-simplex Hom at the same
  vertex labels. -/
theorem ordered_map_image (a b : Fin (n + 3)) (hab : a ≤ b)
    (h : a ≠ 0 ∨ b ≠ Fin.last (n + 2)) :
    (HornOrderedMaps.orderedMap f hi₀ hiₙ a b hab h ≫
        F.map (HornFaces.object f a) (HornFaces.object f b)) ≫ (homIso F f σ sq a b).hom =
      σ.map (.mk (ULift.up a)) (.mk (ULift.up b)) := by
  have hN := HornMapNaturality.outside_homMap_postcompose F f hi₀ hiₙ a b hab h
  have hE : HornOutsideIntervals.homMap (f ≫ coherentNerveFunctor.map F) hi₀ hiₙ a b hab h ≫
      (homIso F f σ sq a b).hom =
      HornOutsideIntervals.homMap (HornFromSimplex.horn σ i) hi₀ hiₙ a b hab h :=
    ordered_congr sq.w hi₀ hiₙ a b hab h
  exact (congrArg (fun p => p ≫ (homIso F f σ sq a b).hom) hN).trans
    (hE.trans (HornBoxReadback.outside_homMap σ i hi₀ hiₙ a b hab h))

/-- The actual scalar relative lift maps to precisely the original outer target Hom, after the same two
  endpoint equalities. -/
theorem outer_map_image (hF : ∀ x y : C, Fibration (F.map x y)) :
    (RelativeHornData.outerMap F f σ sq hi₀ hiₙ hF ≫
        F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))) ≫
      (homIso F f σ sq 0 (Fin.last (n + 2))).hom =
      σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2)))) := by
  let E := RelativeHornData.endpointIso F f σ sq
  let M := σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2))))
  have hT : RelativeHornData.outerMap F f σ sq hi₀ hiₙ hF ≫
      F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))) = M ≫ E.inv :=
    RelativeHornData.outerMap_target F f σ sq hi₀ hiₙ hF
  exact (congrArg (fun p => p ≫ E.hom) hT).trans
    ((Category.assoc M E.inv E.hom).trans
      ((congrArg (fun p => M ≫ p) E.inv_hom_id).trans (Category.comp_id _)))

end CategoryTheory.CoherentRealization.RelativeHornImages
