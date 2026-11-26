/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRelativeOpenBox

/-!
# Actual relative outer Hom data of a coherent inner horn

The original commutative nerve square determines the exact target Hom
map and both endpoint equalities. Genuine fibrancy of the original
enriched Hom map supplies a scalar box lift with both full equations.
No source or target Kan assumption, enriched filler certificate or
Bergner model is an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace CategoryTheory.CoherentRealization.RelativeHornData
open SimplicialEnrichment HornBoxFaces

variable {C D : Carrier.{u}} {n : ℕ} {i : Fin (n + 3)}
  (F : C ⟶ D) (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C)
  (σ : coherentSimplex.{u} ⦋n + 2⦌ ⟶ D)
  (sq : CommSq f (Λ[n + 2, i]).ι (coherentNerveFunctor.map F) (SSet.yonedaEquiv.symm σ))

include sq in
/-- The original relative square gives exactly the same target object at every individual horn vertex. -/
theorem object_image (t : Fin (n + 3)) :
    F.obj (HornFaces.object f t) = σ.obj (.mk (ULift.up t)) :=
  (congrArg (fun f' => HornFaces.object f' t) sq.w).trans
    (HornFromSimplex.object_readback σ i t)

/-- The precise original outer-endpoint Hom equality isomorphism from the actual square. -/
def endpointIso :
    (F.obj (HornFaces.object f 0) ⟶[SSet.{u}] F.obj (HornFaces.object f (Fin.last (n + 2)))) ≅
      (σ.obj (.mk (ULift.up 0)) ⟶[SSet.{u}] σ.obj (.mk (ULift.up (Fin.last (n + 2))))) :=
  eqToIso (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
    (object_image F f σ sq 0) (object_image F f σ sq (Fin.last (n + 2))))

/-- The entire specified target outer Hom map with precisely the original source-image endpoints. -/
def targetMap : outerHom.{u} n ⟶
    (F.obj (HornFaces.object f 0) ⟶[SSet.{u}] F.obj (HornFaces.object f (Fin.last (n + 2)))) :=
  σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2)))) ≫ (endpointIso F f σ sq).inv

private theorem boxMap_congr {f₁ f₂ : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj D}
    (h : f₁ = f₂) (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2)) :
    HornBoxGlue.boxMap hi₀ hiₙ f₁ ≫
      eqToHom (congrArg₂ (fun x y : D => x ⟶[SSet.{u}] y)
        (congrArg (fun f' => HornFaces.object f' 0) h)
        (congrArg (fun f' => HornFaces.object f' (Fin.last (n + 2))) h)) =
      HornBoxGlue.boxMap hi₀ hiₙ f₂ := by
  subst f₂
  change HornBoxGlue.boxMap hi₀ hiₙ f₁ ≫ 𝟙 _ = HornBoxGlue.boxMap hi₀ hiₙ f₁
  exact Category.comp_id _

variable (hi₀ : i ≠ 0) (hiₙ : i ≠ Fin.last (n + 2))

/-- The whole supplied original Hom box and exact target Hom form the genuine relative scalar square. -/
theorem box_square :
    HornBoxGlue.boxMap hi₀ hiₙ f ≫
        F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))) =
      (HornBoxGlue.box i hi₀ hiₙ).ι ≫ targetMap F f σ sq := by
  let E := endpointIso F f σ sq
  let M := σ.map (.mk (ULift.up 0)) (.mk (ULift.up (Fin.last (n + 2))))
  have hE : HornBoxGlue.boxMap hi₀ hiₙ (f ≫ coherentNerveFunctor.map F) ≫ E.hom =
      HornBoxGlue.boxMap hi₀ hiₙ (HornFromSimplex.horn σ i) := boxMap_congr sq.w hi₀ hiₙ
  have hT : HornBoxGlue.boxMap hi₀ hiₙ (f ≫ coherentNerveFunctor.map F) ≫ E.hom =
      (HornBoxGlue.box i hi₀ hiₙ).ι ≫ M :=
    hE.trans (HornBoxReadback.boxMap σ i hi₀ hiₙ)
  have hI : ((HornBoxGlue.box i hi₀ hiₙ).ι ≫ M) ≫ E.inv =
      HornBoxGlue.boxMap hi₀ hiₙ (f ≫ coherentNerveFunctor.map F) :=
    (Iso.comp_inv_eq E).mpr hT.symm
  exact (HornBoxReadback.boxMap_postcompose (i := i) F f hi₀ hiₙ).trans
    (hI.symm.trans (Category.assoc _ _ _))

private def liftingSquare :
    CommSq (HornBoxGlue.boxMap hi₀ hiₙ f) (HornBoxGlue.box i hi₀ hiₙ).ι
      (F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))))
      (targetMap F f σ sq) := ⟨box_square F f σ sq hi₀ hiₙ⟩

/-- The original Hom fibration constructs an actual outer Hom lift over the full prescribed target map. -/
def outerMap (hF : ∀ x y : C, Fibration (F.map x y)) : outerHom.{u} n ⟶
    (HornFaces.object f 0 ⟶[SSet.{u}] HornFaces.object f (Fin.last (n + 2))) := by
  let _ := hF (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))
  exact (RelativeOpenBox.exists_fill (show (ULift.up.{u} (0 : Fin (n + 3))) ≤
      ULift.up (Fin.last (n + 2)) from Fin.zero_le _) (inner i hi₀ hiₙ)
    (F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))))
    (HornBoxGlue.boxMap hi₀ hiₙ f) (targetMap F f σ sq) (liftingSquare F f σ sq hi₀ hiₙ)).choose

variable (hF : ∀ x y : C, Fibration (F.map x y))

/-- The actual relative lift retains the entire supplied original Hom box. -/
theorem outerMap_box : (HornBoxGlue.box i hi₀ hiₙ).ι ≫ outerMap F f σ sq hi₀ hiₙ hF =
    HornBoxGlue.boxMap hi₀ hiₙ f := by
  let _ := hF (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))
  exact (RelativeOpenBox.exists_fill (show (ULift.up.{u} (0 : Fin (n + 3))) ≤
      ULift.up (Fin.last (n + 2)) from Fin.zero_le _) (inner i hi₀ hiₙ)
    (F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))))
    (HornBoxGlue.boxMap hi₀ hiₙ f) (targetMap F f σ sq) (liftingSquare F f σ sq hi₀ hiₙ)).choose_spec.1

/-- The actual relative lift maps to the whole specified original target Hom, with both endpoint equalities
  unchanged. -/
theorem outerMap_target : outerMap F f σ sq hi₀ hiₙ hF ≫
    F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))) = targetMap F f σ sq := by
  let _ := hF (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2)))
  exact (RelativeOpenBox.exists_fill (show (ULift.up.{u} (0 : Fin (n + 3))) ≤
      ULift.up (Fin.last (n + 2)) from Fin.zero_le _) (inner i hi₀ hiₙ)
    (F.map (HornFaces.object f 0) (HornFaces.object f (Fin.last (n + 2))))
    (HornBoxGlue.boxMap hi₀ hiₙ f) (targetMap F f σ sq) (liftingSquare F f σ sq hi₀ hiₙ)).choose_spec.2

end CategoryTheory.CoherentRealization.RelativeHornData
