/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHornBoxFaces
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomRetargetAlgebra

/-!
# Literal original negative-piece chart and map comparisons

The supplied negative Hom-box chart reads back the original ordinal face
operator with its actual two outer endpoint transports. Its constructed
map is precisely the original supplied negative-face map under those same
source and object transports. No overlap or filler conclusion is an input.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HornNegativeMaps
open SimplicialEnrichment HornBoxFaces
variable {n : ℕ} (k : Interior.{u} n)

/-- The original raw face endpoints agree with the actual two outer endpoints. -/
def endpointIso :
    (HomBoxDecomposition.negative ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up
      0)) k.val
      ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1)))) : SSet.{u}) ≅
    HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last (n + 2))) :=
  eqToIso (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) =>
    (HomBoxDecomposition.negative a k.val b : SSet.{u}))
    (ULift.ext (source_zero k)) (ULift.ext (target_last k)))

/-- The actual whole negative chart followed by its original inclusion is the original
ordinal Hom map with
  exact outer endpoint transport. -/
theorem chart_operator :
    (negativeChart k).hom ≫ (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up
      (Fin.last (n + 2)))).ι =
      (coherentSimplexMap (SimplexCategory.δ (HornBoxFaces.vertex k))).map
        (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1)))) ≫
          eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) =>
            nerve (SimplicialThickening.Path a b))
            (ULift.ext (source_zero k)) (ULift.ext (target_last k))) := by
  let E := OrdinalFace.negativeIso (HornBoxFaces.vertex k) (ULift.up (0 : Fin (n + 2)))
    (ULift.up (Fin.last (n + 1)))
  let S := endpointIso k
  let T := eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (n + 3)) =>
    nerve (SimplicialThickening.Path a b))
    (ULift.ext (source_zero k)) (ULift.ext (target_last k)))
  have h := eqToHom_naturality
    (f := fun p : ULift.{u} (Fin (n + 3)) × ULift.{u} (Fin (n + 3)) =>
      (HomBoxDecomposition.negative p.1 k.val p.2 : SSet.{u}))
    (g := fun p : ULift.{u} (Fin (n + 3)) × ULift.{u} (Fin (n + 3)) =>
      nerve (SimplicialThickening.Path p.1 p.2))
    (fun p => (HomBoxDecomposition.negative p.1 k.val p.2).ι)
    (show (((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (0 : Fin (n + 2)))),
        ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1))))) =
      ((ULift.up (0 : Fin (n + 3))), (ULift.up (Fin.last (n + 2)))) from
        Prod.ext (ULift.ext (source_zero k)) (ULift.ext (target_last k)))
  have hT : S.hom ≫ (HomBoxDecomposition.negative (ULift.up 0) k.val (ULift.up (Fin.last
    (n + 2)))).ι =
      (HomBoxDecomposition.negative ((OrdinalFace.embedding (HornBoxFaces.vertex k))
        (ULift.up 0)) k.val
        ((OrdinalFace.embedding (HornBoxFaces.vertex k)) (ULift.up (Fin.last (n + 1))))).ι
          ≫ T := h.symm
  exact (Category.assoc E.hom S.hom _).trans
    ((congrArg (fun h => E.hom ≫ h) hT).trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ T)
          (OrdinalFace.negativeIso_operator (HornBoxFaces.vertex k) (ULift.up 0) (ULift.up
            (Fin.last (n + 1)))))))

variable {C : Carrier.{u}} {i : Fin (n + 3)}
  (f : (Λ[n + 2, i] : SSet.{u}) ⟶ coherentNerveFunctor.obj C) (hk : HornBoxFaces.vertex k ≠ i)

/-- The constructed negative piece is the original supplied negative map with the same exact
source and
  object endpoint transports. -/
theorem map_original :
    (endpointIso k).inv ≫
      HornHomFaces.negativeMap f (HornBoxFaces.vertex k) hk
        (ULift.up (0 : Fin (n + 2))) (ULift.up (Fin.last (n + 1))) ≫
          eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
            (congrArg (HornFaces.object f) (source_zero k)) (congrArg (HornFaces.object f)
              (target_last k))) =
    HornBoxFaces.negativeMap f k hk := by
  let E := OrdinalFace.negativeIso (HornBoxFaces.vertex k) (ULift.up (0 : Fin (n + 2)))
    (ULift.up (Fin.last (n + 1)))
  let S := endpointIso k
  let T := eqToHom (congrArg₂ (fun x y : C => x ⟶[SSet.{u}] y)
    (congrArg (HornFaces.object f) (source_zero k)) (congrArg (HornFaces.object f) (target_last k)))
  let M := HornHomFaces.retargetMap (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
    (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
    (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk (.mk (ULift.up 0)))
    (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk (.mk (ULift.up (Fin.last (n + 1)))))
  have h := HomRetargetAlgebra.target_trans (HornFaces.faceFunctor f (HornBoxFaces.vertex k) hk)
    (.mk (ULift.up (0 : Fin (n + 2)))) (.mk (ULift.up (Fin.last (n + 1))))
    (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk (.mk (ULift.up 0)))
    (HornFaces.faceFunctor_obj f (HornBoxFaces.vertex k) hk (.mk (ULift.up (Fin.last (n + 1)))))
    (congrArg (HornFaces.object f) (source_zero k)) (congrArg (HornFaces.object f) (target_last k))
  exact (congrArg (fun h => S.inv ≫ h) (Category.assoc E.inv M T)).trans
    ((congrArg (fun h => S.inv ≫ (E.inv ≫ h)) h).trans (Category.assoc _ _ _).symm)

end CategoryTheory.CoherentRealization.HornNegativeMaps
