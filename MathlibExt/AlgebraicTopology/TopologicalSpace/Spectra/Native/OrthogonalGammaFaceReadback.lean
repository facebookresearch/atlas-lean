/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaSmashFaces

/-!
# Evaluation of the original orthogonal Gamma faces

The sphere coefficient maps keep the original identity and positive block
crossing frames. All native maps use the original free/evaluation adjunction
and the complete original coefficient isomorphism.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory BraidedCategory CategoryTheory.Limits
open CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalComplementBundle
open CategoryTheory.Spectra.OrthogonalCoendThom
open CategoryTheory.Spectra.OrthogonalSmashGammaGeometry
open PointedCGWH
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalFreeSphereSmashFlatness
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces.Geometry
open scoped ZeroObject
attribute [local instance] HasZeroObject.zeroMorphismsOfZeroObject

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.Geometry

/-- The original identity frame splits the first and second coordinate blocks. -/
theorem coordinatePair_identity (n : ℕ) (x : Euclidean (n + n)) :
    coordinatePair n (n + n) n (OrthogonalMatrixHom.id (n + n)) x =
      EuclideanSpace.finAddEquivProd x := by
  apply Prod.ext
  · apply WithLp.ofLp_injective
    funext i
    change (coefficientCoordinates n (n + n) n (OrthogonalMatrixHom.id (n + n)) x).ofLp i = _
    rw [coefficientCoordinates_id_apply]
    dsimp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]
  · apply WithLp.ofLp_injective
    funext i
    change (retainedCoordinates n (n + n) n (OrthogonalMatrixHom.id (n + n)) x).ofLp i = _
    rw [retainedCoordinates_id_apply]
    dsimp [EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd]

/-- The original sphere tensorator retains both original coordinate blocks. -/
theorem sphereTensor_point (n : ℕ) (x : Euclidean (n + n)) :
    spherePoint.{u, v} (n + n) x ≫ (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom =
      pointPair
        (spherePoint.{u, v} n (coefficientCoordinates n (n + n) n (OrthogonalMatrixHom.id (n + n)) x))
        (spherePoint.{u, v} n (retainedCoordinates n (n + n) n (OrthogonalMatrixHom.id (n + n)) x)) := by
  apply pointValue_injective
  rw [pointValue_comp, spherePoint_value, PointedCGWH.orthogonalSphereTensorIso_apply_coe]
  rw [pointPair_value, spherePoint_value, spherePoint_value]
  erw [PointedCGWH.canonicalProduct_choose]
  dsimp only
  rw [PointedCGWH.orthogonalSphereSplitHomeomorph_apply, ← coordinatePair_identity]
  rfl

/-- The unchanged identity matrix gives the original coefficient-first native coend leg. -/
def identityInclusion (n : ℕ) : PointedCGWH.orthogonalSphere.{u, v} n ⟶
    (OrthogonalOperatorIndex.ofIndex.{u, v} n ⟶[PointedCGWH.{u, v}]
      OrthogonalOperatorIndex.ofIndex.{u, v} (n + n)) :=
  (λ_ (PointedCGWH.orthogonalSphere.{u, v} n)).inv ≫
    (OrthogonalIndex.matrixPoint.{u, v} (OrthogonalMatrixHom.id (n + n)) ⊗ₘ
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} n)) ≫ OrthogonalOperatorIndex.ι.{u, v} n (n + n) n

/-- Every finite sphere coefficient enters the original identity matrix leg unchanged. -/
theorem identityInclusion_spherePoint (n : ℕ) (x : Euclidean n) :
    spherePoint.{u, v} n x ≫ identityInclusion.{u, v} n =
      pointPair (OrthogonalIndex.matrixPoint.{u, v} (OrthogonalMatrixHom.id (n + n)))
        (spherePoint.{u, v} n x) ≫ OrthogonalOperatorIndex.ι.{u, v} n (n + n) n := by
  dsimp only [identityInclusion]
  rw [pointPair_factor_left]
  simp only [Category.assoc]

/-- The entire identity-frame coefficient retains the original tensorator and ambient braid. -/
theorem coefficientMap_identity (n : ℕ) :
    coefficientMap.{u, v} n (n + n) n (OrthogonalMatrixHom.id (n + n)) =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
        (β_ (PointedCGWH.orthogonalSphere.{u, v} n) (PointedCGWH.orthogonalSphere.{u, v} n)).hom ≫
        (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ identityInclusion.{u, v} n) := by
  apply PointedCGWH.isSeparator_tensorUnit.def
  intro p
  rcases spherePoint_cases (n + n) p with hp | ⟨x, rfl⟩
  · rw [hp, zero_comp, zero_comp]
  · rw [coefficientMap_point]
    rw [← Category.assoc, sphereTensor_point, ← Category.assoc, pointPair_braiding, pointPairNatural,
      Category.comp_id, identityInclusion_spherePoint]

/-- The complete block-crossing coefficient is the original native sphere inclusion. -/
theorem coefficientMap_blockSwap (n : ℕ) :
    coefficientMap.{u, v} n (n + n) n (OrthogonalIndex.blockSwap n n) =
      (PointedCGWH.orthogonalSphereTensorIso.{u, v} n n).hom ≫
        (𝟙 (PointedCGWH.orthogonalSphere.{u, v} n) ⊗ₘ OrthogonalOperatorIndex.nu.{u, v} n n) := by
  apply PointedCGWH.isSeparator_tensorUnit.def
  intro p
  rcases spherePoint_cases (n + n) p with hp | ⟨x, rfl⟩
  · rw [hp, zero_comp, zero_comp]
  · have hr : retainedCoordinates n (n + n) n (OrthogonalIndex.blockSwap n n) x =
        coefficientCoordinates n (n + n) n (OrthogonalMatrixHom.id (n + n)) x := by
      apply WithLp.ofLp_injective
      funext i
      rw [retainedCoordinates_blockSwap_apply, coefficientCoordinates_id_apply]
    have hc : coefficientCoordinates n (n + n) n (OrthogonalIndex.blockSwap n n) x =
        retainedCoordinates n (n + n) n (OrthogonalMatrixHom.id (n + n)) x := by
      apply WithLp.ofLp_injective
      funext i
      rw [coefficientCoordinates_blockSwap_apply, retainedCoordinates_id_apply]
    rw [coefficientMap_point, hr, hc]
    rw [← Category.assoc, sphereTensor_point, pointPairNatural, Category.comp_id, nu_spherePoint]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.Geometry

open HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.Geometry

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  HomotopicalAlgebra.EnrichedProjective.Native.allObjectsFibrant
  PointedCGWH.modelCategory.allObjectsFibrant
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The original sphere rotation equates the two complete explicitly read coefficient maps. -/
theorem explicit_rotation_map_eq (n : ℕ) :
    (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
      (Free.extend (OrthogonalOperatorIndex.ofIndex (n + n)) (PointedCGWH.orthogonalSphere (n + n))
        (sphereFree n)
        ((PointedCGWH.orthogonalSphereTensorIso n n).hom ≫
          (β_ (PointedCGWH.orthogonalSphere n) (PointedCGWH.orthogonalSphere n)).hom ≫
          (𝟙 (PointedCGWH.orthogonalSphere n) ⊗ₘ identityInclusion n))) =
    (HomotopicalAlgebra.toHomotopyCategory Actual.OrthogonalCarrier.{u, v}).map
      (Free.extend (OrthogonalOperatorIndex.ofIndex (n + n)) (PointedCGWH.orthogonalSphere (n + n))
        (sphereFree n)
        ((PointedCGWH.orthogonalSphereTensorIso n n).hom ≫
          (𝟙 (PointedCGWH.orthogonalSphere n) ⊗ₘ OrthogonalOperatorIndex.nu n n))) := by
  simpa only [spectrumMap, coefficientMap_identity, coefficientMap_blockSwap] using
    spectrumMap_rotation_map_eq.{u, v} n

/-- The genuine original native cylinder has exactly the complete identity coefficient endpoint. -/
theorem nativeRotation_zero (n : ℕ) :
    PointedCGWH.EnrichedIntervalCylinder.inclusion 0 (sphereFree.{u, v} (n + n)) ≫
      (nativeRotationHomotopy.{u, v} n).val =
    Free.extend (OrthogonalOperatorIndex.ofIndex (n + n)) (PointedCGWH.orthogonalSphere (n + n))
      (sphereFree n)
      ((PointedCGWH.orthogonalSphereTensorIso n n).hom ≫
        (β_ (PointedCGWH.orthogonalSphere n) (PointedCGWH.orthogonalSphere n)).hom ≫
        (𝟙 (PointedCGWH.orthogonalSphere n) ⊗ₘ identityInclusion n)) := by
  simpa only [spectrumMap, coefficientMap_identity] using (nativeRotationHomotopy.{u, v} n).property.1

/-- The same original native cylinder has exactly the complete positive block-crossing endpoint. -/
theorem nativeRotation_one (n : ℕ) :
    PointedCGWH.EnrichedIntervalCylinder.inclusion 1 (sphereFree.{u, v} (n + n)) ≫
      (nativeRotationHomotopy.{u, v} n).val =
    Free.extend (OrthogonalOperatorIndex.ofIndex (n + n)) (PointedCGWH.orthogonalSphere (n + n))
      (sphereFree n)
      ((PointedCGWH.orthogonalSphereTensorIso n n).hom ≫
        (𝟙 (PointedCGWH.orthogonalSphere n) ⊗ₘ OrthogonalOperatorIndex.nu n n)) := by
  simpa only [spectrumMap, coefficientMap_blockSwap] using (nativeRotationHomotopy.{u, v} n).property.2

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.Geometry


universe uC vC uD vD

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.SourceTransport
open PointedCGWH.Spectra.Orthogonal.CanonicalSourceFreeSmash.Primitive
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
  {D : Type uD} [Category.{vD} D] (E : C ≌ D)
theorem reconstruction_left_unitor (N : C) :
    letI := Monoidal.transport E
    (reconstructionIso E (𝟙_ C) N).inv ≫ (λ_ (E.functor.obj N)).hom =
      E.functor.map (λ_ N).hom := by
  let := Monoidal.transport E
  change E.functor.map (E.unitIso.hom.app (𝟙_ C) ⊗ₘ E.unitIso.hom.app N) ≫
    E.functor.map ((E.unitIso.inv.app (𝟙_ C) ▷ E.inverse.obj (E.functor.obj N)) ≫
      (λ_ (E.inverse.obj (E.functor.obj N))).hom) ≫ E.counitIso.hom.app (E.functor.obj N) = _
  have h : (E.unitIso.hom.app (𝟙_ C) ⊗ₘ E.unitIso.hom.app N) ≫
      ((E.unitIso.inv.app (𝟙_ C) ▷ E.inverse.obj (E.functor.obj N)) ≫
        (λ_ (E.inverse.obj (E.functor.obj N))).hom) =
      (λ_ N).hom ≫ E.unitIso.hom.app N := by
    rw [← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [E.unitIso.hom_inv_id_app, Functor.id_obj, Category.comp_id, id_tensorHom]
    exact leftUnitor_naturality (E.unitIso.hom.app N)
  rw [← Category.assoc, ← E.functor.map_comp, h, E.functor.map_comp, Category.assoc]
  simp only [E.functor_unitIso_comp, Category.comp_id]

theorem reconstruction_right_unitor (N : C) :
    letI := Monoidal.transport E
    (reconstructionIso E N (𝟙_ C)).inv ≫ (ρ_ (E.functor.obj N)).hom =
      E.functor.map (ρ_ N).hom := by
  let := Monoidal.transport E
  change E.functor.map (E.unitIso.hom.app N ⊗ₘ E.unitIso.hom.app (𝟙_ C)) ≫
    E.functor.map ((E.inverse.obj (E.functor.obj N) ◁ E.unitIso.inv.app (𝟙_ C)) ≫
      (ρ_ (E.inverse.obj (E.functor.obj N))).hom) ≫ E.counitIso.hom.app (E.functor.obj N) = _
  have h : (E.unitIso.hom.app N ⊗ₘ E.unitIso.hom.app (𝟙_ C)) ≫
      ((E.inverse.obj (E.functor.obj N) ◁ E.unitIso.inv.app (𝟙_ C)) ≫
        (ρ_ (E.inverse.obj (E.functor.obj N))).hom) =
      (ρ_ N).hom ≫ E.unitIso.hom.app N := by
    rw [← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [E.unitIso.hom_inv_id_app, Functor.id_obj, Category.comp_id, tensorHom_id]
    exact rightUnitor_naturality (E.unitIso.hom.app N)
  rw [← Category.assoc, ← E.functor.map_comp, h, E.functor.map_comp, Category.assoc]
  simp only [E.functor_unitIso_comp, Category.comp_id]

theorem reconstruction_inv_naturality {P P' Q Q' : C} (f : P ⟶ P') (g : Q ⟶ Q') :
    letI := Monoidal.transport E
    (reconstructionIso E P Q).inv ≫ (E.functor.map f ⊗ₘ E.functor.map g) =
      E.functor.map (f ⊗ₘ g) ≫ (reconstructionIso E P' Q').inv := by
  let := Monoidal.transport E
  apply (cancel_mono (reconstructionIso E P' Q').hom).1
  rw [Category.assoc, reconstructionIso_naturality, Iso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem pair_left {P Q R N : C} {A B T Z : D}
    (eP : E.functor.obj P ≅ A) (eQ : E.functor.obj Q ≅ B)
    (eR : E.functor.obj R ≅ T) (eZ : E.functor.obj N ≅ Z)
    (e : P ⊗ Q ≅ R) (f : P ⟶ 𝟙_ C) (g : Q ⟶ N) :
    letI := Monoidal.transport E
    (ofIso E eP eQ eR e).inv ≫
      ((eP.inv ≫ E.functor.map f) ⊗ₘ (eQ.inv ≫ E.functor.map g ≫ eZ.hom)) ≫ (λ_ Z).hom =
      eR.inv ≫ E.functor.map (e.inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) ≫ eZ.hom := by
  let := Monoidal.transport E
  have hMap : (eP.hom ⊗ₘ eQ.hom) ≫
      ((eP.inv ≫ E.functor.map f) ⊗ₘ (eQ.inv ≫ E.functor.map g ≫ eZ.hom)) =
      (E.functor.map f ⊗ₘ E.functor.map g) ≫ (𝟙_ D ◁ eZ.hom) := by
    rw [tensorHom_comp_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id_assoc]
    change (E.functor.map f ⊗ₘ (E.functor.map g ≫ eZ.hom)) =
      ((E.functor.map f ≫ 𝟙 (E.functor.obj (𝟙_ C))) ⊗ₘ (E.functor.map g ≫ eZ.hom))
    rw [Category.comp_id]
  calc
    _ = eR.inv ≫ E.functor.map e.inv ≫ (reconstructionIso E P Q).inv ≫
        ((eP.hom ⊗ₘ eQ.hom) ≫
          ((eP.inv ≫ E.functor.map f) ⊗ₘ (eQ.inv ≫ E.functor.map g ≫ eZ.hom))) ≫ (λ_ Z).hom := by
      rw [ofIso_inv]
      simp only [reconstructionIso_inv, Category.assoc]
    _ = eR.inv ≫ E.functor.map e.inv ≫ (reconstructionIso E P Q).inv ≫
        (E.functor.map f ⊗ₘ E.functor.map g) ≫ (𝟙_ D ◁ eZ.hom) ≫ (λ_ Z).hom := by
      rw [hMap]
      simp only [Category.assoc]
    _ = eR.inv ≫ E.functor.map e.inv ≫
        ((reconstructionIso E P Q).inv ≫ (E.functor.map f ⊗ₘ E.functor.map g)) ≫
        (λ_ (E.functor.obj N)).hom ≫ eZ.hom := by
      rw [leftUnitor_naturality]
      simp only [Category.assoc]
    _ = eR.inv ≫ E.functor.map e.inv ≫ E.functor.map (f ⊗ₘ g) ≫
        ((reconstructionIso E (𝟙_ C) N).inv ≫ (λ_ (E.functor.obj N)).hom) ≫ eZ.hom := by
      rw [reconstruction_inv_naturality]
      simp only [Category.assoc]
    _ = _ := by
      rw [reconstruction_left_unitor, E.functor.map_comp, E.functor.map_comp]
      simp only [Category.assoc]

theorem pair_right {P Q R N : C} {A B T Z : D}
    (eP : E.functor.obj P ≅ A) (eQ : E.functor.obj Q ≅ B)
    (eR : E.functor.obj R ≅ T) (eZ : E.functor.obj N ≅ Z)
    (e : P ⊗ Q ≅ R) (f : P ⟶ N) (g : Q ⟶ 𝟙_ C) :
    letI := Monoidal.transport E
    (ofIso E eP eQ eR e).inv ≫
      ((eP.inv ≫ E.functor.map f ≫ eZ.hom) ⊗ₘ (eQ.inv ≫ E.functor.map g)) ≫ (ρ_ Z).hom =
      eR.inv ≫ E.functor.map (e.inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom) ≫ eZ.hom := by
  let := Monoidal.transport E
  have hMap : (eP.hom ⊗ₘ eQ.hom) ≫
      ((eP.inv ≫ E.functor.map f ≫ eZ.hom) ⊗ₘ (eQ.inv ≫ E.functor.map g)) =
      (E.functor.map f ⊗ₘ E.functor.map g) ≫ (eZ.hom ▷ 𝟙_ D) := by
    rw [tensorHom_comp_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id_assoc]
    change ((E.functor.map f ≫ eZ.hom) ⊗ₘ E.functor.map g) =
      ((E.functor.map f ≫ eZ.hom) ⊗ₘ (E.functor.map g ≫ 𝟙 (E.functor.obj (𝟙_ C))))
    rw [Category.comp_id]
  calc
    _ = eR.inv ≫ E.functor.map e.inv ≫ (reconstructionIso E P Q).inv ≫
        ((eP.hom ⊗ₘ eQ.hom) ≫
          ((eP.inv ≫ E.functor.map f ≫ eZ.hom) ⊗ₘ (eQ.inv ≫ E.functor.map g))) ≫ (ρ_ Z).hom := by
      rw [ofIso_inv]
      simp only [reconstructionIso_inv, Category.assoc]
    _ = eR.inv ≫ E.functor.map e.inv ≫ (reconstructionIso E P Q).inv ≫
        (E.functor.map f ⊗ₘ E.functor.map g) ≫ (eZ.hom ▷ 𝟙_ D) ≫ (ρ_ Z).hom := by
      rw [hMap]
      simp only [Category.assoc]
    _ = eR.inv ≫ E.functor.map e.inv ≫
        ((reconstructionIso E P Q).inv ≫ (E.functor.map f ⊗ₘ E.functor.map g)) ≫
        (ρ_ (E.functor.obj N)).hom ≫ eZ.hom := by
      rw [rightUnitor_naturality]
      simp only [Category.assoc]
    _ = eR.inv ≫ E.functor.map e.inv ≫ E.functor.map (f ⊗ₘ g) ≫
        ((reconstructionIso E N (𝟙_ C)).inv ≫ (ρ_ (E.functor.obj N)).hom) ≫ eZ.hom := by
      rw [reconstruction_inv_naturality]
      simp only [Category.assoc]
    _ = _ := by
      rw [reconstruction_right_unitor, E.functor.map_comp, E.functor.map_comp]
      simp only [Category.assoc]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.SourceTransport


universe uA uV vV uI vI uJ

open scoped MonoidalClosed CategoryTheory.MonObj
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
attribute [local instance] Enriched.prodCategory EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.SourceCast

theorem cast_heq_original {A B C : Sort uA}
    (h : A = B) (x : A) (y : C) (hxy : HEq x y) : HEq (cast h x) y :=
  (cast_heq h x).trans hxy

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {D : Type uD} [Category.{vD} D]

theorem leftFamily_cast (M N : MonoidalCategory D) (h : M = N)
    (P : ℕ → V → D) (S : ℕ → V)
    (gamma : Independent.GammaType M P S)
    (pair : Independent.PairFormula M P (fun n r => n + r)) :
    Independent.leftFaceFamily M P S gamma pair =
      Independent.leftFaceFamily N P S
        (cast (congrArg (fun Q => Independent.GammaType Q P S) h) gamma)
        (cast (congrArg (fun Q => Independent.PairFormula Q P (fun n r => n + r)) h) pair) := by
  cases h
  rfl

theorem rightFamily_cast (M N : MonoidalCategory D) (h : M = N)
    (P : ℕ → V → D) (S : ℕ → V)
    (gamma : Independent.GammaType M P S)
    (pair : Independent.PairFormula M P (fun n r => n + r)) :
    Independent.rightFaceFamily M P S gamma pair =
      Independent.rightFaceFamily N P S
        (cast (congrArg (fun Q => Independent.GammaType Q P S) h) gamma)
        (cast (congrArg (fun Q => Independent.PairFormula Q P (fun n r => n + r)) h) pair) := by
  cases h
  rfl

theorem leftSphereFamily_cast (M N : MonoidalCategory D) (h : M = N)
    (F : ℕ → V ⥤ D) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => (F n).obj K) S)
    (pair : Independent.PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) :
    Independent.leftSphereFamily M F S gamma pair coefficient =
      Independent.leftSphereFamily N F S
        (cast (congrArg (fun Q => Independent.GammaType Q (fun n K => (F n).obj K) S) h) gamma)
        (cast (congrArg (fun Q => Independent.PairFormula Q (fun n K => (F n).obj K)
          (fun n r => n + r)) h) pair) coefficient := by
  cases h
  rfl

theorem rightSphereFamily_cast (M N : MonoidalCategory D) (h : M = N)
    (F : ℕ → V ⥤ D) (S : ℕ → V)
    (gamma : Independent.GammaType M (fun n K => (F n).obj K) S)
    (pair : Independent.PairFormula M (fun n K => (F n).obj K) (fun n r => n + r))
    (coefficient : ∀ n : ℕ, S (n + n) ≅ S n ⊗ S n) :
    Independent.rightSphereFamily M F S gamma pair coefficient =
      Independent.rightSphereFamily N F S
        (cast (congrArg (fun Q => Independent.GammaType Q (fun n K => (F n).obj K) S) h) gamma)
        (cast (congrArg (fun Q => Independent.PairFormula Q (fun n K => (F n).obj K)
          (fun n r => n + r)) h) pair) coefficient := by
  cases h
  rfl

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.SourceCast


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.BinaryEvaluation
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {C : Type uC} [EnrichedCategory V C] {D : Type uD} [EnrichedCategory V D]
  {J : Type uJ} [EnrichedCategory V J] (T : EnrichedFunctor V (C × D) J)
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : J),
    HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : J),
    HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ (F : EnrichedFunctor V C V) (G : EnrichedFunctor V D V) (k : J),
    HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : J),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : J),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (C × D)) (k : J),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) F.toEnrichedFunctor)]

theorem pair_evaluate (n : C) (r : D) (K L : V)
    (M : EnrichedFunctorCat V C) (N : EnrichedFunctorCat V D) (Y : EnrichedFunctorCat V J)
    (f : Free.object n K ⟶ M) (g : Free.object r L ⟶ N)
    (h : (EnrichedDayKernel.Input.bifunctor T).obj (M, N) ⟶ Y) :
    Free.evaluate (T.obj (n, r)) (K ⊗ L) Y
      ((EnrichedDayKernel.FreePairComparison.iso T n r K L).inv ≫
        (EnrichedDayKernel.Input.bifunctor T).map
          (X := (Free.object n K, Free.object r L)) (Y := (M, N)) (f, g) ≫ h) =
      (Free.evaluate n K M f ⊗ₘ Free.evaluate r L N g) ≫
        EnrichedDayKernel.Generators.point T M.toEnrichedFunctor N.toEnrichedFunctor (n, r) ≫
          component h (T.obj (n, r)) := by
  have hInv := EnrichedDayKernel.FreePairComparison.evaluate_iso_inv T n r K L
  have hInput := EnrichedDayKernel.Generators.point_input_natural T f g (n, r)
  have hInput' :
      EnrichedDayKernel.Generators.point T (Free.object n K).toEnrichedFunctor
        (Free.object r L).toEnrichedFunctor (n, r) ≫ EnrichedDayKernel.Input.mapAt T f g (T.obj (n, r)) =
      (component f n ⊗ₘ component g r) ≫
        EnrichedDayKernel.Generators.point T M.toEnrichedFunctor N.toEnrichedFunctor (n, r) := hInput
  have hCoefficients :
      (((ρ_ K).inv ≫ (K ◁ eId V n)) ⊗ₘ ((ρ_ L).inv ≫ (L ◁ eId V r))) ≫
        (component f n ⊗ₘ component g r) = (Free.evaluate n K M f ⊗ₘ Free.evaluate r L N g) := by
    rw [tensorHom_comp_tensorHom]
    simp only [Free.evaluate, Category.assoc]
  have hMap :
      component ((EnrichedDayKernel.Input.bifunctor T).map
          (X := (Free.object n K, Free.object r L)) (Y := (M, N)) (f, g)) (T.obj (n, r)) =
        EnrichedDayKernel.Input.mapAt T f g (T.obj (n, r)) :=
    EnrichedDayKernel.Input.bifunctor_map_component T
      (F := Free.object n K) (F' := M) (G := Free.object r L) (G' := N) f g (T.obj (n, r))
  rw [Free.evaluate_postcomp, EnrichedFunctorCat.evaluation_map, component_comp]
  rw [hInv, EnrichedDayKernel.FreePairComparison.inverseCoefficient]
  simp only [Category.assoc]
  rw [hMap, ← Category.assoc _ _ (component h (T.obj (n, r))), hInput']
  simpa only [Category.assoc] using congrArg
    (fun z : K ⊗ L ⟶ M.toEnrichedFunctor.obj n ⊗ N.toEnrichedFunctor.obj r =>
      z ≫ EnrichedDayKernel.Generators.point T M.toEnrichedFunctor N.toEnrichedFunctor (n, r) ≫
        component h (T.obj (n, r))) hCoefficients

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.BinaryEvaluation


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.DayEvaluation
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] (d : EnrichedMonoidalCategoryData V I)

theorem diagram_pair_evaluate_generic (n r : I) (K L : V)
    (M N Y : EnrichedFunctorCat V I)
    (f : Free.object n K ⟶ M) (g : Free.object r L ⟶ N)
    (h : letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d; M ⊗ N ⟶ Y) :
    let := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    Free.evaluate (d.tensorEnrichedFunctor.obj (n, r)) (K ⊗ L) Y
      ((EnrichedDayKernel.FreePairComparison.iso
        d.tensorEnrichedFunctor n r K L).inv ≫ (f ⊗ₘ g) ≫ h) =
      (Free.evaluate n K M f ⊗ₘ Free.evaluate r L N g) ≫
        EnrichedDayKernel.Generators.point d.tensorEnrichedFunctor
          M.toEnrichedFunctor N.toEnrichedFunctor (n, r) ≫ component h (d.tensorEnrichedFunctor.obj (n, r)) := by
  letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  let T := d.tensorEnrichedFunctor
  change Free.evaluate (T.obj (n, r)) (K ⊗ L) Y
    ((EnrichedDayKernel.FreePairComparison.iso T n r K L).inv ≫
      (EnrichedDayKernel.Input.bifunctor T).map
        (X := (Free.object n K, Free.object r L)) (Y := (M, N)) (f, g) ≫ h) = _
  exact PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.BinaryEvaluation.pair_evaluate
    T n r K L M N Y f g h

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.DayEvaluation




open CommutativeModuleConversion
open CategoryTheory.Spectra.OrthogonalSourceRightModule
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.ModuleAdjunct
open PointedCGWH.Spectra.Orthogonal.SphereSmashFree
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open CommutativeModuleConversion

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)] [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The right-module tensor used to evaluate the original free-source adjunction and
precomposition maps. -/
local instance : MonoidalCategory (RightModule S) := RightModuleFree.tensorMonoidal S

/-- The two original source adjunctions read the unchanged left-unit pair through its entire generator. -/
theorem left_pair (n r t : I) (K L : V)
    (e : Free.object n K ⊗ Free.object r L ≅ Free.object t (K ⊗ L))
    (N : RightModule S)
    (f : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K ⟶ 𝟙_ (RightModule S))
    (g : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S r).obj L ⟶ N) :
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S t).homEquiv (K ⊗ L) N
      ((Evaluation.ofIso S n r t K L e).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) =
    Free.evaluate t (K ⊗ L) N.X
      (e.inv ≫ ((RightModuleFree.freeGenerator S (Free.object n K) ≫ f.hom) ⊗ₘ
        (RightModuleFree.freeGenerator S (Free.object r L) ≫ g.hom)) ≫ leftAction S N) := by
  have hEval := CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.hom_apply_generator
    S t (K ⊗ L) N ((Evaluation.ofIso S n r t K L e).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom)
  have hGenerator := Source.left_pair_generator S (Free.object n K) (Free.object r L)
    (Free.object t (K ⊗ L)) e N f g
  exact hEval.trans (congrArg
    (fun h : Free.object t (K ⊗ L) ⟶ N.X => Free.evaluate t (K ⊗ L) N.X h) hGenerator)

/-- The actual right-unit pair retains both original free coefficients and the whole target right action. -/
theorem right_pair (n r t : I) (K L : V)
    (e : Free.object n K ⊗ Free.object r L ≅ Free.object t (K ⊗ L))
    (N : RightModule S)
    (f : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K ⟶ N)
    (g : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S r).obj L ⟶ 𝟙_ (RightModule S)) :
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S t).homEquiv (K ⊗ L) N
      ((Evaluation.ofIso S n r t K L e).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom) =
    Free.evaluate t (K ⊗ L) N.X
      (e.inv ≫ ((RightModuleFree.freeGenerator S (Free.object n K) ≫ f.hom) ⊗ₘ
        (RightModuleFree.freeGenerator S (Free.object r L) ≫ g.hom)) ≫ N.action) := by
  have hEval := CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.hom_apply_generator
    S t (K ⊗ L) N ((Evaluation.ofIso S n r t K L e).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom)
  have hGenerator := Source.right_pair_generator S (Free.object n K) (Free.object r L)
    (Free.object t (K ⊗ L)) e N f g
  exact hEval.trans (congrArg
    (fun h : Free.object t (K ⊗ L) ⟶ N.X => Free.evaluate t (K ⊗ L) N.X h) hGenerator)

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.ModuleAdjunct


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.ModuleDayEvaluation
open PointedCGWH.Spectra.Orthogonal.SphereSmashFree
open CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [EnrichedCategory V I]
  [MonoidalCategory (EnrichedFunctorCat V I)] [SymmetricCategory (EnrichedFunctorCat V I)]
  (S : EnrichedFunctorCat V I) [MonObj S] [IsCommMonObj S]
  [HasCoequalizers (EnrichedFunctorCat V I)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : EnrichedFunctorCat V I, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  (T : EnrichedFunctor V (I × I) I)
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.relations T F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I), HasCoproduct (EnrichedDayKernel.objects T F G k)]
  [∀ (F G : EnrichedFunctor V I V) (k : I),
    HasCoequalizer (EnrichedDayKernel.leftMap T F G k) (EnrichedDayKernel.rightMap T F G k)]
  [∀ (F : EnrichedFunctorCat V (I × I)) (k : I),
    HasCoproduct (Enriched.weightedCoend.relations (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (I × I)) (k : I),
    HasCoproduct (Enriched.weightedCoend.objects (leftKanWeight T k) F.toEnrichedFunctor)]
  [∀ (F : EnrichedFunctorCat V (I × I)) (k : I),
    HasCoequalizer (Enriched.weightedCoend.leftMap (leftKanWeight T k) F.toEnrichedFunctor)
      (Enriched.weightedCoend.rightMap (leftKanWeight T k) F.toEnrichedFunctor)]
  (tensorComparison : tensor (EnrichedFunctorCat V I) ≅ EnrichedDayKernel.Input.bifunctor T)

/-- The right-module tensor used to evaluate the original free-source adjunction and
precomposition maps. -/
local instance : MonoidalCategory (RightModule S) := RightModuleFree.tensorMonoidal S

/-- The original source tensor comparison and both source free adjuncts give the complete left-unit evaluation. -/
theorem left_pair (n r : I) (K L : V) (N : RightModule S)
    (f : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K ⟶ 𝟙_ (RightModule S))
    (g : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S r).obj L ⟶ N) :
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S (T.obj (n, r))).homEquiv
      (K ⊗ L) N
      ((Evaluation.ofIso S n r (T.obj (n, r)) K L
        (tensorComparison.app (Free.object n K, Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso T n r K L)).inv ≫ (f ⊗ₘ g) ≫ (λ_ N).hom) =
    ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
        K (𝟙_ (RightModule S)) f ⊗ₘ
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S r).homEquiv L N g) ≫
      EnrichedDayKernel.Generators.point T S.toEnrichedFunctor N.X.toEnrichedFunctor (n, r) ≫
        component (tensorComparison.inv.app (S, N.X) ≫ leftAction S N) (T.obj (n, r)) := by
  let P := Free.object n K
  let Q := Free.object r L
  let fp : P ⟶ S := RightModuleFree.freeGenerator S P ≫ f.hom
  let gp : Q ⟶ N.X := RightModuleFree.freeGenerator S Q ≫ g.hom
  let e := tensorComparison.app (P, Q) ≪≫ EnrichedDayKernel.FreePairComparison.iso T n r K L
  have hFirst := ModuleAdjunct.left_pair S n r (T.obj (n, r)) K L e N f g
  have hn : tensorComparison.inv.app (P, Q) ≫ (fp ⊗ₘ gp) =
      (EnrichedDayKernel.Input.bifunctor T).map (X := (P, Q)) (Y := (S, N.X)) (fp, gp) ≫
        tensorComparison.inv.app (S, N.X) :=
    (tensorComparison.inv.naturality (X := (P, Q)) (Y := (S, N.X)) (fp, gp)).symm
  have hArrow : e.inv ≫ (fp ⊗ₘ gp) ≫ leftAction S N =
      (EnrichedDayKernel.FreePairComparison.iso T n r K L).inv ≫
        (EnrichedDayKernel.Input.bifunctor T).map (X := (P, Q)) (Y := (S, N.X)) (fp, gp) ≫
          (tensorComparison.inv.app (S, N.X) ≫ leftAction S N) := by
    change ((EnrichedDayKernel.FreePairComparison.iso T n r K L).inv ≫
      tensorComparison.inv.app (P, Q)) ≫ (fp ⊗ₘ gp) ≫ leftAction S N = _
    simp only [Category.assoc]
    rw [← Category.assoc (tensorComparison.inv.app (P, Q)) (fp ⊗ₘ gp) (leftAction S N), hn]
    simp only [Category.assoc]
  have hDay := BinaryEvaluation.pair_evaluate T n r K L S N.X N.X fp gp
    (tensorComparison.inv.app (S, N.X) ≫ leftAction S N)
  have hf : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
      K (𝟙_ (RightModule S)) f = Free.evaluate n K S fp :=
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.hom_apply_generator S n K
      (𝟙_ (RightModule S)) f
  have hg : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S r).homEquiv
      L N g = Free.evaluate r L N.X gp :=
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.hom_apply_generator S r L N g
  have hMap := congrArg (Free.evaluate (T.obj (n, r)) (K ⊗ L) N.X) hArrow
  have hLast := congrArg₂
    (fun (a : K ⟶ S.toEnrichedFunctor.obj n) (b : L ⟶ N.X.toEnrichedFunctor.obj r) =>
      (a ⊗ₘ b) ≫ EnrichedDayKernel.Generators.point T S.toEnrichedFunctor N.X.toEnrichedFunctor (n, r) ≫
        component (tensorComparison.inv.app (S, N.X) ≫ leftAction S N) (T.obj (n, r))) hf.symm hg.symm
  exact hFirst.trans (hMap.trans (hDay.trans hLast))


/-- Both full original coefficients and the actual source right unit determine the complete right-unit evaluation. -/
theorem right_pair (n r : I) (K L : V) (N : RightModule S)
    (f : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S n).obj K ⟶ N)
    (g : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free S r).obj L ⟶ 𝟙_ (RightModule S)) :
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S (T.obj (n, r))).homEquiv
      (K ⊗ L) N
      ((Evaluation.ofIso S n r (T.obj (n, r)) K L
        (tensorComparison.app (Free.object n K, Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso T n r K L)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ N).hom) =
    ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
        K N f ⊗ₘ
      (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S r).homEquiv L (𝟙_ (RightModule S)) g) ≫
      EnrichedDayKernel.Generators.point T N.X.toEnrichedFunctor S.toEnrichedFunctor (n, r) ≫
        component (tensorComparison.inv.app (N.X, S) ≫ N.action) (T.obj (n, r)) := by
  let P := Free.object n K
  let Q := Free.object r L
  let fp : P ⟶ N.X := RightModuleFree.freeGenerator S P ≫ f.hom
  let gp : Q ⟶ S := RightModuleFree.freeGenerator S Q ≫ g.hom
  let e := tensorComparison.app (P, Q) ≪≫ EnrichedDayKernel.FreePairComparison.iso T n r K L
  have hFirst := ModuleAdjunct.right_pair S n r (T.obj (n, r)) K L e N f g
  have hn : tensorComparison.inv.app (P, Q) ≫ (fp ⊗ₘ gp) =
      (EnrichedDayKernel.Input.bifunctor T).map (X := (P, Q)) (Y := (N.X, S)) (fp, gp) ≫
        tensorComparison.inv.app (N.X, S) :=
    (tensorComparison.inv.naturality (X := (P, Q)) (Y := (N.X, S)) (fp, gp)).symm
  have hArrow : e.inv ≫ (fp ⊗ₘ gp) ≫ N.action =
      (EnrichedDayKernel.FreePairComparison.iso T n r K L).inv ≫
        (EnrichedDayKernel.Input.bifunctor T).map (X := (P, Q)) (Y := (N.X, S)) (fp, gp) ≫
          (tensorComparison.inv.app (N.X, S) ≫ N.action) := by
    change ((EnrichedDayKernel.FreePairComparison.iso T n r K L).inv ≫
      tensorComparison.inv.app (P, Q)) ≫ (fp ⊗ₘ gp) ≫ N.action = _
    simp only [Category.assoc]
    rw [← Category.assoc (tensorComparison.inv.app (P, Q)) (fp ⊗ₘ gp) (N.action), hn]
    simp only [Category.assoc]
  have hDay := BinaryEvaluation.pair_evaluate T n r K L N.X S N.X fp gp
    (tensorComparison.inv.app (N.X, S) ≫ N.action)
  have hf : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S n).homEquiv
      K N f = Free.evaluate n K N.X fp :=
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.hom_apply_generator S n K N f
  have hg : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction S r).homEquiv
      L (𝟙_ (RightModule S)) g = Free.evaluate r L S gp :=
    CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.hom_apply_generator S r L (𝟙_ (RightModule S)) g
  have hMap := congrArg (Free.evaluate (T.obj (n, r)) (K ⊗ L) N.X) hArrow
  have hLast := congrArg₂
    (fun (a : K ⟶ N.X.toEnrichedFunctor.obj n) (b : L ⟶ S.toEnrichedFunctor.obj r) =>
      (a ⊗ₘ b) ≫ EnrichedDayKernel.Generators.point T N.X.toEnrichedFunctor S.toEnrichedFunctor (n, r) ≫
        component (tensorComparison.inv.app (N.X, S) ≫ N.action) (T.obj (n, r))) hf.symm hg.symm
  exact hFirst.trans (hMap.trans (hDay.trans hLast))

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.ModuleDayEvaluation


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.DayTensorBridge
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] (d : EnrichedMonoidalCategoryData V I)

/-- The original constructed Day tensor is the original binary input functor on every object and map. -/
def originalTensorComparison :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    tensor (EnrichedFunctorCat V I) ≅ EnrichedDayKernel.Input.bifunctor d.tensorEnrichedFunctor := by
  letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  exact eqToIso rfl

/-- Both complete original comparison components are the same original identity arrows. -/
theorem originalTensorComparison_components (F G : EnrichedFunctorCat V I) :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    (originalTensorComparison d).hom.app (F, G) = 𝟙 (F ⊗ G) ∧
      (originalTensorComparison d).inv.app (F, G) = 𝟙 (F ⊗ G) := by
  letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  constructor <;> rfl

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.DayTensorBridge


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.FreeAction
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A]

/-- The identity-evaluated free generator followed by any full enriched coefficient is that original coefficient. -/
theorem identity_coefficient (a b : A) (K L : V) (D : L ⟶ (a ⟶[V] b)) :
    (Free.evaluate a K (Free.object a K) (𝟙 (Free.object a K)) ⊗ₘ D) ≫
      MonoidalClosed.uncurry ((Free.object a K).toEnrichedFunctor.map a b) = K ◁ D := by
  let ev := Free.evaluate a K (Free.object a K) (𝟙 (Free.object a K))
  let H := a ⟶[V] b
  have h := Free.reconstruct_component a K (Free.object a K) (𝟙 (Free.object a K)) b
  rw [component_id] at h
  dsimp only [Free.extensionComponent] at h
  change 𝟙 (K ⊗ H) = (ev ⊗ₘ 𝟙 H) ≫
    MonoidalClosed.uncurry ((Free.object a K).toEnrichedFunctor.map a b) at h
  have ht : (K ◁ D) ≫ (ev ⊗ₘ 𝟙 H) = ev ⊗ₘ D := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
    change (ev ⊗ₘ (D ≫ 𝟙 (a ⟶[V] b))) = ev ⊗ₘ D
    rw [Category.comp_id]
  calc
    _ = ((K ◁ D) ≫ (ev ⊗ₘ 𝟙 H)) ≫
        MonoidalClosed.uncurry ((Free.object a K).toEnrichedFunctor.map a b) :=
      congrArg (fun z => z ≫ MonoidalClosed.uncurry ((Free.object a K).toEnrichedFunctor.map a b)) ht.symm
    _ = _ := by
      rw [Category.assoc, ← h, Category.comp_id]

variable {I : Type uI} [Category.{vI} I] [EnrichedOrdinaryCategory V I]

/-- Every coefficient in a free object retains the actual ordinary index action and enriched Hom composition. -/
theorem index_map (j : EnrichedFunctor V I A) (a : A) (K : V) {b c : I} (g : b ⟶ c) :
    ((restriction j).obj (Free.object a K)).toEnrichedFunctor.toOrdinaryFunctor.map g =
      (ρ_ (K ⊗ (a ⟶[V] j.obj b))).inv ≫
        (K ⊗ (a ⟶[V] j.obj b)) ◁ (eHomEquiv V g ≫ j.map b c) ≫
        (α_ K (a ⟶[V] j.obj b) (j.obj b ⟶[V] j.obj c)).hom ≫
        K ◁ eComp V a (j.obj b) (j.obj c) := by
  change (eHomEquiv V).symm
    (eHomEquiv V g ≫ j.map b c ≫ (Free.object a K).toEnrichedFunctor.map (j.obj b) (j.obj c)) = _
  rw [MonoidalClosed.enrichedOrdinaryCategorySelf_homEquiv_symm]
  dsimp only [MonoidalClosed.uncurry']
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_curry]
  simp only [Free.action, whiskerLeft_comp, Category.assoc]

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.FreeAction


namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeFreeAction

/-- On every original native free coefficient, the actual sphere action of its identity generator is the original nu. -/
theorem nu_identity (r n : ℕ) (K : PointedCGWH.{u, v}) :
    (Free.evaluate (OrthogonalOperatorIndex.ofIndex r) K
        (Free.object (OrthogonalOperatorIndex.ofIndex r) K) (𝟙 (Free.object (OrthogonalOperatorIndex.ofIndex r) K)) ▷
      PointedCGWH.orthogonalSphere n) ≫
      sphereAction (Free.object (OrthogonalOperatorIndex.ofIndex r) K) r n =
    K ◁ OrthogonalOperatorIndex.nu r n := by
  rw [sphereAction_original_nu, ← Category.assoc, ← tensorHom_def]
  exact FreeAction.identity_coefficient (OrthogonalOperatorIndex.ofIndex r)
    (OrthogonalOperatorIndex.ofIndex (r + n)) K (PointedCGWH.orthogonalSphere n)
    (OrthogonalOperatorIndex.nu r n)

/-- The full original left-ordered coefficient word retains its actual braid and original native nu. -/
theorem left_nu_identity (r n : ℕ) (K : PointedCGWH.{u, v}) :
    (PointedCGWH.orthogonalSphere n ◁
      Free.evaluate (OrthogonalOperatorIndex.ofIndex r) K
        (Free.object (OrthogonalOperatorIndex.ofIndex r) K) (𝟙 (Free.object (OrthogonalOperatorIndex.ofIndex r) K))) ≫
      (β_ (PointedCGWH.orthogonalSphere n)
        ((Free.object (OrthogonalOperatorIndex.ofIndex r) K).toEnrichedFunctor.obj
          (OrthogonalOperatorIndex.ofIndex r))).hom ≫
      sphereAction (Free.object (OrthogonalOperatorIndex.ofIndex r) K) r n =
    (β_ (PointedCGWH.orthogonalSphere n) K).hom ≫ (K ◁ OrthogonalOperatorIndex.nu r n) := by
  let ev := Free.evaluate (OrthogonalOperatorIndex.ofIndex r) K
    (Free.object (OrthogonalOperatorIndex.ofIndex r) K) (𝟙 (Free.object (OrthogonalOperatorIndex.ofIndex r) K))
  have h : (PointedCGWH.orthogonalSphere n ◁ ev) ≫
      (β_ (PointedCGWH.orthogonalSphere n)
        ((Free.object (OrthogonalOperatorIndex.ofIndex r) K).toEnrichedFunctor.obj
          (OrthogonalOperatorIndex.ofIndex r))).hom =
      (β_ (PointedCGWH.orthogonalSphere n) K).hom ≫ (ev ▷ PointedCGWH.orthogonalSphere n) := by
    simpa only [id_tensorHom, tensorHom_id] using
      braiding_naturality (𝟙 (PointedCGWH.orthogonalSphere n)) ev
  rw [← Category.assoc, h, Category.assoc]
  exact congrArg (fun f => (β_ (PointedCGWH.orthogonalSphere n) K).hom ≫ f) (nu_identity r n K)

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeFreeAction





set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.SelectedEvaluation
open PointedCGWH.Spectra.Orthogonal.SphereSmashFree
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V I)

/-- The selected free-pair adjunct with a unit target in its left factor equals the Day
left-action coefficient word. -/
def LeftReadback : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  ∀ (n r : I) (K L : V) (N : q.Module)
    (f : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient n).obj K ⟶ 𝟙_ q.Module)
    (g : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient r).obj L ⟶ N),
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient (n ⊗ r)).homEquiv
      (K ⊗ L) N ((Selected.sourcePair q n r K L).inv ≫
        (tensorHom
          (X₁ := (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient n).obj K)
          (Y₁ := 𝟙_ q.Module)
          (X₂ := (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient r).obj L)
          (Y₂ := N) f g) ≫ (λ_ N).hom) =
      ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient n).homEquiv
          K (𝟙_ q.Module) f ⊗ₘ
        (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient r).homEquiv L N g) ≫
        EnrichedDayKernel.Generators.point q.monoidalData.tensorEnrichedFunctor
          q.coefficient.toEnrichedFunctor N.X.toEnrichedFunctor (n, r) ≫
          component (leftAction q.coefficient N) (n ⊗ r)

theorem left_readback : LeftReadback q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.primitiveMonoidal
  intro n r K L N f g
  let T := q.monoidalData.tensorEnrichedFunctor
  let tc := DayTensorBridge.originalTensorComparison q.monoidalData
  have hApp : tc.app (Free.object n K, Free.object r L) =
      Iso.refl (Free.object n K ⊗ Free.object r L) := by
    apply Iso.ext
    exact (DayTensorBridge.originalTensorComparison_components q.monoidalData
      (Free.object n K) (Free.object r L)).1
  have hPair : tc.app (Free.object n K, Free.object r L) ≪≫
      EnrichedDayKernel.FreePairComparison.iso T n r K L = Selected.diagramPair q n r K L := by
    calc
      _ = Iso.refl (Free.object n K ⊗ Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso T n r K L :=
        congrArg (fun e => e ≪≫ EnrichedDayKernel.FreePairComparison.iso T n r K L) hApp
      _ = EnrichedDayKernel.FreePairComparison.iso T n r K L := Iso.refl_trans _
      _ = Selected.diagramPair q n r K L := rfl
  have hTarget := (DayTensorBridge.originalTensorComparison_components q.monoidalData q.coefficient N.X).2
  have h := ModuleDayEvaluation.left_pair q.coefficient T tc n r K L N f g
  have hAction : tc.inv.app (q.coefficient, N.X) ≫ leftAction q.coefficient N =
      leftAction q.coefficient N := by
    calc
      _ = 𝟙 (q.coefficient ⊗ N.X) ≫ leftAction q.coefficient N :=
        congrArg (fun k => k ≫ leftAction q.coefficient N) hTarget
      _ = leftAction q.coefficient N := Category.id_comp _
  rw [hPair, hAction] at h
  exact h

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.SelectedEvaluation



set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open scoped MonoidalClosed CategoryTheory.MonObj
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.SelectedEvaluationRight
open PointedCGWH.Spectra.Orthogonal.SphereSmashFree
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open CommutativeModuleConversion
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [SymmetricCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V] [HasProducts.{uI} V] [HasEqualizers V]
  (q : Enriched.ModuleMappingR.SelectedSource V I)

/-- The selected free-pair adjunct with a unit target in its right factor equals the Day
right-action coefficient word. -/
def RightReadback : Prop :=
  letI := q.dayMonoidal
  letI := q.daySymmetric
  letI := q.coefficientMonObj
  letI := q.coefficientIsComm
  letI := q.dayCoequalizers
  letI := q.dayTensorLeftPreserves
  letI := q.dayTensorRightPreserves
  letI := q.primitiveMonoidal
  ∀ (n r : I) (K L : V) (N : q.Module)
    (f : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient n).obj K ⟶ N)
    (g : (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient r).obj L ⟶ 𝟙_ q.Module),
    (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient (n ⊗ r)).homEquiv
      (K ⊗ L) N ((Selected.sourcePair q n r K L).inv ≫
        (tensorHom
          (X₁ := (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient n).obj K)
          (Y₁ := N)
          (X₂ := (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.free q.coefficient r).obj L)
          (Y₂ := 𝟙_ q.Module) f g) ≫ (ρ_ N).hom) =
      ((CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient n).homEquiv
          K N f ⊗ₘ
        (CategoryTheory.Enriched.RightModuleFreeEvaluation.Primitive.adjunction q.coefficient r).homEquiv L
          (𝟙_ q.Module) g) ≫
        EnrichedDayKernel.Generators.point q.monoidalData.tensorEnrichedFunctor
          N.X.toEnrichedFunctor q.coefficient.toEnrichedFunctor (n, r) ≫
          component (N.action) (n ⊗ r)

theorem right_readback : RightReadback q := by
  let := q.dayMonoidal
  let := q.daySymmetric
  let := q.coefficientMonObj
  let := q.coefficientIsComm
  let := q.dayCoequalizers
  let := q.dayTensorLeftPreserves
  let := q.dayTensorRightPreserves
  let := q.primitiveMonoidal
  intro n r K L N f g
  let T := q.monoidalData.tensorEnrichedFunctor
  let tc := DayTensorBridge.originalTensorComparison q.monoidalData
  have hApp : tc.app (Free.object n K, Free.object r L) =
      Iso.refl (Free.object n K ⊗ Free.object r L) := by
    apply Iso.ext
    exact (DayTensorBridge.originalTensorComparison_components q.monoidalData
      (Free.object n K) (Free.object r L)).1
  have hPair : tc.app (Free.object n K, Free.object r L) ≪≫
      EnrichedDayKernel.FreePairComparison.iso T n r K L = Selected.diagramPair q n r K L := by
    calc
      _ = Iso.refl (Free.object n K ⊗ Free.object r L) ≪≫
          EnrichedDayKernel.FreePairComparison.iso T n r K L :=
        congrArg (fun e => e ≪≫ EnrichedDayKernel.FreePairComparison.iso T n r K L) hApp
      _ = EnrichedDayKernel.FreePairComparison.iso T n r K L := Iso.refl_trans _
      _ = Selected.diagramPair q n r K L := rfl
  have hTarget := (DayTensorBridge.originalTensorComparison_components q.monoidalData N.X q.coefficient).2
  have h := ModuleDayEvaluation.right_pair q.coefficient T tc n r K L N f g
  have hAction : tc.inv.app (N.X, q.coefficient) ≫ N.action =
      N.action := by
    calc
      _ = 𝟙 (N.X ⊗ q.coefficient) ≫ N.action :=
        congrArg (fun k => k ≫ N.action) hTarget
      _ = N.action := Category.id_comp _
  rw [hPair, hAction] at h
  exact h

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.SelectedEvaluationRight



set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  MonoidalLeftAction.monoidalOppositeLeftAction Enriched.prodCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeSource

/-- The primitive tensor of native sphere modules selected by `SphereSmash.sourceData`. -/
@[instance_reducible]
def primitiveSourceMonoidal : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmash.sourceData.{u, v}.primitiveMonoidal

/-- The primitive sphere-module tensor transported to native orthogonal spectra by the source
equivalence. -/
@[instance_reducible]
def primitiveNativeMonoidal : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  letI := primitiveSourceMonoidal.{u, v}
  Monoidal.transport CanonicalSourceSmash.sourceEquivalence.{u, v}

theorem nativeMonoidal_eq_primitive :
    CanonicalSourceSmash.monoidalCategory.{u, v} = primitiveNativeMonoidal.{u, v} :=
  congrArg (fun M => @Monoidal.transport NativeSphereModule.Carrier.{u, v} _ M
    CanonicalSourceSmash.Carrier.{u, v} _ CanonicalSourceSmash.sourceEquivalence.{u, v})
      SphereSmash.sourceData.{u, v}.moduleMonoidal_eq_primitive

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeSource



set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization.LambdaUnitSource
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed
attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  MonoidalLeftAction.monoidalOppositeLeftAction Enriched.prodCategory PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.WordFactor

theorem three {C : Type uC} [Category.{vC} C] {A B D E T : C}
    (p : A ⟶ B) (q : B ⟶ D) (z : D ⟶ T) (a : D ⟶ E) (b : E ⟶ T)
    (h : z = a ≫ b) : p ≫ q ≫ z = (p ≫ q ≫ a) ≫ b := by
  calc
    _ = p ≫ q ≫ (a ≫ b) := congrArg (fun f => p ≫ q ≫ f) h
    _ = (p ≫ q) ≫ (a ≫ b) := (Category.assoc p q (a ≫ b)).symm
    _ = ((p ≫ q) ≫ a) ≫ b := (Category.assoc (p ≫ q) a b).symm
    _ = _ := congrArg (fun f => f ≫ b) (Category.assoc p q a)

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.WordFactor

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeUnit
/-- The selected sphere-module tensor used to compare the source unit with the native smash unit. -/
local instance : MonoidalCategory NativeSphereModule.Carrier.{u, v} :=
  SphereSmash.sourceData.{u, v}.moduleMonoidal
/-- The canonical source smash tensor on native orthogonal spectra. -/
local instance : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

theorem original_unit_inverse_factor :
    CanonicalSourceSmashUnit.unitIso.{u, v}.inv =
      CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv ≫
        CanonicalSourceSmash.sourceEquivalence.{u, v}.functor.map
          (CanonicalSourceSmashUnit.TypedSource.sourceUnitIso SphereSmash.sourceData.{u, v}).inv := by
  exact CanonicalSourceSmashUnit.unitIso_inv.{u, v}

theorem gamma_regular_factor (n : ℕ) :
    gamma.{u, v} n = RegularEvaluation.regularGamma.{u, v} n ≫
      CanonicalSourceSmash.sourceEquivalence.{u, v}.functor.map
        (CanonicalSourceSmashUnit.TypedSource.sourceUnitIso SphereSmash.sourceData.{u, v}).inv := by
  exact WordFactor.three (gammaSourceIso.{u, v} n).hom
    (HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.orthogonalStabilization.{u, v} 0 n)
    CanonicalSourceSmashUnit.unitIso.{u, v}.inv
    CanonicalSourceRightModuleFreeUnit.regularSphereNativeFreeIso.{u, v}.inv
    (CanonicalSourceSmash.sourceEquivalence.{u, v}.functor.map
      (CanonicalSourceSmashUnit.TypedSource.sourceUnitIso SphereSmash.sourceData.{u, v}).inv)
    original_unit_inverse_factor.{u, v}

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.NativeUnit
