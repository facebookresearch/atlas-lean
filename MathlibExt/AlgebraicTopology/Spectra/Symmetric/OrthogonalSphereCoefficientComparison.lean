/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.TensorPowerPermutationFunctor
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.DimensionPermutation
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereMultiplication
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OrthogonalRestriction
import MathlibExt.Topology.Category.PointedCGWH.NativeCopowerCoefficient

/-!
# The original symmetric and restricted orthogonal sphere coefficients

The original ordered circle-to-representation-sphere comparison retains
all finite permutation matrices and the complete native enriched Hom
maps. Its actual component maps form an enriched functor isomorphism
whose unit and ordered multiplication equations are the original ones.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower
open CategoryTheory.MonoidalCategory.SymmetricTensorPower
open CategoryTheory.MonoidalCategory.TensorPower.PermutationFunctorCompatibility

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory OrthogonalIndex.category
  OrthogonalIndex.monoidalCategory OrthogonalIndex.enrichedOrdinaryCategory
  OrthogonalIndex.symmetricCategory

universe u v

/-- The original ordered representation splitting retains every actual finite coordinate action. -/
theorem originalOrthogonalSpherePowerIso_permutation {m n : ℕ} (e : Fin m ≃ Fin n) :
    orthogonalSphereMap.{u, v} (OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix e)) ≫
      (originalOrthogonalSpherePowerIso.{u, v} n).hom =
    (originalOrthogonalSpherePowerIso.{u, v} m).hom ≫
      (permutationIso (PointedCGWH.orthogonalSphere.{u, v} 1) e).hom := by
  let _ := originalOrthogonalSphereBraided.{u, v}
  let G := originalOrthogonalSphereOrdinary.{u, v}
  let dm := orthogonalDimensionPower.{v, u} m
  let dn := orthogonalDimensionPower.{v, u} n
  let cm : G.obj m ⟶ G.obj (tensorPowObj (1 : OrthogonalIndex) m) :=
    eqToHom (congrArg G.obj dm.symm)
  let cn : G.obj n ⟶ G.obj (tensorPowObj (1 : OrthogonalIndex) n) :=
    eqToHom (congrArg G.obj dn.symm)
  let pm := (mapTensorPowObjIso G (1 : OrthogonalIndex) m).hom
  let pn := (mapTensorPowObjIso G (1 : OrthogonalIndex) n).hom
  have hPower := mapTensorPowObjIso_permutation
    G (1 : OrthogonalIndex) e
  have hDimension := originalDimensionPower_permutation.{u, v} e
  have hRaw : dimensionMatrixPoint.{u, v} e ≫ eqToHom dn.symm =
      eqToHom dm.symm ≫ (permutationIso (1 : OrthogonalIndex) e).hom := by
    apply (cancel_mono (eqToHom dn)).1
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rw [hDimension, ← Category.assoc, eqToHom_trans]
    simp
  have hMapped := congrArg G.map hRaw
  have hMatrix : G.map (dimensionMatrixPoint.{u, v} e) ≫ cn =
      cm ≫ G.map (permutationIso (1 : OrthogonalIndex) e).hom := by
    simpa only [G.map_comp, eqToHom_map, cm, cn] using hMapped
  have hm : cm ≫ pm = (originalOrthogonalSpherePowerIso.{u, v} m).hom :=
    congrArg Iso.hom (originalSphereMonoidalPowerIso_eq.{u, v} m)
  have hn : cn ≫ pn = (originalOrthogonalSpherePowerIso.{u, v} n).hom :=
    congrArg Iso.hom (originalSphereMonoidalPowerIso_eq.{u, v} n)
  have hWhole : G.map (dimensionMatrixPoint.{u, v} e) ≫ (cn ≫ pn) =
      (cm ≫ pm) ≫ (permutationIso (G.obj 1) e).hom := by
    calc
      _ = (G.map (dimensionMatrixPoint.{u, v} e) ≫ cn) ≫ pn :=
        (Category.assoc _ _ _).symm
      _ = (cm ≫ G.map (permutationIso (1 : OrthogonalIndex) e).hom) ≫ pn :=
        congrArg (fun z => z ≫ pn) hMatrix
      _ = cm ≫ (G.map (permutationIso (1 : OrthogonalIndex) e).hom ≫ pn) :=
        Category.assoc _ _ _
      _ = cm ≫ pm ≫ (permutationIso (G.obj 1) e).hom :=
        congrArg (fun z => cm ≫ z) hPower
      _ = _ := (Category.assoc _ _ _).symm
  rw [hm, hn] at hWhole
  exact hWhole

/-- The original circle smash powers compare naturally with the actual
coordinate sphere action. -/
theorem originalSpherePowerComparisonIso_permutation {m n : ℕ} (e : Fin m ≃ Fin n) :
    (permutationIso PointedCGWH.sphereOne.{u, v} e).hom ≫
      (originalSpherePowerComparisonIso.{u, v} n).hom =
    (originalSpherePowerComparisonIso.{u, v} m).hom ≫
      orthogonalSphereMap.{u, v}
        (OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix e)) := by
  let seed := orthogonalOneSphereIsoSphereOne.{u, v}.inv
  have hSeed := permutationIso_hom_naturality seed e
  have hOrth := originalOrthogonalSpherePowerIso_permutation.{u, v} e
  apply (cancel_mono (originalOrthogonalSpherePowerIso.{u, v} n).hom).1
  have hm : (originalSpherePowerComparisonIso.{u, v} m).hom =
      tensorPowMap seed m ≫ (originalOrthogonalSpherePowerIso.{u, v} m).inv := rfl
  have hn : (originalSpherePowerComparisonIso.{u, v} n).hom =
      tensorPowMap seed n ≫ (originalOrthogonalSpherePowerIso.{u, v} n).inv := rfl
  rw [hm, hn]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hOrth, Iso.inv_hom_id_assoc]
  exact hSeed.symm

end CategoryTheory.Spectra


namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf


universe u v

/-- The unchanged symmetric sphere coefficient on the full native finite-bijection index. -/
abbrev OriginalSymmetricSphere :
    EnrichedFunctorCat PointedCGWH.{u, v}
      (PointedCGWH.CopowerIndex.{u, v, 0} Operad.SmallFinBijGroupoid) :=
  ⟨PointedCGWH.sphereCopowerEnrichedFunctor.{u, v}⟩

/-- The actual orthogonal representation-sphere coefficient restricted
along permutation matrices. -/
abbrev RestrictedOrthogonalSphere :
    EnrichedFunctorCat PointedCGWH.{u, v}
      (PointedCGWH.CopowerIndex.{u, v, 0} Operad.SmallFinBijGroupoid) :=
  (EnrichedFunctorCat.restriction symmetricOrthogonalIndexFunctor.{u, v}).obj
    ⟨orthogonalSphereFunctor.{u, v}⟩

/-- Every original permutation is retained by the original full coefficient comparison. -/
theorem originalSymmetricOrthogonalCoefficientIso_naturality
    {A B : Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    PointedCGWH.sphereSequence.{u, v}.functor.map f ≫
      (originalSymmetricOrthogonalCoefficientIso.{u, v} B).hom =
    (originalSymmetricOrthogonalCoefficientIso.{u, v} A).hom ≫
      orthogonalSphereMap.{u, v} (OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix f)) :=
  originalSpherePowerComparisonIso_permutation.{u, v} (smallFiniteBijection f)

private def coefficientOrdinaryIso :
    PointedCGWH.sphereSequence.{u, v}.functor ≅
      PointedCGWH.restrictCopowerDiagram.{u, v, 0} RestrictedOrthogonalSphere.{u, v} :=
  NatIso.ofComponents (originalSymmetricOrthogonalCoefficientIso.{u, v}) (by
    intro A B f
    have hRestriction :
        (PointedCGWH.restrictCopowerDiagram.{u, v, 0}
          RestrictedOrthogonalSphere.{u, v}).map f =
        orthogonalSphereMap.{u, v}
          (OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix f)) := by
      have h := symmetricOrthogonalRestriction_generator
        (⟨orthogonalSphereFunctor.{u, v}⟩ :
          EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) f
      exact congrArg (eHomEquiv PointedCGWH.{u, v}).symm h
    rw [hRestriction]
    exact originalSymmetricOrthogonalCoefficientIso_naturality f)

/-- The complete native Hom-object square holds before the functor isomorphism is assembled. -/
theorem originalSymmetricOrthogonalCoefficientIso_fullNaturality
    (A B : Operad.SmallFinBijGroupoid) :
    MonoidalClosed.uncurry
      (OriginalSymmetricSphere.{u, v}.toEnrichedFunctor.map
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A)
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B)) ≫
      (originalSymmetricOrthogonalCoefficientIso.{u, v} B).hom =
    ((originalSymmetricOrthogonalCoefficientIso.{u, v} A).hom ⊗ₘ
      𝟙 (PointedCGWH.basedDiscreteObj.{u, v, 0} (A ⟶ B))) ≫
    MonoidalClosed.uncurry
      (RestrictedOrthogonalSphere.{u, v}.toEnrichedFunctor.map
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A)
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B)) := by
  have h := PointedCGWH.enrichOriginalDiagram_uncurried_naturality.{u, v, 0}
    coefficientOrdinaryIso.{u, v}.hom A B
  rw [← PointedCGWH.enrich_restrictCopowerDiagram_map.{u, v, 0}
    RestrictedOrthogonalSphere.{u, v} A B]
  exact h

/-- The full original symmetric sphere coefficient agrees with restriction of the Orth sphere. -/
def originalSymmetricOrthogonalCoefficientNatIso :
    OriginalSymmetricSphere.{u, v} ≅ RestrictedOrthogonalSphere.{u, v} :=
  (PointedCGWH.enrichOriginalDiagramFunctor.{u, v, 0}).mapIso
    coefficientOrdinaryIso.{u, v} ≪≫
      PointedCGWH.copowerDiagramCounitIso.{u, v, 0} RestrictedOrthogonalSphere.{u, v}

/-- The actual forward component is the original ordered sphere comparison. -/
theorem originalSymmetricOrthogonalCoefficientNatIso_hom_component
    (A : Operad.SmallFinBijGroupoid) :
    EnrichedFunctorCat.component originalSymmetricOrthogonalCoefficientNatIso.{u, v}.hom
      (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A) =
      (originalSymmetricOrthogonalCoefficientIso.{u, v} A).hom := by
  change EnrichedFunctorCat.component
    (PointedCGWH.enrichOriginalDiagramMap.{u, v, 0} coefficientOrdinaryIso.{u, v}.hom ≫
      (PointedCGWH.copowerDiagramCounitIso.{u, v, 0} RestrictedOrthogonalSphere.{u, v}).hom)
    (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A) = _
  rw [EnrichedFunctorCat.component_comp, PointedCGWH.enrichOriginalDiagramMap_component,
    PointedCGWH.copowerDiagramCounitIso_hom_component]
  exact Category.comp_id _

/-- The actual inverse component is the original inverse ordered sphere comparison. -/
theorem originalSymmetricOrthogonalCoefficientNatIso_inv_component
    (A : Operad.SmallFinBijGroupoid) :
    EnrichedFunctorCat.component originalSymmetricOrthogonalCoefficientNatIso.{u, v}.inv
      (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A) =
      (originalSymmetricOrthogonalCoefficientIso.{u, v} A).inv := by
  apply (cancel_mono (originalSymmetricOrthogonalCoefficientIso.{u, v} A).hom).1
  have h := congrArg
    (fun f => EnrichedFunctorCat.component f
      (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A))
    originalSymmetricOrthogonalCoefficientNatIso.{u, v}.inv_hom_id
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_id,
    originalSymmetricOrthogonalCoefficientNatIso_hom_component] at h
  exact h.trans (originalSymmetricOrthogonalCoefficientIso.{u, v} A).inv_hom_id.symm

end CategoryTheory.Spectra


namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory OrthogonalIndex.category
  OrthogonalIndex.monoidalCategory OrthogonalIndex.enrichedOrdinaryCategory
  OrthogonalIndex.symmetricCategory
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  MonoidalClosed.enrichedCategorySelf MonoidalClosed.enrichedOrdinaryCategorySelf

universe u v

/-- The same full coefficient comparison retains the literal original sphere unit. -/
theorem originalSymmetricOrthogonalCoefficientNatIso_unit :
    PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon ≫
      EnrichedFunctorCat.component originalSymmetricOrthogonalCoefficientNatIso.{u, v}.hom
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid
          (𝟙_ Operad.SmallFinBijGroupoid)) =
      orthogonalSphereMonoidalData.{u, v}.epsilon := by
  rw [originalSymmetricOrthogonalCoefficientNatIso_hom_component]
  have hSym : PointedCGWH.sphereCopowerLaxData.{u, v}.epsilon =
      𝟙 (𝟙_ PointedCGWH.{u, v}) := rfl
  have hComp := congrArg (fun z : 𝟙_ PointedCGWH.{u, v} ⟶ 𝟙_ PointedCGWH.{u, v} =>
    z ≫ (originalSpherePowerComparisonIso.{u, v} 0).hom) hSym
  exact hComp.trans ((Category.id_comp _).trans
    (originalSpherePowerComparisonIso_zero.trans orthogonalSphereMonoidalData_epsilon.symm))

/-- The same full coefficient comparison retains the original ordered sphere multiplication. -/
theorem originalSymmetricOrthogonalCoefficientNatIso_tensor
    (A B : Operad.SmallFinBijGroupoid) :
    PointedCGWH.sphereCopowerLaxData.{u, v}.mu
      ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj A)
      ((PointedCGWH.copowerRestriction.{u, v, 0} Operad.SmallFinBijGroupoid).obj B) ≫
      EnrichedFunctorCat.component originalSymmetricOrthogonalCoefficientNatIso.{u, v}.hom
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid (A ⊗ B)) =
    (EnrichedFunctorCat.component originalSymmetricOrthogonalCoefficientNatIso.{u, v}.hom
      (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A) ⊗ₘ
      EnrichedFunctorCat.component originalSymmetricOrthogonalCoefficientNatIso.{u, v}.hom
      (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B)) ≫
      orthogonalSphereMonoidalData.{u, v}.mu A.of.len B.of.len := by
  rw [originalSymmetricOrthogonalCoefficientNatIso_hom_component,
    originalSymmetricOrthogonalCoefficientNatIso_hom_component,
    originalSymmetricOrthogonalCoefficientNatIso_hom_component,
    orthogonalSphereMonoidalData_mu]
  exact originalSpherePowerComparisonIso_multiplication A.of.len B.of.len

end CategoryTheory.Spectra
