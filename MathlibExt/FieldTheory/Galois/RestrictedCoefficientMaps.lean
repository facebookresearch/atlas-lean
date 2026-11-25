/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact
public import MathlibExt.FieldTheory.Galois.UnitsContinuousModule

/-!
Original Profinite group/coefficient maps through the existing discrete restriction provider,
with one actual coefficient arrow for every degree.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace ContinuousCohomology

open CategoryTheory CategoryTheory.Limits
universe a b r

variable {G : ProfiniteGrp.{a}} {H : ProfiniteGrp.{b}}

/-- The genuine restriction representation has literal identity coefficient map. -/
def restrictionTopRepHom (φ : H →ₜ* G)
    (A : DiscreteAbelianAction.{a, max a (max b r)} G) :
    TopRep.res (φ : H →* G) (inhomogeneousOriginalTopRep.{0, a, max b r} G A) ⟶
      inhomogeneousOriginalTopRep.{0, b, max a r} H
        ((GaloisUnits.restrictModules.{a, b, max a (max b r)} φ).obj A) :=
  𝟙 _


-- The exact generic statement reached 200000 in retained v1.
/-- The original coefficient arrow after actual restriction acts through the
same original group/cochain map and the literal stored coefficient map. -/
theorem mappedGroupCoefficient_factorization (n : ℕ) (φ : H →ₜ* G)
    (A : DiscreteAbelianAction.{a, max a (max b r)} G)
    (B : DiscreteAbelianAction.{b, max b (max a r)} H)
    (f : (GaloisUnits.restrictModules.{a, b, max a (max b r)} φ).obj A ⟶ B) :
    discreteCoefficientForget.{max a (max b r)}.map
        (nativeGroupCoefficientCohomologyMap.{0, a, b, r} φ
          ((discreteCoefficientTopRepFunctor.{b, max a r} H).map f) n) =
      discreteCoefficientForget.{max a (max b r)}.map
        (nativeGroupCoefficientCohomologyMap.{0, a, b, r} φ
          (restrictionTopRepHom.{a, b, r} φ A) n) ≫
      (discreteCoefficientCohomologyFunctor.{b, max a r} H n).map f := by
  let P := discreteCoefficientTopRepFunctor.{a, max b r} G
  let Q := discreteCoefficientTopRepFunctor.{b, max a r} H
  let R := GaloisUnits.restrictModules.{a, b, max a (max b r)} φ
  have ha : (TopRep.resFunctor (φ : H →* G)).map (P.map (𝟙 A)) = 𝟙 _ :=
    (congrArg (TopRep.resFunctor (φ : H →* G)).map (P.map_id A)).trans
      ((TopRep.resFunctor (φ : H →* G)).map_id _)
  have hψ : (𝟙 _ : TopRep.res (φ : H →* G) (P.obj A) ⟶ Q.obj (R.obj A)) ≫ Q.map f =
      (TopRep.resFunctor (φ : H →* G)).map (P.map (𝟙 A)) ≫ Q.map f :=
    (Category.id_comp _).trans
      ((congrArg (· ≫ Q.map f) ha).trans (Category.id_comp _)).symm
  have h := discreteCoefficientGroupCohomologySquare.{a, b, r}
    (A₁ := A) (A₂ := A) (B₁ := R.obj A) (B₂ := B)
    φ (𝟙 A) f (restrictionTopRepHom.{a, b, r} φ A) (Q.map f) hψ n
  let f' : TopRep.res (φ : H →* G) (P.obj A) ⟶ Q.obj B := Q.map f
  let μ : (discreteCoefficientCohomologyFunctor.{a, max b r} G n).obj A ⟶
      (discreteCoefficientCohomologyFunctor.{b, max a r} H n).obj B :=
    discreteCoefficientForget.{max a (max b r)}.map
      (nativeGroupCoefficientCohomologyMap.{0, a, b, r}
        (X := P.obj A) (Y := Q.obj B) φ f' n)
  have hi := (discreteCoefficientCohomologyFunctor.{a, max b r} G n).map_id A
  exact ((congrArg (· ≫ μ) hi).trans (Category.id_comp μ)).symm.trans h

end ContinuousCohomology

namespace ContinuousCohomology

open CategoryTheory CategoryTheory.Limits
universe a b r
variable {G : ProfiniteGrp.{a}} {H : ProfiniteGrp.{b}}

/-- Every original intertwiner is represented by the actual full discrete-module
functor after restriction, with no linear or equivariant section premise. -/
theorem originalCoefficient_factorization_all (φ : H →ₜ* G)
    (A : DiscreteAbelianAction.{a, max a (max b r)} G)
    (B : DiscreteAbelianAction.{b, max b (max a r)} H)
    (f : TopRep.res (φ : H →* G) (inhomogeneousOriginalTopRep.{0, a, max b r} G A) ⟶
      inhomogeneousOriginalTopRep.{0, b, max a r} H B) :
    ∃ g : (GaloisUnits.restrictModules.{a, b, max a (max b r)} φ).obj A ⟶ B,
      (discreteCoefficientTopRepFunctor.{b, max a r} H).map g = f ∧
      ∀ n, discreteCoefficientForget.{max a (max b r)}.map
          (nativeGroupCoefficientCohomologyMap.{0, a, b, r} φ f n) =
        discreteCoefficientForget.{max a (max b r)}.map
          (nativeGroupCoefficientCohomologyMap.{0, a, b, r} φ
            (restrictionTopRepHom.{a, b, r} φ A) n) ≫
          (discreteCoefficientCohomologyFunctor.{b, max a r} H n).map g := by
  let R := GaloisUnits.restrictModules.{a, b, max a (max b r)} φ
  let Q := discreteCoefficientTopRepFunctor.{b, max a r} H
  let U := TopRep.fromActionTopModFunc.{max a (max b r), 0, b} (k := ℤ) (G := H)
  let f' : U.obj (R.obj A).obj.obj ⟶ U.obj B.obj.obj := f
  let g : R.obj A ⟶ B := ObjectProperty.homMk (ObjectProperty.homMk (U.preimage f'))
  have hg : Q.map g = f := by
    change U.map (U.preimage f') = f'
    exact Functor.map_preimage U f'
  refine ⟨g, hg, ?_⟩
  intro n
  let χ : (TopRep.res (φ : H →* G) (inhomogeneousOriginalTopRep.{0, a, max b r} G A) ⟶
      inhomogeneousOriginalTopRep.{0, b, max a r} H B) →
      ((discreteCoefficientCohomologyFunctor.{a, max b r} G n).obj A ⟶
        (discreteCoefficientCohomologyFunctor.{b, max a r} H n).obj B) :=
    fun t => discreteCoefficientForget.{max a (max b r)}.map
      (nativeGroupCoefficientCohomologyMap.{0, a, b, r} φ t n)
  exact (congrArg χ hg).symm.trans
    (mappedGroupCoefficient_factorization.{a, b, r} n φ A B g)

end ContinuousCohomology
