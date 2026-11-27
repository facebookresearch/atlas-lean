/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.CategoryCohomology.RoosUniversal
public import MathlibExt.CategoryTheory.CategoryCohomology.RoosLimitZero
public import MathlibExt.CategoryTheory.Limits.Shapes.DiscreteCofreeEnoughInjectives
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.CommSq

/-!
# Roos cohomology and right-derived limits

For an abelian coefficient category with sized exact products, assume injective
resolutions in the diagram category. The universal Roos δ-functor is then
isomorphic to the right-derived limit δ-functor. The degree-zero component is
normalized by the limit comparison, and the higher components commute with
coefficient maps and connecting morphisms.

Enough injectives in the coefficient category supply the diagram-resolution
hypothesis through cofree presentations. The comparison uses the full
weak-chain Roos complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.CategoryCohomology

variable {I : Type u₁} [Category.{v₁} I]
  {A : Type u₂} [Category.{v₂} A] [Abelian A] [HasProducts.{max u₁ v₁} A]

local instance : HasLimitsOfShape I A := by
  let : HasLimitsOfSize.{max u₁ v₁, max u₁ v₁} A :=
    has_limits_of_hasEqualizers_and_products
  let : HasLimitsOfSize.{v₁, u₁} A := hasLimitsOfSizeShrink A
  infer_instance

local notation "Γ" => lim (J := I) (C := A)

local instance : Functor.PreservesZeroMorphisms Γ := inferInstance
local instance : Functor.Additive Γ := Functor.additive_of_preserves_binary_products Γ

variable [HasInjectiveResolutions (I ⥤ A)]

variable [AB4StarOfSize.{max u₁ v₁} A]

local notation "R" => roosCohomologicalDeltaFunctor (I := I) (A := A)
local notation "D" => Functor.rightDerivedDeltaFunctor Γ

private def nativeDerivedDegreeIso (n : ℕ) : (D).T n ≅ Functor.rightDerived Γ n :=
  eqToIso (Functor.rightDerivedDeltaFunctor_T Γ n)

private def roosDerivedZeroIso : (R).T 0 ≅ (D).T 0 :=
  roosDeltaFunctorHomologyIso (I := I) (A := A) 0 ≪≫
    roosHomologyZeroNatIso (I := I) (A := A) ≪≫
      (Functor.rightDerivedZeroIsoSelf Γ).symm ≪≫
      (nativeDerivedDegreeIso (I := I) (A := A) 0).symm

/-- Compare the Roos and derived-limit δ-functors through degree zero. -/
@[no_expose]
def roosRightDerivedDeltaFunctorIso : R ≅ D :=
  CohomologicalDeltaFunctor.isoOfZeroIso (I ⥤ A) A R D
    (roosCohomologicalDeltaFunctor_isUniversal (I := I) (A := A))
    (Functor.isUniversal_rightDerivedDeltaFunctor Γ)
    (roosDerivedZeroIso (I := I) (A := A))

/-- The given Nat Roos homology is naturally the right-derived limit. -/
@[no_expose]
def roosHomologyRightDerivedIso (n : ℕ) :
    (roosComplexFunctor ⋙ HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n) ≅
      Functor.rightDerived Γ n :=
  (roosDeltaFunctorHomologyIso (I := I) (A := A) n).symm ≪≫
    ((CohomologicalDeltaFunctor.evaluation (I ⥤ A) A n).mapIso
        (roosRightDerivedDeltaFunctorIso (I := I) (A := A)) ≪≫
      nativeDerivedDegreeIso (I := I) (A := A) n)

/-- Degree zero is normalized by the H0-to-limit and R0-to-limit comparisons. -/
theorem roosHomologyRightDerivedIso_zero :
    (roosHomologyRightDerivedIso (I := I) (A := A) 0).hom ≫
        (Functor.rightDerivedZeroIsoSelf Γ).hom =
      (roosHomologyZeroNatIso (I := I) (A := A)).hom := by
  have h : CohomologicalDeltaFunctor.Hom.app
      (roosRightDerivedDeltaFunctorIso (I := I) (A := A)).hom 0 =
      (roosDerivedZeroIso (I := I) (A := A)).hom :=
    CohomologicalDeltaFunctor.isoOfZeroIso_hom_app_zero (I ⥤ A) A R D
      (roosCohomologicalDeltaFunctor_isUniversal (I := I) (A := A))
      (Functor.isUniversal_rightDerivedDeltaFunctor Γ)
      (roosDerivedZeroIso (I := I) (A := A))
  unfold roosHomologyRightDerivedIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  dsimp only [CohomologicalDeltaFunctor.evaluation]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  change (roosDeltaFunctorHomologyIso (I := I) (A := A) 0).inv ≫
      CohomologicalDeltaFunctor.Hom.app
        (roosRightDerivedDeltaFunctorIso (I := I) (A := A)).hom 0 ≫
      (nativeDerivedDegreeIso (I := I) (A := A) 0).hom ≫
      (Functor.rightDerivedZeroIsoSelf Γ).hom = _
  rw [h]
  simp only [roosDerivedZeroIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The coefficient square uses Roos homology maps and higher maps. -/
theorem roosHomologyRightDerivedIso_hom_naturality (n : ℕ) {M N : I ⥤ A} (α : M ⟶ N) :
    HomologicalComplex.homologyMap ((roosComplexFunctor (I := I) (A := A)).map α) n ≫
        (roosHomologyRightDerivedIso (I := I) (A := A) n).hom.app N =
      (roosHomologyRightDerivedIso (I := I) (A := A) n).hom.app M ≫
        (Functor.rightDerived Γ n).map α :=
  (roosHomologyRightDerivedIso (I := I) (A := A) n).hom.naturality α

/-- Nat Roos and derived-limit connecting maps commute under the comparison. -/
theorem roosHomologyRightDerivedIso_connecting (n : ℕ)
    (S : ShortComplex.ShortExactSequences (I ⥤ A)) :
    (roosComplexFunctor_map_shortExact S.obj S.property).δ n (n + 1) (by rfl) ≫
        (roosHomologyRightDerivedIso (I := I) (A := A) (n + 1)).hom.app S.obj.X₁ =
      (roosHomologyRightDerivedIso (I := I) (A := A) n).hom.app S.obj.X₃ ≫
        RightDerivedDelta.RDdelta Γ n S.obj S.property
          (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃) := by
  let r₀ := (roosDeltaFunctorHomologyIso (I := I) (A := A) n).app S.obj.X₃
  let r₁ := (roosDeltaFunctorHomologyIso (I := I) (A := A) (n + 1)).app S.obj.X₁
  let s₀ := (nativeDerivedDegreeIso (I := I) (A := A) n).app S.obj.X₃
  let s₁ := (nativeDerivedDegreeIso (I := I) (A := A) (n + 1)).app S.obj.X₁
  let δN := (roosComplexFunctor_map_shortExact S.obj S.property).δ n (n + 1) (by rfl)
  let δR := ((R).connecting n).app S
  let δD := ((D).connecting n).app S
  let δΓ := RightDerivedDelta.RDdelta Γ n S.obj S.property
    (injectiveResolution S.obj.X₁) (injectiveResolution S.obj.X₃)
  let a₀ := (CohomologicalDeltaFunctor.Hom.app
    (roosRightDerivedDeltaFunctorIso (I := I) (A := A)).hom n).app S.obj.X₃
  let a₁ := (CohomologicalDeltaFunctor.Hom.app
    (roosRightDerivedDeltaFunctorIso (I := I) (A := A)).hom (n + 1)).app S.obj.X₁
  have p : CommSq r₀.hom δR δN r₁.hom :=
    ⟨roosCohomologicalDeltaFunctor_connecting_app n S⟩
  have pA : CommSq r₀.inv δN δR r₁.inv :=
    CommSq.horiz_inv (f := r₀) (i := r₁) p
  have h := DeltaFunctor.System.comm
    (roosRightDerivedDeltaFunctorIso (I := I) (A := A)).hom.hom n S
  change δR ≫ a₁ = a₀ ≫ δD at h
  have pB : CommSq a₀ δR δD a₁ := ⟨h.symm⟩
  have pC : CommSq s₀.hom δD δΓ s₁.hom := by
    constructor
    dsimp only [s₀, s₁, nativeDerivedDegreeIso]
    change 𝟙 _ ≫ δΓ = δD ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact (Functor.rightDerivedDeltaFunctor_connecting_app Γ n S).symm
  change δN ≫ (r₁.inv ≫ (a₁ ≫ s₁.hom)) = (r₀.inv ≫ (a₀ ≫ s₀.hom)) ≫ δΓ
  exact (pA.horiz_comp (pB.horiz_comp pC)).w.symm

end CategoryTheory.CategoryCohomology

end
