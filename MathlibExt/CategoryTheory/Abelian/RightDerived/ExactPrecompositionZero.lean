/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.ExactPrecomposition
public import MathlibExt.CategoryTheory.Abelian.CoaugmentationCycles

/-!
# Coaugmentation classes and degree-zero source comparisons

For an additive functor between abelian categories and a coaugmentation
quasi-isomorphism `X[0] → K`, its degree-zero cycle class maps to the
canonical map from the original functor to its zeroth right-derived
functor. Consequently, for an additive homology-preserving source change
`U : C → D` and additive `L : D → A`, the directional comparison in
degree zero carries the original `L(U(X))` coaugmentation class to the
same class in `R⁰L(U(X))`.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

universe uC vC uD vD uA vA

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {A : Type uA} [Category.{vA} A] [Abelian A]

section AugmentedClass

variable [HasInjectiveResolutions C]

/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. For a coaugmentation quasi-isomorphism
`ι : X[0] → K`, its mapped cycle `F(X) → Z⁰(F(K))`, followed by the
homology quotient and `H⁰(F(K)) → R⁰F(X)`, equals the canonical
map `F(X) → R⁰F(X)`. -/
theorem augmentedResolutionToRightDerivedHom_coaugmentation
    (F : C ⥤ D) [F.Additive] {X : C} (K : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ K) [QuasiIso ι] :
    F.mappedCoaugmentationCycle K ι ≫
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ 0 ≫
          F.augmentedResolutionToRightDerivedHom K ι 0 = F.toRightDerivedZero.app X := by
  let I := injectiveResolution X
  let r := augmentedResolutionComparison K ι
  let KF := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let IF := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let a := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map r.val
  have hCycles : F.mappedCoaugmentationCycle K ι ≫ HomologicalComplex.cyclesMap a 0 =
      I.toRightDerivedZero' F := by
    apply (cancel_mono (IF.iCycles 0)).1
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
      mappedCoaugmentationCycle_i, InjectiveResolution.toRightDerivedZero'_comp_iCycles]
    change F.map (ι.f 0) ≫ F.map (r.val.f 0) = F.map (I.ι.f 0)
    exact (F.map_comp _ _).symm.trans
      (congrArg F.map ((HomologicalComplex.comp_f ι r.val 0).symm.trans
        (HomologicalComplex.congr_hom r.property 0)))
  have hπ : KF.homologyπ 0 ≫ HomologicalComplex.homologyMap a 0 =
      HomologicalComplex.cyclesMap a 0 ≫ IF.homologyπ 0 :=
    HomologicalComplex.homologyπ_naturality a 0
  change F.mappedCoaugmentationCycle K ι ≫ KF.homologyπ 0 ≫
      (HomologicalComplex.homologyMap a 0 ≫ (I.isoRightDerivedObj F 0).inv) = _
  calc
    _ = (F.mappedCoaugmentationCycle K ι ≫
        (KF.homologyπ 0 ≫ HomologicalComplex.homologyMap a 0)) ≫
          (I.isoRightDerivedObj F 0).inv := by simp only [Category.assoc]
    _ = (F.mappedCoaugmentationCycle K ι ≫
        (HomologicalComplex.cyclesMap a 0 ≫ IF.homologyπ 0)) ≫
          (I.isoRightDerivedObj F 0).inv := congrArg
            (fun f => (F.mappedCoaugmentationCycle K ι ≫ f) ≫
              (I.isoRightDerivedObj F 0).inv) hπ
    _ = I.toRightDerivedZero' F ≫ IF.homologyπ 0 ≫ (I.isoRightDerivedObj F 0).inv := by
      rw [← Category.assoc, hCycles]
      exact Category.assoc _ _ _
    _ = F.toRightDerivedZero.app X := (I.toRightDerivedZero_eq F).symm

end AugmentedClass

/-- Let `C,D,A` be abelian, `U : C → D`, `L : D → A` additive,
and `I` an injective resolution of `X`. The cycle of the coaugmentation
in `(U ⋙ L)(I)` becomes the cycle of the coaugmentation of `U(I)`
under the natural identification with `L(U(I))`. -/
theorem mapCochainCoaugmentation_cycles_composition
    (U : C ⥤ D) [U.Additive] (L : D ⥤ A) [L.Additive]
    {X : C} (I : InjectiveResolution X) :
    I.toRightDerivedZero' (U ⋙ L) ≫ HomologicalComplex.cyclesMap
        ((Functor.mapHomologicalComplexCompIso (F := U) (G := L)
          (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)).inv.app I.cocomplex) 0 =
      L.mappedCoaugmentationCycle
        ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
        (mapCochainCoaugmentation U I.ι) := by
  let K := (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj
    ((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  let a := (Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)).inv.app I.cocomplex
  have hi : HomologicalComplex.cyclesMap a 0 ≫ K.iCycles 0 =
      (((U ⋙ L).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles 0 ≫
        a.f 0 := HomologicalComplex.cyclesMap_i a 0
  apply (cancel_mono (K.iCycles 0)).1
  rw [Category.assoc, hi,
    ← Category.assoc, InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    mappedCoaugmentationCycle_i, mapCochainCoaugmentation_f_zero]
  change L.map (U.map (I.ι.f 0)) ≫ 𝟙 _ = L.map (U.map (I.ι.f 0))
  exact Category.comp_id _

section Directional

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology]
  (L : D ⥤ A) [L.Additive]

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`U : C → D` additive and preserving homology, and `L : D → A` additive.
The canonical map `U ⋙ L → R⁰(U ⋙ L)` followed by the directional
comparison equals the canonical map `U ⋙ L → U ⋙ R⁰L`. -/
@[reassoc]
theorem rightDerivedPrecompHomOfPreservesHomology_toRightDerivedZero :
    (U ⋙ L).toRightDerivedZero ≫ rightDerivedPrecompHomOfPreservesHomology U L 0 =
      whiskerLeft U L.toRightDerivedZero := by
  apply NatTrans.ext
  funext X
  let I := injectiveResolution X
  let K := ((U ⋙ L).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let Q := (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let T := (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj Q
  let ι := mapCochainCoaugmentation U I.ι
  let : QuasiIso ι := mapCochainCoaugmentation_quasiIso U I.ι
  let a := (Functor.mapHomologicalComplexCompIso (F := U) (G := L)
    (Iso.refl (U ⋙ L)) (ComplexShape.up ℕ)).inv.app I.cocomplex
  rw [NatTrans.comp_app, rightDerivedPrecompHomOfPreservesHomology_app U L 0 I,
    I.toRightDerivedZero_eq (U ⋙ L)]
  change (I.toRightDerivedZero' (U ⋙ L) ≫ K.homologyπ 0 ≫
      (I.isoRightDerivedObj (U ⋙ L) 0).inv) ≫
    ((I.isoRightDerivedObj (U ⋙ L) 0).hom ≫ HomologicalComplex.homologyMap a 0 ≫
      L.augmentedResolutionToRightDerivedHom Q ι 0) = L.toRightDerivedZero.app (U.obj X)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hπ := HomologicalComplex.homologyπ_naturality a 0
  rw [← Category.assoc (K.homologyπ 0), hπ]
  have hCycles : I.toRightDerivedZero' (U ⋙ L) ≫
      HomologicalComplex.cyclesMap a 0 = L.mappedCoaugmentationCycle Q ι :=
    mapCochainCoaugmentation_cycles_composition U L I
  calc
    _ = (I.toRightDerivedZero' (U ⋙ L) ≫ HomologicalComplex.cyclesMap a 0) ≫
        T.homologyπ 0 ≫ L.augmentedResolutionToRightDerivedHom Q ι 0 := by
      simp only [Category.assoc]
      rfl
    _ = L.mappedCoaugmentationCycle Q ι ≫ T.homologyπ 0 ≫
        L.augmentedResolutionToRightDerivedHom Q ι 0 :=
      congrArg (fun z => z ≫ T.homologyπ 0 ≫
        L.augmentedResolutionToRightDerivedHom Q ι 0) hCycles
    _ = _ := L.augmentedResolutionToRightDerivedHom_coaugmentation Q ι

end Directional

end CategoryTheory.Functor
