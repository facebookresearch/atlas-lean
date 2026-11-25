/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.ExactPrecompositionConnecting

/-!
# Composition of directional right-derived source comparisons

For abelian `C,D,E,A`, injective resolutions in `C,D,E`, additive
homology-preserving `U : C → D`, `V : D → E`, and additive `L : E → A`,
the comparison for `U ⋙ V` is the composite of the comparisons for `U`
and `V`, with the functor associators. Identity source change gives the
identity comparison. Mapped coaugmentations satisfy the corresponding
composition law.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits

attribute [local instance 100] Functor.preservesFiniteLimits_of_preservesHomology
  Functor.preservesFiniteColimits_of_preservesHomology

universe uC vC uD vD uE vE uA vA

namespace CategoryTheory.Functor

variable {C : Type uC} [Category.{vC} C] [Abelian C]
  {D : Type uD} [Category.{vD} D] [Abelian D]
  {E : Type uE} [Category.{vE} E] [Abelian E]
  {A : Type uA} [Category.{vA} A] [Abelian A]

/-- Let `C,D,E` be abelian and `U : C → D`, `V : D → E` additive.
For a coaugmentation `ι : X[0] → K`, mapping by `U ⋙ V` and then
identifying the mapped complex with `V(U(K))` gives the same
coaugmentation as mapping first by `U` and then by `V`. -/
theorem mapCochainCoaugmentation_comp
    (U : C ⥤ D) [U.Additive] (V : D ⥤ E) [V.Additive]
    {X : C} {K : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ K) :
    mapCochainCoaugmentation (U ⋙ V) ι ≫
        (Functor.mapHomologicalComplexCompIso (F := U) (G := V)
          (Iso.refl (U ⋙ V)) (ComplexShape.up ℕ)).inv.app K =
      mapCochainCoaugmentation V (mapCochainCoaugmentation U ι) := by
  apply CochainComplex.coaugmentation_comp_eq_of_f_zero
  rw [mapCochainCoaugmentation_f_zero, mapCochainCoaugmentation_f_zero,
    mapCochainCoaugmentation_f_zero]
  change V.map (U.map (ι.f 0)) ≫ 𝟙 _ = V.map (U.map (ι.f 0))
  exact Category.comp_id _

section Derived

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  [HasInjectiveResolutions E]
  (U : C ⥤ D) [U.Additive] [U.PreservesHomology]
  (V : D ⥤ E) [V.Additive] [V.PreservesHomology]
  (L : E ⥤ A) [L.Additive]

/-- Let `C,D,E,A` be abelian, with injective resolutions in `C,D,E`,
`U : C → D`, `V : D → E` additive and preserving homology, and
`L : E → A` additive. After the functor associators, the comparison
`R^n((U ⋙ V) ⋙ L) → (U ⋙ V) ⋙ R^nL` is the comparison for `U`
followed by the comparison for `V`. Neither `U` nor `V` needs to
preserve injective objects. -/
theorem rightDerivedPrecompHomOfPreservesHomology_comp (n : ℕ) :
    NatTrans.rightDerived (Functor.associator U V L).hom n ≫
        rightDerivedPrecompHomOfPreservesHomology U (V ⋙ L) n ≫
          whiskerLeft U (rightDerivedPrecompHomOfPreservesHomology V L n) ≫
            (Functor.associator U V (L.rightDerived n)).inv =
      rightDerivedPrecompHomOfPreservesHomology (U ⋙ V) L n := by
  apply NatTrans.ext
  funext X
  let I := injectiveResolution X
  let K := (U.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let T := ((U ⋙ V).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let T' := (V.mapHomologicalComplex (ComplexShape.up ℕ)).obj K
  let ι := mapCochainCoaugmentation U I.ι
  let κ := mapCochainCoaugmentation (U ⋙ V) I.ι
  let κ' := mapCochainCoaugmentation V ι
  let : QuasiIso ι := mapCochainCoaugmentation_quasiIso U I.ι
  let : QuasiIso κ := mapCochainCoaugmentation_quasiIso (U ⋙ V) I.ι
  let : QuasiIso κ' := mapCochainCoaugmentation_quasiIso V ι
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n
  let e := Functor.associator U V L
  let θ := (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℕ)).app I.cocomplex
  let a := (Functor.mapHomologicalComplexCompIso (F := U) (G := V ⋙ L)
    (Iso.refl (U ⋙ (V ⋙ L))) (ComplexShape.up ℕ)).inv.app I.cocomplex
  let b := (Functor.mapHomologicalComplexCompIso (F := V) (G := L)
    (Iso.refl (V ⋙ L)) (ComplexShape.up ℕ)).inv.app K
  let c := (Functor.mapHomologicalComplexCompIso (F := U ⋙ V) (G := L)
    (Iso.refl ((U ⋙ V) ⋙ L)) (ComplexShape.up ℕ)).inv.app I.cocomplex
  let d := (Functor.mapHomologicalComplexCompIso (F := U) (G := V)
    (Iso.refl (U ⋙ V)) (ComplexShape.up ℕ)).inv.app I.cocomplex
  let q := L.augmentedResolutionToRightDerivedHom T κ n
  let q' := L.augmentedResolutionToRightDerivedHom T' κ' n
  let qK := (V ⋙ L).augmentedResolutionToRightDerivedHom K ι n
  have hAssoc := I.isoRightDerivedObj_hom_naturality_functor e.hom n
  change (NatTrans.rightDerived e.hom n).app X ≫
      (I.isoRightDerivedObj (U ⋙ (V ⋙ L)) n).hom =
    (I.isoRightDerivedObj ((U ⋙ V) ⋙ L) n).hom ≫ H.map θ at hAssoc
  have hK : qK ≫ (rightDerivedPrecompHomOfPreservesHomology V L n).app (U.obj X) =
      H.map b ≫ q' := augmentedResolutionToRightDerivedHom_precomp V L K ι n
  have hCoaug : κ ≫ d = κ' := mapCochainCoaugmentation_comp U V I.ι
  have hQ := L.augmentedResolutionToRightDerivedHom_naturality κ κ'
    (𝟙 ((U ⋙ V).obj X)) d (by simpa only [Functor.map_id, Category.id_comp] using hCoaug) n
  have hQ' : H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map d) ≫ q' = q := by
    simpa only [q, q', H, HomologicalComplex.homologyFunctor_map,
      Functor.map_id, Category.comp_id] using hQ
  have hMaps : θ ≫ a ≫ b = c ≫ (L.mapHomologicalComplex (ComplexShape.up ℕ)).map d := by
    apply HomologicalComplex.hom_ext
    intro i
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ L.map (𝟙 _)
    rw [L.map_id]
    simp only [Category.id_comp]
  have hHomology : H.map θ ≫ H.map a ≫ H.map b =
      H.map c ≫ H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map d) := by
    rw [← H.map_comp, ← H.map_comp, hMaps, H.map_comp]
  rw [NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    rightDerivedPrecompHomOfPreservesHomology_app U (V ⋙ L) n I,
    rightDerivedPrecompHomOfPreservesHomology_app (U ⋙ V) L n I]
  change (NatTrans.rightDerived e.hom n).app X ≫
      ((I.isoRightDerivedObj (U ⋙ (V ⋙ L)) n).hom ≫ H.map a ≫ qK) ≫
        (rightDerivedPrecompHomOfPreservesHomology V L n).app (U.obj X) ≫ 𝟙 _ =
    (I.isoRightDerivedObj ((U ⋙ V) ⋙ L) n).hom ≫ H.map c ≫ q
  simp only [Category.comp_id]
  calc
    _ = ((NatTrans.rightDerived e.hom n).app X ≫
        (I.isoRightDerivedObj (U ⋙ (V ⋙ L)) n).hom) ≫ H.map a ≫
          (qK ≫ (rightDerivedPrecompHomOfPreservesHomology V L n).app (U.obj X)) := by
      simp only [Category.assoc]
    _ = ((I.isoRightDerivedObj ((U ⋙ V) ⋙ L) n).hom ≫ H.map θ) ≫ H.map a ≫
        (H.map b ≫ q') := congrArg₂ (fun f g => f ≫ H.map a ≫ g) hAssoc hK
    _ = (I.isoRightDerivedObj ((U ⋙ V) ⋙ L) n).hom ≫
        (H.map θ ≫ H.map a ≫ H.map b) ≫ q' := by
      simp only [Category.assoc]
    _ = (I.isoRightDerivedObj ((U ⋙ V) ⋙ L) n).hom ≫
        (H.map c ≫ H.map ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map d)) ≫ q' :=
      congrArg (fun f => (I.isoRightDerivedObj ((U ⋙ V) ⋙ L) n).hom ≫ f ≫ q') hHomology
    _ = (I.isoRightDerivedObj ((U ⋙ V) ⋙ L) n).hom ≫ H.map c ≫ q := by
      simp only [Category.assoc]
      rw [hQ']

end Derived

section Identity

variable [HasInjectiveResolutions C]

/-- Let `C,A` be abelian, with injective resolutions in `C`, and
`L : C → A` additive. The directional right-derived comparison for
the identity functor of `C` is `𝟙 (R^nL)` in every degree `n`. -/
theorem rightDerivedPrecompHomOfPreservesHomology_id (L : C ⥤ A) [L.Additive] (n : ℕ) :
    rightDerivedPrecompHomOfPreservesHomology (𝟭 C) L n = 𝟙 (L.rightDerived n) := by
  let γ := rightDerivedPrecompHomOfPreservesHomology (𝟭 C) L n
  have hAssoc : (Functor.associator (𝟭 C) (𝟭 C) L).hom = 𝟙 L := by
    apply NatTrans.ext
    funext X
    rfl
  have h := rightDerivedPrecompHomOfPreservesHomology_comp (𝟭 C) (𝟭 C) L n
  have hId : NatTrans.rightDerived (𝟙 L) n = 𝟙 (L.rightDerived n) :=
    NatTrans.rightDerived_id L n
  rw [hAssoc] at h
  have h' := congrArg (fun z => z ≫
    rightDerivedPrecompHomOfPreservesHomology (𝟭 C) ((𝟭 C) ⋙ L) n ≫
      whiskerLeft (𝟭 C) γ ≫ (Functor.associator (𝟭 C) (𝟭 C) (L.rightDerived n)).inv) hId
  have h := h'.symm.trans h
  change 𝟙 _ ≫ γ ≫ γ ≫ 𝟙 _ = γ at h
  simp only [Category.id_comp, Category.comp_id] at h
  have : IsIso γ := by
    change IsIso (rightDerivedPrecompHomOfPreservesHomology (𝟭 C) L n)
    rw [rightDerivedPrecompHomOfPreservesHomology_eq_hom]
    infer_instance
  apply (cancel_epi γ).1
  exact h.trans (Category.comp_id γ).symm

end Identity

end CategoryTheory.Functor
