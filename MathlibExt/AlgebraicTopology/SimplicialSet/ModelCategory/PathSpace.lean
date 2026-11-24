/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Path spaces for simplicial sets

For a simplicial set `X`, the path space is the internal hom from `Δ[1]`:
`pathSpace X := (ihom Δ[1]).obj X`.  Its points are maps `Δ[1] ⊗ Δ[n] → X`,
i.e. paths in `X`.  The constant path map and the two endpoint evaluations
are obtained from the unique map `Δ[1] → Δ[0]` and the two vertex inclusions
`Δ[0] → Δ[1]`; all three maps are natural in `X`.  For a Kan complex `X`, the
path space is again a Kan complex and the endpoint evaluations are Kan
fibrations, as a direct consequence of the pushout-product / pullback-hom
adjunction for anodyne extensions.
-/

universe u

open CategoryTheory MonoidalCategory Simplicial SSet HomotopicalAlgebra Limits
open SSet.modelCategoryQuillen

namespace SSet

/-- Auxiliary iso `Δ[0] ≅ 𝟙_ SSet`. -/
public abbrev Δ0IsoUnit : (Δ[0] : SSet.{u}) ≅ (𝟙_ SSet.{u}) :=
  stdSimplex.isTerminalObj₀.uniqueUpToIso
    CartesianMonoidalCategory.isTerminalTensorUnit

/-- The path space of a simplicial set, defined as the internal hom from `Δ[1]`.

For `X : SSet`, `pathSpace X` has `n`-simplices `Hom(Δ[1] ⊗ Δ[n], X)`. -/
public abbrev pathSpace (X : SSet.{u}) : SSet.{u} :=
  (ihom (Δ[1] : SSet.{u})).obj X

/-- The constant path inclusion `X ⟶ pathSpace X`.

It is the currying of the second projection `Δ[1] ⊗ X ⟶ X`. -/
public noncomputable def constPath (X : SSet.{u}) : X ⟶ pathSpace (X := X) :=
  MonoidalClosed.curry (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X)

/-- The uncurried constant-path inclusion is the second projection. -/
public lemma uncurry_constPath (X : SSet.{u}) :
    MonoidalClosed.uncurry (constPath X) =
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X := by
  unfold constPath
  rw [MonoidalClosed.uncurry_curry]

/-- Evaluation at the 0-vertex `0 : Δ[0] ⟶ Δ[1]`. -/
public noncomputable def eval₀ {X : SSet.{u}} : pathSpace (X := X) ⟶ X :=
  (MonoidalClosed.pre (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1])).app X ≫
    (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
      (MonoidalClosed.unitIsoSelf (X := X)).hom

/-- Evaluation at the 1-vertex `1 : Δ[0] ⟶ Δ[1]`. -/
public noncomputable def eval₁ {X : SSet.{u}} : pathSpace (X := X) ⟶ X :=
  (MonoidalClosed.pre (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])).app X ≫
    (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
      (MonoidalClosed.unitIsoSelf (X := X)).hom

/-- Currying a map out of `𝟙_ SSet ⊗ A` and then applying the unit
internal-hom isomorphism is the left unitor followed by the original
map. -/
public lemma curry_unitIsoSelf {A B : SSet.{u}}
    (g : (𝟙_ SSet.{u}) ⊗ A ⟶ B) :
    MonoidalClosed.curry g ≫ (MonoidalClosed.unitIsoSelf (X := B)).hom =
      (λ_ A).inv ≫ g := by
  let f : A ⟶ B := (λ_ A).inv ≫ g
  let e := MonoidalClosed.unitNatIso (C := SSet.{u})
  calc
    MonoidalClosed.curry g ≫ (MonoidalClosed.unitIsoSelf (X := B)).hom =
        (e.hom.app A ≫ (ihom (𝟙_ SSet.{u})).map f) ≫ e.inv.app B := by
          dsimp only [f, e, MonoidalClosed.unitIsoSelf]
          rw [show g = (λ_ A).hom ≫ ((λ_ A).inv ≫ g) by simp,
            MonoidalClosed.curry_natural_right]
          rfl
    _ = e.hom.app A ≫
        ((ihom (𝟙_ SSet.{u})).map f ≫ e.inv.app B) := by
          rw [Category.assoc]
    _ = e.hom.app A ≫ (e.inv.app A ≫ f) := by
          rw [e.inv.naturality]
          simp only [Functor.id_map]
    _ = f := by simp
    _ = (λ_ A).inv ≫ g := rfl

/-- Composing an internal path with evaluation at its initial endpoint is
restriction of its uncurried map along the initial vertex. -/
public lemma comp_eval₀_eq_ι₀_braiding_uncurry
    {A B : SSet.{u}} (f : A ⟶ pathSpace B) :
    f ≫ (eval₀ : pathSpace B ⟶ B) =
      SSet.ι₀ ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry f := by
  with_unfolding_all dsimp only [eval₀]
  rw [← MonoidalClosed.curry_uncurry f]
  rw [MonoidalClosed.curry_pre_app_assoc,
    MonoidalClosed.curry_pre_app_assoc]
  rw [curry_unitIsoSelf]
  change (SSet.ι₀ ≫ (β_ A (Δ[1] : SSet.{u})).hom) ≫
      MonoidalClosed.uncurry f = _
  rw [MonoidalClosed.uncurry_curry, Category.assoc]

/-- Composing an internal path with evaluation at its final endpoint is
restriction of its uncurried map along the final vertex. -/
public lemma comp_eval₁_eq_ι₁_braiding_uncurry
    {A B : SSet.{u}} (f : A ⟶ pathSpace B) :
    f ≫ (eval₁ : pathSpace B ⟶ B) =
      SSet.ι₁ ≫ (β_ A (Δ[1] : SSet.{u})).hom ≫
        MonoidalClosed.uncurry f := by
  with_unfolding_all dsimp only [eval₁]
  rw [← MonoidalClosed.curry_uncurry f]
  rw [MonoidalClosed.curry_pre_app_assoc,
    MonoidalClosed.curry_pre_app_assoc]
  rw [curry_unitIsoSelf]
  change (SSet.ι₁ ≫ (β_ A (Δ[1] : SSet.{u})).hom) ≫
      MonoidalClosed.uncurry f = _
  rw [MonoidalClosed.uncurry_curry, Category.assoc]

/-- Evaluation at the initial vertex is natural under maps of simplicial
sets. -/
@[reassoc]
public lemma pathSpace_map_eval₀ {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{u})).map f ≫
        (eval₀ : pathSpace Y ⟶ Y) =
      (eval₀ : pathSpace X ⟶ X) ≫ f := by
  unfold eval₀
  simp only [Category.assoc]
  rw [NatTrans.naturality_assoc, NatTrans.naturality_assoc]
  slice_lhs 3 4 =>
    exact MonoidalClosed.unitNatIso.inv.naturality f
  simp only [MonoidalClosed.unitIsoSelf, Functor.id_map]
  rfl

/-- Evaluation at the final vertex is natural under maps of simplicial
sets. -/
@[reassoc]
public lemma pathSpace_map_eval₁ {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom (Δ[1] : SSet.{u})).map f ≫
        (eval₁ : pathSpace Y ⟶ Y) =
      (eval₁ : pathSpace X ⟶ X) ≫ f := by
  unfold eval₁
  simp only [Category.assoc]
  rw [NatTrans.naturality_assoc, NatTrans.naturality_assoc]
  slice_lhs 3 4 =>
    exact MonoidalClosed.unitNatIso.inv.naturality f
  simp only [MonoidalClosed.unitIsoSelf, Functor.id_map]
  rfl

/-- The constant-path inclusion is natural under maps of simplicial sets. -/
@[reassoc]
public lemma constPath_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ constPath Y =
      constPath X ≫ (ihom (Δ[1] : SSet.{u})).map f := by
  unfold constPath
  rw [← MonoidalClosed.curry_natural_left,
    ← MonoidalClosed.curry_natural_right]
  congr 1

/-- The combined endpoint map `pathSpace X ⟶ X ⊗ X` (equivalently `X × X`).

It is the pairing of the two endpoint evaluations, using the cartesian
monoidal structure (`X ⊗ X` is the categorical product). -/
public noncomputable def evalPair {X : SSet.{u}} : pathSpace (X := X) ⟶ X ⊗ X :=
  CartesianMonoidalCategory.lift (eval₀ (X := X)) (eval₁ (X := X))

@[reassoc (attr := simp)]
public lemma evalPair_fst {X : SSet.{u}} :
    evalPair (X := X) ≫ CartesianMonoidalCategory.fst X X = eval₀ := by
  simp [evalPair]

@[reassoc (attr := simp)]
public lemma evalPair_snd {X : SSet.{u}} :
    evalPair (X := X) ≫ CartesianMonoidalCategory.snd X X = eval₁ := by
  simp [evalPair]

private lemma boundaryOneBicart :
    Subcomplex.BicartSq (⊥ : (Δ[1] : SSet.{u}).Subcomplex)
      (stdSimplex.face ({1}ᶜ : Finset (Fin 2)))
      (stdSimplex.face ({0}ᶜ : Finset (Fin 2))) (boundary 1) := by
  constructor
  · calc
      stdSimplex.face (({1}ᶜ : Finset (Fin 2))) ⊔
          stdSimplex.face (({0}ᶜ : Finset (Fin 2))) =
        stdSimplex.face (({0}ᶜ : Finset (Fin 2))) ⊔
          stdSimplex.face (({1}ᶜ : Finset (Fin 2))) := sup_comm _ _
      _ = ⨆ i : Fin 2, stdSimplex.face (({i}ᶜ : Finset (Fin 2))) := by
        apply le_antisymm
        · exact sup_le
            (le_iSup (f := fun i : Fin 2 =>
              stdSimplex.face (({i}ᶜ : Finset (Fin 2)))) 0)
            (le_iSup (f := fun i : Fin 2 =>
              stdSimplex.face (({i}ᶜ : Finset (Fin 2)))) 1)
        · apply iSup_le
          intro i
          fin_cases i
          · exact le_sup_left
          · exact le_sup_right
      _ = boundary 1 := (boundary_eq_iSup (n := 1)).symm
  · rw [stdSimplex.face_inter_face]
    have h : (({1}ᶜ : Finset (Fin 2)) ⊓ {0}ᶜ : Finset (Fin 2)) = ∅ := by decide
    rw [h]
    exact stdSimplex.face_empty 1

public noncomputable def boundaryOneCofanIsColimit :
    IsColimit (BinaryCofan.mk (boundary.ι (1 : Fin 2)) (boundary.ι (0 : Fin 2))) := by
  have hPush := boundaryOneBicart.{u}.isPushout
  have hPush' : IsPushout
      ((Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).to (Δ[0] : SSet.{u}))
      ((Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).to (Δ[0] : SSet.{u}))
      (boundary.ι (1 : Fin 2)) (boundary.ι (0 : Fin 2)) := by
    fapply hPush.of_iso' (Iso.refl (((⊥ : (Δ[1] : SSet.{u}).Subcomplex) : SSet)))
      (stdSimplex.faceSingletonComplIso (1 : Fin 2))
      (stdSimplex.faceSingletonComplIso (0 : Fin 2)) (Iso.refl _)
    · apply (Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).hom_ext
    · apply (Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))).hom_ext
    · change (stdSimplex.faceSingletonComplIso (1 : Fin 2)).hom ≫
          boundary.faceι 1 = boundary.ι 1
      rw [← boundary.faceSingletonComplIso_inv_ι, Iso.hom_inv_id_assoc]
    · change (stdSimplex.faceSingletonComplIso (0 : Fin 2)).hom ≫
          boundary.faceι 0 = boundary.ι 0
      rw [← boundary.faceSingletonComplIso_inv_ι, Iso.hom_inv_id_assoc]
  exact isCoproductOfIsInitialIsPushout _ _ _ _
    (Subcomplex.isInitialBot (X := (Δ[1] : SSet.{u}))) hPush'.isColimit

public noncomputable def boundaryOneTensorCofanIsColimit (Y : SSet.{u}) :
    IsColimit (BinaryCofan.mk (boundary.ι (1 : Fin 2) ▷ Y)
      (boundary.ι (0 : Fin 2) ▷ Y)) :=
  mapIsColimitOfPreservesOfIsColimit (tensorRight Y) _ _ boundaryOneCofanIsColimit

public noncomputable def boundaryOneTensorDesc {Y Z : SSet.{u}}
    (f₀ f₁ : Δ[0] ⊗ Y ⟶ Z) : (boundary 1 : SSet.{u}) ⊗ Y ⟶ Z :=
  BinaryCofan.IsColimit.desc (boundaryOneTensorCofanIsColimit Y) f₀ f₁

@[reassoc (attr := simp)]
private lemma boundary_ι_one_whiskerRight_desc {Y Z : SSet.{u}}
    (f₀ f₁ : Δ[0] ⊗ Y ⟶ Z) :
    (boundary.ι (1 : Fin 2) ▷ Y) ≫ boundaryOneTensorDesc f₀ f₁ = f₀ :=
  BinaryCofan.IsColimit.inl_desc (boundaryOneTensorCofanIsColimit Y) _ _

@[reassoc (attr := simp)]
private lemma boundary_ι_zero_whiskerRight_desc {Y Z : SSet.{u}}
    (f₀ f₁ : Δ[0] ⊗ Y ⟶ Z) :
    (boundary.ι (0 : Fin 2) ▷ Y) ≫ boundaryOneTensorDesc f₀ f₁ = f₁ :=
  BinaryCofan.IsColimit.inr_desc (boundaryOneTensorCofanIsColimit Y) _ _

private noncomputable def ihomZeroPreIso (X : SSet.{u}) :
    (ihom (Δ[0] : SSet.{u})).obj X ≅ (ihom (𝟙_ SSet.{u})).obj X where
  hom := (MonoidalClosed.pre Δ0IsoUnit.inv).app X
  inv := (MonoidalClosed.pre Δ0IsoUnit.hom).app X
  hom_inv_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.hom_inv_id,
      MonoidalClosed.pre_id, NatTrans.id_app]
  inv_hom_id := by
    rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.inv_hom_id,
      MonoidalClosed.pre_id, NatTrans.id_app]

private noncomputable def ihomZeroPreNatIso :
    ihom (Δ[0] : SSet.{u}) ≅ ihom (𝟙_ SSet.{u}) :=
  NatIso.ofComponents (fun X ↦ ihomZeroPreIso X)
    (fun f ↦ (MonoidalClosed.pre Δ0IsoUnit.inv).naturality f)

private noncomputable def ihomZeroNatIso :
    ihom (Δ[0] : SSet.{u}) ≅ 𝟭 SSet.{u} :=
  ihomZeroPreNatIso ≪≫ MonoidalClosed.unitNatIso.symm

/-- Evaluation at `Δ[0]`: the canonical isomorphism
`(ihom Δ[0]).obj X ≅ X`. -/
public noncomputable def ihomZeroIso (X : SSet.{u}) :
    (ihom (Δ[0] : SSet.{u})).obj X ≅ X :=
  ihomZeroNatIso.app X

public lemma ihomZeroIso_hom (X : SSet.{u}) :
    (ihomZeroIso X).hom =
      (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
        (MonoidalClosed.unitIsoSelf (X := X)).hom := by
  simp [ihomZeroIso, ihomZeroNatIso, ihomZeroPreNatIso, ihomZeroPreIso,
    MonoidalClosed.unitIsoSelf]

/-- `eval₀` is the pullback-hom at the `0`-vertex inclusion followed by
the `ihom Δ[0] ≅ id` isomorphism. (Exposed unfolding for downstream
`I.rlp` transport, which cannot unfold `eval₀` across modules.) -/
public theorem eval₀_eq_pre_app (X : SSet.{u}) :
    eval₀ (X := X) =
      (MonoidalClosed.pre (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1])).app X ≫
        (ihomZeroIso X).hom := by
  unfold eval₀
  rw [← ihomZeroIso_hom]

/-- The tensor-to-product comparison preserves the first projection. -/
public lemma tensorLeftIsoProd_hom_fst (X Y : SSet.{u}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app Y ≫
        Limits.prod.fst =
      CartesianMonoidalCategory.fst X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.left⟩

/-- The tensor-to-product comparison preserves the second projection. -/
public lemma tensorLeftIsoProd_hom_snd (X Y : SSet.{u}) :
    (CartesianMonoidalCategory.tensorLeftIsoProd X).hom.app Y ≫
        Limits.prod.snd =
      CartesianMonoidalCategory.snd X Y :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct X Y)
    (limit.isLimit _) ⟨WalkingPair.right⟩

private lemma snd_unit_unitIsoSelf_hom (X : SSet.{u}) :
    CartesianMonoidalCategory.snd (𝟙_ SSet.{u})
      ((ihom (𝟙_ SSet.{u})).obj X) ≫
        (MonoidalClosed.unitIsoSelf (X := X)).hom =
      (ihom.ev (𝟙_ SSet.{u})).app X := by
  rfl

private lemma snd_ihomZeroIso_hom (X : SSet.{u}) :
    CartesianMonoidalCategory.snd (Δ[0] : SSet.{u})
      ((ihom (Δ[0] : SSet.{u})).obj X) ≫ (ihomZeroIso X).hom =
    (ihom.ev (Δ[0] : SSet.{u})).app X := by
  let H := (ihom (Δ[0] : SSet.{u})).obj X
  let H₁ := (ihom (𝟙_ SSet.{u})).obj X
  have hunit : Δ0IsoUnit.hom =
      CartesianMonoidalCategory.toUnit (Δ[0] : SSet.{u}) :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  have hsnd : CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) H =
      (Δ0IsoUnit.hom ▷ H) ≫
        CartesianMonoidalCategory.snd (𝟙_ SSet.{u}) H := by
    rw [hunit]
    exact (CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom
      (Δ[0] : SSet.{u}) H).symm.trans (by
        rw [CartesianMonoidalCategory.leftUnitor_hom])
  change CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) H ≫
      (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
        (MonoidalClosed.unitIsoSelf (X := X)).hom = _
  rw [hsnd]
  simp only [Category.assoc]
  rw [← CartesianMonoidalCategory.whiskerLeft_snd_assoc,
    snd_unit_unitIsoSelf_hom,
    MonoidalClosed.id_tensor_pre_app_comp_ev]
  change (Δ0IsoUnit.hom ▷ H) ≫ (Δ0IsoUnit.inv ▷ H) ≫
      (ihom.ev (Δ[0] : SSet.{u})).app X = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, Iso.hom_inv_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

private lemma curry_snd_eq_ihomZeroIso_inv (X : SSet.{u}) :
    MonoidalClosed.curry
      (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X) =
        (ihomZeroIso X).inv := by
  change MonoidalClosed.curry
      (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X) =
    (MonoidalClosed.unitIsoSelf (X := X)).inv ≫
      (MonoidalClosed.pre Δ0IsoUnit.hom).app X
  have h₃ : MonoidalClosed.curry
      (CartesianMonoidalCategory.snd (𝟙_ SSet.{u}) X) =
      (MonoidalClosed.unitIsoSelf (X := X)).inv := rfl
  rw [← h₃, MonoidalClosed.curry_pre_app]
  congr 1

private lemma curry_snd_comp {X Y : SSet.{u}} (f : X ⟶ Y) :
    MonoidalClosed.curry
      (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X ≫ f) =
        f ≫ (ihomZeroIso Y).inv := by
  rw [MonoidalClosed.curry_natural_right, curry_snd_eq_ihomZeroIso_inv]
  exact (ihomZeroNatIso.inv.naturality f).symm

public noncomputable def boundaryOneIhomIso (X : SSet.{u}) :
    (ihom (boundary 1 : SSet.{u})).obj X ≅ X ⊗ X where
  hom := CartesianMonoidalCategory.lift
    ((MonoidalClosed.pre (boundary.ι (1 : Fin 2))).app X ≫ (ihomZeroIso X).hom)
    ((MonoidalClosed.pre (boundary.ι (0 : Fin 2))).app X ≫ (ihomZeroIso X).hom)
  inv := MonoidalClosed.curry (boundaryOneTensorDesc
    (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) (X ⊗ X) ≫
      CartesianMonoidalCategory.fst X X)
    (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) (X ⊗ X) ≫
      CartesianMonoidalCategory.snd X X))
  hom_inv_id := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
    apply BinaryCofan.IsColimit.hom_ext
      (boundaryOneTensorCofanIsColimit ((ihom (boundary 1 : SSet.{u})).obj X))
    · change (boundary.ι (1 : Fin 2) ▷ _) ≫
          (boundary 1 : SSet.{u}) ◁ _ ≫ _ =
        (boundary.ι (1 : Fin 2) ▷ _) ≫ MonoidalClosed.uncurry (𝟙 _)
      rw [← MonoidalCategory.whisker_exchange_assoc,
        boundary_ι_one_whiskerRight_desc]
      rw [CartesianMonoidalCategory.whiskerLeft_snd_assoc,
        CartesianMonoidalCategory.lift_fst]
      rw [← CartesianMonoidalCategory.whiskerLeft_snd_assoc,
        snd_ihomZeroIso_hom, MonoidalClosed.id_tensor_pre_app_comp_ev,
        MonoidalClosed.uncurry_id_eq_ev]
    · change (boundary.ι (0 : Fin 2) ▷ _) ≫
          (boundary 1 : SSet.{u}) ◁ _ ≫ _ =
        (boundary.ι (0 : Fin 2) ▷ _) ≫ MonoidalClosed.uncurry (𝟙 _)
      rw [← MonoidalCategory.whisker_exchange_assoc,
        boundary_ι_zero_whiskerRight_desc]
      rw [CartesianMonoidalCategory.whiskerLeft_snd_assoc,
        CartesianMonoidalCategory.lift_snd]
      rw [← CartesianMonoidalCategory.whiskerLeft_snd_assoc,
        snd_ihomZeroIso_hom, MonoidalClosed.id_tensor_pre_app_comp_ev,
        MonoidalClosed.uncurry_id_eq_ev]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · change MonoidalClosed.curry (boundaryOneTensorDesc
          (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) (X ⊗ X) ≫
            CartesianMonoidalCategory.fst X X)
          (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) (X ⊗ X) ≫
            CartesianMonoidalCategory.snd X X)) ≫
          (MonoidalClosed.pre (boundary.ι (1 : Fin 2))).app X ≫
            (ihomZeroIso X).hom = CartesianMonoidalCategory.fst X X
      rw [MonoidalClosed.curry_pre_app_assoc,
        boundary_ι_one_whiskerRight_desc]
      rw [← cancel_mono (ihomZeroIso X).inv, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
      exact curry_snd_comp (CartesianMonoidalCategory.fst X X)
    · change MonoidalClosed.curry (boundaryOneTensorDesc
          (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) (X ⊗ X) ≫
            CartesianMonoidalCategory.fst X X)
          (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) (X ⊗ X) ≫
            CartesianMonoidalCategory.snd X X)) ≫
          (MonoidalClosed.pre (boundary.ι (0 : Fin 2))).app X ≫
            (ihomZeroIso X).hom = CartesianMonoidalCategory.snd X X
      rw [MonoidalClosed.curry_pre_app_assoc,
        boundary_ι_zero_whiskerRight_desc]
      rw [← cancel_mono (ihomZeroIso X).inv, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
      exact curry_snd_comp (CartesianMonoidalCategory.snd X X)

@[reassoc (attr := simp)]
public lemma boundaryOneIhomIso_hom_fst (X : SSet.{u}) :
    (boundaryOneIhomIso X).hom ≫ CartesianMonoidalCategory.fst X X =
      (MonoidalClosed.pre (boundary.ι (1 : Fin 2))).app X ≫
        (ihomZeroIso X).hom := by
  simp [boundaryOneIhomIso]

@[reassoc (attr := simp)]
public lemma boundaryOneIhomIso_hom_snd (X : SSet.{u}) :
    (boundaryOneIhomIso X).hom ≫ CartesianMonoidalCategory.snd X X =
      (MonoidalClosed.pre (boundary.ι (0 : Fin 2))).app X ≫
        (ihomZeroIso X).hom := by
  simp [boundaryOneIhomIso]

private lemma pre_boundary_ι_comp_boundaryOneIhomIso (X : SSet.{u}) :
    (MonoidalClosed.pre (boundary 1).ι).app X ≫ (boundaryOneIhomIso X).hom =
      evalPair (X := X) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, boundaryOneIhomIso_hom_fst,
      ← NatTrans.comp_app_assoc, ← MonoidalClosed.pre_map, boundary.ι_ι]
    rfl
  · rw [Category.assoc, boundaryOneIhomIso_hom_snd,
      ← NatTrans.comp_app_assoc, ← MonoidalClosed.pre_map, boundary.ι_ι]
    rfl

public instance {X : SSet.{u}} [KanComplex X] : Fibration (evalPair (X := X)) := by
  let e' : Arrow.mk ((MonoidalClosed.pre (boundary 1).ι).app X) ≅
      Arrow.mk (evalPair (X := X)) :=
    Arrow.isoMk (Iso.refl _) (boundaryOneIhomIso X)
      (pre_boundary_ι_comp_boundaryOneIhomIso X)
  let e : Arrow.mk (evalPair (X := X)) ≅
      Arrow.mk ((MonoidalClosed.pre (boundary 1).ι).app X) := e'.symm
  rw [HomotopicalAlgebra.fibration_iff]
  exact (MorphismProperty.arrow_mk_iso_iff _ e).2 (by
    rw [← HomotopicalAlgebra.fibration_iff]
    infer_instance)

private lemma eval_constPath_aux (X : SSet.{u}) (i : Fin 2) :
    constPath (X := X) ≫
        ((MonoidalClosed.pre (stdSimplex.δ i : Δ[0] ⟶ Δ[1])).app X ≫
          (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
            (MonoidalClosed.unitIsoSelf (X := X)).hom) =
      𝟙 X := by
  unfold constPath
  have h1 : (stdSimplex.δ i ▷ X) ≫
      CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X =
      CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X := rfl
  have h2 : (Δ0IsoUnit.inv ▷ X) ≫
      CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X =
      CartesianMonoidalCategory.snd (𝟙_ SSet.{u}) X := rfl
  have h3 : MonoidalClosed.curry
      (CartesianMonoidalCategory.snd (𝟙_ SSet.{u}) X) =
      (MonoidalClosed.unitIsoSelf (X := X)).inv := rfl
  have h_curry1 :
      MonoidalClosed.curry
        (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X) ≫
        (MonoidalClosed.pre (stdSimplex.δ i)).app X =
      MonoidalClosed.curry
        ((stdSimplex.δ i ▷ X) ≫
          CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X) := by
    rw [MonoidalClosed.curry_pre_app]
  have h_curry2 :
      MonoidalClosed.curry
        (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X) ≫
        (MonoidalClosed.pre Δ0IsoUnit.inv).app X =
      MonoidalClosed.curry
        ((Δ0IsoUnit.inv ▷ X) ≫
          CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X) := by
    rw [MonoidalClosed.curry_pre_app]
  calc MonoidalClosed.curry
        (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X) ≫
        (MonoidalClosed.pre (stdSimplex.δ i)).app X ≫
          (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
            (MonoidalClosed.unitIsoSelf (X := X)).hom
      = MonoidalClosed.curry
          ((stdSimplex.δ i ▷ X) ≫
            CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X) ≫
          (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
            (MonoidalClosed.unitIsoSelf (X := X)).hom := by
        calc _ =
            (MonoidalClosed.curry
                (CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X) ≫
              (MonoidalClosed.pre (stdSimplex.δ i)).app X) ≫
              (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
                (MonoidalClosed.unitIsoSelf (X := X)).hom := by
              simp [Category.assoc]
          _ = MonoidalClosed.curry
              ((stdSimplex.δ i ▷ X) ≫
                CartesianMonoidalCategory.snd (Δ[1] : SSet.{u}) X) ≫
              (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
                (MonoidalClosed.unitIsoSelf (X := X)).hom := by
              rw [h_curry1]
      _ = MonoidalClosed.curry
          (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X) ≫
          (MonoidalClosed.pre Δ0IsoUnit.inv).app X ≫
            (MonoidalClosed.unitIsoSelf (X := X)).hom := by
        rw [h1]
      _ = MonoidalClosed.curry
          ((Δ0IsoUnit.inv ▷ X) ≫
            CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X) ≫
          (MonoidalClosed.unitIsoSelf (X := X)).hom := by
        calc _ =
            (MonoidalClosed.curry
                (CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X) ≫
              (MonoidalClosed.pre Δ0IsoUnit.inv).app X) ≫
              (MonoidalClosed.unitIsoSelf (X := X)).hom := by
              simp [Category.assoc]
          _ = MonoidalClosed.curry
              ((Δ0IsoUnit.inv ▷ X) ≫
                CartesianMonoidalCategory.snd (Δ[0] : SSet.{u}) X) ≫
              (MonoidalClosed.unitIsoSelf (X := X)).hom := by
              rw [h_curry2]
      _ = MonoidalClosed.curry
          (CartesianMonoidalCategory.snd (𝟙_ SSet.{u}) X) ≫
          (MonoidalClosed.unitIsoSelf (X := X)).hom := by
        rw [h2]
      _ = 𝟙 X := by
        rw [h3]
        simp [Iso.inv_hom_id]

/-- Evaluation at time zero followed by the constant-path inclusion is
precomposition by the constant-zero endomorphism of the simplicial interval. -/
@[reassoc]
public lemma eval₀_constPath_eq_pre_constZero (X : SSet.{u}) :
    (eval₀ : pathSpace X ⟶ X) ≫ constPath X =
      (MonoidalClosed.pre
        (SSet.const (X := (Δ[1] : SSet.{u}))
          (stdSimplex.obj₀Equiv.{u}.symm 0))).app X := by
  let I := (Δ[1] : SSet.{u})
  let toUnit : I ⟶ 𝟙_ SSet.{u} :=
    CartesianMonoidalCategory.toUnit I
  have hConstPath : constPath X =
      (MonoidalClosed.unitIsoSelf (X := X)).inv ≫
        (MonoidalClosed.pre toUnit).app X := by
    change MonoidalClosed.curry
        (CartesianMonoidalCategory.snd I X) = _
    have hUnit : MonoidalClosed.curry
        (CartesianMonoidalCategory.snd (𝟙_ SSet.{u}) X) =
        (MonoidalClosed.unitIsoSelf (X := X)).inv := rfl
    rw [← hUnit, MonoidalClosed.curry_pre_app]
    congr 1
  have hConst :
      toUnit ≫ Δ0IsoUnit.inv ≫
          (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) =
        SSet.const (X := I) (stdSimplex.obj₀Equiv.{u}.symm 0) := by
    rw [stdSimplex.δ_one_eq_const]
    simp
  have hPre :
      MonoidalClosed.pre
          (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) ≫
        MonoidalClosed.pre Δ0IsoUnit.inv ≫
          MonoidalClosed.pre toUnit =
        MonoidalClosed.pre
          (SSet.const (X := I) (stdSimplex.obj₀Equiv.{u}.symm 0)) := by
    rw [← MonoidalClosed.pre_map, ← MonoidalClosed.pre_map,
      Category.assoc, hConst]
  rw [hConstPath]
  unfold eval₀
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact congr_app hPre X

@[simp]
public lemma eval₀_constPath (X : SSet.{u}) : constPath (X := X) ≫ eval₀ = 𝟙 X := by
  unfold eval₀
  exact eval_constPath_aux X 1

@[simp]
public lemma eval₁_constPath (X : SSet.{u}) : constPath (X := X) ≫ eval₁ = 𝟙 X := by
  unfold eval₁
  exact eval_constPath_aux X 0

@[simp]
public lemma evalPair_constPath (X : SSet.{u}) :
    constPath (X := X) ≫ evalPair =
      CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X) := by
  unfold evalPair
  simp [eval₀_constPath, eval₁_constPath]

public instance {X : SSet.{u}} [KanComplex X] : KanComplex (pathSpace (X := X)) := by
  unfold pathSpace
  infer_instance

public instance {X : SSet.{u}} [KanComplex X] : Fibration (eval₀ (X := X)) := by
  unfold eval₀
  have : Mono (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]) := inferInstance
  have : Mono (Δ0IsoUnit.inv : (𝟙_ SSet.{u}) ⟶ (Δ[0] : SSet.{u})) :=
    inferInstance
  infer_instance

public instance {X : SSet.{u}} [KanComplex X] : Fibration (eval₁ (X := X)) := by
  unfold eval₁
  have : Mono (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]) := inferInstance
  have : Mono (Δ0IsoUnit.inv : (𝟙_ SSet.{u}) ⟶ (Δ[0] : SSet.{u})) :=
    inferInstance
  infer_instance

end SSet
