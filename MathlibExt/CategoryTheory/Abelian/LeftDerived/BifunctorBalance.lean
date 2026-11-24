/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.BifunctorAugmentation
public import MathlibExt.CategoryTheory.Abelian.LeftDerivedBifunctor
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Isomorphism

/-!
# Balanced left derivation of the additive bifunctor

Both comparisons use the same total of projective resolutions. The augmentation quasi-isomorphisms
are proved from exactness on their projective terms. No acyclic resolution or comparison is
supplied.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.LeftDerivedBalance

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X : C₁, (F.obj X).Additive]
  [HasProjectiveResolutions C₁] [HasProjectiveResolutions C₂]

local notation "c" => ComplexShape.down ℕ

attribute [local instance] flippedAdditive flippedObjAdditive

/-- Left derivation in the second variable, using functors and maps. -/
def deriveSecond (n : ℕ) : C₁ ⥤ C₂ ⥤ D :=
  (F.flip.leftDerivedBifunctor n).flip

/-- Left derivation in the first variable, with the original variable order. -/
def deriveFirst (n : ℕ) : C₁ ⥤ C₂ ⥤ D :=
  F.leftDerivedBifunctor n

/-- The map between the second-variable resolution computations. -/
def secondComputationMap {A A' : C₁} (a : A ⟶ A')
    {Q Q' : ChainComplex C₂ ℕ} (g : Q ⟶ Q') :
    ((F.obj A).mapHomologicalComplex c).obj Q ⟶
      ((F.obj A').mapHomologicalComplex c).obj Q' :=
  ((F.obj A).mapHomologicalComplex c).map g ≫
    ((NatTrans.mapHomologicalComplex (F.map a) c).app Q')

/-- The map between the first-variable resolution computations. -/
def firstComputationMap {P P' : ChainComplex C₁ ℕ} (f : P ⟶ P')
    {B B' : C₂} (b : B ⟶ B') :
    ((F.flip.obj B).mapHomologicalComplex c).obj P ⟶
      ((F.flip.obj B').mapHomologicalComplex c).obj P' :=
  secondComputationMap F.flip b f

omit [HasProjectiveResolutions C₁] [F.Additive] [Abelian C₁] in
/-- Simultaneous derived maps computed in second-variable resolutions. -/
theorem deriveSecond_map_computation (n : ℕ) {A A' : C₁} (a : A ⟶ A')
    {B B' : C₂} (b : B ⟶ B')
    (Q : ProjectiveResolution B) (Q' : ProjectiveResolution B')
    (g : Q.complex ⟶ Q'.complex)
    (hg : g ≫ Q'.π = Q.π ≫ (ChainComplex.single₀ C₂).map b) :
    ((deriveSecond F n).obj A).map b ≫ ((deriveSecond F n).map a).app B' =
      (Q.isoLeftDerivedObj (F.obj A) n).hom ≫
        (HomologicalComplex.homologyFunctor D c n).map (secondComputationMap F a g) ≫
        (Q'.isoLeftDerivedObj (F.obj A') n).inv := by
  let G : C₂ ⥤ D := F.obj A
  let G' : C₂ ⥤ D := F.obj A'
  let α : G ⟶ G' := F.map a
  let H := HomologicalComplex.homologyFunctor D c n
  let K₀ := (G.mapHomologicalComplex c).obj Q.complex
  let K₁ := (G.mapHomologicalComplex c).obj Q'.complex
  let K₂ := (G'.mapHomologicalComplex c).obj Q'.complex
  let u : K₀ ⟶ K₁ := (G.mapHomologicalComplex c).map g
  let v : K₁ ⟶ K₂ := (NatTrans.mapHomologicalComplex α c).app Q'.complex
  let e₀ : (G.leftDerived n).obj B ≅ H.obj K₀ := Q.isoLeftDerivedObj G n
  let e₁ : (G.leftDerived n).obj B' ≅ H.obj K₁ := Q'.isoLeftDerivedObj G n
  let e₂ : (G'.leftDerived n).obj B' ≅ H.obj K₂ := Q'.isoLeftDerivedObj G' n
  let m : (G.leftDerived n).obj B ⟶ (G.leftDerived n).obj B' := (G.leftDerived n).map b
  let t : (G.leftDerived n).obj B' ⟶ (G'.leftDerived n).obj B' :=
    (NatTrans.leftDerived α n).app B'
  have hMap : m = e₀.hom ≫ H.map u ≫ e₁.inv :=
    Functor.leftDerived_map_eq G n b (P := Q) (Q := Q') g hg
  have hTransformation : t = e₁.hom ≫ H.map v ≫ e₂.inv :=
    ProjectiveResolution.leftDerived_app_eq α Q' n
  have hIdentity : e₁.inv ≫ e₁.hom = 𝟙 (H.obj K₁) := e₁.inv_hom_id
  change m ≫ t = e₀.hom ≫ H.map (u ≫ v) ≫ e₂.inv
  calc
    m ≫ t = (e₀.hom ≫ H.map u ≫ e₁.inv) ≫ (e₁.hom ≫ H.map v ≫ e₂.inv) :=
      (congrArg (fun f => f ≫ t) hMap).trans
        (congrArg (fun f => (e₀.hom ≫ H.map u ≫ e₁.inv) ≫ f) hTransformation)
    _ = e₀.hom ≫ H.map u ≫ (e₁.inv ≫ e₁.hom) ≫ H.map v ≫ e₂.inv := by
      simp only [Category.assoc]
    _ = e₀.hom ≫ H.map u ≫ H.map v ≫ e₂.inv := by
      exact (congrArg (fun f => e₀.hom ≫ H.map u ≫ f ≫ H.map v ≫ e₂.inv) hIdentity).trans
        (by simp only [Category.id_comp])
    _ = e₀.hom ≫ (H.map u ≫ H.map v) ≫ e₂.inv := by simp only [Category.assoc]
    _ = e₀.hom ≫ H.map (u ≫ v) ≫ e₂.inv :=
      congrArg (fun f => e₀.hom ≫ f ≫ e₂.inv) (H.map_comp u v).symm

omit [HasProjectiveResolutions C₂] [∀ X : C₁, (F.obj X).Additive] [Abelian C₂] in
/-- The same simultaneous computation in the original first variable. -/
theorem deriveFirst_map_computation (n : ℕ) {A A' : C₁} (a : A ⟶ A')
    {B B' : C₂} (b : B ⟶ B')
    (P : ProjectiveResolution A) (P' : ProjectiveResolution A')
    (f : P.complex ⟶ P'.complex)
    (hf : f ≫ P'.π = P.π ≫ (ChainComplex.single₀ C₁).map a) :
    ((deriveFirst F n).obj A).map b ≫ ((deriveFirst F n).map a).app B' =
      (P.isoLeftDerivedObj (F.flip.obj B) n).hom ≫
        (HomologicalComplex.homologyFunctor D c n).map (firstComputationMap F f b) ≫
        (P'.isoLeftDerivedObj (F.flip.obj B') n).inv := by
  let G : C₁ ⥤ D := F.flip.obj B
  let G' : C₁ ⥤ D := F.flip.obj B'
  let α : G ⟶ G' := F.flip.map b
  have hNaturality : (NatTrans.leftDerived α n).app A ≫ (G'.leftDerived n).map a =
      (G.leftDerived n).map a ≫ (NatTrans.leftDerived α n).app A' :=
    ((NatTrans.leftDerived α n).naturality a).symm
  have hComputation : (G.leftDerived n).map a ≫ (NatTrans.leftDerived α n).app A' =
      (P.isoLeftDerivedObj G n).hom ≫
        (HomologicalComplex.homologyFunctor D c n).map (firstComputationMap F f b) ≫
          (P'.isoLeftDerivedObj G' n).inv := by
    have h := deriveSecond_map_computation F.flip n b a P P' f hf
    change (G.leftDerived n).map a ≫ (NatTrans.leftDerived α n).app A' = _ at h
    exact h
  change (NatTrans.leftDerived α n).app A ≫ (G'.leftDerived n).map a = _
  exact hNaturality.trans hComputation

/-- Both resolution augmentations give the objectwise balance map. -/
def resolutionBalanceIso
    (h₁ : ∀ X : C₁, Projective X → (F.obj X).PreservesHomology)
    (h₂ : ∀ Y : C₂, Projective Y → (F.flip.obj Y).PreservesHomology)
    (n : ℕ) {A : C₁} {B : C₂}
    (P : ProjectiveResolution A) (Q : ProjectiveResolution B) :
    ((deriveSecond F n).obj A).obj B ≅ ((deriveFirst F n).obj A).obj B := by
  let H := HomologicalComplex.homologyFunctor D c n
  letI : QuasiIso (leftAugmentation F P Q.complex) :=
    leftAugmentation_quasiIso F h₂ P Q
  letI : QuasiIso (rightAugmentation F P.complex Q) :=
    rightAugmentation_quasiIso F h₁ P Q
  letI : IsIso (H.map (leftAugmentation F P Q.complex)) := by
    change IsIso (HomologicalComplex.homologyMap (leftAugmentation F P Q.complex) n)
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  letI : IsIso (H.map (rightAugmentation F P.complex Q)) := by
    change IsIso (HomologicalComplex.homologyMap (rightAugmentation F P.complex Q) n)
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  exact (Q.isoLeftDerivedObj (F.obj A) n) ≪≫
    (asIso (H.map (leftAugmentation F P Q.complex))).symm ≪≫
    asIso (H.map (rightAugmentation F P.complex Q)) ≪≫
    (P.isoLeftDerivedObj (F.flip.obj B) n).symm

omit [Abelian D] in
private theorem augmentationComparison_naturality
    {T T' L L' V V' : D} (t : T ⟶ T') (l : L ⟶ L') (v : V ⟶ V')
    (a : T ⟶ L) (a' : T' ⟶ L') (b : T ⟶ V) (b' : T' ⟶ V')
    [IsIso a] [IsIso a']
    (ha : t ≫ a' = a ≫ l) (hb : t ≫ b' = b ≫ v) :
    l ≫ (asIso a').inv ≫ b' = (asIso a).inv ≫ b ≫ v := by
  apply (cancel_epi a).1
  calc
    a ≫ (l ≫ (asIso a').inv ≫ b') = (a ≫ l) ≫ (asIso a').inv ≫ b' := by
      simp only [Category.assoc]
    _ = (t ≫ a') ≫ (asIso a').inv ≫ b' := congrArg (fun q => q ≫ (asIso a').inv ≫ b') ha.symm
    _ = t ≫ b' := by simp only [Category.assoc, asIso_inv, IsIso.hom_inv_id_assoc]
    _ = b ≫ v := hb
    _ = a ≫ ((asIso a).inv ≫ b ≫ v) := by
      simp only [asIso_inv, IsIso.hom_inv_id_assoc]

/--
Naturality of balance is constructed from both augmentation squares, not from an arbitrary choice
of objectwise comparison isomorphisms.
-/
theorem resolutionBalanceIso_hom_naturality
    (h₁ : ∀ X : C₁, Projective X → (F.obj X).PreservesHomology)
    (h₂ : ∀ Y : C₂, Projective Y → (F.flip.obj Y).PreservesHomology)
    (n : ℕ) {A A' : C₁} (a : A ⟶ A') {B B' : C₂} (b : B ⟶ B')
    (P : ProjectiveResolution A) (P' : ProjectiveResolution A')
    (Q : ProjectiveResolution B) (Q' : ProjectiveResolution B')
    (f : P.complex ⟶ P'.complex) (g : Q.complex ⟶ Q'.complex)
    (hf : f ≫ P'.π = P.π ≫ (ChainComplex.single₀ C₁).map a)
    (hg : g ≫ Q'.π = Q.π ≫ (ChainComplex.single₀ C₂).map b) :
    (((deriveSecond F n).obj A).map b ≫ ((deriveSecond F n).map a).app B') ≫
        (resolutionBalanceIso F h₁ h₂ n P' Q').hom =
      (resolutionBalanceIso F h₁ h₂ n P Q).hom ≫
        (((deriveFirst F n).obj A).map b ≫ ((deriveFirst F n).map a).app B') := by
  let H := HomologicalComplex.homologyFunctor D c n
  let : QuasiIso (leftAugmentation F P Q.complex) :=
    leftAugmentation_quasiIso F h₂ P Q
  let : QuasiIso (leftAugmentation F P' Q'.complex) :=
    leftAugmentation_quasiIso F h₂ P' Q'
  let : IsIso (H.map (leftAugmentation F P Q.complex)) := by
    change IsIso (HomologicalComplex.homologyMap (leftAugmentation F P Q.complex) n)
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  let : IsIso (H.map (leftAugmentation F P' Q'.complex)) := by
    change IsIso (HomologicalComplex.homologyMap (leftAugmentation F P' Q'.complex) n)
    exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  have ha : H.map (totalMap F f g) ≫ H.map (leftAugmentation F P' Q'.complex) =
      H.map (leftAugmentation F P Q.complex) ≫ H.map (secondComputationMap F a g) := by
    rw [← H.map_comp, leftAugmentation_naturality F P P' f g a hf, H.map_comp]
    rfl
  have hb : H.map (totalMap F f g) ≫ H.map (rightAugmentation F P'.complex Q') =
      H.map (rightAugmentation F P.complex Q) ≫ H.map (firstComputationMap F f b) := by
    rw [← H.map_comp, rightAugmentation_naturality F Q Q' f g b hg, H.map_comp]
    rfl
  have hc := augmentationComparison_naturality
    (H.map (totalMap F f g)) (H.map (secondComputationMap F a g))
    (H.map (firstComputationMap F f b))
    (H.map (leftAugmentation F P Q.complex))
    (H.map (leftAugmentation F P' Q'.complex))
    (H.map (rightAugmentation F P.complex Q))
    (H.map (rightAugmentation F P'.complex Q')) ha hb
  let e : ((F.obj A).leftDerived n).obj B ⟶ ((F.flip.obj B).leftDerived n).obj A := by
    let e₀ := (resolutionBalanceIso F h₁ h₂ n P Q).hom
    change ((F.obj A).leftDerived n).obj B ⟶ ((F.flip.obj B).leftDerived n).obj A at e₀
    exact e₀
  let e' : ((F.obj A').leftDerived n).obj B' ⟶ ((F.flip.obj B').leftDerived n).obj A' := by
    let e₀ := (resolutionBalanceIso F h₁ h₂ n P' Q').hom
    change ((F.obj A').leftDerived n).obj B' ⟶ ((F.flip.obj B').leftDerived n).obj A' at e₀
    exact e₀
  let m := ((F.obj A).leftDerived n).map b ≫ (NatTrans.leftDerived (F.map a) n).app B'
  let m' := (NatTrans.leftDerived (F.flip.map b) n).app A ≫
    ((F.flip.obj B').leftDerived n).map a
  change m ≫ e' = e ≫ m'
  have hSecond := deriveSecond_map_computation F n a b Q Q' g hg
  change ((F.obj A).leftDerived n).map b ≫ (NatTrans.leftDerived (F.map a) n).app B' =
    (Q.isoLeftDerivedObj (F.obj A) n).hom ≫
      H.map (secondComputationMap F a g) ≫ (Q'.isoLeftDerivedObj (F.obj A') n).inv at hSecond
  have hFirst := deriveFirst_map_computation F n a b P P' f hf
  change (NatTrans.leftDerived (F.flip.map b) n).app A ≫
      ((F.flip.obj B').leftDerived n).map a =
    (P.isoLeftDerivedObj (F.flip.obj B) n).hom ≫
      H.map (firstComputationMap F f b) ≫ (P'.isoLeftDerivedObj (F.flip.obj B') n).inv at hFirst
  let s := (Q.isoLeftDerivedObj (F.obj A) n).hom ≫
    H.map (secondComputationMap F a g) ≫ (Q'.isoLeftDerivedObj (F.obj A') n).inv
  let s' := (P.isoLeftDerivedObj (F.flip.obj B) n).hom ≫
    H.map (firstComputationMap F f b) ≫ (P'.isoLeftDerivedObj (F.flip.obj B') n).inv
  have he : e = (Q.isoLeftDerivedObj (F.obj A) n).hom ≫
      (asIso (H.map (leftAugmentation F P Q.complex))).inv ≫
        H.map (rightAugmentation F P.complex Q) ≫
          (P.isoLeftDerivedObj (F.flip.obj B) n).inv := rfl
  have he' : e' = (Q'.isoLeftDerivedObj (F.obj A') n).hom ≫
      (asIso (H.map (leftAugmentation F P' Q'.complex))).inv ≫
        H.map (rightAugmentation F P'.complex Q') ≫
          (P'.isoLeftDerivedObj (F.flip.obj B') n).inv := rfl
  have hComparisons : s ≫ e' = e ≫ s' := by
    rw [he, he']
    dsimp only [s, s']
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Category.assoc] using
      congrArg (fun q => (Q.isoLeftDerivedObj (F.obj A) n).hom ≫ q ≫
        (P'.isoLeftDerivedObj (F.flip.obj B') n).inv) hc
  exact (congrArg (fun q => q ≫ e') hSecond).trans
    (hComparisons.trans (congrArg (fun q => e ≫ q) hFirst.symm))

/--
The bifunctor balance isomorphism, natural in both original objects, using the chosen projective
resolutions.
-/
def balanceIso
    (h₁ : ∀ X : C₁, Projective X → (F.obj X).PreservesHomology)
    (h₂ : ∀ Y : C₂, Projective Y → (F.flip.obj Y).PreservesHomology)
    (n : ℕ) : deriveSecond F n ≅ deriveFirst F n :=
  NatIso.ofComponents
    (fun A => NatIso.ofComponents
      (fun B => resolutionBalanceIso F h₁ h₂ n (projectiveResolution A) (projectiveResolution B))
      (fun {B B'} b => by
        simpa only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.comp_id] using
          resolutionBalanceIso_hom_naturality F h₁ h₂ n (𝟙 A) b
            (projectiveResolution A) (projectiveResolution A)
            (projectiveResolution B) (projectiveResolution B')
            (𝟙 _) (ProjectiveResolution.lift b _ _) (by simp)
            (ProjectiveResolution.lift_commutes b _ _)))
    (fun {A A'} a => by
      apply NatTrans.ext
      funext B
      simp only [NatTrans.comp_app, ← Iso.app_hom, NatIso.ofComponents.app]
      simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using
        resolutionBalanceIso_hom_naturality F h₁ h₂ n a (𝟙 B)
          (projectiveResolution A) (projectiveResolution A')
          (projectiveResolution B) (projectiveResolution B)
          (ProjectiveResolution.lift a _ _) (𝟙 _)
          (ProjectiveResolution.lift_commutes a _ _) (by simp))

end CategoryTheory.Functor.LeftDerivedBalance
