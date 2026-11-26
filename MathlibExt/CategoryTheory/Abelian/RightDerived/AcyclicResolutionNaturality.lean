/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.LeftDerived.AcyclicResolutionNaturality
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AcyclicResolution


/- The left-derived naturality API remains publicly imported for existing users of this module. -/

/-!
# Naturality of acyclic right-derived comparisons

For an additive left-exact functor between abelian categories with
injective resolutions in the source, maps between exact coaugmented
termwise acyclic complexes give comparison squares with the derived
maps of their resolved objects. Opposite duality identifies these
squares with the corresponding left-derived augmented-chain squares.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v₁ u₁ v₂ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency.types false in
/-- For an abelian category `C`, the identification of the opposite
of a nonnegative cochain complex concentrated at degree zero with the
chain complex concentrated at degree zero in `Cᵒᵖ` is natural in
every map `f : X → Y`. -/
theorem single₀OpIso_hom_naturality
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {X Y : C} (f : X ⟶ Y) :
    (HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map
        ((CochainComplex.single₀ C).map f).op ≫ (single₀OpIso X).hom =
      (single₀OpIso Y).hom ≫ (ChainComplex.single₀ Cᵒᵖ).map f.op := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change (((CochainComplex.single₀ C).map f).f 0).op ≫
          (single₀OpIso X).hom.f 0 =
        (single₀OpIso Y).hom.f 0 ≫ ((ChainComplex.single₀ Cᵒᵖ).map f.op).f 0
      rw [CochainComplex.single₀_map_f_zero, ChainComplex.single₀_map_f_zero,
        single₀OpIso_hom_f_zero, single₀OpIso_hom_f_zero]
      simp
  | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
        (Opposite.op X) (n + 1) (by omega)).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- In an abelian category `C`, let `ι : X[0] → I`, `κ : Y[0] → J`
be coaugmentations and `a : I → J` lie over `f : X → Y`, so
`ι ≫ a = f[0] ≫ κ`. Taking opposites gives the commutative
augmentation square for `aᵒᵖ : Jᵒᵖ → Iᵒᵖ` and `fᵒᵖ : Yᵒᵖ → Xᵒᵖ`,
using the degree-zero opposite-complex identifications. -/
theorem oppositeAcyclicAugmentationMap_comm
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {X Y : C} {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj Y ⟶ J)
    (f : X ⟶ Y) (a : I ⟶ J)
    (h : ι ≫ a = (CochainComplex.single₀ C).map f ≫ κ) :
    (HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map a.op ≫
        ((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map ι.op ≫
          (single₀OpIso X).hom) =
      ((HomologicalComplex.opFunctor C (ComplexShape.up ℕ)).map κ.op ≫
        (single₀OpIso Y).hom) ≫ (ChainComplex.single₀ Cᵒᵖ).map f.op := by
  let O := HomologicalComplex.opFunctor C (ComplexShape.up ℕ)
  have ho : a.op ≫ ι.op = κ.op ≫ ((CochainComplex.single₀ C).map f).op :=
    congrArg Quiver.Hom.op h
  calc
    O.map a.op ≫ (O.map ι.op ≫ (single₀OpIso X).hom) =
        O.map (a.op ≫ ι.op) ≫ (single₀OpIso X).hom := by rw [O.map_comp, Category.assoc]
    _ = O.map (κ.op ≫ ((CochainComplex.single₀ C).map f).op) ≫
        (single₀OpIso X).hom := by rw [ho]
    _ = O.map κ.op ≫ (O.map ((CochainComplex.single₀ C).map f).op ≫
        (single₀OpIso X).hom) := by rw [O.map_comp, Category.assoc]
    _ = O.map κ.op ≫ ((single₀OpIso Y).hom ≫ (ChainComplex.single₀ Cᵒᵖ).map f.op) := by
      rw [single₀OpIso_hom_naturality f]
    _ = (O.map κ.op ≫ (single₀OpIso Y).hom) ≫
        (ChainComplex.single₀ Cᵒᵖ).map f.op := (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- In a category `Dᵒᵖ`, let `l : L₁ → L₀`, `b : H₁ → H₀`,
`e₀ : L₀ ≅ H₀`, `e₁ : L₁ ≅ H₁`, with `l ≫ e₀ = e₁ ≫ b`.
The inverse comparison maps in `D` satisfy
`l.unop ≫ e₁⁻¹.unop = e₀⁻¹.unop ≫ b.unop`. -/
theorem inverseUnopComparison_naturality
    {D : Type u₂} [Category.{v₂} D]
    {L₀ L₁ H₀ H₁ : Dᵒᵖ}
    (l : L₁ ⟶ L₀) (b : H₁ ⟶ H₀) (e₀ : L₀ ≅ H₀) (e₁ : L₁ ≅ H₁)
    (h : l ≫ e₀.hom = e₁.hom ≫ b) :
    l.unop ≫ e₁.inv.unop = e₀.inv.unop ≫ b.unop := by
  have hinv : e₁.inv ≫ l = b ≫ e₀.inv := by
    apply (cancel_mono e₀.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h, Iso.inv_hom_id_assoc]
  exact congrArg Quiver.Hom.unop hinv

end CategoryTheory

namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. Suppose
`ι : X[0] → I`, `κ : Y[0] → J` are quasi-isomorphisms with termwise
vanishing positive right-derived values, and `a : I → J` lies over
`f : X → Y`, so `ι ≫ a = f[0] ≫ κ`. If the corresponding left-derived acyclic comparisons for
`Fᵒᵖ` are natural for every choice of projective-resolution supply in
`Cᵒᵖ` and finite-colimit-preservation structure on `Fᵒᵖ`, then
`R^nF(f) ≫ comparison_J = comparison_I ≫ Hⁿ(F(a))`. -/
theorem rightDerivedAcyclicComparison_naturality_of_left
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (leftNatural : ∀ (HP : HasProjectiveResolutions Cᵒᵖ)
      (FC : PreservesFiniteColimits F.op)
      {M N : Cᵒᵖ} (Q R : ChainComplex Cᵒᵖ ℕ)
      (π : Q ⟶ (ChainComplex.single₀ Cᵒᵖ).obj M)
      (ρ : R ⟶ (ChainComplex.single₀ Cᵒᵖ).obj N)
      (hπ : QuasiIso π) (hρ : QuasiIso ρ)
      (hQ : ∀ q j : ℕ, IsZero ((F.op.leftDerived (j + 1)).obj (Q.X q)))
      (hR : ∀ q j : ℕ, IsZero ((F.op.leftDerived (j + 1)).obj (R.X q)))
      (f : M ⟶ N) (a : Q ⟶ R)
      (_h : a ≫ ρ = π ≫ (ChainComplex.single₀ Cᵒᵖ).map f) (n : ℕ),
      (F.op.leftDerived n).map f ≫
        (@leftDerivedObjIsoHomologyOfAcyclicResolution
          _ _ _ HP _ _ _ F.op _ FC _ R ρ hρ hR n).hom =
        (@leftDerivedObjIsoHomologyOfAcyclicResolution
          _ _ _ HP _ _ _ F.op _ FC _ Q π hπ hQ n).hom ≫
            HomologicalComplex.homologyMap
              ((F.op.mapHomologicalComplex (ComplexShape.down ℕ)).map a) n)
    {X Y : C} (I J : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj Y ⟶ J)
    [QuasiIso ι] [QuasiIso κ]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q)))
    (hJ : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (J.X q)))
    (f : X ⟶ Y) (a : I ⟶ J)
    (h : ι ≫ a = (CochainComplex.single₀ C).map f ≫ κ) (n : ℕ) :
    (F.rightDerived n).map f ≫
        (rightDerivedObjIsoHomologyOfAcyclicResolution F J κ hJ n).hom =
      (rightDerivedObjIsoHomologyOfAcyclicResolution F I ι hI n).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n := by
  let : HasProjectiveResolutions Cᵒᵖ :=
    { out Z := ⟨⟨injectiveResolutionOpProj (injectiveResolution Z.unop)⟩⟩ }
  let : PreservesFiniteColimits F.op := preservesFiniteColimits_op F
  let O := HomologicalComplex.opFunctor C (ComplexShape.up ℕ)
  let π : I.op ⟶ (ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X) :=
    O.map ι.op ≫ (single₀OpIso X).hom
  let ρ : J.op ⟶ (ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op Y) :=
    O.map κ.op ≫ (single₀OpIso Y).hom
  have hπ : QuasiIso π := by
    have h₁ : QuasiIso (O.map ι.op) :=
      (HomologicalComplex.quasiIso_opFunctor_map_iff _).mpr inferInstance
    have h₂ : QuasiIso (single₀OpIso X).hom := by
      let _ : IsIso (single₀OpIso X).hom := (single₀OpIso X).isIso_hom
      exact quasiIso_of_isIso _
    exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂)
  have hρ : QuasiIso ρ := by
    have h₁ : QuasiIso (O.map κ.op) :=
      (HomologicalComplex.quasiIso_opFunctor_map_iff _).mpr inferInstance
    have h₂ : QuasiIso (single₀OpIso Y).hom := by
      let _ : IsIso (single₀OpIso Y).hom := (single₀OpIso Y).isIso_hom
      exact quasiIso_of_isIso _
    exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂)
  have hIop : ∀ q j : ℕ, IsZero ((F.op.leftDerived (j + 1)).obj (I.op.X q)) := by
    intro q j
    change IsZero ((F.op.leftDerived (j + 1)).obj (Opposite.op (I.X q)))
    have hu : IsZero (Opposite.unop
        ((F.op.leftDerived (j + 1)).obj (Opposite.op (I.X q)))) :=
      (hI q j).of_iso ((F.rightDerivedOpIso (j + 1)).app (I.X q)).symm
    exact hu.op
  have hJop : ∀ q j : ℕ, IsZero ((F.op.leftDerived (j + 1)).obj (J.op.X q)) := by
    intro q j
    change IsZero ((F.op.leftDerived (j + 1)).obj (Opposite.op (J.X q)))
    have hu : IsZero (Opposite.unop
        ((F.op.leftDerived (j + 1)).obj (Opposite.op (J.X q)))) :=
      (hJ q j).of_iso ((F.rightDerivedOpIso (j + 1)).app (J.X q)).symm
    exact hu.op
  let eI := @leftDerivedObjIsoHomologyOfAcyclicResolution
    _ _ _ _ _ _ _ F.op _ _ _ I.op π hπ hIop n
  let eJ := @leftDerivedObjIsoHomologyOfAcyclicResolution
    _ _ _ _ _ _ _ F.op _ _ _ J.op ρ hρ hJop n
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I
  let L := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J
  let b := (F.mapHomologicalComplex (ComplexShape.up ℕ)).map a
  let qI := eI ≪≫ K.homologyOp n
  let qJ := eJ ≪≫ L.homologyOp n
  have hleft := leftNatural inferInstance inferInstance J.op I.op ρ π hρ hπ
    hJop hIop f.op (O.map a.op) (oppositeAcyclicAugmentationMap_comm ι κ f a h) n
  have hop := HomologicalComplex.homologyOp_hom_naturality b n
  have hmap : ((F.op.mapHomologicalComplex (ComplexShape.down ℕ)).map (O.map a.op)) =
      (HomologicalComplex.opFunctor D (ComplexShape.up ℕ)).map b.op := rfl
  have hcombined : (F.op.leftDerived n).map f.op ≫ qI.hom =
      qJ.hom ≫ (HomologicalComplex.homologyMap b n).op := by
    change (F.op.leftDerived n).map f.op ≫
        (eI.hom ≫ (K.homologyOp n).hom) =
      (eJ.hom ≫ (L.homologyOp n).hom) ≫ (HomologicalComplex.homologyMap b n).op
    rw [← Category.assoc, hleft, Category.assoc, hmap]
    exact (congrArg (fun t => eJ.hom ≫ t) hop).trans (Category.assoc _ _ _).symm
  have hinv := inverseUnopComparison_naturality
    ((F.op.leftDerived n).map f.op) (HomologicalComplex.homologyMap b n).op qI qJ hcombined
  have hopNative := (F.rightDerivedOpIso n).hom.naturality f
  have heI : (rightDerivedObjIsoHomologyOfAcyclicResolution F I ι hI n).hom =
      ((F.rightDerivedOpIso n).app X).hom ≫ qI.inv.unop := by
    change ((F.rightDerivedOpIso n).app X).hom ≫
        (((K.homologyOp n).inv ≫
          ((HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) n).map
            (𝟙 ((F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj I.op)))) ≫
            eI.inv).unop = _
    let Z := (F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj I.op
    let H := HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) n
    have hid : H.map (𝟙 Z) = 𝟙 (H.obj Z) := H.map_id Z
    exact (congrArg (fun t => ((F.rightDerivedOpIso n).app X).hom ≫
      (((K.homologyOp n).inv ≫ t) ≫ eI.inv).unop) hid).trans
        (congrArg (fun t => ((F.rightDerivedOpIso n).app X).hom ≫
          (t ≫ eI.inv).unop) (Category.comp_id (K.homologyOp n).inv))
  have heJ : (rightDerivedObjIsoHomologyOfAcyclicResolution F J κ hJ n).hom =
      ((F.rightDerivedOpIso n).app Y).hom ≫ qJ.inv.unop := by
    change ((F.rightDerivedOpIso n).app Y).hom ≫
        (((L.homologyOp n).inv ≫
          ((HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) n).map
            (𝟙 ((F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj J.op)))) ≫
            eJ.inv).unop = _
    let Z := (F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj J.op
    let H := HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) n
    have hid : H.map (𝟙 Z) = 𝟙 (H.obj Z) := H.map_id Z
    exact (congrArg (fun t => ((F.rightDerivedOpIso n).app Y).hom ≫
      (((L.homologyOp n).inv ≫ t) ≫ eJ.inv).unop) hid).trans
        (congrArg (fun t => ((F.rightDerivedOpIso n).app Y).hom ≫
          (t ≫ eJ.inv).unop) (Category.comp_id (L.homologyOp n).inv))
  rw [heI, heJ]
  have hnative : (F.rightDerived n).map f ≫ ((F.rightDerivedOpIso n).app Y).hom =
      ((F.rightDerivedOpIso n).app X).hom ≫ ((F.op.leftDerived n).map f.op).unop :=
    hopNative
  have s₀ : CommSq ((F.rightDerivedOpIso n).app X).hom
      ((F.rightDerived n).map f) ((F.op.leftDerived n).map f.op).unop
      ((F.rightDerivedOpIso n).app Y).hom := ⟨hnative.symm⟩
  have s₁ : CommSq qI.inv.unop ((F.op.leftDerived n).map f.op).unop
      (HomologicalComplex.homologyMap b n) qJ.inv.unop := ⟨hinv.symm⟩
  exact (s₀.horiz_comp s₁).w.symm

end CategoryTheory.Functor


namespace CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. Suppose
`ι : X[0] → I`, `κ : Y[0] → J` are quasi-isomorphisms with termwise
vanishing positive right-derived values, and `a : I → J` lies over
`f : X → Y`, so `ι ≫ a = f[0] ≫ κ`. The acyclic comparisons satisfy
`R^nF(f) ≫ comparison_J = comparison_I ≫ Hⁿ(F(a))` in every degree `n`. -/
theorem rightDerivedObjIsoHomologyOfAcyclicResolution_naturality
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X Y : C} (I J : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj Y ⟶ J) [QuasiIso ι] [QuasiIso κ]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q)))
    (hJ : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (J.X q)))
    (f : X ⟶ Y) (a : I ⟶ J)
    (h : ι ≫ a = (CochainComplex.single₀ C).map f ≫ κ) (n : ℕ) :
    (F.rightDerived n).map f ≫
        (F.rightDerivedObjIsoHomologyOfAcyclicResolution J κ hJ n).hom =
      (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI n).hom ≫
        HomologicalComplex.homologyMap
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map a) n := by
  apply rightDerivedAcyclicComparison_naturality_of_left F ?_ I J ι κ hI hJ f a h n
  intro HP FC M N Q R π ρ hπ hρ hQ hR f a h n
  let : HasProjectiveResolutions Cᵒᵖ := HP
  let : PreservesFiniteColimits F.op := FC
  let : QuasiIso π := hπ
  let : QuasiIso ρ := hρ
  exact leftDerivedObjIsoHomologyOfAcyclicResolution_naturality F.op Q R π ρ hQ hR f a h n

end CategoryTheory.Functor
