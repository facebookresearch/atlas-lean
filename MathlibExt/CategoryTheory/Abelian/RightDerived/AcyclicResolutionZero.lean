/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.RightDerived.AcyclicResolution

/- The proof uses the opposite augmentation cokernel and homology duality. -/

/-!
# Degree-zero coaugmentation under the acyclic comparison

Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. For a termwise
`F`-acyclic coaugmentation quasi-isomorphism `X[0] → I`, the degree-zero
comparison identifies the canonical map to `R⁰F(X)` with the mapped
coaugmentation cycle class. Under `R⁰F(X) ≅ F(X)`, its cycle inclusion
is precisely the map `F(X) → F(I⁰)`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe v₁ u₁ v₂ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

set_option backward.isDefEq.respectTransparency.types false in
private theorem homologyOpIso_hom_homologyπ_op
    {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
    (S : ShortComplex D) [S.HasHomology] :
    S.homologyOpIso.hom ≫ S.homologyπ.op =
      S.op.homologyι ≫ S.opcyclesOpIso.hom := by
  let h := S.rightHomologyData
  have he : S.homologyOpIso.hom = h.op.homologyIso.hom ≫ h.homologyIso.hom.op := by
    dsimp only [h]
    rw [RightHomologyData.homologyIso_rightHomologyData]
    simp only [homologyOpIso, LeftHomologyData.homologyIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc]
    rfl
  have hh : S.homologyπ ≫ h.homologyIso.hom ≫ h.ι = S.iCycles ≫ h.p := by
    rw [h.homologyIso_hom_comp_ι, ← Category.assoc, homology_π_ι, Category.assoc,
      RightHomologyData.pOpcycles_comp_opcyclesIso_hom]
  apply (cancel_epi S.op.homologyπ).1
  rw [he]
  calc
    S.op.homologyπ ≫ ((h.op.homologyIso.hom ≫ h.homologyIso.hom.op) ≫ S.homologyπ.op) =
        (S.op.homologyπ ≫ h.op.homologyIso.hom) ≫
          (h.homologyIso.hom.op ≫ S.homologyπ.op) := by
      simp only [Category.assoc]
    _ = (h.op.cyclesIso.hom ≫ h.op.π) ≫
        (h.homologyIso.hom.op ≫ S.homologyπ.op) := by
      rw [LeftHomologyData.homologyπ_comp_homologyIso_hom]
    _ = h.op.cyclesIso.hom ≫ (S.homologyπ ≫ h.homologyIso.hom ≫ h.ι).op := by
      simp only [RightHomologyData.op_π, op_comp, Category.assoc]
    _ = h.op.cyclesIso.hom ≫ (S.iCycles ≫ h.p).op :=
      congrArg (fun t => h.op.cyclesIso.hom ≫ t.op) hh
    _ = (h.op.cyclesIso.hom ≫ h.op.i) ≫ S.iCycles.op := by
      simp only [RightHomologyData.op_i, op_comp, Category.assoc]
    _ = S.op.iCycles ≫ S.iCycles.op := by
      rw [LeftHomologyData.cyclesIso_hom_comp_i]
    _ = S.op.homologyπ ≫ (S.op.homologyι ≫ S.opcyclesOpIso.hom) := by
      rw [← Category.assoc, homology_π_ι, Category.assoc,
        op_pOpcycles_opcyclesOpIso_hom]

end CategoryTheory.ShortComplex

namespace HomologicalComplex

set_option backward.isDefEq.respectTransparency.types false in
private theorem homologyOp_zero_carrier
    {D : Type u₂} [Category.{v₂} D] [Abelian D] (K : CochainComplex D ℕ) :
    let Q : ChainComplex Dᵒᵖ ℕ := K.op
    let h : Q.homology 0 ≅ Opposite.op (K.homology 0) := K.homologyOp 0
    h.inv.unop ≫ (CochainComplex.isoHomologyπ₀ K).inv ≫ K.iCycles 0 =
      (ChainComplex.isoHomologyι₀ Q).inv.unop ≫ (Q.pOpcycles 0).unop := by
  let Q : ChainComplex Dᵒᵖ ℕ := K.op
  let h : Q.homology 0 ≅ Opposite.op (K.homology 0) := K.homologyOp 0
  let eπ := CochainComplex.isoHomologyπ₀ K
  let eι := ChainComplex.isoHomologyι₀ Q
  change h.inv.unop ≫ eπ.inv ≫ K.iCycles 0 = eι.inv.unop ≫ (Q.pOpcycles 0).unop
  have hc : h.hom ≫ eπ.hom.op = eι.hom ≫ (K.opcyclesOpIso 0).hom :=
    ShortComplex.homologyOpIso_hom_homologyπ_op (K.sc 0)
  apply Quiver.Hom.op_inj
  simp only [op_comp, Quiver.Hom.op_unop, Category.assoc]
  change (K.iCycles 0).op ≫ eπ.inv.op ≫ h.inv = Q.pOpcycles 0 ≫ eι.inv
  have hL : ((K.iCycles 0).op ≫ eπ.inv.op ≫ h.inv) ≫
      (h.hom ≫ eπ.hom.op) = (K.iCycles 0).op := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← op_comp, Iso.hom_inv_id, op_id, Category.comp_id]
  have hR : (Q.pOpcycles 0 ≫ eι.inv) ≫ (h.hom ≫ eπ.hom.op) = (K.iCycles 0).op := by
    rw [Category.assoc, hc, Iso.inv_hom_id_assoc]
    exact ShortComplex.op_pOpcycles_opcyclesOpIso_hom (K.sc 0)
  apply (cancel_mono (h.hom ≫ eπ.hom.op)).1
  exact hL.trans hR.symm

end HomologicalComplex

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C,D` be abelian, with injective resolutions in `C` and
projective resolutions in `Cᵒᵖ`, and `F : C → D` additive.
The canonical map `F(X) → R⁰F(X)`, followed by right-derived opposite
duality, equals the unop of `L₀(Fᵒᵖ)(Xᵒᵖ) → Fᵒᵖ(Xᵒᵖ)`. -/
theorem toRightDerivedZero_rightDerivedOpIso [HasProjectiveResolutions Cᵒᵖ]
    (F : C ⥤ D) [F.Additive] (X : C) :
    F.toRightDerivedZero.app X ≫ ((F.rightDerivedOpIso 0).app X).hom =
      (F.op.fromLeftDerivedZero.app (Opposite.op X)).unop := by
  let J : InjectiveResolution X := injectiveResolution X
  let P : ProjectiveResolution (Opposite.op X) := injectiveResolutionOpProj J
  let K : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  let i : X ⟶ J.cocomplex.X 0 := J.ι.f 0
  let a : Opposite.op (J.cocomplex.X 0) ⟶ Opposite.op X := P.π.f 0
  let Q : ChainComplex Dᵒᵖ ℕ := (F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  let h : Q.homology 0 ≅ Opposite.op (K.homology 0) := K.homologyOp 0
  let eπ : K.cycles 0 ≅ K.homology 0 := CochainComplex.isoHomologyπ₀ K
  let eι : Q.homology 0 ≅ Q.opcycles 0 := ChainComplex.isoHomologyι₀ Q
  let j : F.obj X ⟶ K.cycles 0 := J.toRightDerivedZero' F
  let p : Q.opcycles 0 ⟶ Opposite.op (F.obj X) := P.fromLeftDerivedZero' F.op
  let eR : (F.rightDerived 0).obj X ≅ K.homology 0 := J.isoRightDerivedObj F 0
  let eL : (F.op.leftDerived 0).obj (Opposite.op X) ≅ Q.homology 0 :=
    P.isoLeftDerivedObj F.op 0
  let m : Opposite.unop (Q.homology 0) ⟶ K.X 0 := eι.inv.unop ≫ (Q.pOpcycles 0).unop
  have hm : m = h.inv.unop ≫ eπ.inv ≫ K.iCycles 0 :=
    (HomologicalComplex.homologyOp_zero_carrier K).symm
  have hH : h.hom.unop ≫ h.inv.unop = 𝟙 _ := by
    simpa only [unop_comp, unop_id] using congrArg Quiver.Hom.unop h.inv_hom_id
  have hι : eι.hom.unop ≫ eι.inv.unop = 𝟙 _ := by
    simpa only [unop_comp, unop_id] using congrArg Quiver.Hom.unop eι.inv_hom_id
  have hp : p.unop ≫ (Q.pOpcycles 0).unop = F.map i := by
    have hv := congrArg Quiver.Hom.unop
      (ProjectiveResolution.pOpcycles_comp_fromLeftDerivedZero' P F.op)
    simp only [unop_comp] at hv
    change p.unop ≫ (Q.pOpcycles 0).unop = F.map a.unop at hv
    have hP : a = i.op ≫ 𝟙 (Opposite.op X) := rfl
    have ha : a.unop = i := by
      rw [hP, unop_comp, unop_id, Category.id_comp, Quiver.Hom.unop_op]
    exact hv.trans (congrArg F.map ha)
  have hA : (j ≫ eπ.hom ≫ h.hom.unop) ≫ m = F.map i := by
    rw [hm]
    simp only [Category.assoc]
    rw [← Category.assoc h.hom.unop, hH, Category.id_comp, Iso.hom_inv_id_assoc]
    exact J.toRightDerivedZero'_comp_iCycles F
  have hB : (p.unop ≫ eι.hom.unop) ≫ m = F.map i := by
    change (p.unop ≫ eι.hom.unop) ≫ (eι.inv.unop ≫ (Q.pOpcycles 0).unop) = _
    rw [Category.assoc, ← Category.assoc eι.hom.unop, hι, Category.id_comp]
    exact hp
  have hmMono : Mono m :=
    mono_comp' (unop_mono_of_epi eι.inv) (unop_mono_of_epi (Q.pOpcycles 0))
  have hBase : j ≫ eπ.hom ≫ h.hom.unop = p.unop ≫ eι.hom.unop := by
    apply (cancel_mono m).1
    exact hA.trans hB.symm
  rw [J.toRightDerivedZero_eq F, P.fromLeftDerivedZero_eq F.op]
  change (j ≫ eπ.hom ≫ eR.inv) ≫ (eR.hom ≫ h.hom.unop ≫ eL.hom.unop) =
    (eL.hom ≫ eι.hom ≫ p).unop
  simp only [Category.assoc, Iso.inv_hom_id_assoc, unop_comp]
  simpa only [Category.assoc] using congrArg (fun t => t ≫ eL.hom.unop) hBase

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. Let
`ι : X[0] → I` be a quasi-isomorphism of nonnegative cochain complexes
with `R^(j+1)F(I^q)=0` for every `q,j`. The canonical map `F(X) → R⁰F(X)`, followed by the acyclic
comparison, `H⁰(F(I)) ≅ Z⁰(F(I))`, and the cycle inclusion into
`F(I⁰)`, equals the mapped coaugmentation `F(ι⁰)`. -/
theorem toRightDerivedZero_acyclicComparison_coaugmentation
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) :
    F.toRightDerivedZero.app X ≫
        (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI 0).hom ≫
          (CochainComplex.isoHomologyπ₀
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I)).inv ≫
              ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).iCycles 0 =
      F.map (ι.f 0) := by
  let : HasProjectiveResolutions Cᵒᵖ :=
    { out Z := ⟨⟨injectiveResolutionOpProj (injectiveResolution Z.unop)⟩⟩ }
  let : PreservesFiniteColimits F.op := preservesFiniteColimits_op F
  let J : ChainComplex Cᵒᵖ ℕ := I.op
  let O := HomologicalComplex.opFunctor C (ComplexShape.up ℕ)
  let π : J ⟶ (ChainComplex.single₀ Cᵒᵖ).obj (Opposite.op X) :=
    O.map ι.op ≫ (single₀OpIso X).hom
  have hπ : QuasiIso π := by
    have h₁ : QuasiIso (O.map ι.op) :=
      (HomologicalComplex.quasiIso_opFunctor_map_iff _).mpr inferInstance
    have h₂ : QuasiIso (single₀OpIso X).hom := by
      let _ : IsIso (single₀OpIso X).hom := (single₀OpIso X).isIso_hom
      exact quasiIso_of_isIso _
    exact quasiIso_comp _ _ (hφ := h₁) (hφ' := h₂)
  have hπ0 : QuasiIsoAt π 0 := hπ.quasiIsoAt 0
  have hIop : ∀ q j : ℕ, IsZero ((F.op.leftDerived (j + 1)).obj (J.X q)) := by
    intro q j
    change IsZero ((F.op.leftDerived (j + 1)).obj (Opposite.op (I.X q)))
    have hu : IsZero (Opposite.unop
        ((F.op.leftDerived (j + 1)).obj (Opposite.op (I.X q)))) :=
      (hI q j).of_iso ((F.rightDerivedOpIso (j + 1)).app (I.X q)).symm
    exact hu.op
  let K : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I
  let Q : ChainComplex Dᵒᵖ ℕ := (F.op.mapHomologicalComplex (ComplexShape.down ℕ)).obj J
  let h : Q.homology 0 ≅ Opposite.op (K.homology 0) := K.homologyOp 0
  let eπ : K.cycles 0 ≅ K.homology 0 := CochainComplex.isoHomologyπ₀ K
  let eι : Q.homology 0 ≅ Q.opcycles 0 := ChainComplex.isoHomologyι₀ Q
  let eA : Q.homology 0 ≅ Opposite.op (F.obj X) :=
    @ChainComplex.homologyZeroIsoOfPreservedAugmentation
      _ _ _ _ _ _ J (Opposite.op X) F.op _ π hπ0 _
  let eL : (F.op.leftDerived 0).obj (Opposite.op X) ≅ Q.homology 0 :=
    @leftDerivedObjIsoHomologyOfAcyclicResolution _ _ _ _ _ _ _ F.op _ _ _ J π hπ hIop 0
  let q := eL ≪≫ h
  let i : X ⟶ I.X 0 := ι.f 0
  let a : Opposite.op (I.X 0) ⟶ Opposite.op X := π.f 0
  have ha : a.unop = i := by
    have hP : a = i.op ≫ 𝟙 (Opposite.op X) := rfl
    rw [hP, unop_comp, unop_id, Category.id_comp, Quiver.Hom.unop_op]
  have hQuota : eA.hom.unop ≫ eι.inv.unop ≫ (Q.pOpcycles 0).unop = F.map i := by
    have hv := congrArg Quiver.Hom.unop
      (@ChainComplex.pOpcycles_homologyZeroIsoOfPreservedAugmentation_hom
        _ _ _ _ _ _ J (Opposite.op X) F.op _ π hπ0 _)
    simp only [unop_comp, Category.assoc] at hv
    change eA.hom.unop ≫ eι.inv.unop ≫ (Q.pOpcycles 0).unop = F.map a.unop at hv
    exact hv.trans (congrArg F.map ha)
  have hCarrier : h.inv.unop ≫ eπ.inv ≫ K.iCycles 0 =
      eι.inv.unop ≫ (Q.pOpcycles 0).unop :=
    HomologicalComplex.homologyOp_zero_carrier K
  have heL : eL = (F.op.leftDerivedZeroIsoSelf.app (Opposite.op X)) ≪≫ eA.symm := by
    change (@leftDerivedObjIsoHomologyOfAcyclicResolution
      _ _ _ _ _ _ _ F.op _ _ _ J π hπ hIop 0) = _
    rw [leftDerivedObjIsoHomologyOfAcyclicResolution]
    rfl
  have hFrom : eL.inv ≫ F.op.fromLeftDerivedZero.app (Opposite.op X) = eA.hom := by
    rw [heL]
    change (eA.hom ≫ (F.op.leftDerivedZeroIsoSelf.app (Opposite.op X)).inv) ≫
      F.op.fromLeftDerivedZero.app (Opposite.op X) = eA.hom
    have h0 : (F.op.leftDerivedZeroIsoSelf.app (Opposite.op X)).inv ≫
        F.op.fromLeftDerivedZero.app (Opposite.op X) = 𝟙 (Opposite.op (F.obj X)) :=
      (F.op.leftDerivedZeroIsoSelf.app (Opposite.op X)).inv_hom_id
    rw [Category.assoc, h0, Category.comp_id]
  have hFromU : (F.op.fromLeftDerivedZero.app (Opposite.op X)).unop ≫ eL.inv.unop =
      eA.hom.unop := congrArg Quiver.Hom.unop hFrom
  have he : (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI 0).hom =
      ((F.rightDerivedOpIso 0).app X).hom ≫ q.inv.unop := by
    change ((F.rightDerivedOpIso 0).app X).hom ≫
        (((h.inv ≫
          ((HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) 0).map (𝟙 Q)))) ≫
            eL.inv).unop = _
    let H := HomologicalComplex.homologyFunctor Dᵒᵖ (ComplexShape.down ℕ) 0
    have hid : H.map (𝟙 Q) = 𝟙 (H.obj Q) := H.map_id Q
    exact (congrArg (fun t => ((F.rightDerivedOpIso 0).app X).hom ≫
      (((h.inv ≫ t) ≫ eL.inv).unop)) hid).trans
        (congrArg (fun t => ((F.rightDerivedOpIso 0).app X).hom ≫ (t ≫ eL.inv).unop)
          (Category.comp_id h.inv))
  have hTo : F.toRightDerivedZero.app X ≫
      (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI 0).hom =
        eA.hom.unop ≫ h.inv.unop := by
    rw [he, ← Category.assoc, toRightDerivedZero_rightDerivedOpIso]
    change (F.op.fromLeftDerivedZero.app (Opposite.op X)).unop ≫
      (h.inv ≫ eL.inv).unop = eA.hom.unop ≫ h.inv.unop
    rw [unop_comp, ← Category.assoc, hFromU]
  change F.toRightDerivedZero.app X ≫
      (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI 0).hom ≫
        eπ.inv ≫ K.iCycles 0 = F.map i
  calc
    F.toRightDerivedZero.app X ≫
        (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI 0).hom ≫ eπ.inv ≫ K.iCycles 0 =
        (eA.hom.unop ≫ h.inv.unop) ≫ (eπ.inv ≫ K.iCycles 0) := by
      rw [← Category.assoc, hTo]
    _ = eA.hom.unop ≫ (h.inv.unop ≫ eπ.inv ≫ K.iCycles 0) := by
      simp only [Category.assoc]
    _ = eA.hom.unop ≫ (eι.inv.unop ≫ (Q.pOpcycles 0).unop) :=
      congrArg (fun t => eA.hom.unop ≫ t) hCarrier
    _ = F.map i := hQuota

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive and preserving finite limits. Let
`ι : X[0] → I` be a quasi-isomorphism of nonnegative cochain complexes
with `R^(j+1)F(I^q)=0` for every `q,j`. The composite `R⁰F(X) → H⁰(F(I)) ≅ Z⁰(F(I)) → F(I⁰)`
is the canonical degree-zero identification `R⁰F(X) → F(X)`
followed by `F(ι⁰)`. -/
theorem rightDerivedAcyclicComparison_zero_coaugmentation
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]
    (hI : ∀ q j : ℕ, IsZero ((F.rightDerived (j + 1)).obj (I.X q))) :
    (F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI 0).hom ≫
        (CochainComplex.isoHomologyπ₀
          ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I)).inv ≫
            ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).iCycles 0 =
      F.rightDerivedZeroIsoSelf.hom.app X ≫ F.map (ι.f 0) := by
  let K : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I
  let e : (F.rightDerived 0).obj X ≅ K.homology 0 :=
    F.rightDerivedObjIsoHomologyOfAcyclicResolution I ι hI 0
  let c : (F.rightDerived 0).obj X ≅ F.obj X := F.rightDerivedZeroIsoSelf.app X
  let p : K.cycles 0 ≅ K.homology 0 := CochainComplex.isoHomologyπ₀ K
  let i : X ⟶ I.X 0 := ι.f 0
  change e.hom ≫ p.inv ≫ K.iCycles 0 = c.hom ≫ F.map i
  have hp : c.inv ≫ e.hom ≫ p.inv ≫ K.iCycles 0 = F.map i :=
    toRightDerivedZero_acyclicComparison_coaugmentation F I ι hI
  apply (cancel_epi c.inv).1
  calc
    c.inv ≫ (e.hom ≫ p.inv ≫ K.iCycles 0) = F.map i := hp
    _ = c.inv ≫ (c.hom ≫ F.map i) := by
      rw [← Category.assoc, c.inv_hom_id, Category.id_comp]

end CategoryTheory.Functor
