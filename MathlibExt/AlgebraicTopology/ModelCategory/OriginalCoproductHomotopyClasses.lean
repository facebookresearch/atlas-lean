/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CoproductWeakEquivalences
public import Mathlib.AlgebraicTopology.ModelCategory.FundamentalLemma

/-!
# Original coproduct Hom functions in the homotopy category

The original cofan injections identify maps out of a cofibrant coproduct with
the full product of homotopy classes. A single actual good path object supplies
all component homotopies, so the complete coproduct descent gives the reverse
function and the original source maps remain explicit.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v w uH vH

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.OriginalCoproductHomotopyClasses

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {J : Type w} {X : J → C} [∀ j, IsCofibrant (X j)]
  (c : Cofan X) (hc : IsColimit c) {Y : C} [IsFibrant Y]

include hc in
/-- Every full caller coproduct homotopy is tested on all of its original injections. -/
theorem rightHomotopyRel_iff {f g : c.pt ⟶ Y} :
    RightHomotopyRel f g ↔ ∀ j, RightHomotopyRel (c.inj j ≫ f) (c.inj j ≫ g) := by
  constructor
  · intro h j
    exact h.precomp (c.inj j)
  · intro h
    obtain ⟨P, hP⟩ := PathObject.exists_very_good Y
    let _ : P.IsVeryGood := hP
    let homotopies (j : J) : P.RightHomotopy (c.inj j ≫ f) (c.inj j ≫ g) :=
      (h j).rightHomotopy P
    let q : c.pt ⟶ P.P := Cofan.IsColimit.desc hc (fun j => (homotopies j).h)
    let homotopy : P.RightHomotopy f g :=
      { h := q
        h₀ := by
          apply hc.hom_ext
          intro j
          change c.inj j.as ≫ q ≫ P.p₀ = c.inj j.as ≫ f
          rw [← CategoryTheory.Category.assoc, Cofan.IsColimit.fac]
          exact (homotopies j.as).h₀
        h₁ := by
          apply hc.hom_ext
          intro j
          change c.inj j.as ≫ q ≫ P.p₁ = c.inj j.as ≫ g
          rw [← CategoryTheory.Category.assoc, Cofan.IsColimit.fac]
          exact (homotopies j.as).h₁ }
    exact homotopy.rightHomotopyRel

/-- The original full forward Hom function restricts every class along the actual cofan leg. -/
def restrict (h : RightHomotopyClass c.pt Y) : ∀ j, RightHomotopyClass (X j) Y :=
  fun j => h.precomp (c.inj j)

include hc in
/-- The full original cofan Hom function is injective on homotopy classes. -/
theorem restrict_injective : Function.Injective (restrict c (Y := Y)) := by
  intro a b h
  obtain ⟨f, rfl⟩ := RightHomotopyClass.mk_surjective a
  obtain ⟨g, rfl⟩ := RightHomotopyClass.mk_surjective b
  apply (RightHomotopyClass.mk_eq_mk_iff f g).mpr
  apply (rightHomotopyRel_iff c hc).mpr
  intro j
  exact (RightHomotopyClass.mk_eq_mk_iff _ _).mp (congrFun h j)

omit [∀ j, IsCofibrant (X j)] [IsFibrant Y] in
include hc in
/-- Every entire family of original component classes descends through the same caller cofan. -/
theorem restrict_surjective : Function.Surjective (restrict c (Y := Y)) := by
  intro a
  choose f hf using (fun j => RightHomotopyClass.mk_surjective (a j))
  refine ⟨RightHomotopyClass.mk (Cofan.IsColimit.desc hc f), ?_⟩
  funext j
  change RightHomotopyClass.mk (c.inj j ≫ Cofan.IsColimit.desc hc f) = a j
  rw [Cofan.IsColimit.fac]
  exact hf j

/-- The complete original coproduct Hom equivalence retains all component classes and both
functions. -/
def homotopyClassEquiv : RightHomotopyClass c.pt Y ≃ ∀ j, RightHomotopyClass (X j) Y :=
  Equiv.ofBijective (restrict c) ⟨restrict_injective c hc, restrict_surjective c hc⟩

variable {H : Type uH} [Category.{vH} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)]

/-- The actual localization identifies the full caller coproduct Hom with every original component
Hom. -/
def localizedHomEquiv : (L.obj c.pt ⟶ L.obj Y) ≃ ∀ j, L.obj (X j) ⟶ L.obj Y := by
  let _ : IsCofibrant c.pt := originalCofanPoint_cofibrant c hc
  let e : RightHomotopyClass c.pt Y ≃ (L.obj c.pt ⟶ L.obj Y) :=
    Equiv.ofBijective (rightHomotopyClassToHom L) (bijective_rightHomotopyClassToHom L c.pt Y)
  let es (j : J) : RightHomotopyClass (X j) Y ≃ (L.obj (X j) ⟶ L.obj Y) :=
    Equiv.ofBijective (rightHomotopyClassToHom L) (bijective_rightHomotopyClassToHom L (X j) Y)
  exact e.symm.trans ((homotopyClassEquiv c hc).trans (Equiv.piCongrRight es))

/-- The full localized forward function is the original precomposition by every caller injection. -/
theorem localizedHomEquiv_apply (g : L.obj c.pt ⟶ L.obj Y) (j : J) :
    localizedHomEquiv c hc L g j = L.map (c.inj j) ≫ g := by
  let _ : IsCofibrant c.pt := originalCofanPoint_cofibrant c hc
  obtain ⟨g, rfl⟩ := map_surjective_of_isLocalization L c.pt Y g
  change rightHomotopyClassToHom L
      ((homotopyClassEquiv c hc)
        ((Equiv.ofBijective (rightHomotopyClassToHom L)
          (bijective_rightHomotopyClassToHom L c.pt Y)).symm (L.map g)) j) =
    L.map (c.inj j) ≫ L.map g
  have h : (Equiv.ofBijective (rightHomotopyClassToHom L)
      (bijective_rightHomotopyClassToHom L c.pt Y)).symm (L.map g) = RightHomotopyClass.mk g := by
    apply (Equiv.ofBijective (rightHomotopyClassToHom L)
      (bijective_rightHomotopyClassToHom L c.pt Y)).injective
    rw [Equiv.apply_symm_apply]
    rfl
  rw [h]
  change L.map (c.inj j ≫ g) = L.map (c.inj j) ≫ L.map g
  exact L.map_comp _ _

/-- The complete inverse Hom function restricts along each original coproduct injection. -/
theorem localizedHomEquiv_symm_injection
    (g : ∀ j, L.obj (X j) ⟶ L.obj Y) (j : J) :
    L.map (c.inj j) ≫ (localizedHomEquiv c hc L (Y := Y)).symm g = g j := by
  exact (localizedHomEquiv_apply c hc L ((localizedHomEquiv c hc L (Y := Y)).symm g) j).symm.trans
    (congrFun ((localizedHomEquiv c hc L (Y := Y)).apply_symm_apply g) j)

end HomotopicalAlgebra.OriginalCoproductHomotopyClasses

namespace HomotopicalAlgebra.OriginalDerivedCoproduct

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {J : Type w} [HasCoproductsOfShape J C] (X : J → C)

/-- The actual derived coproduct uses every original chosen cofibrant resolution. -/
def object : C := ∐ fun j => CofibrantObject.HoCat.resolutionObj (X j)

/-- The full comparison to the unchanged original coproduct retains every original counit. -/
def comparison : object X ⟶ ∐ X :=
  Limits.Sigma.map (fun j => CofibrantObject.HoCat.pResolutionObj (X j))

/-- Every original summand counit remains the corresponding comparison component. -/
theorem comparison_injection (j : J) :
    Limits.Sigma.ι (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j ≫ comparison X =
      CofibrantObject.HoCat.pResolutionObj (X j) ≫ Limits.Sigma.ι X j :=
  Limits.Sigma.ι_map _ j

/-- The entire derived coproduct map retains every original chosen resolution map. -/
def map {Y : J → C} (f : ∀ j, X j ⟶ Y j) : object X ⟶ object Y :=
  Limits.Sigma.map (fun j => CofibrantObject.HoCat.resolutionMap (f j))

/-- The comparison square keeps both original coproduct maps and all resolution factor equations. -/
theorem map_comparison {Y : J → C} (f : ∀ j, X j ⟶ Y j) :
    map X f ≫ comparison Y = comparison X ≫ Limits.Sigma.map f := by
  change (Limits.Sigma.map (fun j => CofibrantObject.HoCat.resolutionMap (f j))) ≫
      Limits.Sigma.map (fun j => CofibrantObject.HoCat.pResolutionObj (Y j)) =
    (Limits.Sigma.map (fun j => CofibrantObject.HoCat.pResolutionObj (X j))) ≫ Limits.Sigma.map f
  apply Limits.Sigma.hom_ext
  intro j
  calc
    _ = CofibrantObject.HoCat.resolutionMap (f j) ≫
        Limits.Sigma.ι (fun a => CofibrantObject.HoCat.resolutionObj (Y a)) j ≫
        Limits.Sigma.map (fun a => CofibrantObject.HoCat.pResolutionObj (Y a)) :=
      Limits.Sigma.ι_map_assoc _ _ _
    _ = CofibrantObject.HoCat.resolutionMap (f j) ≫
        CofibrantObject.HoCat.pResolutionObj (Y j) ≫ Limits.Sigma.ι Y j :=
      congrArg (fun h => CofibrantObject.HoCat.resolutionMap (f j) ≫ h)
        (Limits.Sigma.ι_map (fun a => CofibrantObject.HoCat.pResolutionObj (Y a)) j)
    _ = CofibrantObject.HoCat.pResolutionObj (X j) ≫ f j ≫ Limits.Sigma.ι Y j := by
      rw [CofibrantObject.HoCat.resolutionMap_fac_assoc]
    _ = _ := by
      calc
        _ = CofibrantObject.HoCat.pResolutionObj (X j) ≫
            Limits.Sigma.ι X j ≫ Limits.Sigma.map f :=
          congrArg (fun h => CofibrantObject.HoCat.pResolutionObj (X j) ≫ h)
            (Limits.Sigma.ι_map f j).symm
        _ = _ := (Limits.Sigma.ι_map_assoc
          (fun a => CofibrantObject.HoCat.pResolutionObj (X a)) j (Limits.Sigma.map f)).symm

/-- Every original component weak equivalence induces a weak map of the full derived coproduct. -/
theorem map_weakEquivalence {Y : J → C} (f : ∀ j, X j ⟶ Y j)
    [∀ j, WeakEquivalence (f j)] : WeakEquivalence (map X f) := by
  let _ : ∀ j, WeakEquivalence (CofibrantObject.HoCat.resolutionMap (f j)) :=
    fun j => (CofibrantObject.HoCat.weakEquivalence_resolutionMap_iff (f j)).mpr inferInstance
  exact weakEquivalence_sigmaMap_of_cofibrant
    (fun j => CofibrantObject.HoCat.resolutionMap (f j))

variable {H : Type uH} [Category.{vH} H] (L : C ⥤ H)
  [L.IsLocalization (weakEquivalences C)] {Y : C} [IsFibrant Y]

/-- The complete derived coproduct Hom family uses every unchanged original target Hom. -/
def homEquiv : (L.obj (object X) ⟶ L.obj Y) ≃ ∀ j, L.obj (X j) ⟶ L.obj Y := by
  let Q (j : J) := CofibrantObject.HoCat.resolutionObj (X j)
  let c : Cofan Q := Cofan.mk (∐ Q) (Limits.Sigma.ι Q)
  let hc : IsColimit c := coproductIsCoproduct Q
  let e (j : J) : L.obj (Q j) ≅ L.obj (X j) := by
    let _ : IsIso (L.map (CofibrantObject.HoCat.pResolutionObj (X j))) :=
      Localization.inverts L (weakEquivalences C) _ (by
        rw [← weakEquivalence_iff]
        infer_instance)
    exact asIso (L.map (CofibrantObject.HoCat.pResolutionObj (X j)))
  exact (OriginalCoproductHomotopyClasses.localizedHomEquiv c hc L).trans
    (Equiv.piCongrRight (fun j => Iso.homCongr (e j) (Iso.refl (L.obj Y))))

/-- The derived Hom function retains each full original resolution map and coproduct injection. -/
theorem homEquiv_resolution_projection (f : L.obj (object X) ⟶ L.obj Y) (j : J) :
    L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫ homEquiv X L f j =
      L.map (Limits.Sigma.ι (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j) ≫ f := by
  let Q (a : J) := CofibrantObject.HoCat.resolutionObj (X a)
  let c : Cofan Q := Cofan.mk (∐ Q) (Limits.Sigma.ι Q)
  let hc : IsColimit c := coproductIsCoproduct Q
  let _ : IsIso (L.map (CofibrantObject.HoCat.pResolutionObj (X j))) :=
    Localization.inverts L (weakEquivalences C) _ (by
      rw [← weakEquivalence_iff]
      infer_instance)
  dsimp only [homEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Iso.homCongr]
  change L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫
      (inv (L.map (CofibrantObject.HoCat.pResolutionObj (X j))) ≫
        OriginalCoproductHomotopyClasses.localizedHomEquiv c hc L f j ≫ 𝟙 (L.obj Y)) = _
  rw [CategoryTheory.Category.comp_id]
  rw [IsIso.hom_inv_id_assoc]
  exact OriginalCoproductHomotopyClasses.localizedHomEquiv_apply c hc L f j

/-- The complete derived inverse Hom function has the actual source-resolution components. -/
theorem homEquiv_symm_resolution_injection
    (g : ∀ j, L.obj (X j) ⟶ L.obj Y) (j : J) :
    L.map (Limits.Sigma.ι (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j) ≫
        (homEquiv X L (Y := Y)).symm g =
      L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫ g j := by
  exact (homEquiv_resolution_projection X L ((homEquiv X L (Y := Y)).symm g) j).symm.trans
    (congrArg (fun k => L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫ k)
      (congrFun ((homEquiv X L (Y := Y)).apply_symm_apply g) j))

/-- The full derived map restricts to precomposition by each unchanged original component arrow. -/
theorem homEquiv_map {X' : J → C} (f : ∀ j, X j ⟶ X' j)
    (g : L.obj (object X') ⟶ L.obj Y) (j : J) :
    homEquiv X L (L.map (map X f) ≫ g) j = L.map (f j) ≫ homEquiv X' L g j := by
  let _ : IsIso (L.map (CofibrantObject.HoCat.pResolutionObj (X j))) :=
    Localization.inverts L (weakEquivalences C) _ (by
      rw [← weakEquivalence_iff]
      infer_instance)
  have hι : Limits.Sigma.ι
      (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j ≫ map X f =
      CofibrantObject.HoCat.resolutionMap (f j) ≫ Limits.Sigma.ι
        (fun a => CofibrantObject.HoCat.resolutionObj (X' a)) j :=
    Limits.Sigma.ι_map (fun a => CofibrantObject.HoCat.resolutionMap (f a)) j
  have hLι : L.map (Limits.Sigma.ι
        (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j) ≫ L.map (map X f) =
      L.map (CofibrantObject.HoCat.resolutionMap (f j)) ≫ L.map (Limits.Sigma.ι
        (fun a => CofibrantObject.HoCat.resolutionObj (X' a)) j) :=
    (L.map_comp _ _).symm.trans ((congrArg L.map hι).trans (L.map_comp _ _))
  have hLp : L.map (CofibrantObject.HoCat.resolutionMap (f j)) ≫
      L.map (CofibrantObject.HoCat.pResolutionObj (X' j)) =
      L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫ L.map (f j) :=
    (L.map_comp _ _).symm.trans
      ((congrArg L.map (CofibrantObject.HoCat.resolutionMap_fac (f j))).trans (L.map_comp _ _))
  apply (cancel_epi (L.map (CofibrantObject.HoCat.pResolutionObj (X j)))).mp
  calc
    _ = L.map (Limits.Sigma.ι
        (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j) ≫
          (L.map (map X f) ≫ g) := homEquiv_resolution_projection X L _ j
    _ = (L.map (CofibrantObject.HoCat.resolutionMap (f j)) ≫ L.map (Limits.Sigma.ι
        (fun a => CofibrantObject.HoCat.resolutionObj (X' a)) j)) ≫ g :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun h => h ≫ g) hLι)
    _ = L.map (CofibrantObject.HoCat.resolutionMap (f j)) ≫
        (L.map (CofibrantObject.HoCat.pResolutionObj (X' j)) ≫ homEquiv X' L g j) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun h => L.map (CofibrantObject.HoCat.resolutionMap (f j)) ≫ h)
          (homEquiv_resolution_projection X' L g j).symm)
    _ = L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫
        (L.map (f j) ≫ homEquiv X' L g j) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (fun h => h ≫ homEquiv X' L g j) hLp).trans (Category.assoc _ _ _))

/-- Every component's full localized Hom bijection gives the same bijection for the actual derived
coproduct map. -/
theorem map_precomp_bijective {X' : J → C} (f : ∀ j, X j ⟶ X' j)
    (hf : ∀ j, Function.Bijective
      (fun g : L.obj (X' j) ⟶ L.obj Y => L.map (f j) ≫ g)) :
    Function.Bijective
      (fun g : L.obj (object X') ⟶ L.obj Y => L.map (map X f) ≫ g) := by
  constructor
  · intro g g' h
    apply (homEquiv X' L (Y := Y)).injective
    funext j
    apply (hf j).1
    change L.map (f j) ≫ homEquiv X' L g j = L.map (f j) ≫ homEquiv X' L g' j
    exact (homEquiv_map X L f g j).symm.trans
      ((congrArg (fun k => homEquiv X L k j) h).trans (homEquiv_map X L f g' j))
  · intro g
    choose k hk using fun j => (hf j).2 (homEquiv X L g j)
    refine ⟨(homEquiv X' L (Y := Y)).symm k, ?_⟩
    apply (homEquiv X L (Y := Y)).injective
    funext j
    rw [homEquiv_map, Equiv.apply_symm_apply]
    exact hk j

omit [IsFibrant Y] in
/-- The full derived coproduct Hom equivalence retains every original target via its actual fibrant
unit. -/
def allTargetHomEquiv : (L.obj (object X) ⟶ L.obj Y) ≃ ∀ j, L.obj (X j) ⟶ L.obj Y := by
  let R := FibrantObject.HoCat.resolutionObj Y
  let unit : Y ⟶ R := FibrantObject.HoCat.iResolutionObj Y
  let _ : IsIso (L.map unit) := Localization.inverts L (weakEquivalences C) unit (by
    rw [← weakEquivalence_iff]
    infer_instance)
  let e : L.obj Y ≅ L.obj R := asIso (L.map unit)
  exact (Iso.homCongr (Iso.refl (L.obj (object X))) e).trans
    ((homEquiv X L (Y := R)).trans
      (Equiv.piCongrRight (fun j => Iso.homCongr (Iso.refl (L.obj (X j))) e.symm)))

omit [IsFibrant Y] in
/-- At every target, the full Hom function retains the original resolution and coproduct legs. -/
theorem allTargetHomEquiv_resolution_projection (f : L.obj (object X) ⟶ L.obj Y) (j : J) :
    L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫ allTargetHomEquiv X L f j =
      L.map (Limits.Sigma.ι (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j) ≫ f := by
  let R := FibrantObject.HoCat.resolutionObj Y
  let unit : Y ⟶ R := FibrantObject.HoCat.iResolutionObj Y
  let _ : IsIso (L.map unit) := Localization.inverts L (weakEquivalences C) unit (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp only [allTargetHomEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply,
    Equiv.coe_fn_mk, Iso.homCongr, Iso.refl_inv, Iso.refl_hom,
    Iso.symm_hom, asIso_hom, asIso_inv, Category.id_comp, Pi.map]
  rw [← Category.assoc, homEquiv_resolution_projection]
  let injection : L.obj (CofibrantObject.HoCat.resolutionObj (X j)) ⟶ L.obj (object X) :=
    L.map (Limits.Sigma.ι (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j)
  change (injection ≫ (f ≫ L.map unit)) ≫ inv (L.map unit) = injection ≫ f
  exact (Category.assoc injection (f ≫ L.map unit) (inv (L.map unit))).trans
    (congrArg (fun k => injection ≫ k)
      ((Category.assoc f (L.map unit) (inv (L.map unit))).trans
        ((congrArg (fun k => f ≫ k) (IsIso.hom_inv_id (L.map unit))).trans
          (Category.comp_id f))))

omit [IsFibrant Y] in
/-- At every target, the inverse Hom function retains all original resolution and coproduct legs. -/
theorem allTargetHomEquiv_symm_resolution_injection
    (g : ∀ j, L.obj (X j) ⟶ L.obj Y) (j : J) :
    L.map (Limits.Sigma.ι (fun a => CofibrantObject.HoCat.resolutionObj (X a)) j) ≫
        (allTargetHomEquiv X L (Y := Y)).symm g =
      L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫ g j := by
  exact (allTargetHomEquiv_resolution_projection X L
    ((allTargetHomEquiv X L (Y := Y)).symm g) j).symm.trans
      (congrArg (fun k => L.map (CofibrantObject.HoCat.pResolutionObj (X j)) ≫ k)
        (congrFun ((allTargetHomEquiv X L (Y := Y)).apply_symm_apply g) j))

omit [IsFibrant Y] in
/-- The complete all-target Hom function commutes with every original derived component map. -/
theorem allTargetHomEquiv_map {X' : J → C} (f : ∀ j, X j ⟶ X' j)
    (g : L.obj (object X') ⟶ L.obj Y) (j : J) :
    allTargetHomEquiv X L (L.map (map X f) ≫ g) j =
      L.map (f j) ≫ allTargetHomEquiv X' L g j := by
  let R := FibrantObject.HoCat.resolutionObj Y
  let unit : Y ⟶ R := FibrantObject.HoCat.iResolutionObj Y
  let _ : IsIso (L.map unit) := Localization.inverts L (weakEquivalences C) unit (by
    rw [← weakEquivalence_iff]
    infer_instance)
  simp only [allTargetHomEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply,
    Equiv.coe_fn_mk, Iso.homCongr, Iso.refl_inv, Iso.refl_hom,
    Iso.symm_hom, asIso_hom, asIso_inv, Category.id_comp, Pi.map]
  rw [Category.assoc, homEquiv_map]
  exact Category.assoc _ _ _

omit [IsFibrant Y] in
/-- Original component Hom bijections induce the full derived coproduct Hom bijection at every
target. -/
theorem allTarget_map_precomp_bijective {X' : J → C} (f : ∀ j, X j ⟶ X' j)
    (hf : ∀ j, Function.Bijective
      (fun g : L.obj (X' j) ⟶ L.obj Y => L.map (f j) ≫ g)) :
    Function.Bijective
      (fun g : L.obj (object X') ⟶ L.obj Y => L.map (map X f) ≫ g) := by
  constructor
  · intro g g' h
    apply (allTargetHomEquiv X' L (Y := Y)).injective
    funext j
    apply (hf j).1
    change L.map (f j) ≫ allTargetHomEquiv X' L g j =
      L.map (f j) ≫ allTargetHomEquiv X' L g' j
    exact (allTargetHomEquiv_map X L f g j).symm.trans
      ((congrArg (fun k => allTargetHomEquiv X L k j) h).trans
        (allTargetHomEquiv_map X L f g' j))
  · intro g
    choose k hk using fun j => (hf j).2 (allTargetHomEquiv X L g j)
    refine ⟨(allTargetHomEquiv X' L (Y := Y)).symm k, ?_⟩
    apply (allTargetHomEquiv X L (Y := Y)).injective
    funext j
    rw [allTargetHomEquiv_map, Equiv.apply_symm_apply]
    exact hk j

end HomotopicalAlgebra.OriginalDerivedCoproduct
