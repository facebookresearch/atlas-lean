/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_
tensorSectionsBilin_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_
tensorSectionsBilin_monoidalV2.lean`,
`Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean`,
`Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_locallyTrivial.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.AlgebraicGeometry.Modules.Monoidal
public import MathlibExt.AlgebraicGeometry.Modules.IsFrameOn
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Restrict
import MathlibExt.Algebra.Category.ModuleCat.PresheafTensorFormulae
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Sections of a tensor product of invertible sheaves

For sheaves of modules `L` and `M` on a scheme `X` and an open `U`, sections `s` of `L` and `t`
of `M` over `U` give a section `tensorSections s t` of `L ⊗ M` over `U`; this is bilinear over
`Γ(X, U)` (`Scheme.Modules.tensorSectionsBilin`). When `L` and `M` are invertible (`IsLineBundle`)
and `U` is affine, the induced map `Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) → Γ(L ⊗ M, U)` is bijective
(`IsLineBundle.bijective_lift_tensorSectionsBilin`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Opposite TensorProduct TopologicalSpace
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries (IsLineBundle structureModule)

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Hom

variable (L M : X.Modules)

/-- **Presheaf tensor product to sheaf tensor product.** The canonical map from the presheaf
tensor product to the sheaf tensor product. -/
def tensorSectionsHom : L.val ⊗ M.val ⟶
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).obj (L ⊗ M) :=
  (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (L.val ⊗ M.val) ≫
    (SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property).map (tensorIsoSheafify L M).hom

end Hom

section Sections

variable {L M : X.Modules} {U : X.Opens}

/-- **Tensor product of sections.** The section of `L ⊗ M` over `U` given by sections `s` of `L`
and `t` of `M`. Through `tensorIsoSheafify` it is
`MathlibExt.AlgebraicGeometry.SheafTensorSections.tensorSection`, which is stated for
`Scheme.{0}` and lands in `SchemeModulesTensor.moduleTensor`. -/
def tensorSections (s : Γ(L, U)) (t : Γ(M, U)) : Γ(L ⊗ M, U) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M, U))
    ((tensorSectionsHom L M).app (op U)).hom
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))

private lemma tensorSections_def (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s t = DFunLike.coe (α := ((L.val ⊗ M.val).obj (op U) :)) (β := fun _ => Γ(L ⊗ M,
      U))
      ((tensorSectionsHom L M).app (op U)).hom
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))) := rfl

lemma tensorSections_add_left (s s' : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (s + s') t = tensorSections s t + tensorSections s' t := by
  rw [tensorSections_def, tensorSections_def, tensorSections_def]
  erw [TensorProduct.add_tmul, map_add]
  rfl

lemma tensorSections_add_right (s : Γ(L, U)) (t t' : Γ(M, U)) :
    tensorSections s (t + t') = tensorSections s t + tensorSections s t' := by
  rw [tensorSections_def, tensorSections_def, tensorSections_def]
  erw [TensorProduct.tmul_add, map_add]
  rfl

lemma tensorSections_smul_left (g : Γ(X, U)) (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections (g • s) t = g • tensorSections s t := by
  rw [tensorSections_def, tensorSections_def]
  let : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  erw [← TensorProduct.smul_tmul', LinearMap.map_smul]
  rfl

lemma tensorSections_smul_right (g : Γ(X, U)) (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSections s (g • t) = g • tensorSections s t := by
  rw [tensorSections_def, tensorSections_def]
  let : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  erw [TensorProduct.tmul_smul, LinearMap.map_smul]
  rfl

variable (L M U) in
/-- **Bilinear tensor product of sections.** `tensorSections` as a `Γ(X, U)`-bilinear map. -/
def tensorSectionsBilin : Γ(L, U) →ₗ[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U) :=
  LinearMap.mk₂ Γ(X, U) tensorSections tensorSections_add_left tensorSections_smul_left
    tensorSections_add_right tensorSections_smul_right

@[simp] lemma tensorSectionsBilin_apply (s : Γ(L, U)) (t : Γ(M, U)) :
    tensorSectionsBilin L M U s t = tensorSections s t := rfl

lemma map_tensorSections {V : X.Opens} (i : V ⟶ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ⊗ M).presheaf.map i.op (tensorSections s t) =
      tensorSections (L.presheaf.map i.op s) (M.presheaf.map i.op t) := by
  rw [tensorSections_def, tensorSections_def]
  have h := PresheafOfModules.naturality_apply (tensorSectionsHom L M) i.op
    ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))
  erw [_root_.PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul] at h
  exact h.symm

lemma map_homOfLE_tensorSections {V : X.Opens} (h : V ≤ U) (s : Γ(L, U)) (t : Γ(M, U)) :
    (L ⊗ M).presheaf.map (homOfLE h).op (tensorSections s t) =
      tensorSections (L.presheaf.map (homOfLE h).op s) (M.presheaf.map (homOfLE h).op t) :=
  map_tensorSections (homOfLE h) s t

end Sections

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

namespace FrameTensor

variable {X : Scheme.{u}}

private lemma bijective_smul_tmul {R : Type*} [CommRing R] {A B : Type*} [AddCommGroup A]
  [AddCommGroup B]
    [Module R A] [Module R B] (a : A) (b : B)
    (ha : Function.Bijective fun r : R => r • a) (hb : Function.Bijective fun r : R => r • b) :
    Function.Bijective fun r : R => r • (a ⊗ₜ[R] b) := by
  let eA : R ≃ₗ[R] A := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R A a) ha
  let eB : R ≃ₗ[R] B := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B b) hb
  let e : R ≃ₗ[R] A ⊗[R] B := (TensorProduct.lid R R).symm ≪≫ₗ TensorProduct.congr eA eB
  have he : (fun r : R => r • (a ⊗ₜ[R] b)) = e := by
    funext r
    change r • (a ⊗ₜ[R] b) = TensorProduct.congr eA eB ((TensorProduct.lid R R).symm r)
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul, LinearEquiv.ofBijective_apply,
      LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply,
        LinearMap.toSpanSingleton_apply,
      one_smul, TensorProduct.tmul_smul]
  rw [he]
  exact e.bijective

section locbij

variable (L M : X.Modules)

private def tsApp (W : X.Opens) (z : (L.val ⊗ M.val).obj (op W)) : Γ(L ⊗ M, W) :=
  DFunLike.coe (α := ((L.val ⊗ M.val).obj (op W) :)) (β := fun _ => Γ(L ⊗ M, W))
    ((tensorSectionsHom L M).app (op W)).hom z

variable {L M}

private lemma tensorSections_eq_tsApp {W : X.Opens} (s : Γ(L, W)) (t : Γ(M, W)) :
    Modules.tensorSections s t = tsApp L M W ((s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)] (t : M.val.obj (op
      W))) :=
  rfl

private lemma tsApp_smul {W : X.Opens} (g : Γ(X, W)) (z : (L.val ⊗ M.val).obj (op W)) :
    tsApp L M W (g • z) = g • tsApp L M W z := by
  exact ((tensorSectionsHom L M).app (op W)).hom.map_smul g z

private lemma tsApp_add {W : X.Opens} (z z' : (L.val ⊗ M.val).obj (op W)) :
    tsApp L M W (z + z') = tsApp L M W z + tsApp L M W z' := by
  exact ((tensorSectionsHom L M).app (op W)).hom.map_add z z'

private lemma map_tsApp {W W' : X.Opens} (i : W' ⟶ W) (z : (L.val ⊗ M.val).obj (op W)) :
    (L ⊗ M).presheaf.map i.op (tsApp L M W z) = tsApp L M W' ((L.val ⊗ M.val).map i.op z) :=
  (PresheafOfModules.naturality_apply (tensorSectionsHom L M) i.op z).symm

private lemma map_smul_tmul {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) (s : Γ(L, W)) (t : Γ(M, W))
  :
    (L.val ⊗ M.val).map i.op (g • ((s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)] (t : M.val.obj (op W)))) =
      X.presheaf.map i.op g • ((L.presheaf.map i.op s : L.val.obj (op W')) ⊗ₜ[Γ(X, W')]
        (M.presheaf.map i.op t : M.val.obj (op W'))) := by
  erw [PresheafOfModules.map_smul, _root_.PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
  rfl

variable (L M) in
private lemma W_tensorSectionsHom :
    (Opens.grothendieckTopology X).W ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M))
      := by
  dsimp only [tensorSectionsHom]
  rw [Functor.map_comp]
  apply MorphismProperty.comp_mem
  · erw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact GrothendieckTopology.W_toSheafify _ _
  · exact MorphismProperty.of_isIso _ _

private instance isLocallySurjective_tensorSectionsHom : Presheaf.IsLocallySurjective
  (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) :=
  (((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).1 (W_tensorSectionsHom L M)).2

private instance isLocallyInjective_tensorSectionsHom : Presheaf.IsLocallyInjective
  (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) :=
  (((Opens.grothendieckTopology X).W_iff_isLocallyBijective _).1 (W_tensorSectionsHom L M)).1

private lemma exists_local_preimage {W : X.Opens} (y : Γ(L ⊗ M, W)) {x : X} (hx : x ∈ W) :
    ∃ (W' : X.Opens) (i : W' ⟶ W), x ∈ W' ∧ ∃ z : (L.val ⊗ M.val).obj (op W'),
      tsApp L M W' z = (L ⊗ M).presheaf.map i.op y := by
  have h := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) y
  obtain ⟨W', i, ⟨z, hz⟩, hxW'⟩ := h x hx
  exact ⟨W', i, hxW', z, hz⟩

private lemma exists_local_eq {W : X.Opens} (z₁ z₂ : (L.val ⊗ M.val).obj (op W))
    (h : tsApp L M W z₁ = tsApp L M W z₂) {x : X} (hx : x ∈ W) :
    ∃ (W' : X.Opens) (i : W' ⟶ W), x ∈ W' ∧ (L.val ⊗ M.val).map i.op z₁ = (L.val ⊗ M.val).map i.op
      z₂ := by
  have hm := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    ((PresheafOfModules.toPresheaf _).map (tensorSectionsHom L M)) z₁ z₂ h
  obtain ⟨W', i, hi, hxW'⟩ := hm x hx
  exact ⟨W', i, hxW', hi⟩

end locbij

section restrict

private lemma image_preimage_of_le {W W₂ : X.Opens} (h : W₂ ≤ W) :
    W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) = W₂ := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

end restrict

section smulHom

variable {N : X.Modules} {W : X.Opens} {τ : Γ(N, W)}

private lemma bijective_smul_map_iff_of_eq {A B : X.Opens} (q : A = B) (τ : Γ(N, B)) :
    (Function.Bijective fun a : Γ(X, A) => a • N.presheaf.map (homOfLE q.le).op τ) ↔
      Function.Bijective fun g : Γ(X, B) => g • τ := by
  subst q
  have e : N.presheaf.map (homOfLE (le_refl A)).op τ = τ := by
    rw [show (homOfLE (le_refl A) : A ⟶ A) = 𝟙 A from rfl, op_id, N.presheaf.map_id]
    rfl
  simp only [e]

private lemma bijective_smul_of_isIso (h : IsIso (smulSectionHom W τ)) :
    Function.Bijective fun g : Γ(X, W) => g • τ := by
  have e : ⇑(ConcreteCategory.hom ((smulSectionHom W τ).app ⊤)) =
      (N.restrictAppIso W.ι ⊤).inv ∘
        (fun g : Γ(X, W.ι ''ᵁ ⊤) => g • N.presheaf.map (homOfLE (W.ι_image_le ⊤)).op τ) ∘
        (W.ι.appIso ⊤).inv :=
    funext (smulSectionHom_app_apply W τ ⊤)
  have hb := ConcreteCategory.bijective_of_isIso ((smulSectionHom W τ).app ⊤)
  rw [e, Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso _),
    Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso _)] at hb
  exact (bijective_smul_map_iff_of_eq (Scheme.Opens.ι_image_top W) τ).1 hb

end smulHom

section main

variable {L M : X.Modules} {U V : X.Opens} {s : Γ(L, U)} {t : Γ(M, U)}

private lemma bijective_smul_tmul_res (hs : IsFrameOn s V) (ht : IsFrameOn t V) {W : X.Opens}
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) =>
      g • ((L.presheaf.map (homOfLE hWU).op s : L.val.obj (op W)) ⊗ₜ[Γ(X, W)]
        (M.presheaf.map (homOfLE hWU).op t : M.val.obj (op W))) :=
  bijective_smul_tmul (R := Γ(X, W)) _ _ (hs hWU hWV) (ht hWU hWV)

variable (W : X.Opens) (hWU : W ≤ U)

private abbrev resL (W' : X.Opens) (h : W' ≤ W) : Γ(L, W') := L.presheaf.map (homOfLE (h.trans
  hWU)).op s

private abbrev resM (W' : X.Opens) (h : W' ≤ W) : Γ(M, W') := M.presheaf.map (homOfLE (h.trans
  hWU)).op t

private abbrev τW : Γ(L ⊗ M, W) :=
  Modules.tensorSections (L.presheaf.map (homOfLE hWU).op s) (M.presheaf.map (homOfLE hWU).op t)

private lemma map_τW (W' : X.Opens) (h : W' ≤ W) :
    (L ⊗ M).presheaf.map (homOfLE h).op (τW (s := s) (t := t) W hWU) =
      tsApp L M W' ((resL (s := s) W hWU W' h : L.val.obj (op W')) ⊗ₜ[Γ(X, W')]
        (resM (t := t) W hWU W' h : M.val.obj (op W'))) := by
  dsimp only [τW]
  rw [map_homOfLE_tensorSections, tensorSections_eq_tsApp]
  congr 2
  · change (L.presheaf.map _ ≫ L.presheaf.map _) s = _
    rw [← L.presheaf.map_comp]
    rfl
  · change (M.presheaf.map _ ≫ M.presheaf.map _) t = _
    rw [← M.presheaf.map_comp]
    rfl

private theorem isIso_smulSectionHom (hs : IsFrameOn s V) (ht : IsFrameOn t V) (hWV : W ≤ V) :
    IsIso (smulSectionHom W (τW (s := s) (t := t) W hWU)) := by
  set ψ := smulSectionHom W (τW (s := s) (t := t) W hWU)
  let J := Opens.grothendieckTopology ((W : X.Opens) : Scheme.{u})
  have pre_le : ∀ (W' : (W : Scheme.{u}).Opens) (W₂ : X.Opens), W₂ ≤ W.ι ''ᵁ W' → W.ι ⁻¹ᵁ W₂ ≤ W'
    := by
    intro W' W₂ h₂ w hw
    obtain ⟨w', hw', hww'⟩ := h₂ hw
    rwa [← W.ι.isOpenEmbedding.injective hww']
  have hsurj : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    rintro W' y
    refine fun x hx => ?_
    have hx' : W.ι.base x ∈ W.ι ''ᵁ W' := ⟨x, hx, rfl⟩
    obtain ⟨W₂, i₂, hxW₂, z, hz⟩ := exists_local_preimage (L := L) (M := M) y hx'
    have h₂W : W₂ ≤ W := i₂.le.trans (W.ι_image_le W')
    obtain ⟨g, hg⟩ := (bijective_smul_tmul_res hs ht (h₂W.trans hWU) (h₂W.trans hWV)).2 z
    dsimp only at hg
    have e₃ : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) ≤ W₂ := (image_preimage_of_le h₂W).le
    refine ⟨W.ι ⁻¹ᵁ W₂, homOfLE (pre_le W' W₂ i₂.le),
      ⟨(W.ι.appIso _).hom (X.presheaf.map (homOfLE e₃).op g), ?_⟩, hxW₂⟩
    have key : g • (L ⊗ M).presheaf.map (homOfLE h₂W).op (τW (s := s) (t := t) W hWU) =
        (L ⊗ M).presheaf.map i₂.op y := by
      rw [map_τW, ← tsApp_smul]
      exact (congrArg (tsApp L M W₂) hg).trans hz
    have key' := congrArg ((L ⊗ M).presheaf.map (homOfLE e₃).op) key
    rw [Scheme.Modules.map_smul] at key'
    change ψ.app (W.ι ⁻¹ᵁ W₂) ((W.ι.appIso _).hom (X.presheaf.map (homOfLE e₃).op g)) =
      (L ⊗ M).presheaf.map (W.ι.opensFunctor.map (homOfLE (pre_le W' W₂ i₂.le))).op y
    rw [smulSectionHom_app_apply, Iso.hom_inv_id_apply]
    change X.presheaf.map (homOfLE e₃).op g •
        (L ⊗ M).presheaf.map (homOfLE (W.ι_image_le (W.ι ⁻¹ᵁ W₂))).op
          (τW (s := s) (t := t) W hWU) = _
    convert key' using 2
    · change _ = ((L ⊗ M).presheaf.map _ ≫ (L ⊗ M).presheaf.map _) _
      rw [← (L ⊗ M).presheaf.map_comp]
      rfl
    · change _ = ((L ⊗ M).presheaf.map _ ≫ (L ⊗ M).presheaf.map _) _
      rw [← (L ⊗ M).presheaf.map_comp]
      rfl
  have hinj : Presheaf.IsLocallyInjective J ((SheafOfModules.toSheaf _).map ψ).hom := by
    constructor
    intro W' a b hab
    refine fun x hx => ?_
    have hab₀ : ψ.app W'.unop a = ψ.app W'.unop b := hab
    rw [smulSectionHom_app_apply, smulSectionHom_app_apply] at hab₀
    have hab' := (ConcreteCategory.bijective_of_isIso
      ((L ⊗ M).restrictAppIso W.ι W'.unop).inv).1 hab₀
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at hab'
    rw [map_τW, ← tsApp_smul, ← tsApp_smul] at hab'
    have hx' : W.ι.base x ∈ W.ι ''ᵁ W'.unop := ⟨x, hx, rfl⟩
    obtain ⟨W₂, i₂, hxW₂, h₂⟩ := exists_local_eq _ _ hab' hx'
    have h₂W : W₂ ≤ W := i₂.le.trans (W.ι_image_le W'.unop)
    erw [map_smul_tmul, map_smul_tmul] at h₂
    have h₃ : X.presheaf.map i₂.op (show Γ(X, W.ι ''ᵁ W'.unop) from a) =
        X.presheaf.map i₂.op (show Γ(X, W.ι ''ᵁ W'.unop) from b) := by
      apply (bijective_smul_tmul_res hs ht (h₂W.trans hWU) (h₂W.trans hWV)).1
      convert h₂ using 2 <;>
      · congr 1
        all_goals first
          | (change _ = (L.presheaf.map _ ≫ L.presheaf.map _) s
             rw [← L.presheaf.map_comp]; rfl)
          | (change _ = (M.presheaf.map _ ≫ M.presheaf.map _) t
             rw [← M.presheaf.map_comp]; rfl)
    have e₃ : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) ≤ W₂ := (image_preimage_of_le h₂W).le
    refine ⟨W.ι ⁻¹ᵁ W₂, homOfLE (pre_le W'.unop W₂ i₂.le), ?_, hxW₂⟩
    have h₄ := congrArg (X.presheaf.map (homOfLE e₃).op) h₃
    change (X.presheaf.map _ ≫ X.presheaf.map _) a = (X.presheaf.map _ ≫ X.presheaf.map _) b at h₄
    rw [← X.presheaf.map_comp] at h₄
    exact h₄
  have h₁ : IsIso ((SheafOfModules.toSheaf _).map ψ) :=
    (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hinj, hsurj⟩
  refine Hom.isIso_iff_isIso_app.mpr fun W' => ?_
  change IsIso (((SheafOfModules.toSheaf _).map ψ).hom.app (op W'))
  infer_instance

end main

private theorem isFrameOn_tensorSections {L M : X.Modules} {U V : X.Opens} {s : Γ(L, U)} {t : Γ(M,
  U)}
    (hs : IsFrameOn s V) (ht : IsFrameOn t V) : IsFrameOn (Modules.tensorSections s t) V := by
  intro W hWU hWV
  have h := bijective_smul_of_isIso (isIso_smulSectionHom W hWU hs ht hWV)
  simp only [Modules.map_homOfLE_tensorSections]
  exact h

end FrameTensor

/-- **Tensor product of frames.** If sections `s` of `L` and `t` of `M` over the same open `U`
are frames on `V`, then `tensorSections s t` is a frame of `L ⊗ M` on `V`. -/
theorem IsFrameOn.tensorSections {X : Scheme.{u}} {L M : X.Modules} {U V : X.Opens} {s : Γ(L, U)}
    {t : Γ(M, U)} (hs : IsFrameOn s V) (ht : IsFrameOn t V) :
    IsFrameOn (Modules.tensorSections s t) V :=
  FrameTensor.isFrameOn_tensorSections hs ht

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

namespace FrameBridge

open FrameTensor

variable {X : Scheme.{u}} {U : X.Opens} {L : X.Modules}
  (e : L.restrict U.ι ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf)

-- The section of `L` over `U.ι ''ᵁ W` that the trivialization `e` sends to `1`.
private def gen (W : (U : Scheme.{u}).Opens) : Γ(L, U.ι ''ᵁ W) :=
  (L.restrictAppIso U.ι W).hom (e.inv.app W (1 : Γ(U, W)))

private lemma gen_spec (W : (U : Scheme.{u}).Opens) (r : Γ(U, W)) :
    (L.restrictAppIso U.ι W).hom (e.inv.app W r) = (U.ι.appIso W).inv r • gen e W := by
  have h : e.inv.app W r = r • e.inv.app W (1 : Γ(U, W)) := by
    rw [← Hom.app_smul]
    exact congrArg (e.inv.app W) (mul_one r).symm
  rw [h, gen, smul_restrictAppIso_hom_apply]

private lemma gen_bijective (W : (U : Scheme.{u}).Opens) :
    Function.Bijective fun b : Γ(X, U.ι ''ᵁ W) => b • gen e W := by
  have h : (fun b : Γ(X, U.ι ''ᵁ W) => b • gen e W) =
      (L.restrictAppIso U.ι W).hom ∘ e.inv.app W ∘ (U.ι.appIso W).hom := by
    funext b
    rw [Function.comp_apply, Function.comp_apply, gen_spec, Iso.hom_inv_id_apply]
  rw [h]
  exact (ConcreteCategory.bijective_of_isIso _).comp
    ((ConcreteCategory.bijective_of_isIso _).comp (ConcreteCategory.bijective_of_isIso _))

private lemma gen_map {W₁ W₂ : (U : Scheme.{u}).Opens} (i : W₁ ⟶ W₂) :
    L.presheaf.map (homOfLE (U.ι.image_mono i.le)).op (gen e W₂) = gen e W₁ := by
  have h1 : (structureModule (U : Scheme.{u})).presheaf.map i.op (1 : Γ(U, W₂)) =
      (1 : Γ(U, W₁)) :=
    ((U : Scheme.{u}).presheaf.map i.op).hom.map_one
  have hnat : e.inv.app W₁ (1 : Γ(U, W₁)) =
      (L.restrict U.ι).presheaf.map i.op (e.inv.app W₂ (1 : Γ(U, W₂))) := by
    rw [← h1]
    exact NatTrans.naturality_apply e.inv.mapPresheaf i.op _
  rw [gen, gen, hnat, map_restrictAppIso_hom_apply]

end FrameBridge

open FrameBridge FrameTensor in
/-- **Frames from trivializations.** If the pullback of `M` to an open `U` is isomorphic to the
structure sheaf of `U`, then `M` has a section over `U` that is a frame on `U`. -/
theorem exists_isFrameOn_of_pullback_iso_unit {X : Scheme.{u}} {M : X.Modules} (U : X.Opens)
    (eU : (Modules.pullback U.ι).obj M ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf) :
    ∃ s : Γ(M, U), IsFrameOn s U := by
  let e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
    (restrictFunctorIsoPullback U.ι).app M ≪≫ eU
  refine ⟨M.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).ge).op (gen e ⊤), ?_⟩
  intro W hWU _
  have q : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := image_preimage_of_le hWU
  have ht : M.presheaf.map (homOfLE q.le).op (M.presheaf.map (homOfLE hWU).op
      (M.presheaf.map (homOfLE (Scheme.Opens.ι_image_top U).ge).op (gen e ⊤))) =
      gen e (U.ι ⁻¹ᵁ W) := by
    rw [← gen_map e (homOfLE le_top : U.ι ⁻¹ᵁ W ⟶ ⊤)]
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  rw [← bijective_smul_map_iff_of_eq q, ht]
  exact gen_bijective e _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

namespace LocGlue

variable {X : Scheme.{u}} (M : X.Modules)

private noncomputable abbrev rM {V W : X.Opens} (h : V ≤ W) : Γ(M, W) → Γ(M, V) := fun y =>
  M.presheaf.map (homOfLE h).op y

private noncomputable abbrev rO {V W : X.Opens} (h : V ≤ W) : Γ(X, W) → Γ(X, V) := fun g =>
  X.presheaf.map (homOfLE h).op g

private theorem rM_rM {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (y : Γ(M, V₁)) :
    rM M h₃₂ (rM M h₂₁ y) = rM M (h₃₂.trans h₂₁) y := by
  change (M.presheaf.map (homOfLE h₂₁).op ≫ M.presheaf.map (homOfLE h₃₂).op) y = _
  rw [← Functor.map_comp]; rfl

omit M in
private theorem rO_rO {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (g : Γ(X, V₁)) :
    rO h₃₂ (rO h₂₁ g) = rO (h₃₂.trans h₂₁) g := by
  change (X.presheaf.map (homOfLE h₂₁).op ≫ X.presheaf.map (homOfLE h₃₂).op).hom g = _
  rw [← Functor.map_comp]; rfl

private theorem rM_smul {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (y : Γ(M, W)) :
    rM M h (g • y) = rO h g • rM M h y := M.map_smul _ _ _

private theorem rM_add {V W : X.Opens} (h : V ≤ W) (y z : Γ(M, W)) : rM M h (y + z) = rM M h y + rM
  M h z := map_add _ _ _
private theorem rM_sub {V W : X.Opens} (h : V ≤ W) (y z : Γ(M, W)) : rM M h (y - z) = rM M h y - rM
  M h z := map_sub _ _ _
private theorem rM_zero {V W : X.Opens} (h : V ≤ W) : rM M h (0 : Γ(M, W)) = 0 := map_zero _

omit M in
private theorem rO_pow {V W : X.Opens} (h : V ≤ W) (g : Γ(X, W)) (n : ℕ) : rO h (g ^ n) = rO h g ^
  n := map_pow _ _ _

private noncomputable def F : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩

private theorem eq_of_forall_rM_eq {ι : Type u} (W : ι → X.Opens) (V : X.Opens) (hWV : ∀ i, W i ≤ V)
    (hcov : V ≤ iSup W) (y z : Γ(M, V)) (h : ∀ i, rM M (hWV i) y = rM M (hWV i) z) : y = z :=
  TopCat.Sheaf.eq_of_locally_eq' (F M) W V (fun i => homOfLE (hWV i)) hcov y z h

private theorem exists_of_compatible {ι : Type u} (W : ι → X.Opens) (V : X.Opens) (hWV : ∀ i, W i ≤
  V)
    (hcov : V ≤ iSup W) (z : ∀ i, Γ(M, W i))
    (hz : ∀ i j, rM M (inf_le_left : W i ⊓ W j ≤ W i) (z i) = rM M (inf_le_right : W i ⊓ W j ≤ W j)
      (z j)) :
    ∃ y : Γ(M, V), ∀ i, rM M (hWV i) y = z i := by
  obtain ⟨y, hy, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F M) W V (fun i => homOfLE (hWV i)) hcov z
    (fun i j => hz i j)
  exact ⟨y, hy⟩

end LocGlue

open LocGlue

private def LocProp {X : Scheme.{u}} (M : X.Modules) (V : X.Opens) (g : Γ(X, V)) : Prop :=
  (∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, V)),
      M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
        = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
    ∧ (∀ y : Γ(M, V), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
        ∃ n : ℕ, (g ^ n : Γ(X, V)) • y = 0)

namespace LocGlue

variable {X : Scheme.{u}} (M : X.Modules)

private theorem pow_smul_eq_zero_of_le {V : X.Opens} (g : Γ(X, V)) (y : Γ(M, V)) {n k : ℕ} (hnk : n
  ≤ k)
    (h : (g ^ n : Γ(X, V)) • y = 0) : (g ^ k : Γ(X, V)) • y = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnk
  rw [add_comm, pow_add, mul_smul, h, smul_zero]

private theorem exists_of_le {V : X.Opens} (g : Γ(X, V)) (x : Γ(M, X.basicOpen g)) {n k : ℕ} (hnk :
  n ≤ k)
    (y : Γ(M, V)) (h : rM M (X.basicOpen_le g) y = rO (X.basicOpen_le g) (g ^ n) • x) :
    rM M (X.basicOpen_le g) ((g ^ (k - n) : Γ(X, V)) • y) = rO (X.basicOpen_le g) (g ^ k) • x := by
  rw [rM_smul, h, ← mul_smul, ← map_mul, ← pow_add, Nat.sub_add_cancel hnk]

end LocGlue

open LocGlue in
private theorem isLocalization_basicOpen_of_finite_basicOpen_cover'
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (s : Finset Γ(X, U.1))
    (hs : U.1 ≤ ⨆ h ∈ s, X.basicOpen h)
    (hloc : ∀ h ∈ s, ∀ g : Γ(X, X.basicOpen h),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, X.basicOpen h)),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, X.basicOpen h), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, X.basicOpen h)) • y = 0)))
    (hloc₂ : ∀ h ∈ s, ∀ h' ∈ s, ∀ g : Γ(X, X.basicOpen h ⊓ X.basicOpen h'),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h'))),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h')), M.presheaf.map (homOfLE (X.basicOpen_le
          g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, (X.basicOpen h ⊓ X.basicOpen h'))) • y = 0)))
    (f : Γ(X, U.1)) :
    ((∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, U.1)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, U.1), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, U.1)) • y = 0)) := by
  classical
  let ι : Type u := {h // h ∈ s}
  let D : ι → X.Opens := fun i => X.basicOpen i.1
  have hDU : ∀ i, D i ≤ U.1 := fun i => X.basicOpen_le _
  have hcovU : U.1 ≤ iSup D := by
    refine hs.trans ?_
    simp only [iSup_le_iff]
    intro h hh
    exact le_iSup D ⟨h, hh⟩
  let W : ι → X.Opens := fun i => X.basicOpen (rO (hDU i) f)
  have hW_eq : ∀ i, W i = D i ⊓ X.basicOpen f := fun i => X.basicOpen_res f (homOfLE (hDU i)).op
  have hWD : ∀ i, W i ≤ D i := fun i => X.basicOpen_le _
  have hWf : ∀ i, W i ≤ X.basicOpen f := fun i => by rw [hW_eq]; exact inf_le_right
  have hcovf : X.basicOpen f ≤ iSup W := by
    intro p hp
    have hpU : p ∈ (iSup D : X.Opens) := hcovU (X.basicOpen_le f hp)
    rw [Opens.mem_iSup] at hpU ⊢
    obtain ⟨i, hi⟩ := hpU
    exact ⟨i, by rw [hW_eq]; exact ⟨hi, hp⟩⟩
  refine ⟨?_, ?_⟩
  · intro x
    have step1 : ∀ i, ∃ (n : ℕ) (yi : Γ(M, D i)),
        rM M (hWD i) yi = rO (hWD i) (rO (hDU i) f ^ n) • rM M (hWf i) x :=
      fun i => (hloc i.1 i.2 (rO (hDU i) f)).1 (rM M (hWf i) x)
    choose n0 y0 hy0 using step1
    let n : ℕ := Finset.univ.sup n0
    obtain ⟨y1, hy1⟩ : ∃ y1 : ∀ i, Γ(M, D i),
        ∀ i, rM M (hWD i) (y1 i) = rO ((hWD i).trans (hDU i)) f ^ n • rM M (hWf i) x := by
      refine ⟨fun i => (rO (hDU i) f ^ (n - n0 i) : Γ(X, D i)) • y0 i, fun i => ?_⟩
      have := exists_of_le M (rO (hDU i) f) (rM M (hWf i) x) (Finset.le_sup (f := n0)
        (Finset.mem_univ i))
        (y0 i) (hy0 i)
      rw [rO_pow, rO_rO] at this
      exact this
    have step2 : ∀ ij : ι × ι, ∃ m : ℕ,
        (rO ((inf_le_left : D ij.1 ⊓ D ij.2 ≤ D ij.1).trans (hDU ij.1)) f ^ m : Γ(X, D ij.1 ⊓ D
          ij.2))
          • (rM M inf_le_left (y1 ij.1) - rM M inf_le_right (y1 ij.2)) = 0 := by
      rintro ⟨i, j⟩
      have hg : rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f = rO (inf_le_left : D i ⊓ D j
        ≤ D i) (rO (hDU i) f) :=
        (rO_rO _ _ f).symm
      have hg' : rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f = rO (inf_le_right : D i ⊓ D
        j ≤ D j) (rO (hDU j) f) :=
        (rO_rO _ _ f).symm
      have hWij_i : X.basicOpen (rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f) ≤ W i := by
        rw [hg, X.basicOpen_res (rO (hDU i) f) (homOfLE (inf_le_left : D i ⊓ D j ≤ D i)).op]; exact
          inf_le_right
      have hWij_j : X.basicOpen (rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f) ≤ W j := by
        rw [hg', X.basicOpen_res (rO (hDU j) f) (homOfLE (inf_le_right : D i ⊓ D j ≤ D j)).op];
          exact inf_le_right
      apply (hloc₂ i.1 i.2 j.1 j.2 (rO ((inf_le_left : D i ⊓ D j ≤ D i).trans (hDU i)) f)).2
      change rM M (X.basicOpen_le _) (rM M inf_le_left (y1 i) - rM M inf_le_right (y1 j)) = 0
      rw [rM_sub, rM_rM, rM_rM]
      have hi : rM M ((X.basicOpen_le _).trans inf_le_left) (y1 i) = rM M hWij_i (rM M (hWD i) (y1
        i)) := by
        rw [rM_rM]
      have hj : rM M ((X.basicOpen_le _).trans inf_le_right) (y1 j) = rM M hWij_j (rM M (hWD j) (y1
        j)) := by
        rw [rM_rM]
      rw [hi, hj, hy1, hy1]
      simp only [rM_smul, rM_rM, rO_pow, rO_rO, sub_self]
    choose m0 hm0 using step2
    let m : ℕ := Finset.univ.sup m0
    obtain ⟨z, hzdef⟩ : ∃ z : ∀ i, Γ(M, D i), ∀ i, z i = (rO (hDU i) f ^ m : Γ(X, D i)) • y1 i :=
      ⟨fun i => (rO (hDU i) f ^ m : Γ(X, D i)) • y1 i, fun i => rfl⟩
    have hz : ∀ i j, rM M (inf_le_left : D i ⊓ D j ≤ D i) (z i) = rM M (inf_le_right : D i ⊓ D j ≤
      D j) (z j) := by
      intro i j
      rw [hzdef, hzdef, rM_smul, rM_smul, rO_pow, rO_pow, rO_rO, rO_rO, ← sub_eq_zero, ← smul_sub]
      exact pow_smul_eq_zero_of_le M _ _ (Finset.le_sup (f := m0) (Finset.mem_univ (i, j))) (hm0
        (i, j))
    obtain ⟨y, hy⟩ := exists_of_compatible M D U.1 hDU hcovU z hz
    refine ⟨m + n, y, ?_⟩
    apply eq_of_forall_rM_eq M W (X.basicOpen f) hWf hcovf
    intro i
    change rM M (hWf i) (rM M (X.basicOpen_le f) y) = rM M (hWf i) (rO (X.basicOpen_le f) (f ^ (m +
      n)) • x)
    have : rM M (hWf i) (rM M (X.basicOpen_le f) y) = rM M (hWD i) (rM M (hDU i) y) := by rw
      [rM_rM, rM_rM]
    rw [this, hy, hzdef, rM_smul, hy1, rM_smul]
    simp only [rO_pow, rO_rO, ← mul_smul, ← pow_add]
  · intro y hy
    have step : ∀ i, ∃ n : ℕ, (rO (hDU i) f ^ n : Γ(X, D i)) • rM M (hDU i) y = 0 := by
      intro i
      apply (hloc i.1 i.2 (rO (hDU i) f)).2
      change rM M (hWD i) (rM M (hDU i) y) = 0
      have : rM M (hWD i) (rM M (hDU i) y) = rM M (hWf i) (rM M (X.basicOpen_le f) y) := by rw
        [rM_rM, rM_rM]
      rw [this]
      change rM M (hWf i) (M.presheaf.map (homOfLE (X.basicOpen_le f)).op y) = 0
      rw [hy, rM_zero]
    choose nOf hnOf using step
    refine ⟨Finset.univ.sup nOf, ?_⟩
    apply eq_of_forall_rM_eq M D U.1 hDU hcovU
    intro i
    rw [rM_smul, rM_zero, rO_pow]
    exact pow_smul_eq_zero_of_le M _ _ (Finset.le_sup (f := nOf) (Finset.mem_univ i)) (hnOf i)

namespace LocGlue

variable {X : Scheme.{u}} (M : X.Modules)

private theorem locProp_of_isFrameOn {V : X.Opens} {s : Γ(M, V)} (hs : IsFrameOn s V) {W : X.Opens}
    (hW : IsAffineOpen W) (hWV : W ≤ V) (g : Γ(X, W)) : LocProp M W g := by
  have := hW.isLocalization_basicOpen g
  have hD : X.basicOpen g ≤ V := (X.basicOpen_le g).trans hWV
  have hres : ∀ a : Γ(X, W), rM M (X.basicOpen_le g) (a • rM M hWV s) =
      rO (X.basicOpen_le g) a • rM M hD s := by
    intro a
    rw [rM_smul, rM_rM]
  constructor
  · intro x
    obtain ⟨b, rfl⟩ := (hs hD hD).2 x
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hab⟩ := IsLocalization.surj (Submonoid.powers g) b
    refine ⟨n, a • rM M hWV s, ?_⟩
    change rM M (X.basicOpen_le g) (a • rM M hWV s) =
      rO (X.basicOpen_le g) (g ^ n) • (b • rM M hD s)
    rw [hres, ← mul_smul]
    congr 1
    change b * rO (X.basicOpen_le g) (g ^ n) = rO (X.basicOpen_le g) a at hab
    rw [mul_comm]
    exact hab.symm
  · intro y hy
    obtain ⟨a, rfl⟩ := (hs hWV hWV).2 y
    change rM M (X.basicOpen_le g) (a • rM M hWV s) = 0 at hy
    rw [hres] at hy
    have h0 : algebraMap Γ(X, W) Γ(X, X.basicOpen g) a = 0 := by
      apply (hs hD hD).1
      change rO (X.basicOpen_le g) a • rM M hD s = (0 : Γ(X, X.basicOpen g)) • rM M hD s
      rw [hy, zero_smul]
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers g)] at h0
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := h0
    refine ⟨n, ?_⟩
    change (g ^ n : Γ(X, W)) • (a • rM M hWV s) = 0
    rw [← mul_smul, hn, zero_smul]

end LocGlue

open LocGlue in
private theorem isLocalization_basicOpen_of_locallyFramed {X : Scheme.{u}} (M : X.Modules)
    (hfr : ∀ x : X, ∃ (V : X.Opens) (s : Γ(M, V)), x ∈ V ∧ IsFrameOn s V)
    (U : X.affineOpens) (f : Γ(X, U.1)) : LocProp M U.1 f := by
  classical
  have hbasis : ∀ x : U.1, ∃ (h : Γ(X, U.1)) (V : X.Opens) (s : Γ(M, V)),
      IsFrameOn s V ∧ (x : X) ∈ X.basicOpen h ∧ X.basicOpen h ≤ V := by
    intro x
    obtain ⟨V, s, hxV, hs⟩ := hfr x
    obtain ⟨h, hhV, hxh⟩ := U.2.exists_basicOpen_le ⟨(x : X), hxV⟩ x.2
    exact ⟨h, V, s, hs, hxh, hhV⟩
  choose hOf VOf sOf hsOf hxh hhV using hbasis
  have hcov : (U.1 : Set X) ⊆ ⋃ x : U.1, (X.basicOpen (hOf x) : Set X) := fun p hp =>
    Set.mem_iUnion.mpr ⟨⟨p, hp⟩, hxh ⟨p, hp⟩⟩
  obtain ⟨t, ht⟩ := U.2.isCompact.elim_finite_subcover
    (fun x : U.1 => (X.basicOpen (hOf x) : Set X)) (fun x => (X.basicOpen (hOf x)).isOpen) hcov
  let s : Finset Γ(X, U.1) := t.image hOf
  have hs : U.1 ≤ ⨆ h ∈ s, X.basicOpen h := by
    intro p hp
    have := ht hp
    simp only [Set.mem_iUnion] at this
    obtain ⟨x, hxt, hpx⟩ := this
    apply Opens.mem_iSup.mpr
    exact ⟨hOf x, Opens.mem_iSup.mpr ⟨Finset.mem_image_of_mem hOf hxt, hpx⟩⟩
  have hmem : ∀ h ∈ s, ∃ x ∈ t, hOf x = h := fun h hh => by simpa [s] using hh
  refine isLocalization_basicOpen_of_finite_basicOpen_cover' M U s hs ?_ ?_ f
  · intro h hh g
    obtain ⟨x, -, rfl⟩ := hmem h hh
    exact locProp_of_isFrameOn M (hsOf x) (U.2.basicOpen _) (hhV x) g
  · intro h hh h' hh' g
    obtain ⟨x, -, rfl⟩ := hmem h hh
    have haff : IsAffineOpen (X.basicOpen (hOf x) ⊓ X.basicOpen h') := by
      have := (U.2.basicOpen (hOf x)).basicOpen
        (X.presheaf.map (homOfLE (X.basicOpen_le (hOf x))).op h')
      rwa [Scheme.basicOpen_res] at this
    exact locProp_of_isFrameOn M (hsOf x) haff (inf_le_left.trans (hhV x)) g

namespace TensorSectionsAux

variable {X : Scheme.{u}}

section BasicOpen

variable (N : X.Modules) (U : X.Opens) (f : Γ(X, U))

@[reducible] private def modBO : Module Γ(X, U) Γ(N, X.basicOpen f) :=
  Module.compHom Γ(N, X.basicOpen f) (algebraMap Γ(X, U) Γ(X, X.basicOpen f))

attribute [local instance] modBO

private instance isScalarTower_modBO : IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(N, X.basicOpen
  f) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private def resBO : Γ(N, U) →ₗ[Γ(X, U)] Γ(N, X.basicOpen f) where
  toFun := N.presheaf.map (homOfLE (X.basicOpen_le f)).op
  map_add' x y := map_add _ x y
  map_smul' a x := Scheme.Modules.map_smul N (homOfLE (X.basicOpen_le f)) a x

private theorem resBO_apply (x : Γ(N, U)) : resBO N U f x = N.presheaf.map (homOfLE (X.basicOpen_le
  f)).op x := rfl

private theorem isLocalizedModule_resBO
    (hN : ∀ x : X, ∃ (V : X.Opens) (s : Γ(N, V)), x ∈ V ∧ IsFrameOn s V) (hU : IsAffineOpen U) :
    IsLocalizedModule (Submonoid.powers f) (resBO N U f) := by
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  obtain ⟨h1, h2⟩ :=
    isLocalization_basicOpen_of_locallyFramed N hN ⟨U, hU⟩ f
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen f) (f ^ n)) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow n
    have := hu.smul_bijective (β := Γ(N, X.basicOpen f))
    convert this using 1
  · intro y
    obtain ⟨n, x, hx⟩ := h1 y
    exact ⟨⟨x, ⟨f ^ n, n, rfl⟩⟩, hx.symm⟩
  · intro x₁ x₂ h
    have h0 : N.presheaf.map (homOfLE (X.basicOpen_le f)).op (x₁ - x₂) = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr h
    obtain ⟨n, hn⟩ := h2 (x₁ - x₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
    exact hn

end BasicOpen

attribute [local instance] modBO

section Theta

variable (L M : X.Modules)

private abbrev theta (U : X.Opens) : Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U) :=
  TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U)

private theorem theta_tmul (U : X.Opens) (s : Γ(L, U)) (t : Γ(M, U)) :
    theta L M U (s ⊗ₜ t) = Scheme.Modules.tensorSections s t := by
  simp [theta]

variable (U : X.Opens) (f : Γ(X, U))

private def thetaBO : Γ(L, X.basicOpen f) ⊗[Γ(X, U)] Γ(M, X.basicOpen f) →ₗ[Γ(X, U)] Γ(L ⊗ M,
  X.basicOpen f) :=
  TensorProduct.lift
    (LinearMap.mk₂ Γ(X, U) (fun x y => Scheme.Modules.tensorSections x y)
      (fun x₁ x₂ y => Scheme.Modules.tensorSections_add_left x₁ x₂ y)
      (fun a x y => by
        rw [← algebraMap_smul Γ(X, X.basicOpen f) a x, Scheme.Modules.tensorSections_smul_left,
          algebraMap_smul])
      (fun x y₁ y₂ => Scheme.Modules.tensorSections_add_right x y₁ y₂)
      (fun a x y => by
        rw [← algebraMap_smul Γ(X, X.basicOpen f) a y, Scheme.Modules.tensorSections_smul_right,
          algebraMap_smul]))

private theorem thetaBO_tmul (x : Γ(L, X.basicOpen f)) (y : Γ(M, X.basicOpen f)) :
    thetaBO L M U f (x ⊗ₜ y) = Scheme.Modules.tensorSections x y := rfl

private theorem thetaBO_comp_map :
    thetaBO L M U f ∘ₗ TensorProduct.map (resBO L U f) (resBO M U f) = resBO (L ⊗ M) U f ∘ₗ theta L
      M U := by
  refine TensorProduct.ext' fun s t => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul, thetaBO_tmul, theta_tmul,
    resBO_apply, resBO_apply, resBO_apply]
  exact (Scheme.Modules.map_homOfLE_tensorSections (X.basicOpen_le f) s t).symm

private theorem thetaBO_bijective_of (hU : IsAffineOpen U)
    (h : Function.Bijective (theta L M (X.basicOpen f))) : Function.Bijective (thetaBO L M U f) :=
      by
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := hU.isLocalization_basicOpen f
  let e : Γ(L, X.basicOpen f) ⊗[Γ(X, X.basicOpen f)] Γ(M, X.basicOpen f) ≃ₗ[Γ(X, U)]
      Γ(L, X.basicOpen f) ⊗[Γ(X, U)] Γ(M, X.basicOpen f) :=
    (IsLocalization.moduleTensorEquiv (Submonoid.powers f) Γ(X, X.basicOpen f)
      Γ(L, X.basicOpen f) Γ(M, X.basicOpen f)).restrictScalars Γ(X, U)
  have he : ∀ x y, e (x ⊗ₜ[Γ(X, X.basicOpen f)] y) = x ⊗ₜ[Γ(X, U)] y := fun x y => rfl
  have hcomp : ∀ z, thetaBO L M U f (e z) = theta L M (X.basicOpen f) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y => rw [he, thetaBO_tmul, theta_tmul]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have hfun : (thetaBO L M U f : _ → _) = theta L M (X.basicOpen f) ∘ e.symm := by
    funext z
    rw [Function.comp_apply, ← hcomp, LinearEquiv.apply_symm_apply]
  rw [hfun]
  exact h.comp e.symm.bijective

end Theta

section Frames

variable {L M : X.Modules} {D : X.Opens}

private theorem res_self (N : X.Modules) (s : Γ(N, D)) : N.presheaf.map (homOfLE (le_refl D)).op s
  = s := by
  have : (homOfLE (le_refl D)).op = 𝟙 (Opposite.op D) := Subsingleton.elim _ _
  rw [this, N.presheaf.map_id]
  rfl

private theorem bijective_smul_of_isFrameOn {N : X.Modules} {s : Γ(N, D)} (hs :
  Scheme.Modules.IsFrameOn s D) :
    Function.Bijective fun g : Γ(X, D) => g • s := by
  have h := hs.bijective (le_refl D) (le_refl D)
  rwa [res_self] at h

private theorem theta_bijective_of_isFrameOn {s : Γ(L, D)} {t : Γ(M, D)}
    (hs : Scheme.Modules.IsFrameOn s D) (ht : Scheme.Modules.IsFrameOn t D) :
    Function.Bijective (theta L M D) := by
  have hst := bijective_smul_of_isFrameOn (hs.tensorSections ht)
  let σ : Γ(X, D) ≃ₗ[Γ(X, D)] Γ(L, D) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, D) Γ(L, D) s)
      (bijective_smul_of_isFrameOn hs)
  let τ : Γ(X, D) ≃ₗ[Γ(X, D)] Γ(M, D) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, D) Γ(M, D) t)
      (bijective_smul_of_isFrameOn ht)
  let ρ : Γ(X, D) ≃ₗ[Γ(X, D)] Γ(L ⊗ M, D) :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, D) Γ(L ⊗ M, D)
      (Scheme.Modules.tensorSections s t))
      hst
  have key : theta L M D ∘ₗ (TensorProduct.congr σ τ).toLinearMap =
      ρ.toLinearMap ∘ₗ (TensorProduct.lid Γ(X, D) Γ(X, D)).toLinearMap := by
    refine TensorProduct.ext' fun g h => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.congr_tmul,
      TensorProduct.lid_tmul,
      σ, τ, ρ, LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, theta_tmul,
      Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right,
        smul_eq_mul, mul_smul]
    exact smul_comm _ _ _
  have hθ : theta L M D = (ρ.toLinearMap ∘ₗ (TensorProduct.lid Γ(X, D) Γ(X, D)).toLinearMap) ∘ₗ
      (TensorProduct.congr σ τ).symm.toLinearMap := by
    rw [← key, LinearMap.comp_assoc]
    refine LinearMap.ext fun z => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [hθ]
  exact (ρ.bijective.comp (TensorProduct.lid Γ(X, D) Γ(X, D)).bijective).comp
    (TensorProduct.congr σ τ).symm.bijective

private theorem exists_basicOpen_isFrameOn (hL : IsLineBundle L) (hM : IsLineBundle M)
    (U : X.Opens) (hU : IsAffineOpen U) {x : X} (hx : x ∈ U) :
    ∃ f : Γ(X, U), x ∈ X.basicOpen f ∧
      (∃ s : Γ(L, X.basicOpen f), Scheme.Modules.IsFrameOn s (X.basicOpen f)) ∧
      (∃ t : Γ(M, X.basicOpen f), Scheme.Modules.IsFrameOn t (X.basicOpen f)) := by
  obtain ⟨WL, hxL, ⟨eL⟩⟩ := hL x
  obtain ⟨WM, hxM, ⟨eM⟩⟩ := hM x
  obtain ⟨sL, hsL⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit WL eL
  obtain ⟨sM, hsM⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit WM eM
  obtain ⟨f, hfle, hxf⟩ := hU.exists_basicOpen_le (⟨x, (⟨hxL, hxM⟩ : x ∈ WL ⊓ WM)⟩ : (WL ⊓ WM :
    X.Opens)) hx
  refine ⟨f, hxf, ⟨L.presheaf.map (homOfLE (hfle.trans inf_le_left)).op sL, ?_⟩,
    ⟨M.presheaf.map (homOfLE (hfle.trans inf_le_right)).op sM, ?_⟩⟩
  · exact (hsL.map (homOfLE (hfle.trans inf_le_left))).mono (hfle.trans inf_le_left)
  · exact (hsM.map (homOfLE (hfle.trans inf_le_right))).mono (hfle.trans inf_le_right)

end Frames

private theorem locallyFramed_of_isLineBundle {N : X.Modules} (hN : IsLineBundle N) :
    ∀ x : X, ∃ (V : X.Opens) (s : Γ(N, V)), x ∈ V ∧ IsFrameOn s V := by
  intro x
  obtain ⟨V, hxV, ⟨e⟩⟩ := hN x
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit V e
  exact ⟨V, s, hxV, hs⟩

private theorem locallyFramed_tensor {L M : X.Modules}
    (hL : ∀ x : X, ∃ (V : X.Opens) (s : Γ(L, V)), x ∈ V ∧ IsFrameOn s V)
    (hM : ∀ x : X, ∃ (V : X.Opens) (s : Γ(M, V)), x ∈ V ∧ IsFrameOn s V) :
    ∀ x : X, ∃ (V : X.Opens) (s : Γ(L ⊗ M, V)), x ∈ V ∧ IsFrameOn s V := by
  intro x
  obtain ⟨VL, sL, hxL, hsL⟩ := hL x
  obtain ⟨VM, sM, hxM, hsM⟩ := hM x
  refine ⟨VL ⊓ VM, Scheme.Modules.tensorSections
    (L.presheaf.map (homOfLE (inf_le_left : VL ⊓ VM ≤ VL)).op sL)
    (M.presheaf.map (homOfLE (inf_le_right : VL ⊓ VM ≤ VM)).op sM), ⟨hxL, hxM⟩, ?_⟩
  exact ((hsL.map (homOfLE inf_le_left)).mono inf_le_left).tensorSections
    ((hsM.map (homOfLE inf_le_right)).mono inf_le_right)

section Global

variable {L M : X.Modules}

private theorem main (hL : IsLineBundle L) (hM : IsLineBundle M) (U : X.affineOpens) :
    Function.Bijective (theta L M U) := by
  let s : Set Γ(X, U) := {f | (∃ s : Γ(L, X.basicOpen f), Scheme.Modules.IsFrameOn s (X.basicOpen
    f)) ∧
    (∃ t : Γ(M, X.basicOpen f), Scheme.Modules.IsFrameOn t (X.basicOpen f))}
  have hspan : Ideal.span s = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hxf, hfL, hfM⟩ := exists_basicOpen_isFrameOn hL hM (U : X.Opens) U.2 hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, hfL, hfM⟩, hxf⟩
  have hL' := locallyFramed_of_isLineBundle hL
  have hM' := locallyFramed_of_isLineBundle hM
  have hLM := locallyFramed_tensor hL' hM'
  have : ∀ r : s, IsLocalizedModule.Away r.1 (resBO L (U : X.Opens) r.1) := fun r =>
    isLocalizedModule_resBO L U r.1 hL' U.2
  have : ∀ r : s, IsLocalizedModule.Away r.1 (resBO M (U : X.Opens) r.1) := fun r =>
    isLocalizedModule_resBO M U r.1 hM' U.2
  have : ∀ r : s, IsLocalizedModule.Away r.1 (resBO (L ⊗ M) (U : X.Opens) r.1) := fun r =>
    isLocalizedModule_resBO (L ⊗ M) U r.1 hLM U.2
  refine bijective_of_isLocalized_span s hspan
    (fun r : s => Γ(L, X.basicOpen r.1) ⊗[Γ(X, U)] Γ(M, X.basicOpen r.1))
    (fun r : s => TensorProduct.map (resBO L (U : X.Opens) r.1) (resBO M (U : X.Opens) r.1))
    (fun r : s => Γ(L ⊗ M, X.basicOpen r.1))
    (fun r : s => resBO (L ⊗ M) (U : X.Opens) r.1)
    (theta L M U) fun r => ?_
  have hmap : IsLocalizedModule.map (Submonoid.powers r.1)
      (TensorProduct.map (resBO L (U : X.Opens) r.1) (resBO M (U : X.Opens) r.1))
      (resBO (L ⊗ M) (U : X.Opens) r.1) (theta L M U) = thetaBO L M U r.1 := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r.1)
      (TensorProduct.map (resBO L (U : X.Opens) r.1) (resBO M (U : X.Opens) r.1))
      (f' := resBO (L ⊗ M) (U : X.Opens) r.1)
    rw [IsLocalizedModule.map_comp, thetaBO_comp_map]
  rw [hmap]
  obtain ⟨⟨sL, hsL⟩, ⟨sM, hsM⟩⟩ := r.2
  exact thetaBO_bijective_of L M U r.1 U.2 (theta_bijective_of_isFrameOn hsL hsM)

end Global

end TensorSectionsAux

end AlgebraicGeometry.Scheme.Modules

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open _root_.AlgebraicGeometry

/-- **Sections of a tensor product of line bundles over an affine open.** For invertible sheaves
`L` and `M` on a scheme `X` and an affine open `U`, the map
`Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) → Γ(L ⊗ M, U)` induced by `tensorSections` is bijective. -/
theorem IsLineBundle.bijective_lift_tensorSectionsBilin
    {X : Scheme.{u}} {L M : X.Modules} (hL : IsLineBundle L) (hM : IsLineBundle M)
    (U : X.affineOpens) :
    Function.Bijective (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U) :
      Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U)) :=
  Scheme.Modules.TensorSectionsAux.main hL hM U

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

end
