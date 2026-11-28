/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_ModulesDet.lean`,
`Definitions/Def_AlgebraicGeometry_ModulesWedge.lean`,
`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_epi_whiskerRight_wedgeVec_of_shortExact.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_epi_sheafification_map_of_locallySurjective.lean` and
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_app_eq_of_exact_of_app_eq_zero.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.WedgeVec
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import MathlibExt.AlgebraicGeometry.Modules.ExteriorPower
public import MathlibExt.AlgebraicGeometry.Modules.LocallyFreeOfRank
public import MathlibExt.AlgebraicGeometry.Modules.Monoidal
import MathlibExt.AlgebraicGeometry.Modules.InvertibleTensorSections
import MathlibExt.AlgebraicGeometry.SchemeModulesEpi
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Topology.Sheaves.Abelian

/-!
# The wedge map on exterior powers of sheaves of modules on a scheme

For a scheme `X`:

* `Scheme.Modules.exteriorPower X n : X.Modules ⥤ X.Modules`, from
  `MathlibExt.AlgebraicGeometry.Modules.ExteriorPower`, is the sheafified sectionwise `n`-th
  exterior power.
* `Scheme.Modules.wedgeVec n M : ⋀ⁿ M ⊗ M ⟶ ⋀ⁿ⁺¹ M` is the sheafification of the sectionwise map
  `x ⊗ m ↦ x ∧ m`.

The main result, `Scheme.Modules.epi_whiskerRight_wedgeVec_of_shortExact`, says: for a short
exact sequence `0 → E₁ → E₂ → E₃ → 0` of sheaves of modules with `E₁` locally free of rank `n`
and `E₃` invertible, the composite `⋀ⁿ E₁ ⊗ E₂ ⟶ ⋀ⁿ E₂ ⊗ E₂ ⟶ ⋀ⁿ⁺¹ E₂` is an epimorphism. Locally,
a basis `e₁, …, eₙ` of `E₁` together with a lift `t` of a generator of `E₃` spans `E₂`, so the
wedges `e₁ ∧ ⋯ ∧ eₙ ∧ t` generate `⋀ⁿ⁺¹ E₂`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

lemma exteriorPower_map (n : ℕ) {M N : X.Modules} (φ : M ⟶ N) :
    (exteriorPower X n).map φ = (sheafify X).map ((presheafExteriorPower X n).map φ.val) := rfl

/-- A sheaf of modules is the sheafification of its underlying presheaf. -/
noncomputable def sheafifyValIso (M : X.Modules) : (sheafify X).obj M.val ≅ M :=
  SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property M

@[reassoc]
lemma sheafifyValIso_hom_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (sheafify X).map φ.val ≫ (sheafifyValIso N).hom = (sheafifyValIso M).hom ≫ φ :=
  (SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).counit.naturality φ

@[reassoc]
lemma sheafifyValIso_inv_naturality {M N : X.Modules} (φ : M ⟶ N) :
    φ ≫ (sheafifyValIso N).inv = (sheafifyValIso M).inv ≫ (sheafify X).map φ.val := by
  rw [Iso.comp_inv_eq, Category.assoc, sheafifyValIso_hom_naturality, Iso.inv_hom_id_assoc]

/-- The wedge map `⋀ⁿ M ⊗ M ⟶ ⋀ⁿ⁺¹ M` of a sheaf of modules on a scheme: the sheafification of
the sectionwise map `x ⊗ m ↦ x ∧ m`. -/
noncomputable def wedgeVec (n : ℕ) (M : X.Modules) :
    (exteriorPower X n).obj M ⊗ M ⟶ (exteriorPower X (n + 1)).obj M :=
  ((exteriorPower X n).obj M ◁ (sheafifyValIso M).inv) ≫
    Functor.LaxMonoidal.μ (sheafify X) ((presheafExteriorPower X n).obj M.val) M.val ≫
      (sheafify X).map (PresheafOfModules.wedgeVec n M.val)

lemma whiskerRight_exteriorPower_map_comp_wedgeVec (n : ℕ) {M N : X.Modules} (φ : M ⟶ N) :
    ((exteriorPower X n).map φ ▷ N) ≫ wedgeVec n N =
      ((exteriorPower X n).obj M ◁ (sheafifyValIso N).inv) ≫
        Functor.LaxMonoidal.μ (sheafify X) ((presheafExteriorPower X n).obj M.val) N.val ≫
          (sheafify X).map
            (((presheafExteriorPower X n).map φ.val ▷ N.val) ≫
              PresheafOfModules.wedgeVec n N.val) := by
  rw [wedgeVec, ← whisker_exchange_assoc, exteriorPower_map,
    Functor.LaxMonoidal.μ_natural_left_assoc, ← Functor.map_comp]

private theorem epi_sheafify_map_of_locallySurjective {P Q : X.PresheafOfModules} (ψ : P ⟶ Q)
    (h : ∀ (U : X.Opens) (s : Q.obj (op U)), ∀ x ∈ U, ∃ (V : X.Opens) (i : V ≤ U),
      x ∈ V ∧ Q.map (homOfLE i).op s ∈ Set.range (ψ.app (op V))) :
    Epi ((sheafify X).map ψ) := by
  let J := Opens.grothendieckTopology X
  let T := PresheafOfModules.toPresheaf X.ringCatSheaf.obj
  have : Presheaf.IsLocallySurjective J (T.map ψ) :=
    ⟨fun {U} s x hx => by
      obtain ⟨V, i, hxV, t, ht⟩ := h U s x hx
      exact ⟨V, homOfLE i, ⟨t, ht⟩, hxV⟩⟩
  apply (SheafOfModules.toSheaf.{u} X.ringCatSheaf).epi_of_epi_map
  change Epi ((presheafToSheaf J AddCommGrpCat.{u}).map (T.map ψ))
  have : Sheaf.IsLocallySurjective ((presheafToSheaf J AddCommGrpCat.{u}).map (T.map ψ)) := by
    change Presheaf.IsLocallySurjective J (CategoryTheory.sheafifyMap J (T.map ψ))
    have : Presheaf.IsLocallySurjective J
        (CategoryTheory.toSheafify J (T.obj P) ≫ CategoryTheory.sheafifyMap J (T.map ψ)) := by
      rw [← CategoryTheory.toSheafify_naturality]
      infer_instance
    exact Presheaf.isLocallySurjective_of_isLocallySurjective J
      (CategoryTheory.toSheafify J (T.obj P)) _
  infer_instance

private instance : (toPresheaf X).Additive where
  map_add := by intros; rfl

private noncomputable abbrev evalAt (U : X.Opens) : TopCat.Presheaf Ab.{u} X ⥤ Ab.{u} :=
  (CategoryTheory.evaluation _ Ab.{u}).obj (op U)

private instance (U : X.Opens) : (evalAt (X := X) U).Additive where
  map_add := by intros; rfl

private theorem exists_app_eq_of_exact_of_app_eq_zero (S : ShortComplex X.Modules)
    (hS : S.Exact) [Mono S.f] (U : X.Opens) (m : Γ(S.X₂, U)) (hm : S.g.app U m = 0) :
    ∃ e : Γ(S.X₁, U), S.f.app U e = m := by
  have hK : IsLimit (KernelFork.ofι S.f S.zero) := hS.fIsKernel
  have hK₁ := KernelFork.mapIsLimit _ hK (toPresheaf X)
  have hPL : PreservesLimitsOfShape WalkingParallelPair (evalAt (X := X) U) :=
    evaluation_preservesLimitsOfShape _
  have hK' := @KernelFork.mapIsLimit _ _ _ _ _ _ _ _ _ _ hK₁ (evalAt (X := X) U) inferInstance
    (hPL.preservesLimit)
  let k : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ (evalAt (X := X) U).obj ((toPresheaf X).obj S.X₂) :=
    AddCommGrpCat.ofHom ((zmultiplesHom Γ(S.X₂, U) m).comp AddEquiv.ulift.toAddMonoidHom)
  have hk1 : k (ULift.up (1 : ℤ)) = m := by
    change (zmultiplesHom Γ(S.X₂, U) m) (1 : ℤ) = m
    simp
  have hk : k ≫ (evalAt (X := X) U).map ((toPresheaf X).map S.g) = 0 := by
    ext ⟨z⟩
    change (S.g.app U) ((zmultiplesHom Γ(S.X₂, U) m) z) = 0
    rw [zmultiplesHom_apply, map_zsmul, hm, smul_zero]
  refine ⟨(KernelFork.IsLimit.lift' hK' k hk).1 (ULift.up (1 : ℤ)), ?_⟩
  have h := (KernelFork.IsLimit.lift' hK' k hk).2
  have h' := congr($h (ULift.up (1 : ℤ)))
  rw [hk1] at h'
  exact h'

open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries (IsLineBundle) in
private theorem exists_isFrameOn_of_isLineBundle {L : X.Modules} (hL : IsLineBundle L) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ u : Γ(L, V), IsFrameOn u V := by
  obtain ⟨U, hx, ⟨e⟩⟩ := hL x
  obtain ⟨s, hs⟩ := exists_isFrameOn_of_pullback_iso_unit U e
  exact ⟨U, hx, s, hs⟩

private lemma ιMulti_comp_mem {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] {m : ℕ} (w : Fin m → M) (P : Submodule A (⋀[A]^m M))
    (hP : _root_.exteriorPower.ιMulti A m w ∈ P) (φ : Fin m → Fin m) :
    _root_.exteriorPower.ιMulti A m (w ∘ φ) ∈ P := by
  by_cases hφ : Function.Injective φ
  · have hbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hφ
    let σ : Equiv.Perm (Fin m) := Equiv.ofBijective φ hbij
    have : (w ∘ φ) = w ∘ σ := rfl
    rw [this, AlternatingMap.map_perm]
    exact P.smul_of_tower_mem _ hP
  · rw [Function.Injective] at hφ
    push Not at hφ
    obtain ⟨i, j, hij, hne⟩ := hφ
    have : _root_.exteriorPower.ιMulti A m (w ∘ φ) = 0 :=
      AlternatingMap.map_eq_zero_of_eq _ (w ∘ φ) (by simp [hij]) hne
    rw [this]
    exact P.zero_mem

private lemma exteriorPower_le_of_span_eq_top {A : Type*} [CommRing A] {M : Type*}
    [AddCommGroup M] [Module A M] {m : ℕ} (w : Fin m → M)
    (hw : Submodule.span A (Set.range w) = ⊤) (P : Submodule A (⋀[A]^m M))
    (hP : _root_.exteriorPower.ιMulti A m w ∈ P) : ⊤ ≤ P := by
  rw [← _root_.exteriorPower.ιMulti_family_span_of_span (n := m) A hw, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  exact ιMulti_comp_mem w P hP _

open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries (IsLineBundle) in
open MathlibExt.AlgebraicGeometry.CurveVectorBundles (IsVectorBundle) in
/-- For a short exact sequence `0 → E₁ → E₂ → E₃ → 0` of sheaves of modules on a scheme with
`E₁` locally free of rank `n` and `E₃` invertible, the composite
`⋀ⁿ E₁ ⊗ E₂ ⟶ ⋀ⁿ E₂ ⊗ E₂ ⟶ ⋀ⁿ⁺¹ E₂` of `⋀ⁿ` of the inclusion with the wedge map is an
epimorphism. -/
theorem epi_whiskerRight_wedgeVec_of_shortExact {n : ℕ} (S : ShortComplex X.Modules)
    (hS : S.ShortExact) (h₁ : IsVectorBundle S.X₁ n) (h₃ : IsLineBundle S.X₃) :
    Epi (((exteriorPower X n).map S.f ▷ S.X₂) ≫ wedgeVec n S.X₂) := by
  have := hS.mono_f
  have := hS.epi_g
  rw [whiskerRight_exteriorPower_map_comp_wedgeVec]
  set θ : (presheafExteriorPower X n).obj S.X₁.val ⊗ S.X₂.val ⟶
      (presheafExteriorPower X (n + 1)).obj S.X₂.val :=
    ((presheafExteriorPower X n).map S.f.val ▷ S.X₂.val) ≫ PresheafOfModules.wedgeVec n S.X₂.val
  suffices hθ : Epi ((sheafify X).map θ) by infer_instance
  refine epi_sheafify_map_of_locallySurjective θ (fun U s x hxU => ?_)
  obtain ⟨V₁, hx₁, e', he'⟩ := h₁.exists_basis x
  obtain ⟨V₀, hx₀, u, hu⟩ := exists_isFrameOn_of_isLineBundle h₃ x
  obtain ⟨V₂, i₂, hx₂, et, het⟩ : ∃ (V₂ : X.Opens) (i : V₂ ≤ V₀), x ∈ V₂ ∧
      ∃ et : Γ(S.X₂, V₂), S.g.app V₂ et = S.X₃.presheaf.map (homOfLE i).op u := by
    obtain ⟨V₂, i, hx₂, ⟨et, het⟩⟩ :=
      (Hom.epi_iff_locallySurjective S.g).mp inferInstance V₀ u x hx₀
    exact ⟨V₂, i, hx₂, et, het⟩
  let V : X.Opens := U ⊓ V₁ ⊓ V₂
  have hVU : V ≤ U := inf_le_left.trans inf_le_left
  have hV₁ : V ≤ V₁ := inf_le_left.trans inf_le_right
  have hV₂ : V ≤ V₂ := inf_le_right
  have hV₀ : V ≤ V₀ := hV₂.trans i₂
  have hxV : x ∈ V := ⟨⟨hxU, hx₁⟩, hx₂⟩
  refine ⟨V, hVU, hxV, ?_⟩
  suffices hsurj : Function.Surjective (θ.app (op V)) from hsurj _
  let A : Type u := Γ(X, V)
  let E₁ : Type u := Γ(S.X₁, V)
  let E₂ : Type u := Γ(S.X₂, V)
  let E₃ : Type u := Γ(S.X₃, V)
  obtain ⟨b₁, hb₁⟩ := he' V hV₁
  let u₃ : E₃ := S.X₃.presheaf.map (homOfLE hV₀).op u
  let fV : E₁ →ₗ[A] E₂ := (S.f.val.app (op V)).hom
  let gV : E₂ →ₗ[A] E₃ := (S.g.val.app (op V)).hom
  have hfV : ∀ e, fV e = S.f.app V e := fun e => rfl
  have hgV : ∀ e, gV e = S.g.app V e := fun e => rfl
  let etV : E₂ := S.X₂.presheaf.map (homOfLE hV₂).op et
  have hget : gV etV = u₃ := by
    rw [hgV]
    change S.g.app V (S.X₂.presheaf.map (homOfLE hV₂).op et) = _
    have hnat := congr($(S.g.mapPresheaf.naturality (homOfLE hV₂).op) et)
    simp only [CategoryTheory.comp_apply, mapPresheaf_app] at hnat
    rw [hnat, het, ← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp,
      Subsingleton.elim (homOfLE hV₂ ≫ homOfLE i₂) (homOfLE hV₀)]
  let w : Fin (n + 1) → E₂ := Fin.append (fun i => fV (b₁ i)) (fun _ : Fin 1 => etV)
  have hw : Submodule.span A (Set.range w) = ⊤ := by
    rw [eq_top_iff]
    rintro m -
    obtain ⟨c, hc⟩ := (hu hV₀ hV₀).2 (gV m)
    have hker : S.g.app V (m - c • etV) = 0 := by
      rw [← hgV, LinearMap.map_sub, LinearMap.map_smul, hget]
      exact sub_eq_zero.2 hc.symm
    obtain ⟨e₁, he₁⟩ := exists_app_eq_of_exact_of_app_eq_zero S hS.exact V (m - c • etV) hker
    have hm : m = fV e₁ + c • etV := by rw [hfV, he₁, sub_add_cancel]
    rw [hm]
    refine Submodule.add_mem _ ?_
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd n 0, by simp [w]⟩))
    have : fV e₁ = ∑ i, (b₁.repr e₁ i) • fV (b₁ i) := by
      conv_lhs => rw [← b₁.sum_repr e₁]
      rw [map_sum]
      exact Finset.sum_congr rfl (fun i _ => LinearMap.map_smul fV _ _)
    rw [this]
    exact Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castAdd 1 i, by simp [w]⟩))
  let θV := (θ.app (op V)).hom
  have hθV : θV ((show ((presheafExteriorPower X n).obj S.X₁.val).obj (op V) from
      _root_.exteriorPower.ιMulti A n (fun i => b₁ i)) ⊗ₜ etV) =
        (show ((presheafExteriorPower X (n + 1)).obj S.X₂.val).obj (op V) from
          _root_.exteriorPower.ιMulti A (n + 1) w) := by
    change _root_.exteriorPower.mulVec A E₂ n
        (_root_.exteriorPower.map n fV (_root_.exteriorPower.ιMulti A n (fun i => b₁ i))) etV =
      _root_.exteriorPower.ιMulti A (n + 1) w
    rw [_root_.exteriorPower.map_apply_ιMulti, _root_.exteriorPower.mulVec_ιMulti]
    rfl
  intro z
  have hz : (show ⋀[A]^(n + 1) E₂ from z) ∈ LinearMap.range θV := by
    refine exteriorPower_le_of_span_eq_top w hw (LinearMap.range θV) ?_ Submodule.mem_top
    exact ⟨_, hθV⟩
  obtain ⟨y, hy⟩ := hz
  exact ⟨y, hy⟩

end AlgebraicGeometry.Scheme.Modules
