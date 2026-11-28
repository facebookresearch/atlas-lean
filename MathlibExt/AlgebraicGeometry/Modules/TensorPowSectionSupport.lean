/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_
zeroSchemeIdeal_eq_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_
eq_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_
zeroSchemeIdeal_eq_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections_monoidalV2.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullbackTensorObjIso_hom_app_pullbackLocalSection_
monoidalV2.lean`,
`Definitions/Def_AlgebraicGeometry_ModulesSectionZeroScheme.lean`,
`Definitions/Def_AlgebraicGeometry_ModulesTensorPowV2.lean`,
`Definitions/Def_AlgebraicGeometry_ModulesPullbackMonoidal.lean` and
`Definitions/Def_AlgebraicGeometry_ModulesPullbackLocalSection.lean`
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

public import MathlibExt.AlgebraicGeometry.Modules.InvertibleTensorSections
public import MathlibExt.AlgebraicGeometry.Modules.SectionPullback
public import MathlibExt.AlgebraicGeometry.SchemeModulesTensor
public import MathlibExt.AlgebraicGeometry.LineBundlePullback
public import MathlibExt.Algebra.Category.ModuleCat.Presheaf.PullbackMonoidal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import MathlibExt.AlgebraicGeometry.IdealSheafOpenCoverGlue

import Mathlib.AlgebraicGeometry.Cover.Open
import MathlibExt.AlgebraicGeometry.IdealSheafComapMul
import MathlibExt.AlgebraicGeometry.LineBundleTensor
import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Zero supports of sections of tensor powers of invertible sheaves

We define the ideal sheaf `Scheme.Modules.zeroSchemeIdeal s` cut out by a global section
`s : 𝟙_ X.Modules ⟶ M` and the monoidal structure on `Scheme.Modules.pullback`. For invertible
sheaves we compute the zero ideal locally, show it commutes with pullback and is multiplicative
for tensor products of sections.

The main result `Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq` says that
for a commutative group scheme over a field and an invertible sheaf `L` satisfying the
theorem-of-the-square isomorphisms, every section `θ` of `L` yields a section of the tensor cube
`SchemeModulesTensor.power L 3` whose zero support is the union of the preimages of the zero
support of `θ` under the translations by `a`, `b` and `(a * b)⁻¹`.

## References

* D. Mumford, *Abelian Varieties*, §6 (the theorem of the square)
-/


universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
  (IsLineBundle pullbackStructureModuleIso)
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts (pullbackSection)
open MathlibExt.AlgebraicGeometry.ModuleTensorPullbackSections (localPullback)

namespace AlgebraicGeometry.Scheme.Modules

section ZeroSchemeDefs
variable {X : Scheme.{u}} {M : X.Modules}
/-- A section of the structure sheaf over `U`, viewed as a section of the tensor unit
`𝟙_ X.Modules` over `U`. -/
@[expose] public def toUnitSection (U : X.Opens) (r : Γ(X, U)) : Γ(𝟙_ X.Modules, U) :=
  r

/-- A section of the tensor unit `𝟙_ X.Modules` over `U`, viewed as a section of the structure
sheaf over `U`; the inverse of `toUnitSection U`. -/
@[expose] public def ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) : Γ(X, U) :=
  m

@[simp] public lemma ofUnitSection_toUnitSection (U : X.Opens) (r : Γ(X, U)) :
    ofUnitSection U (toUnitSection U r) = r := rfl

@[simp] public lemma toUnitSection_ofUnitSection (U : X.Opens) (m : Γ(𝟙_ X.Modules, U)) :
    toUnitSection U (ofUnitSection U m) = m := rfl

public lemma ofUnitSection_injective (U : X.Opens) :
    Function.Injective (ofUnitSection (X := X) U) :=
  fun _ _ h => h

public lemma ofUnitSection_map {U V : X.Opens} (i : V ⟶ U) (m : Γ(𝟙_ X.Modules, U)) :
    ofUnitSection V ((𝟙_ X.Modules).presheaf.map i.op m) =
      X.presheaf.map i.op (ofUnitSection U m) := rfl

public lemma ofUnitSection_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(𝟙_ X.Modules, U)) :
    ofUnitSection U (r • m) = r * ofUnitSection U m := rfl

/-- The restriction of a global section `s : 𝟙_ X.Modules ⟶ M` to the open subscheme `U`, as a
section of `M.restrict U.ι` over `⊤`. -/
@[expose] public def restrictSection (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Γ(M.restrict U.ι, ⊤) :=
  s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1)

/-- The coefficient of `s` over `U` with respect to `φ : M|_U ⟶ 𝒪_U`: the function `φ (s|_U)`
on `U`, as an element of `Γ(X, U)`. -/
@[expose] public def coeff (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : Γ(X, U) :=
  U.topIso.hom (ofUnitSection ⊤ (φ.app ⊤ (restrictSection s U)))

/-- The ideal of `Γ(X, U)` generated by the coefficients `φ (s|_U)` of `s` for all
`φ : M|_U ⟶ 𝒪_U`. -/
@[expose] public def coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) : Ideal Γ(X, U) :=
  Ideal.span (Set.range (coeff s U))

public lemma coeff_mem_coeffIdeal (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) : coeff s U φ ∈ coeffIdeal s U :=
  Ideal.subset_span ⟨φ, rfl⟩

/-- The ideal sheaf of the zero scheme of `s`, the smallest ideal sheaf that contains, on each
affine open `U`, the elements `φ (s|_U)` for all `φ : M|_U ⟶ 𝒪_U`. -/
@[expose] public def zeroSchemeIdeal (s : 𝟙_ X.Modules ⟶ M) : X.IdealSheafData :=
  sInf {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U}

/-- The zero scheme of `s`, the closed subscheme cut out by `zeroSchemeIdeal s`. -/
public abbrev zeroScheme (s : 𝟙_ X.Modules ⟶ M) : Scheme.{u} :=
  (zeroSchemeIdeal s).subscheme

public lemma zeroSchemeIdeal_le {s : 𝟙_ X.Modules ⟶ M} {J : X.IdealSheafData}
    (h : ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) : zeroSchemeIdeal s ≤ J :=
  sInf_le h

public lemma le_zeroSchemeIdeal {s : 𝟙_ X.Modules ⟶ M} {K : X.IdealSheafData}
    (h : ∀ J : X.IdealSheafData, (∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) → K ≤ J) :
    K ≤ zeroSchemeIdeal s :=
  le_sInf fun _ hJ => h _ hJ

public lemma zeroSchemeIdeal_eq_of_isLeast {s : 𝟙_ X.Modules ⟶ M} {P : X.IdealSheafData}
    (hP : IsLeast {J : X.IdealSheafData | ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U} P) :
    zeroSchemeIdeal s = P :=
  hP.isGLB.sInf_eq

end ZeroSchemeDefs

end AlgebraicGeometry.Scheme.Modules

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

public theorem IsLineBundle.exists_restrict_iso {X : Scheme.{u}} {M : X.Modules}
    (hM : IsLineBundle M)
    {V : X.Opens} {x : X} (hx : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules) := by
  obtain ⟨U₀, hxU₀, ⟨e⟩⟩ := (LineBundleTensor.isLineBundle_iff_restrict M).mp hM x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ V ⊓ U₀ from ⟨hx, hxU₀⟩)
      (V ⊓ U₀).isOpen
  exact ⟨⟨U, hU⟩, hxU, fun y hy => (hUle hy).1,
    ⟨LineBundleTensor.restrictTrivializationOfLE M (fun y hy => (hUle hy).2) e⟩⟩

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of presheaves of modules along a morphism of schemes `f`, before sheafification. -/
public abbrev pullback₀ {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pb (TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

public instance pullback₀_monoidal {X Y : Scheme.{u}} (f : X ⟶ Y) : (pullback₀ f).Monoidal :=
  inferInstanceAs (PresheafOfModules.PullbackMonoidal.pb (TopologicalSpace.Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c).Monoidal

public instance sheafify_isLocalization' {Y : Scheme.{u}} : (Modules.sheafify Y).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
  inferInstanceAs
    ((SheafOfModules.sheafifyFunctor Y.sheaf.obj Y.ringCatSheaf.property).IsLocalization
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj))

public instance pullback_lifting {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CategoryTheory.Localization.Lifting (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom⟩

public instance pullback_monoidal {X Y : Scheme.{u}} (f : X ⟶ Y) : (Modules.pullback f).Monoidal :=
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  CategoryTheory.Localization.Monoidal.functorMonoidalOfComp (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)

/-- The isomorphism `f^* (L ⊗ M) ≅ f^* L ⊗ f^* M` given by the monoidal structure of
`Scheme.Modules.pullback f`. -/
@[expose] public def pullbackTensorObjIso {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : Y.Modules) :
    (Scheme.Modules.pullback f).obj (L ⊗ M) ≅
      (Scheme.Modules.pullback f).obj L ⊗ (Scheme.Modules.pullback f).obj M :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback f) L M).symm

/-- The isomorphism `f^* 𝟙_ ≅ 𝟙_` from the monoidal structure of `Scheme.Modules.pullback f`. -/
@[expose] public def pullbackTensorUnitObjIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm

namespace ZeroSchemeLoc


variable {X : Scheme.{u}} {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)

def sAt (V : (U : Scheme.{u}).Opens) : Γ(M, U.ι ''ᵁ V) :=
  s.app (U.ι ''ᵁ V) (toUnitSection (U.ι ''ᵁ V) 1)

lemma sAt_top : sAt s U ⊤ = restrictSection s U := rfl

lemma unit_map_one {W W' : X.Opens} (i : W' ⟶ W) :
    (𝟙_ X.Modules).presheaf.map i.op (toUnitSection W 1) = toUnitSection W' 1 :=
  ofUnitSection_injective W' (by rw [ofUnitSection_map]; exact map_one _)

lemma map_sAt {V V' : (U : Scheme.{u}).Opens} (i : V' ⟶ V) :
    M.presheaf.map (U.ι.opensFunctor.map i).op (sAt s U V) = sAt s U V' := by
  unfold sAt
  have nat := congrArg (fun g => g (toUnitSection (U.ι ''ᵁ V) 1))
    (s.mapPresheaf.naturality (U.ι.opensFunctor.map i).op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  rw [← nat, unit_map_one]

lemma restrict_smul (V : (U : Scheme.{u}).Opens) (r : Γ((U : Scheme.{u}), V))
    (m : Γ(M.restrict U.ι, V)) :
    r • m = (id r : Γ(X, U.ι ''ᵁ V)) • (id m : Γ(M, U.ι ''ᵁ V)) := by
  change ((U.ι.appIso V).inv.hom r) • (id m : Γ(M, U.ι ''ᵁ V)) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

variable {U} in
lemma app_smul' {N : (U : Scheme.{u}).Modules} (φ : M.restrict U.ι ⟶ N) (V : (U : Scheme.{u}).Opens)
    (r : Γ(X, U.ι ''ᵁ V)) (m : Γ(M, U.ι ''ᵁ V)) :
    φ.app V (r • m) = (id r : Γ((U : Scheme.{u}), V)) • φ.app V m := by
  have h := Scheme.Modules.Hom.app_smul φ (id r : Γ((U : Scheme.{u}), V))
    (id m : Γ(M.restrict U.ι, V))
  rw [restrict_smul] at h
  exact h

variable {U} in
def coord (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens)
    (m : Γ(M, U.ι ''ᵁ V)) : Γ(X, U.ι ''ᵁ V) :=
  ofUnitSection V (φ.app V m)

variable {U} in
def cf (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens) :
    Γ(X, U.ι ''ᵁ V) :=
  coord φ V (sAt s U V)

lemma cf_top (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    U.topIso.hom.hom (cf s φ ⊤) = coeff s U φ := rfl

variable {U} in
lemma map_coord (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {V V' : (U : Scheme.{u}).Opens}
    (i : V' ⟶ V) (m : Γ(M, U.ι ''ᵁ V)) :
    X.presheaf.map (U.ι.opensFunctor.map i).op (coord φ V m) =
      coord φ V' (M.presheaf.map (U.ι.opensFunctor.map i).op m) := by
  have nat := congrArg (fun g => g m) (φ.mapPresheaf.naturality i.op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  unfold coord
  change ofUnitSection V' ((𝟙_ (U : Scheme.{u}).Modules).presheaf.map i.op (φ.app V m)) = _
  exact (congrArg (ofUnitSection V') nat).symm

variable {U} in
lemma map_cf (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {V V' : (U : Scheme.{u}).Opens}
    (i : V' ⟶ V) : X.presheaf.map (U.ι.opensFunctor.map i).op (cf s φ V) = cf s φ V' := by
  unfold cf
  rw [map_coord, map_sAt]

variable {U} in
lemma coord_smul (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens)
    (r : Γ(X, U.ι ''ᵁ V)) (m : Γ(M, U.ι ''ᵁ V)) :
    coord φ V (r • m) = r * coord φ V m := by
  unfold coord
  rw [app_smul']
  rfl

variable {U} in
def gen (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens) :
    Γ(M, U.ι ''ᵁ V) :=
  τ.inv.app V (toUnitSection V 1)

variable {U} in
lemma coord_smul_gen (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens)
    (m : Γ(M, U.ι ''ᵁ V)) : coord τ.hom V m • gen τ V = m := by
  have h1 : (id (coord τ.hom V m) : Γ((U : Scheme.{u}), V)) • toUnitSection V 1 = τ.hom.app V m :=
    congrArg (toUnitSection V) (mul_one (ofUnitSection V (τ.hom.app V m)))
  have h2 := Scheme.Modules.Hom.app_smul τ.inv (id (coord τ.hom V m) : Γ((U : Scheme.{u}), V))
    (toUnitSection V 1)
  rw [restrict_smul, h1] at h2
  have h3 := congrArg (fun g => Scheme.Modules.Hom.app g V m) τ.hom_inv_id
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h3
  change τ.inv.app V (τ.hom.app V m) = m at h3
  rw [h3] at h2
  exact h2.symm

variable {U} in
lemma cf_eq_mul (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules)
    (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens) :
    cf s φ V = cf s τ.hom V * coord φ V (gen τ V) := by
  unfold cf
  conv_lhs => rw [← coord_smul_gen τ V (sAt s U V)]
  exact coord_smul φ V _ _

variable {U}

lemma image_preimage_eq_of_le {W : X.Opens} (hW : W ≤ U) : U.ι ''ᵁ (U.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hW

def resX {W : X.Opens} (hW : W ≤ U) : Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) ⟶ Γ(X, W) :=
  X.presheaf.map (homOfLE (image_preimage_eq_of_le hW).ge).op

def resX' {W : X.Opens} (hW : W ≤ U) : Γ(X, W) ⟶ Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) :=
  X.presheaf.map (homOfLE (image_preimage_eq_of_le hW).le).op

def resM {W : X.Opens} (hW : W ≤ U) : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) ⟶ Γ(M, W) :=
  M.presheaf.map (homOfLE (image_preimage_eq_of_le hW).ge).op

def resM' {W : X.Opens} (hW : W ≤ U) : Γ(M, W) ⟶ Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)) :=
  M.presheaf.map (homOfLE (image_preimage_eq_of_le hW).le).op

omit s in
lemma resX_resX' {W : X.Opens} (hW : W ≤ U) (r : Γ(X, W)) : resX hW (resX' hW r) = r := by
  unfold resX resX'
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE _ ≫ homOfLE _) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

omit s in
lemma resX'_resX {W : X.Opens} (hW : W ≤ U) (r : Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) :
    resX' hW (resX hW r) = r := by
  unfold resX resX'
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE _ ≫ homOfLE _) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

omit s in
lemma resM_resM' {W : X.Opens} (hW : W ≤ U) (m : Γ(M, W)) : resM (M := M) hW (resM' hW m) = m := by
  unfold resM resM'
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE _ ≫ homOfLE _) (𝟙 _), op_id, CategoryTheory.Functor.map_id]
  rfl

omit s in
lemma resM_smul {W : X.Opens} (hW : W ≤ U) (r : Γ(X, U.ι ''ᵁ (U.ι ⁻¹ᵁ W)))
    (m : Γ(M, U.ι ''ᵁ (U.ι ⁻¹ᵁ W))) : resM (M := M) hW (r • m) = resX hW r • resM hW m :=
  Scheme.Modules.map_smul M _ r m

omit s in
lemma resM'_smul {W : X.Opens} (hW : W ≤ U) (r : Γ(X, W)) (m : Γ(M, W)) :
    resM' (M := M) (U := U) hW (r • m) = resX' hW r • resM' hW m :=
  Scheme.Modules.map_smul M _ r m

lemma resM'_sApp {W : X.Opens} (hW : W ≤ U) :
    resM' (U := U) hW (s.app W (toUnitSection W 1)) = sAt s U (U.ι ⁻¹ᵁ W) := by
  unfold resM' sAt
  have nat := congrArg (fun g => g (toUnitSection W 1))
    (s.mapPresheaf.naturality (homOfLE (image_preimage_eq_of_le hW).le).op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  rw [← nat, unit_map_one]

def cX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U) : Γ(X, W) :=
  resX hW (cf s φ (U.ι ⁻¹ᵁ W))

def tX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U)
    (m : Γ(M, W)) : Γ(X, W) :=
  resX hW (coord φ (U.ι ⁻¹ᵁ W) (resM' hW m))

def eX (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U) : Γ(M, W) :=
  resM hW (gen τ (U.ι ⁻¹ᵁ W))

lemma tX_sApp (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U) :
    tX φ hW (s.app W (toUnitSection W 1)) = cX s φ hW := by
  unfold tX cX cf
  rw [resM'_sApp]

omit s in
lemma tX_smul (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U)
    (r : Γ(X, W)) (m : Γ(M, W)) : tX φ hW (r • m) = r * tX φ hW m := by
  unfold tX
  rw [resM'_smul, coord_smul, map_mul, resX_resX']

omit s in
lemma tX_smul_eX (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U)
    (m : Γ(M, W)) : tX τ.hom hW m • eX τ hW = m := by
  unfold tX eX
  rw [← resM_smul]
  exact (congrArg (resM hW) (coord_smul_gen τ (U.ι ⁻¹ᵁ W) (resM' hW m))).trans (resM_resM' hW m)

lemma cX_dvd (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {W : X.Opens} (hW : W ≤ U)
    (t : Γ(M, W) → Γ(X, W)) (ht : ∀ (r : Γ(X, W)) (m : Γ(M, W)), t (r • m) = r * t m) :
    cX s τ.hom hW ∣ t (s.app W (toUnitSection W 1)) := by
  refine ⟨t (eX τ hW), ?_⟩
  conv_lhs => rw [← tX_smul_eX τ hW (s.app W (toUnitSection W 1))]
  rw [ht, tX_sApp]

lemma map_cX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) {W W' : X.Opens} (hW : W ≤ U)
    (h : W' ≤ W) : X.presheaf.map (homOfLE h).op (cX s φ hW) = cX s φ (h.trans hW) := by
  unfold cX resX
  have hi : U.ι ⁻¹ᵁ W' ≤ U.ι ⁻¹ᵁ W := fun x hx => h hx
  rw [← map_cf s φ (homOfLE hi), ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← Functor.map_comp]
  exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (X.presheaf.map k)))
    (Subsingleton.elim _ _)) _

lemma cX_image (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) (V : (U : Scheme.{u}).Opens)
    (h : U.ι ''ᵁ V ≤ U) : cX s φ h = cf s φ V := by
  unfold cX resX
  have hi : V ≤ U.ι ⁻¹ᵁ (U.ι ''ᵁ V) := (U.ι.preimage_image_eq V).ge
  rw [← map_cf s φ (homOfLE hi)]
  exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (X.presheaf.map k)))
    (Subsingleton.elim _ _)) _

omit s in
theorem mem_ideal_of_forall_exists_basicOpen {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (Ω : Y.affineOpens) (r : Γ(Y, Ω.1))
    (h : ∀ y ∈ Ω.1, ∃ g : Γ(Y, Ω.1), y ∈ Y.basicOpen g ∧
      Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op r ∈ I.ideal (Y.affineBasicOpen g)) :
    r ∈ I.ideal Ω := by
  classical
  let S : Set Γ(Y, Ω.1) :=
    {g | Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op r ∈ I.ideal (Y.affineBasicOpen g)}
  have hcov : Ω.1 ≤ ⨆ g : S, Y.basicOpen g.1 := fun y hy => by
    obtain ⟨g, hyg, hg⟩ := h y hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hyg⟩
  have hspan : Ideal.span S = ⊤ := Ω.2.self_le_iSup_basicOpen_iff.mp hcov
  have : ∀ g : S, IsLocalization.Away g.1 Γ(Y, Y.basicOpen g.1) :=
    fun g => Ω.2.isLocalization_basicOpen g.1
  refine Submodule.mem_of_isLocalized_span S hspan
    (fun g : S => Γ(Y, Y.basicOpen g.1))
    (fun g : S => Algebra.linearMap Γ(Y, Ω.1) Γ(Y, Y.basicOpen g.1)) (fun g => ?_)
  rw [← Submodule.restrictScalars_localized' Γ(Y, Y.basicOpen g.1), Submodule.restrictScalars_mem,
    Submodule.localized'_eq_span]
  have hg : Y.presheaf.map (homOfLE (Y.basicOpen_le g.1)).op r ∈ I.ideal (Y.affineBasicOpen g.1) :=
    g.2
  rw [← I.map_ideal_basicOpen] at hg
  exact hg

omit s in
theorem ideal_eq_of_forall_exists_basicOpen {Y : Scheme.{u}} (I₁ I₂ : Y.IdealSheafData)
    (Ω : Y.affineOpens)
    (h : ∀ y ∈ Ω.1, ∃ g : Γ(Y, Ω.1), y ∈ Y.basicOpen g ∧
      I₁.ideal (Y.affineBasicOpen g) = I₂.ideal (Y.affineBasicOpen g)) :
    I₁.ideal Ω = I₂.ideal Ω := by
  refine le_antisymm (fun r hr => ?_) (fun r hr => ?_)
  · refine mem_ideal_of_forall_exists_basicOpen I₂ Ω r fun y hy => ?_
    obtain ⟨g, hyg, hg⟩ := h y hy
    refine ⟨g, hyg, ?_⟩
    rw [← hg, ← I₁.map_ideal_basicOpen]
    exact Ideal.mem_map_of_mem _ hr
  · refine mem_ideal_of_forall_exists_basicOpen I₁ Ω r fun y hy => ?_
    obtain ⟨g, hyg, hg⟩ := h y hy
    refine ⟨g, hyg, ?_⟩
    rw [hg, ← I₂.map_ideal_basicOpen]
    exact Ideal.mem_map_of_mem _ hr

variable (M) in
def Idx : Type u := Σ U : X.affineOpens, (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)

def piece (j : Idx M) : (j.1.1 : Scheme.{u}).IdealSheafData where
  ideal V := Ideal.span {(id (cf s j.2.hom V.1) : Γ((j.1.1 : Scheme.{u}), V.1))}
  map_ideal_basicOpen V f := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun x => Ideal.span ({x} : Set Γ((j.1.1 : Scheme.{u}), _)))
      (map_cf s j.2.hom (homOfLE ((j.1.1 : Scheme.{u}).basicOpen_le f)))

lemma ideal_piece (j : Idx M) (V : (j.1.1 : Scheme.{u}).affineOpens) :
    (piece s j).ideal V = Ideal.span {(id (cf s j.2.hom V.1) : Γ((j.1.1 : Scheme.{u}), V.1))} :=
  rfl

def cover (hM : IsLineBundle M) : X.OpenCover :=
  Scheme.Cover.mkOfCovers (Idx M) (fun j => (j.1.1 : Scheme.{u})) (fun j => j.1.1.ι) (fun x => by
    obtain ⟨U, hxU, -, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := x) trivial
    exact ⟨⟨U, τ⟩, ⟨x, hxU⟩, rfl⟩)

lemma span_cX_eq (j j' : Idx M) {W : X.Opens} (hj : W ≤ j.1.1) (hj' : W ≤ j'.1.1) :
    Ideal.span {cX s j.2.hom hj} = Ideal.span {cX s j'.2.hom hj'} := by
  apply le_antisymm
  · refine Ideal.span_singleton_le_span_singleton.mpr ?_
    have := cX_dvd s j'.2 hj' (tX j.2.hom hj) (tX_smul j.2.hom hj)
    rwa [tX_sApp] at this
  · refine Ideal.span_singleton_le_span_singleton.mpr ?_
    have := cX_dvd s j.2 hj (tX j'.2.hom hj') (tX_smul j'.2.hom hj')
    rwa [tX_sApp] at this

lemma ideal_comap_piece (j : Idx M) {V : Scheme.{u}} (a : V ⟶ (j.1.1 : Scheme.{u}))
    {W : X.Opens} (hW : W ≤ j.1.1) (hWa : IsAffineOpen W) (Ω : V.affineOpens)
    (hΩ : (Ω : V.Opens) ≤ (a ≫ j.1.1.ι) ⁻¹ᵁ W) :
    ((piece s j).comap a).ideal Ω =
      Ideal.span {((a ≫ j.1.1.ι).appLE W Ω hΩ).hom (cX s j.2.hom hW)} := by
  have hVa : IsAffineOpen (j.1.1.ι ⁻¹ᵁ W) := hWa.preimage_of_isOpenImmersion j.1.1.ι
    (by rw [Scheme.Opens.opensRange_ι]; exact hW)
  have hΩ' : (Ω : V.Opens) ≤ a ⁻¹ᵁ (j.1.1.ι ⁻¹ᵁ W) := hΩ
  rw [IdealSheafComapMulAux.ideal_comap_of_le (piece s j) a ⟨_, hVa⟩ Ω hΩ', ideal_piece,
    Ideal.map_span, Set.image_singleton]
  refine congrArg (fun x => Ideal.span ({x} : Set Γ(V, Ω))) ?_
  rw [Scheme.Hom.comp_appLE]
  change _ = (a.appLE (j.1.1.ι ⁻¹ᵁ W) Ω hΩ').hom (resX' hW (cX s j.2.hom hW))
  unfold cX
  rw [resX'_resX]
  rfl

lemma comap_piece_eq (j j' : Idx M) {V : Scheme.{u}} (a : V ⟶ (j.1.1 : Scheme.{u}))
    (b : V ⟶ (j'.1.1 : Scheme.{u})) (hab : a ≫ j.1.1.ι = b ≫ j'.1.1.ι) :
    (piece s j).comap a = (piece s j').comap b := by
  refine Scheme.IdealSheafData.ext (funext fun Ω => ?_)
  refine ideal_eq_of_forall_exists_basicOpen _ _ Ω fun z hz => ?_
  have hzj : (a ≫ j.1.1.ι) z ∈ (j.1.1 : X.Opens) := by
    rw [Scheme.Hom.comp_apply]; exact (a z).2
  have hzj' : (a ≫ j.1.1.ι) z ∈ (j'.1.1 : X.Opens) := by
    rw [hab, Scheme.Hom.comp_apply]; exact (b z).2
  obtain ⟨_, ⟨W, hWa, rfl⟩, hzW, hWle⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show (a ≫ j.1.1.ι) z ∈ (j.1.1 : X.Opens) ⊓ j'.1.1 from ⟨hzj, hzj'⟩)
      ((j.1.1 : X.Opens) ⊓ j'.1.1).isOpen
  have hWj : W ≤ j.1.1 := fun x hx => (hWle hx).1
  have hWj' : W ≤ j'.1.1 := fun x hx => (hWle hx).2
  obtain ⟨g, hgle, hzg⟩ :=
    Ω.2.exists_basicOpen_le (V := (Ω : V.Opens) ⊓ (a ≫ j.1.1.ι) ⁻¹ᵁ W) ⟨z, hz, hzW⟩ hz
  refine ⟨g, hzg, ?_⟩
  have hΩ : (V.affineBasicOpen g : V.Opens) ≤ (a ≫ j.1.1.ι) ⁻¹ᵁ W :=
    hgle.trans inf_le_right
  have hΩ' : (V.affineBasicOpen g : V.Opens) ≤ (b ≫ j'.1.1.ι) ⁻¹ᵁ W := hab ▸ hΩ
  rw [ideal_comap_piece s j a hWj hWa _ hΩ, ideal_comap_piece s j' b hWj' hWa _ hΩ']
  have key := congrArg (Ideal.map ((a ≫ j.1.1.ι).appLE W (V.affineBasicOpen g) hΩ).hom)
    (span_cX_eq s j j' hWj hWj')
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton] at key
  refine key.trans ?_
  have hc : ∀ {v₁ v₂ : V ⟶ X} (_ : v₁ = v₂) (h₁ : (V.affineBasicOpen g : V.Opens) ≤ v₁ ⁻¹ᵁ W)
      (h₂ : (V.affineBasicOpen g : V.Opens) ≤ v₂ ⁻¹ᵁ W),
      v₁.appLE W (V.affineBasicOpen g) h₁ = v₂.appLE W (V.affineBasicOpen g) h₂ := by
    rintro _ _ rfl _ _; rfl
  rw [hc hab hΩ hΩ']

lemma coeff_eq_cX (φ : M.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff s U φ = cX s φ (le_refl U) := by
  have h : U.ι ''ᵁ ⊤ ≤ U := (Scheme.Opens.ι_image_top U).le
  rw [← map_cX s φ h (Scheme.Opens.ι_image_top U).ge, cX_image, ← cf_top, Scheme.Opens.topIso_hom]
  exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (X.presheaf.map k)))
    (Subsingleton.elim _ _)) _

variable (hM : IsLineBundle M)

def P : X.IdealSheafData :=
  (Scheme.IdealSheafData.exists_comap_eq_of_openCover (cover hM) (fun j => piece s j)
    (fun j j' _ a b hab => comap_piece_eq s j j' a b hab)).choose

lemma P_comap (j : Idx M) : (P s hM).comap j.1.1.ι = piece s j :=
  (Scheme.IdealSheafData.exists_comap_eq_of_openCover (cover hM) (fun j => piece s j)
    (fun j j' _ a b hab => comap_piece_eq s j j' a b hab)).choose_spec j

lemma ideal_P_self (W : X.affineOpens) (τ : M.restrict W.1.ι ≅ 𝟙_ (W.1 : Scheme.{u}).Modules) :
    (P s hM).ideal W = Ideal.span {cX s τ.hom (le_refl _)} := by
  have : IsAffine (W.1 : Scheme.{u}) := W.2
  let T : (W.1 : Scheme.{u}).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have h1 := congrArg (fun I : (W.1 : Scheme.{u}).IdealSheafData => I.ideal T)
    (P_comap s hM ⟨W, τ⟩)
  dsimp only at h1
  rw [ideal_piece, Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso,
    Iso.refl_inv] at h1
  change Ideal.comap (RingHom.id _) _ = _ at h1
  rw [Ideal.comap_id] at h1
  have h1' : (P s hM).ideal ⟨W.1.ι ''ᵁ ⊤, T.2.image_of_isOpenImmersion _⟩ =
      Ideal.span {(cf s τ.hom ⊤ : Γ(X, W.1.ι ''ᵁ ⊤))} := h1
  have hle : (W.1 : X.Opens) ≤ W.1.ι ''ᵁ ⊤ := (Scheme.Opens.ι_image_top _).ge
  rw [← Scheme.IdealSheafData.map_ideal (P s hM) (U := W)
    (V := ⟨W.1.ι ''ᵁ ⊤, T.2.image_of_isOpenImmersion _⟩) hle, h1', Ideal.map_span,
    Set.image_singleton]
  refine congrArg (fun x => Ideal.span ({x} : Set Γ(X, W.1))) ?_
  change (X.presheaf.map (homOfLE hle).op) (cf s τ.hom ⊤) = _
  rw [← cX_image s τ.hom ⊤ (Scheme.Opens.ι_image_top _).le,
    map_cX s τ.hom (Scheme.Opens.ι_image_top _).le hle]

lemma ideal_P_of_le (W : X.affineOpens) (τ : M.restrict W.1.ι ≅ 𝟙_ (W.1 : Scheme.{u}).Modules)
    (Ω : X.affineOpens) (h : (Ω : X.Opens) ≤ W.1) :
    (P s hM).ideal Ω = Ideal.span {cX s τ.hom h} := by
  rw [← Scheme.IdealSheafData.map_ideal (P s hM) h, ideal_P_self, Ideal.map_span,
    Set.image_singleton]
  exact congrArg (fun x => Ideal.span ({x} : Set Γ(X, Ω.1))) (map_cX s τ.hom (le_refl _) h)

lemma coeffIdeal_le_P (V : X.affineOpens) : coeffIdeal s V.1 ≤ (P s hM).ideal V := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨φ, rfl⟩
  refine mem_ideal_of_forall_exists_basicOpen _ V _ fun x hx => ?_
  obtain ⟨W, hxW, hWV, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := V.1) hx
  obtain ⟨g, hgW, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxW⟩ hx
  refine ⟨g, hxg, ?_⟩
  rw [ideal_P_of_le s hM W τ (X.affineBasicOpen g) hgW]
  refine Ideal.mem_span_singleton.mpr ?_
  rw [coeff_eq_cX, map_cX s φ (le_refl _) (X.basicOpen_le g)]
  have := cX_dvd s τ hgW (tX φ ((X.basicOpen_le g).trans (le_refl _))) (tX_smul φ _)
  rw [tX_sApp] at this
  exact this

lemma P_le (J : X.IdealSheafData) (hJ : ∀ U : X.affineOpens, coeffIdeal s U.1 ≤ J.ideal U) :
    P s hM ≤ J := by
  refine Scheme.IdealSheafData.le_def.mpr fun V r hr => ?_
  refine mem_ideal_of_forall_exists_basicOpen J V r fun x hx => ?_
  obtain ⟨W, hxW, hWV, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := V.1) hx
  obtain ⟨g, hgW, hxg⟩ := V.2.exists_basicOpen_le ⟨x, hxW⟩ hx
  refine ⟨g, hxg, ?_⟩
  have h1 : X.presheaf.map (homOfLE (X.basicOpen_le g)).op r ∈
      (P s hM).ideal (X.affineBasicOpen g) := by
    rw [← (P s hM).map_ideal_basicOpen]
    exact Ideal.mem_map_of_mem _ hr
  rw [ideal_P_of_le s hM W τ (X.affineBasicOpen g) hgW] at h1
  refine (Ideal.span_singleton_le_iff_mem _).mpr ?_ h1
  have e : (X.presheaf.map (homOfLE hgW).op).hom (coeff s W τ.hom) = cX s τ.hom hgW := by
    rw [coeff_eq_cX]; exact map_cX s τ.hom (le_refl _) hgW
  have mem : (X.presheaf.map (homOfLE hgW).op).hom (coeff s W τ.hom) ∈
      J.ideal (X.affineBasicOpen g) := by
    rw [← Scheme.IdealSheafData.map_ideal J (U := X.affineBasicOpen g) (V := W) hgW]
    exact Ideal.mem_map_of_mem _ (hJ W (coeff_mem_coeffIdeal s W.1 τ.hom))
  rw [e] at mem
  exact mem

theorem zeroSchemeIdeal_eq_P : zeroSchemeIdeal s = P s hM :=
  zeroSchemeIdeal_eq_of_isLeast ⟨coeffIdeal_le_P s hM, fun J hJ => P_le s hM J hJ⟩

end ZeroSchemeLoc


end AlgebraicGeometry.Scheme.Modules

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

/-- For a line bundle `M` and a section `s`, the zero ideal sheaf of `s` contains `coeffIdeal s V`
on every affine open `V`, and on an affine open `U` where `M` is trivialized by `τ` it is generated
by the single coefficient `coeff s U τ.hom` and equals `coeffIdeal s U`. -/
public theorem IsLineBundle.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
    {X : Scheme.{u}} {M : X.Modules} (hM : IsLineBundle M) (s : 𝟙_ X.Modules ⟶ M) :
    (∀ V : X.affineOpens,
        Scheme.Modules.coeffIdeal s V.1 ≤ (Scheme.Modules.zeroSchemeIdeal s).ideal V) ∧
    ∀ (U : X.affineOpens) (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
      (Scheme.Modules.zeroSchemeIdeal s).ideal U = Ideal.span {Scheme.Modules.coeff s U.1 τ.hom} ∧
        (Scheme.Modules.zeroSchemeIdeal s).ideal U = Scheme.Modules.coeffIdeal s U.1 := by
  rw [ZeroSchemeLoc.zeroSchemeIdeal_eq_P s hM]
  refine ⟨ZeroSchemeLoc.coeffIdeal_le_P s hM, fun U τ => ?_⟩
  have h := ZeroSchemeLoc.ideal_P_self s hM U τ
  rw [← ZeroSchemeLoc.coeff_eq_cX] at h
  refine ⟨h, le_antisymm ?_ (ZeroSchemeLoc.coeffIdeal_le_P s hM U)⟩
  rw [h]
  exact (Ideal.span_singleton_le_iff_mem _).mpr (Scheme.Modules.coeff_mem_coeffIdeal s U.1 τ.hom)

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

namespace AlgebraicGeometry.Scheme.Modules


namespace PullSections


variable {X X' : Scheme.{u}} (F : X' ⟶ X)

abbrev unitApp (N : X.Modules) :
    N ⟶ (Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback F).obj N) :=
  (Scheme.Modules.pullbackPushforwardAdjunction F).unit.app N

variable {F} in
lemma map_localPullback {N N' : X.Modules} (g : N ⟶ N') (U : X.Opens) (m : Γ(N, U)) :
    ((Scheme.Modules.pullback F).map g).app (F ⁻¹ᵁ U) (localPullback F N U m) =
      localPullback F N' U (g.app U m) := by
  have nat : g ≫ unitApp F N' =
      unitApp F N ≫ (Scheme.Modules.pushforward F).map ((Scheme.Modules.pullback F).map g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction F).unit.naturality g
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U m) nat
  dsimp only at h
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app] at h
  exact h.symm

lemma localPullback_map (N : X.Modules) {U V : X.Opens} (i : V ⟶ U) (m : Γ(N, U)) :
    ((Scheme.Modules.pullback F).obj N).presheaf.map
        ((TopologicalSpace.Opens.map F.base).map i).op (localPullback F N U m) =
      localPullback F N V (N.presheaf.map i.op m) := by
  have nat := congrArg (fun g => g m) ((unitApp F N).mapPresheaf.naturality i.op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  exact nat.symm

lemma localPullback_smul (N : X.Modules) (U : X.Opens) (r : Γ(X, U)) (m : Γ(N, U)) :
    localPullback F N U (r • m) = F.app U r • localPullback F N U m :=
  Scheme.Modules.Hom.app_smul (unitApp F N) r m

lemma pullbackStructureModuleIso_hom_localPullback (U : X.Opens) (r : Γ(X, U)) :
    (pullbackStructureModuleIso F).hom.app (F ⁻¹ᵁ U)
        (localPullback F (𝟙_ X.Modules) U (toUnitSection U r)) =
      toUnitSection (F ⁻¹ᵁ U) (F.app U r) := by
  have key0 := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    F.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at key0
  have key : unitApp F (𝟙_ X.Modules) ≫
      (Scheme.Modules.pushforward F).map (pullbackStructureModuleIso F).hom =
      (SheafOfModules.unitToPushforwardObjUnit F.toRingCatSheafHom :
        (𝟙_ X.Modules) ⟶ (Scheme.Modules.pushforward F).obj (𝟙_ X'.Modules)) := key0
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U (toUnitSection U r)) key
  dsimp only at h
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app] at h
  exact h

lemma restrictFunctorIsoPullback_hom_app_apply {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (N : X.Modules) (U : X.Opens) (m : Γ(N, U)) :
    ((restrictFunctorIsoPullback j).hom.app N).app (j ⁻¹ᵁ U)
        (N.presheaf.map (homOfLE (j.image_preimage_le U)).op m) = localPullback j N U m := by
  have h : ((restrictAdjunction j).unit.app N :
      N ⟶ (Scheme.Modules.pushforward j).obj (N.restrict j)) ≫
      (Scheme.Modules.pushforward j).map ((restrictFunctorIsoPullback j).hom.app N) = unitApp j N :=
    Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j)
      (Scheme.Modules.pullbackPushforwardAdjunction j) N
  exact congrArg (fun k => Scheme.Modules.Hom.app k U m) h

lemma restrictFunctorIsoPullback_inv_app_localPullback {Y : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j]
    (N : X.Modules) (U : X.Opens) (m : Γ(N, U)) :
    ((restrictFunctorIsoPullback j).inv.app N).app (j ⁻¹ᵁ U) (localPullback j N U m) =
      N.presheaf.map (homOfLE (j.image_preimage_le U)).op m := by
  rw [← restrictFunctorIsoPullback_hom_app_apply]
  have := congrArg (fun k => Scheme.Modules.Hom.app k (j ⁻¹ᵁ U)
    (N.presheaf.map (homOfLE (j.image_preimage_le U)).op m))
    ((restrictFunctorIsoPullback j).hom_inv_id_app N)
  dsimp only at this
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at this
  exact this

lemma pullbackCongr_hom_app_localPullback {f₁ f₂ : X' ⟶ X} (e : f₁ = f₂) (N : X.Modules)
    (U : X.Opens)
    (m : Γ(N, U)) :
    ((pullbackCongr e).hom.app N).app (f₁ ⁻¹ᵁ U) (localPullback f₁ N U m) =
      ((Scheme.Modules.pullback f₂).obj N).presheaf.map
        (eqToHom (show f₁ ⁻¹ᵁ U = f₂ ⁻¹ᵁ U by rw [e])).op (localPullback f₂ N U m) := by
  subst e
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  rfl

lemma pullbackComp_inv_app_localPullback {Y : Scheme.{u}} (f : X' ⟶ Y) (g : Y ⟶ X) (N : X.Modules)
    (U : X.Opens) (m : Γ(N, U)) :
    ((pullbackComp f g).inv.app N).app ((f ≫ g) ⁻¹ᵁ U) (localPullback (f ≫ g) N U m) =
      localPullback f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U) (localPullback g N U m) := by
  have h0 := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv N
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h0
  have h : ((unitApp g N ≫ (Scheme.Modules.pushforward g).map
      (unitApp f ((Scheme.Modules.pullback g).obj N))) ≫
      (pushforwardComp f g).hom.app
        ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj N)) :
        N ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj _) =
      unitApp (f ≫ g) N ≫ (Scheme.Modules.pushforward (f ≫ g)).map ((pullbackComp f g).inv.app N) :=
    h0
  exact (congrArg (fun k => Scheme.Modules.Hom.app k U m) h).symm

lemma pullbackComp_hom_app_localPullback {Y : Scheme.{u}} (f : X' ⟶ Y) (g : Y ⟶ X) (N : X.Modules)
    (U : X.Opens) (m : Γ(N, U)) :
    ((pullbackComp f g).hom.app N).app ((f ≫ g) ⁻¹ᵁ U)
        (localPullback f ((Scheme.Modules.pullback g).obj N) (g ⁻¹ᵁ U) (localPullback g N U m)) =
      localPullback (f ≫ g) N U m := by
  rw [← pullbackComp_inv_app_localPullback]
  have := congrArg (fun k => Scheme.Modules.Hom.app k ((f ≫ g) ⁻¹ᵁ U) (localPullback (f ≫ g) N U m))
    ((pullbackComp f g).inv_hom_id_app N)
  dsimp only at this
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at this
  exact this

end PullSections



namespace ZeroSchemeBC

open PullSections ZeroSchemeLoc


variable {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M)

lemma app_map {Y : Scheme.{u}} {N N' : Y.Modules} (φ : N ⟶ N') {W₁ W₂ : Y.Opens} (i : W₁ ⟶ W₂)
    (x : Γ(N, W₂)) : φ.app W₁ (N.presheaf.map i.op x) = N'.presheaf.map i.op (φ.app W₂ x) := by
  have nat := congrArg (fun g => g x) (φ.mapPresheaf.naturality i.op)
  simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
  exact nat

lemma inv_app_hom_app {Y : Scheme.{u}} {N N' : Y.Modules} (e : N ≅ N') (W : Y.Opens) (x : Γ(N, W)) :
    e.inv.app W (e.hom.app W x) = x := by
  have := congrArg (fun k => Scheme.Modules.Hom.app k W x) e.hom_inv_id
  dsimp only at this
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at this
  exact this

lemma pullbackSection_app (U : X.Opens) :
    (pullbackSection F s).app (F ⁻¹ᵁ U) (toUnitSection (F ⁻¹ᵁ U) 1) =
      localPullback F M U (s.app U (toUnitSection U 1)) := by
  have h1 : (pullbackStructureModuleIso F).hom.app (F ⁻¹ᵁ U)
      (localPullback F (𝟙_ X.Modules) U (toUnitSection U 1)) = toUnitSection (F ⁻¹ᵁ U) 1 := by
    rw [pullbackStructureModuleIso_hom_localPullback, map_one]
  have h2 : (pullbackStructureModuleIso F).inv.app (F ⁻¹ᵁ U) (toUnitSection (F ⁻¹ᵁ U) 1) =
      localPullback F (𝟙_ X.Modules) U (toUnitSection U 1) := by
    rw [← h1, inv_app_hom_app]
  change ((pullbackStructureModuleIso F).inv ≫ (Scheme.Modules.pullback F).map s).app (F ⁻¹ᵁ U)
    (toUnitSection (F ⁻¹ᵁ U) 1) = _
  rw [Scheme.Modules.Hom.comp_app]
  change ((Scheme.Modules.pullback F).map s).app (F ⁻¹ᵁ U)
    ((pullbackStructureModuleIso F).inv.app (F ⁻¹ᵁ U) (toUnitSection (F ⁻¹ᵁ U) 1)) = _
  rw [h2, map_localPullback]

lemma G_comp {U : X.Opens} {Ω : X'.Opens} (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    F.resLE U Ω hΩ ≫ U.ι = Ω.ι ≫ F := Scheme.Hom.resLE_comp_ι F hΩ

def triv {U : X.Opens} (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules) {Ω : X'.Opens}
    (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    ((Scheme.Modules.pullback F).obj M).restrict Ω.ι ≅ 𝟙_ (Ω : Scheme.{u}).Modules :=
  (restrictFunctorIsoPullback Ω.ι).app _ ≪≫
  (pullbackComp Ω.ι F).app M ≪≫
  (pullbackCongr (G_comp F hΩ).symm).app M ≪≫
  ((pullbackComp (F.resLE U Ω hΩ) U.ι).app M).symm ≪≫
  (Scheme.Modules.pullback (F.resLE U Ω hΩ)).mapIso
    (((restrictFunctorIsoPullback U.ι).app M).symm ≪≫ τ) ≪≫
  pullbackStructureModuleIso (F.resLE U Ω hΩ)

lemma V₀_eq {U : X.Opens} {Ω : X'.Opens} (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    (Ω.ι ≫ F) ⁻¹ᵁ U = (F.resLE U Ω hΩ ≫ U.ι) ⁻¹ᵁ U := by
  rw [G_comp]

lemma app_triv_sAt {U : X.Opens} (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules)
    {Ω : X'.Opens} (hΩ : Ω ≤ F ⁻¹ᵁ U) :
    (triv F τ hΩ).hom.app ((Ω.ι ≫ F) ⁻¹ᵁ U) (sAt (pullbackSection F s) Ω ((Ω.ι ≫ F) ⁻¹ᵁ U)) =
      (𝟙_ (Ω : Scheme.{u}).Modules).presheaf.map (eqToHom (V₀_eq F hΩ)).op
        (toUnitSection ((F.resLE U Ω hΩ) ⁻¹ᵁ (U.ι ⁻¹ᵁ U))
          ((F.resLE U Ω hΩ).app (U.ι ⁻¹ᵁ U) (cf s τ.hom (U.ι ⁻¹ᵁ U)))) := by
  set sU := s.app U (toUnitSection U 1) with hsU
  have hin : sAt (pullbackSection F s) Ω ((Ω.ι ≫ F) ⁻¹ᵁ U) =
      ((Scheme.Modules.pullback F).obj M).presheaf.map
        (homOfLE (Ω.ι.image_preimage_le (F ⁻¹ᵁ U))).op (localPullback F M U sU) := by
    rw [← pullbackSection_app]
    unfold sAt
    have nat := congrArg (fun g => g (toUnitSection (F ⁻¹ᵁ U) 1))
      ((pullbackSection F s).mapPresheaf.naturality
        (homOfLE (Ω.ι.image_preimage_le (F ⁻¹ᵁ U))).op)
    simp only [Scheme.Modules.mapPresheaf_app, Opposite.unop_op, ConcreteCategory.comp_apply] at nat
    rw [← nat]
    erw [unit_map_one]
    rfl
  rw [hin]
  unfold triv
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.trans_hom,
    Scheme.Modules.Hom.comp_app]
  change (pullbackStructureModuleIso (F.resLE U Ω hΩ)).hom.app _
    (((Scheme.Modules.pullback (F.resLE U Ω hΩ)).map
      (((restrictFunctorIsoPullback U.ι).inv.app M) ≫ τ.hom)).app _
      (((pullbackComp (F.resLE U Ω hΩ) U.ι).inv.app M).app _
        (((pullbackCongr (G_comp F hΩ).symm).hom.app M).app ((Ω.ι ≫ F) ⁻¹ᵁ U)
          (((pullbackComp Ω.ι F).hom.app M).app ((Ω.ι ≫ F) ⁻¹ᵁ U)
            (((restrictFunctorIsoPullback Ω.ι).hom.app _).app ((Ω.ι ≫ F) ⁻¹ᵁ U)
              (((Scheme.Modules.pullback F).obj M).presheaf.map
                (homOfLE (Ω.ι.image_preimage_le (F ⁻¹ᵁ U))).op (localPullback F M U sU))))))) = _
  have hA : ((restrictFunctorIsoPullback Ω.ι).hom.app ((Scheme.Modules.pullback F).obj M)).app
      ((Ω.ι ≫ F) ⁻¹ᵁ U) (((Scheme.Modules.pullback F).obj M).presheaf.map
        (homOfLE (Ω.ι.image_preimage_le (F ⁻¹ᵁ U))).op (localPullback F M U sU)) =
      localPullback Ω.ι ((Scheme.Modules.pullback F).obj M) (F ⁻¹ᵁ U) (localPullback F M U sU) :=
    restrictFunctorIsoPullback_hom_app_apply Ω.ι _ (F ⁻¹ᵁ U) (localPullback F M U sU)
  rw [hA]
  rw [pullbackComp_hom_app_localPullback Ω.ι F M U sU]
  rw [pullbackCongr_hom_app_localPullback (G_comp F hΩ).symm M U sU]
  change ((((pullbackComp (F.resLE U Ω hΩ) U.ι).inv.app M) ≫
    ((Scheme.Modules.pullback (F.resLE U Ω hΩ)).map
      (((restrictFunctorIsoPullback U.ι).inv.app M) ≫ τ.hom)) ≫
    (pullbackStructureModuleIso (F.resLE U Ω hΩ)).hom).app ((Ω.ι ≫ F) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback (F.resLE U Ω hΩ ≫ U.ι)).obj M).presheaf.map
        (eqToHom (show (Ω.ι ≫ F) ⁻¹ᵁ U = (F.resLE U Ω hΩ ≫ U.ι) ⁻¹ᵁ U by rw [G_comp])).op
        (localPullback (F.resLE U Ω hΩ ≫ U.ι) M U sU))) = _
  rw [app_map, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  refine congrArg ((𝟙_ (Ω : Scheme.{u}).Modules).presheaf.map _) ?_
  change (pullbackStructureModuleIso (F.resLE U Ω hΩ)).hom.app _
    (((Scheme.Modules.pullback (F.resLE U Ω hΩ)).map
      (((restrictFunctorIsoPullback U.ι).inv.app M) ≫ τ.hom)).app _
      (((pullbackComp (F.resLE U Ω hΩ) U.ι).inv.app M).app ((F.resLE U Ω hΩ ≫ U.ι) ⁻¹ᵁ U)
        (localPullback (F.resLE U Ω hΩ ≫ U.ι) M U sU))) = _
  rw [pullbackComp_inv_app_localPullback (F.resLE U Ω hΩ) U.ι M U sU]
  change (pullbackStructureModuleIso (F.resLE U Ω hΩ)).hom.app ((F.resLE U Ω hΩ) ⁻¹ᵁ (U.ι ⁻¹ᵁ
      U))
      (((Scheme.Modules.pullback (F.resLE U Ω hΩ)).map
        (((restrictFunctorIsoPullback U.ι).inv.app M) ≫
            τ.hom)).app ((F.resLE U Ω hΩ) ⁻¹ᵁ (U.ι ⁻¹ᵁ U))
        (localPullback (F.resLE U Ω hΩ) _ (U.ι ⁻¹ᵁ U) (localPullback U.ι M U sU))) = _
  rw [map_localPullback, Scheme.Modules.Hom.comp_app]
  change (pullbackStructureModuleIso (F.resLE U Ω hΩ)).hom.app _
      (localPullback (F.resLE U Ω hΩ) _ (U.ι ⁻¹ᵁ U)
        (τ.hom.app (U.ι ⁻¹ᵁ U)
          (((restrictFunctorIsoPullback U.ι).inv.app M).app (U.ι ⁻¹ᵁ U)
            (localPullback U.ι M U sU)))) = _
  rw [restrictFunctorIsoPullback_inv_app_localPullback]
  have hres : M.presheaf.map (homOfLE (U.ι.image_preimage_le U)).op sU = sAt s U (U.ι ⁻¹ᵁ U) := by
    rw [hsU, ← resM'_sApp s (le_refl U)]
    exact congrFun (congrArg (fun k => ⇑(ConcreteCategory.hom (M.presheaf.map k)))
      (Subsingleton.elim _ _)) _
  rw [hres]
  have hτ : τ.hom.app (U.ι ⁻¹ᵁ U) (sAt s U (U.ι ⁻¹ᵁ U)) =
      toUnitSection (X := (U : Scheme.{u})) (U.ι ⁻¹ᵁ U) (cf s τ.hom (U.ι ⁻¹ᵁ U)) := rfl
  rw [hτ]
  exact pullbackStructureModuleIso_hom_localPullback (F.resLE U Ω hΩ) (U.ι ⁻¹ᵁ U)
    (cf s τ.hom (U.ι ⁻¹ᵁ U))

lemma gen_eq (U : X.affineOpens) (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
    (Ω : X'.affineOpens) (hΩ : (Ω : X'.Opens) ≤ F ⁻¹ᵁ (U : X.Opens)) :
    (F.appLE U Ω hΩ).hom (coeff s U.1 τ.hom) =
        coeff (pullbackSection F s) Ω.1 (triv F τ hΩ).hom := by
  rw [coeff_eq_cX]
  change (F.appLE U Ω hΩ).hom ((X.presheaf.map (homOfLE _).op).hom (cf s τ.hom (U.1.ι ⁻¹ᵁ U.1))) = _
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rw [← cf_top]
  have hi : (⊤ : (Ω.1 : Scheme.{u}).Opens) ≤ (Ω.1.ι ≫ F) ⁻¹ᵁ U.1 := fun x _ => hΩ x.2
  rw [← map_cf (pullbackSection F s) (triv F τ hΩ).hom (homOfLE hi)]
  unfold cf coord
  rw [app_triv_sAt]
  change (F.appLE _ _ _).hom (cf s τ.hom (U.1.ι ⁻¹ᵁ U.1)) =
    ((F.resLE U.1 Ω.1 hΩ).app (U.1.ι ⁻¹ᵁ U.1) ≫ X'.presheaf.map _ ≫ X'.presheaf.map _ ≫
      X'.presheaf.map _).hom (cf s τ.hom (U.1.ι ⁻¹ᵁ U.1))
  rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
  change _ = (F.appLE _ _ _ ≫ X'.presheaf.map _ ≫ X'.presheaf.map _ ≫ X'.presheaf.map _).hom
    (cf s τ.hom (U.1.ι ⁻¹ᵁ U.1))
  simp only [← Functor.map_comp]
  erw [Scheme.Hom.appLE_map]

lemma ideal_eq_of_le (hM : IsLineBundle M) (U : X.affineOpens) (τ : M.restrict
    U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
    (Ω : X'.affineOpens) (hΩ : (Ω : X'.Opens) ≤ F ⁻¹ᵁ (U : X.Opens)) :
    ((zeroSchemeIdeal s).comap F).ideal Ω = (zeroSchemeIdeal (pullbackSection F s)).ideal Ω := by
  rw [IdealSheafComapMulAux.ideal_comap_of_le _ F U Ω hΩ,
    ((hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U τ).1, Ideal.map_span,
    Set.image_singleton]
  have hM' : IsLineBundle ((Scheme.Modules.pullback F).obj M) := hM.pullback F
  rw [((hM'.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq (pullbackSection F s)).2 Ω
    (triv F τ hΩ)).1]
  exact congrArg (fun x => Ideal.span ({x} : Set Γ(X', Ω.1))) (gen_eq F s U τ Ω hΩ)

theorem comap_zeroSchemeIdeal_eq (hM : IsLineBundle M) :
    (zeroSchemeIdeal s).comap F = zeroSchemeIdeal (pullbackSection F s) := by
  refine Scheme.IdealSheafData.ext (funext fun Ω₀ => ?_)
  refine ideal_eq_of_forall_exists_basicOpen _ _ Ω₀ fun z hz => ?_
  obtain ⟨U, hzU, -, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := F z) trivial
  obtain ⟨g, hgle, hzg⟩ :=
    Ω₀.2.exists_basicOpen_le (V := (Ω₀ : X'.Opens) ⊓ F ⁻¹ᵁ U.1) ⟨z, hz, hzU⟩ hz
  exact ⟨g, hzg, ideal_eq_of_le F s hM U τ (X'.affineBasicOpen g) (hgle.trans inf_le_right)⟩

end ZeroSchemeBC


end AlgebraicGeometry.Scheme.Modules

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

/-- For a line bundle, the zero ideal sheaf commutes with pullback: its comap along `F` is the zero
ideal sheaf of the pulled-back section `pullbackSection F s`. -/
public theorem IsLineBundle.comap_zeroSchemeIdeal
    {X X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules} (hM : IsLineBundle M)
    (s : 𝟙_ X.Modules ⟶ M) :
    (Scheme.Modules.zeroSchemeIdeal s).comap F =
      Scheme.Modules.zeroSchemeIdeal (pullbackSection F s) :=
  ZeroSchemeBC.comap_zeroSchemeIdeal_eq F s hM

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

namespace AlgebraicGeometry.Scheme.Modules

namespace ZeroSchemeComp

open AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M M' : X.Modules}

theorem restrictFunctor_map_app {U : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (f : M ⟶ M')
    (W : U.Opens) : ((Scheme.Modules.restrictFunctor i).map f).app W = f.app (i ''ᵁ W) := rfl

theorem restrictSection_comp (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens) :
    restrictSection (s ≫
        f) U = ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤ (restrictSection s U) := by
  rfl

theorem coeff_comp (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens)
    (φ : M'.restrict U.ι ⟶ 𝟙_ (U : Scheme.{u}).Modules) :
    coeff (s ≫ f) U φ = coeff s U ((Scheme.Modules.restrictFunctor U.ι).map f ≫ φ) := by
  rfl

theorem coeffIdeal_comp_le (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') (U : X.Opens) :
    coeffIdeal (s ≫ f) U ≤ coeffIdeal s U := by
  apply Ideal.span_mono
  rintro _ ⟨φ, rfl⟩
  exact ⟨(Scheme.Modules.restrictFunctor U.ι).map f ≫ φ, (coeff_comp s f U φ).symm⟩

end ZeroSchemeComp

public theorem zeroSchemeIdeal_comp_le
    {X : Scheme.{u}} {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') :
    Scheme.Modules.zeroSchemeIdeal (s ≫ f) ≤ Scheme.Modules.zeroSchemeIdeal s := by
  apply Scheme.Modules.le_zeroSchemeIdeal
  intro J hJ
  exact Scheme.Modules.zeroSchemeIdeal_le fun U => (ZeroSchemeComp.coeffIdeal_comp_le s f
      U.1).trans (hJ U)
public theorem zeroSchemeIdeal_comp_eq_of_isIso
    {X : Scheme.{u}} {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') [IsIso f] :
    zeroSchemeIdeal (s ≫ f) = zeroSchemeIdeal s := by
  refine le_antisymm (zeroSchemeIdeal_comp_le s f) ?_
  have h := zeroSchemeIdeal_comp_le (s ≫ f) (inv f)
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
end AlgebraicGeometry.Scheme.Modules

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

-- `IsLineBundle.moduleTensor` transported along `moduleTensor X L M ≅ L ⊗ M`.
private theorem IsLineBundle.tensor {X : AlgebraicGeometry.Scheme.{u}}
    {L M : X.Modules} (hL : IsLineBundle L)
    (hM : IsLineBundle M) :
    IsLineBundle (L ⊗ M) := by
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := hL.moduleTensor hM x
  exact ⟨U, hxU, ⟨(Scheme.Modules.pullback U.ι).mapIso (moduleTensorIso L M).symm ≪≫ e⟩⟩

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

namespace AlgebraicGeometry.Scheme.Modules

namespace TensorHomApp

open Functor.LaxMonoidal Functor.OplaxMonoidal

abbrev adj (Z : Scheme.{u}) := SheafOfModules.sheafifyAdj Z.sheaf.obj Z.ringCatSheaf.property

abbrev forgetPre (Z : Scheme.{u}) := SheafOfModules.toPMod Z.sheaf.obj Z.ringCatSheaf.property

def shUnit {Z : Scheme.{u}} (A : Z.PresheafOfModules) (W : Z.Opens) (a : A.obj (op W)) :
    Γ((Modules.sheafify Z).obj A, W) :=
  ((adj Z).unit.app A).app (op W) a

lemma sheafify_map_app_shUnit {Z : Scheme.{u}} {A A' : Z.PresheafOfModules} (g : A ⟶ A') (W :
    Z.Opens)
    (z : A.obj (op W)) :
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) =
        shUnit A' W (g.app (op W) z) := by
  have h := (adj Z).unit.naturality g
  exact (congr($(h.symm).app (op W) z) :)

variable {Y : Scheme.{u}}

def cmpIso (L M : Y.Modules) : (Modules.sheafify Y).obj ((forgetPre Y).obj L ⊗ (forgetPre Y).obj
    M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify Y) ((forgetPre Y).obj L) ((forgetPre Y).obj M)).symm ≪≫
    ((asIso (adj Y).counit).app L ⊗ᵢ (asIso (adj Y).counit).app M)

lemma cmpIso_hom (L M : Y.Modules) :
    (cmpIso L M).hom = δ (Modules.sheafify Y) ((forgetPre Y).obj L) ((forgetPre Y).obj M) ≫
      ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) := rfl

lemma tensorSections_eq (L M : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) (t : Γ(M, V)) :
    Modules.tensorSections s t = Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y,
          V)] (t : M.val.obj (op V)))) := rfl

lemma cmpIso_hom_comp_tensorHom {L L' M M' : Y.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') :
    (cmpIso L M).hom ≫ (φ ⊗ₘ ψ) =
      (Modules.sheafify Y).map ((forgetPre Y).map φ ⊗ₘ (forgetPre Y).map ψ) ≫
          (cmpIso L' M').hom := by
  have hφ := (adj Y).counit.naturality φ
  have hψ := (adj Y).counit.naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at hφ hψ
  have hε : ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) ≫ (φ ⊗ₘ ψ) =
      ((Modules.sheafify Y).map ((forgetPre Y).map φ) ⊗ₘ (Modules.sheafify Y).map ((forgetPre
          Y).map ψ)) ≫
        ((adj Y).counit.app L' ⊗ₘ (adj Y).counit.app M') := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
    erw [← hφ, ← hψ]
    rfl
  have hδ := Functor.OplaxMonoidal.δ_natural (Modules.sheafify Y) ((forgetPre Y).map φ)
      ((forgetPre Y).map ψ)
  rw [cmpIso_hom, cmpIso_hom, Category.assoc, hε, ← Category.assoc]
  erw [hδ]
  rw [Category.assoc]

lemma tensorHom_app_tensorSections {L L' M M' : Y.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') (V : Y.Opens)
    (s : Γ(L, V)) (t : Γ(M, V)) :
    Scheme.Modules.Hom.app (φ ⊗ₘ ψ) V (Modules.tensorSections s t) =
      Modules.tensorSections (Scheme.Modules.Hom.app φ V s) (Scheme.Modules.Hom.app ψ V t) := by
  have h := congr(Scheme.Modules.Hom.app $(cmpIso_hom_comp_tensorHom φ ψ) V
    (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y,
        V)] (t : M.val.obj (op V)))))
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h
  change Scheme.Modules.Hom.app (φ ⊗ₘ ψ) V (Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y,
          V)] (t : M.val.obj (op V))))) =
    Scheme.Modules.Hom.app (cmpIso L' M').hom V (Scheme.Modules.Hom.app
      ((Modules.sheafify Y).map ((forgetPre Y).map φ ⊗ₘ (forgetPre Y).map ψ)) V
      (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y,
          V)] (t : M.val.obj (op V))))) at h
  rw [sheafify_map_app_shUnit] at h
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul] at h
  rw [tensorSections_eq, tensorSections_eq]
  exact h

end TensorHomApp



public theorem tensorHom_app_tensorSections
    {X : Scheme.{u}} {L L' M M' : X.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ⊗ₘ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (φ.app U s) (ψ.app U t) := by
  exact AlgebraicGeometry.Scheme.Modules.TensorHomApp.tensorHom_app_tensorSections φ ψ U s t
namespace UnitorSections

open Opposite TensorProduct

variable {X : Scheme.{u}}

open TensorHomApp (adj forgetPre)

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z :
    P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma counit_val_app_unit (N : X.Modules) (V : (X.Opens)ᵒᵖ) (y : N.val.obj V) :
    (((adj X).counit.app N).val.app V) (((adj X).unit.app ((forgetPre X).obj N)).app V y) = y := by
  have h := (adj X).right_triangle_components N
  exact (congr($(h).app V y) :)

variable (N : X.Modules)

def unitTensorIso : (Modules.sheafify X).obj (𝟙_ X.PresheafOfModules ⊗ (forgetPre X).obj N) ≅ 𝟙_
    X.Modules ⊗ N :=
  (Functor.Monoidal.μIso (Modules.sheafify X) (𝟙_ X.PresheafOfModules) ((forgetPre X).obj N)).symm
      ≪≫
    ((Functor.Monoidal.εIso (Modules.sheafify X)).symm ⊗ᵢ (asIso (adj X).counit).app N)

lemma unitTensorIso_hom_comp_leftUnitor_hom :
    (unitTensorIso N).hom ≫ (λ_ N).hom =
      (Modules.sheafify X).map (λ_ ((forgetPre X).obj N)).hom ≫ (adj X).counit.app N := by
  dsimp only [unitTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_inv]
  rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, Functor.Monoidal.map_leftUnitor,
    MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  erw [← MonoidalCategory.leftUnitor_naturality ((adj X).counit.app N)]
  rfl

theorem leftUnitor_hom_app_tensorSections {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U (Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n := by
  have h := congr($(unitTensorIso_hom_comp_leftUnitor_hom N).val.app (op U)
    (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (forgetPre X).obj N)).app (op U)
      ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U)))))
  have h' : (λ_ N).hom.val.app (op U) ((unitTensorIso N).hom.val.app (op U)
      (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (forgetPre X).obj N)).app (op U)
        ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) =
      ((adj X).counit.app N).val.app (op U) (((Modules.sheafify X).map (λ_ ((forgetPre X).obj
          N)).hom).val.app (op U)
        (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (forgetPre X).obj N)).app (op U)
          ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) := h
  change (λ_ N).hom.val.app (op U) ((unitTensorIso N).hom.val.app (op U)
      (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (forgetPre X).obj N)).app (op U)
        ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) = g • n
  rw [h']
  let : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  exact (congrArg (((adj X).counit.app N).val.app (op U))
      (sheafify_map_val_app_unit (λ_ ((forgetPre X).obj N)).hom (op U) _)).trans
    ((counit_val_app_unit N (op U) _).trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply _ _))

end UnitorSections




public theorem leftUnitor_hom_app_tensorSections {X : AlgebraicGeometry.Scheme.{u}} {N : X.Modules}
    {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n :=
  UnitorSections.leftUnitor_hom_app_tensorSections N g n
section PullbackLocalSection

variable {X Y : Scheme.{u}} (φ : X ⟶ Y) {L : Y.Modules} {U : Y.Opens}

lemma localPullback_app {L' : Y.Modules} (θ : L ⟶ L') (s : Γ(L, U)) :
    localPullback φ L' U (θ.app U s) =
      ((Modules.pullback φ).map θ).app (φ ⁻¹ᵁ U) (localPullback φ L U s) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U s)
    ((Modules.pullbackPushforwardAdjunction φ).unit.naturality θ)
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply] at h
  exact h

end PullbackLocalSection

namespace PullbackTensorSections

open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

open TensorHomApp (adj forgetPre cmpIso cmpIso_hom tensorSections_eq cmpIso_hom_comp_tensorHom)

abbrev pf := PresheafOfModules.PullbackMonoidal.pf (TopologicalSpace.Opens.map f.base)
  (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

abbrev adj₀ := PresheafOfModules.PullbackMonoidal.adj (TopologicalSpace.Opens.map f.base)
  (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

abbrev e : Modules.sheafify Y ⋙ Modules.pullback f ≅ pullback₀ f ⋙ Modules.sheafify X :=
  SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom

def pb₀Section (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    ((pullback₀ f).obj P).obj (op (f ⁻¹ᵁ V)) :=
  ((adj₀ f).unit.app P).app (op V) s

def shUnit {Z : Scheme.{u}} (A : Z.PresheafOfModules) (W : Z.Opens) (a : A.obj (op W)) :
    Γ((Modules.sheafify Z).obj A, W) :=
  ((adj Z).unit.app A).app (op W) a

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl
example : adj₀ f = PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom := rfl
example : e f =
    Localization.Lifting.iso (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) := rfl

lemma sheafify_map_app_shUnit {Z : Scheme.{u}} {A A' : Z.PresheafOfModules} (g : A ⟶ A') (W :
    Z.Opens)
    (z : A.obj (op W)) :
    Scheme.Modules.Hom.app ((Modules.sheafify Z).map g) W (shUnit A W z) =
        shUnit A' W (g.app (op W) z) := by
  have h := (adj Z).unit.naturality g
  exact (congr($(h.symm).app (op W) z) :)

lemma counit_app_shUnit (L : Y.Modules) (V : Y.Opens) (s : Γ(L, V)) :
    Scheme.Modules.Hom.app ((adj Y).counit.app L) V (shUnit ((forgetPre Y).obj L) V s) = s := by
  have h := (adj Y).right_triangle_components L
  exact (congr($(h).app (op V) s) :)

lemma homEquiv_symm_app_pb₀Section {A : Y.PresheafOfModules} {B : X.PresheafOfModules}
    (k : A ⟶ (pf f).obj B) (V : Y.Opens) (z : A.obj (op V)) :
    (((adj₀ f).homEquiv A B).symm k).app (op (f ⁻¹ᵁ V)) (pb₀Section f A V z) =
      (k.app (op V) z : B.obj (op (f ⁻¹ᵁ V))) := by
  have h1 := (adj₀ f).homEquiv_unit (X := A) (Y := B) (f := ((adj₀ f).homEquiv A B).symm k)
  rw [Equiv.apply_symm_apply] at h1
  exact (congr($(h1.symm).app (op V) z) :)

lemma e_hom_app_localPullback (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    Scheme.Modules.Hom.app ((e f).hom.app P) (f ⁻¹ᵁ V) (localPullback f _ _ (shUnit P V s)) =
      shUnit ((pullback₀ f).obj P) (f ⁻¹ᵁ V) (pb₀Section f P V s) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom))
    ((PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom).comp
      (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj))) P
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  exact (congr($(h).app (op V) s) :)

lemma e_inv_app_shUnit (P : Y.PresheafOfModules) (V : Y.Opens) (s : P.obj (op V)) :
    Scheme.Modules.Hom.app ((e f).inv.app P) (f ⁻¹ᵁ V) (shUnit ((pullback₀ f).obj P) (f ⁻¹ᵁ V)
        (pb₀Section f P V s)) =
      localPullback f _ _ (shUnit P V s) := by
  rw [← e_hom_app_localPullback]
  change Scheme.Modules.Hom.app ((e f).hom.app P ≫ (e f).inv.app P) (f ⁻¹ᵁ V) _ = _
  rw [Iso.hom_inv_id_app]
  rfl

lemma pb₀_δ_eq (P Q : Y.PresheafOfModules) :
    δ (pullback₀ f) P Q = ((adj₀ f).homEquiv _ _).symm
      (((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q) ≫ μ (pf f) _ _) := by
  exact Adjunction.leftAdjointOplaxMonoidal_δ (adj₀ f) P Q

lemma pb₀_δ_app_pb₀Section_tmul (P Q : Y.PresheafOfModules) (V : Y.Opens) (x : P.obj (op V)) (y :
    Q.obj (op V)) :
    (δ (pullback₀ f) P Q).app (op (f ⁻¹ᵁ V)) (pb₀Section f (P ⊗ Q) V (x ⊗ₜ[Γ(Y, V)] y)) =
      (pb₀Section f P V x ⊗ₜ[Γ(X, f ⁻¹ᵁ V)] pb₀Section f Q V y :
        (PresheafOfModulesOfCommRing.obj ((pullback₀ f).obj P) (op (f ⁻¹ᵁ V)) ⊗
          PresheafOfModulesOfCommRing.obj ((pullback₀ f).obj Q) (op (f ⁻¹ᵁ V)) :)) := by
  rw [pb₀_δ_eq]
  refine (homEquiv_symm_app_pb₀Section f
    (((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q) ≫ μ (pf f) _ _) V (x ⊗ₜ[Γ(Y, V)] y)).trans ?_
  change (μ (pf f) ((pullback₀ f).obj P) ((pullback₀ f).obj Q)).app (op V)
    ((((adj₀ f).unit.app P ⊗ₘ (adj₀ f).unit.app Q)).app (op V) (x ⊗ₜ[Γ(Y, V)] y)) = _
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul]
  erw [PresheafOfModules.PullbackMonoidal.pf_μ_app_tmul]
  rfl

lemma tensorHom_app_tensorSections_inl {L L' M M' : Y.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') (V :
    Y.Opens)
    (s : Γ(L, V)) (t : Γ(M, V)) :
    Scheme.Modules.Hom.app (φ ⊗ₘ ψ) V (Modules.tensorSections s t) =
      Modules.tensorSections (Scheme.Modules.Hom.app φ V s) (Scheme.Modules.Hom.app ψ V t) := by
  have h := congr(Scheme.Modules.Hom.app $(cmpIso_hom_comp_tensorHom φ ψ) V
    (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y,
        V)] (t : M.val.obj (op V)))))
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h
  change Scheme.Modules.Hom.app (φ ⊗ₘ ψ) V (Scheme.Modules.Hom.app (cmpIso L M).hom V
      (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y,
          V)] (t : M.val.obj (op V))))) =
    Scheme.Modules.Hom.app (cmpIso L' M').hom V (Scheme.Modules.Hom.app
      ((Modules.sheafify Y).map ((forgetPre Y).map φ ⊗ₘ (forgetPre Y).map ψ)) V
      (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y,
          V)] (t : M.val.obj (op V))))) at h
  rw [sheafify_map_app_shUnit] at h
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul] at h
  rw [tensorSections_eq, tensorSections_eq]
  exact h

lemma sheafify_map_unit_tensor_unit_comp_cmpIso_hom (A B : X.PresheafOfModules) :
    (Modules.sheafify X).map ((adj X).unit.app A ⊗ₘ (adj X).unit.app B) ≫
        (cmpIso ((Modules.sheafify X).obj A) ((Modules.sheafify X).obj B)).hom =
      δ (Modules.sheafify X) A B := by
  have hδ := Functor.OplaxMonoidal.δ_natural (Modules.sheafify X) ((adj X).unit.app A) ((adj
      X).unit.app B)
  have hA := (adj X).left_triangle_components A
  have hB := (adj X).left_triangle_components B
  rw [cmpIso_hom, ← Category.assoc]
  erw [← hδ]
  rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  erw [hA, hB, MonoidalCategory.id_tensorHom_id, Category.comp_id]
  rfl

lemma sheafify_δ_app_shUnit_tmul (A B : X.PresheafOfModules) (W : X.Opens) (a : A.obj (op W)) (b :
    B.obj (op W)) :
    (δ (Modules.sheafify X) A B).app W (shUnit (A ⊗ B) W (a ⊗ₜ[Γ(X, W)] b)) =
      Modules.tensorSections (L := (Modules.sheafify X).obj A) (M := (Modules.sheafify X).obj B)
        (shUnit A W a) (shUnit B W b) := by
  have h := congr(Scheme.Modules.Hom.app $(sheafify_map_unit_tensor_unit_comp_cmpIso_hom A B) W
    (shUnit (A ⊗ B) W (a ⊗ₜ[Γ(X, W)] b)))
  rw [Scheme.Modules.Hom.comp_app] at h
  change Scheme.Modules.Hom.app (cmpIso ((Modules.sheafify X).obj A) ((Modules.sheafify X).obj
      B)).hom W
      (Scheme.Modules.Hom.app ((Modules.sheafify X).map ((adj X).unit.app A ⊗ₘ (adj X).unit.app
          B)) W
        (shUnit (A ⊗ B) W (a ⊗ₜ[Γ(X, W)] b))) = _ at h
  erw [sheafify_map_app_shUnit] at h
  erw [PresheafOfModules.PullbackMonoidal.tensorHom_app_tmul] at h
  rw [tensorSections_eq]
  exact h.symm

lemma e_hom_app_tensor_comp_δ (P Q : Y.PresheafOfModules) :
    (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q =
      δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ ((e f).hom.app P ⊗ₘ (e f).hom.app Q) := by
  let := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  have hmon : NatTrans.IsMonoidal (F₁ := Modules.sheafify Y ⋙ Modules.pullback f)
      (F₂ := pullback₀ f ⋙ Modules.sheafify X) (e f).hom :=
    Localization.Monoidal.lifting_isMonoidal (Modules.sheafify Y)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
      (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)
  have T := hmon.tensor P Q
  calc (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q
      = (δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫
          μ (Modules.sheafify Y ⋙ Modules.pullback f) P Q) ≫
          (e f).hom.app (P ⊗ Q) ≫ δ (pullback₀ f ⋙ Modules.sheafify X) P Q := by
        rw [Functor.Monoidal.δ_μ, Category.id_comp]
    _ = δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫
          (((e f).hom.app P ⊗ₘ (e f).hom.app Q) ≫ μ (pullback₀ f ⋙ Modules.sheafify X) P Q) ≫
            δ (pullback₀ f ⋙ Modules.sheafify X) P Q := by
        rw [← T]; simp only [Category.assoc]
    _ = δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q ≫ ((e f).hom.app P ⊗ₘ (e f).hom.app Q) := by
        rw [Category.assoc, Functor.Monoidal.μ_δ, Category.comp_id]

lemma δ_sheafify_comp_pullback_eq (P Q : Y.PresheafOfModules) :
    δ (Modules.sheafify Y ⋙ Modules.pullback f) P Q =
      (e f).hom.app (P ⊗ Q) ≫
        ((Modules.sheafify X).map (δ (pullback₀ f) P Q) ≫
          δ (Modules.sheafify X) ((pullback₀ f).obj P) ((pullback₀ f).obj Q)) ≫
        ((e f).inv.app P ⊗ₘ (e f).inv.app Q) := by
  rw [← Functor.OplaxMonoidal.comp_δ, ← Category.assoc, e_hom_app_tensor_comp_δ, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, Iso.hom_inv_id_app, Iso.hom_inv_id_app,
    MonoidalCategory.id_tensorHom_id, Category.comp_id]

theorem pullbackTensorObjIso_hom_app_localPullback_tensorSections (L M : Y.Modules) (V :
    Y.Opens)
    (s : Γ(L, V)) (t : Γ(M, V)) :
    ((pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V)) (localPullback f _ _
        (Modules.tensorSections s t)) =
      Modules.tensorSections (localPullback f _ _ s) (localPullback f _ _ t) := by
  have hnat := Functor.OplaxMonoidal.δ_natural (Modules.pullback f)
    ((adj Y).counit.app L) ((adj Y).counit.app M)
  have key :
    Scheme.Modules.Hom.app (δ (Modules.sheafify Y ⋙ Modules.pullback f) ((forgetPre Y).obj L)
        ((forgetPre Y).obj M)) (f ⁻¹ᵁ V)
      (localPullback f _ _ (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V
        ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))) =
      Modules.tensorSections (localPullback f _ _ (shUnit ((forgetPre Y).obj L) V s))
        (localPullback f _ _ (shUnit ((forgetPre Y).obj M) V t)) := by
    rw [δ_sheafify_comp_pullback_eq]
    change Scheme.Modules.Hom.app ((e f).inv.app ((forgetPre Y).obj L) ⊗ₘ (e f).inv.app
        ((forgetPre Y).obj M)) (f ⁻¹ᵁ V)
      (Scheme.Modules.Hom.app (δ (Modules.sheafify X) ((pullback₀ f).obj ((forgetPre Y).obj L))
          ((pullback₀ f).obj ((forgetPre Y).obj M))) (f ⁻¹ᵁ V)
        (Scheme.Modules.Hom.app ((Modules.sheafify X).map (δ (pullback₀ f) ((forgetPre Y).obj L)
            ((forgetPre Y).obj M)))
            (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app ((e f).hom.app ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M)) (f
              ⁻¹ᵁ V)
            (localPullback f _ _ (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V
              ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))))) = _
    rw [e_hom_app_localPullback, sheafify_map_app_shUnit]
    erw [pb₀_δ_app_pb₀Section_tmul]
    rw [sheafify_δ_app_shUnit_tmul]
    erw [tensorHom_app_tensorSections_inl]
    rw [e_inv_app_shUnit, e_inv_app_shUnit]
  calc ((pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V)) (localPullback f _ _
      (Modules.tensorSections s t))
      = Scheme.Modules.Hom.app (δ (Modules.pullback f) L M) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L ⊗ₘ (adj
              Y).counit.app M))
              (f ⁻¹ᵁ V)
            (Scheme.Modules.Hom.app ((Modules.pullback f).map
                (δ (Modules.sheafify Y) ((forgetPre Y).obj L) ((forgetPre Y).obj M))) (f ⁻¹ᵁ V)
              (localPullback f _ _ (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) := by
        rw [tensorSections_eq, cmpIso_hom]
        have a1 := localPullback_app f ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M)
          (Scheme.Modules.Hom.app (δ (Modules.sheafify Y) ((forgetPre Y).obj L) ((forgetPre Y).obj
              M)) V
            (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V
              ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))
        have a2 := localPullback_app f (δ (Modules.sheafify Y) ((forgetPre Y).obj L)
            ((forgetPre Y).obj M))
          (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V
            ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))
        change (pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V) (localPullback f _ _
          (Scheme.Modules.Hom.app ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M) V
            (Scheme.Modules.Hom.app (δ (Modules.sheafify Y) ((forgetPre Y).obj L) ((forgetPre
                Y).obj M)) V
              (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) = _
        refine (congrArg (fun w => (pullbackTensorObjIso f L M).hom.app (f ⁻¹ᵁ V) w)
          (a1.trans (congrArg (fun w => Scheme.Modules.Hom.app
            ((Modules.pullback f).map ((adj Y).counit.app L ⊗ₘ (adj Y).counit.app M)) (f ⁻¹ᵁ V) w)
                a2))).trans ?_
        rfl
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app (δ (Modules.pullback f) _ _) (f ⁻¹ᵁ V)
            (Scheme.Modules.Hom.app ((Modules.pullback f).map
                (δ (Modules.sheafify Y) ((forgetPre Y).obj L) ((forgetPre Y).obj M))) (f ⁻¹ᵁ V)
              (localPullback f _ _ (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V
                ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V))))))) :=
        (congr($(hnat.symm).app (f ⁻¹ᵁ V) _) :)
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Scheme.Modules.Hom.app (δ (Modules.sheafify Y ⋙ Modules.pullback f) ((forgetPre Y).obj
              L) ((forgetPre Y).obj M))
              (f ⁻¹ᵁ V)
            (localPullback f _ _ (shUnit ((forgetPre Y).obj L ⊗ (forgetPre Y).obj M) V
              ((s : L.val.obj (op V)) ⊗ₜ[Γ(Y, V)] (t : M.val.obj (op V)))))) := by
        rw [Functor.OplaxMonoidal.comp_δ]
        rfl
    _ = Scheme.Modules.Hom.app ((Modules.pullback f).map ((adj Y).counit.app L) ⊗ₘ
            (Modules.pullback f).map ((adj Y).counit.app M)) (f ⁻¹ᵁ V)
          (Modules.tensorSections (localPullback f _ _ (shUnit ((forgetPre Y).obj L) V s))
            (localPullback f _ _ (shUnit ((forgetPre Y).obj M) V t))) := by rw [key]; rfl
    _ = Modules.tensorSections (localPullback f _ _ s) (localPullback f _ _ t) := by
        erw [tensorHom_app_tensorSections_inl]
        rw [← localPullback_app, ← localPullback_app]
        erw [counit_app_shUnit, counit_app_shUnit]
        rfl

end PullbackTensorSections




public theorem pullbackTensorObjIso_hom_app_localPullback {X Y : AlgebraicGeometry.Scheme.{u}}
    (φ : X ⟶ Y) {L M : Y.Modules} {U : Y.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    (pullbackTensorObjIso φ L M).hom.app (φ ⁻¹ᵁ U)
        (localPullback φ (L ⊗ M) U (tensorSections s t)) =
      tensorSections (localPullback φ L U s) (localPullback φ M U t) :=
  PullbackTensorSections.pullbackTensorObjIso_hom_app_localPullback_tensorSections φ L M U s t

namespace ZeroSchemeTensor

open TopologicalSpace


variable {X : Scheme.{u}}

theorem app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (k : V ⟶ U) (m : Γ(M, U)) :
    φ.app V (M.presheaf.map k.op m) = N.presheaf.map k.op (φ.app U m) :=
  PresheafOfModules.naturality_apply φ.val k.op m

theorem restrictFunctorIsoPullback_hom_app_app {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (W : Y.Opens) (m : Γ(M, j ''ᵁ W)) :
    ((restrictFunctorIsoPullback j).hom.app M).app W (show Γ(M.restrict j, W) from m)
      = ((Scheme.Modules.pullback j).obj M).presheaf.map (eqToHom (j.preimage_image_eq W).symm).op
          (localPullback j _ _ m) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) M
  have h' := CategoryTheory.ConcreteCategory.congr_hom
    (congrArg (fun k => Scheme.Modules.Hom.app k (j ''ᵁ W)) h) m
  change ((restrictFunctorIsoPullback j).hom.app M).app (j ⁻¹ᵁ j ''ᵁ W)
      ((M.restrict j).presheaf.map (eqToHom (j.preimage_image_eq W)).op (show Γ(M.restrict j,
          W) from m))
    = localPullback j _ _ m at h'
  rw [app_naturality] at h'
  rw [← h', ← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl,
    op_id, CategoryTheory.Functor.map_id]
  rfl

section local_computation

variable {L M : X.Modules} (U : X.affineOpens)
  (eL : (Scheme.Modules.pullback U.1.ι).obj L ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
  (eM : (Scheme.Modules.pullback U.1.ι).obj M ≅ 𝟙_ (U.1 : Scheme.{u}).Modules)
  (s : 𝟙_ X.Modules ⟶ L) (s' : 𝟙_ X.Modules ⟶ M)

noncomputable def τL : L.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules :=
  (restrictFunctorIsoPullback U.1.ι).app L ≪≫ eL

noncomputable def τT : (L ⊗ M).restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules :=
  (restrictFunctorIsoPullback U.1.ι).app (L ⊗ M) ≪≫ pullbackTensorObjIso U.1.ι L M ≪≫
      (eL ⊗ᵢ eM) ≪≫ λ_ _

noncomputable abbrev tens : 𝟙_ X.Modules ⟶ L ⊗ M := (λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s')

omit U eL eM in
theorem tens_app_one (V : X.Opens) :
    (tens s s').app V (toUnitSection V 1) =
        tensorSections (s.app V (toUnitSection V 1)) (s'.app V (toUnitSection V 1)) := by
  have h1 : (λ_ (𝟙_ X.Modules)).inv.app V (toUnitSection V 1)
      = tensorSections (L := 𝟙_ X.Modules) (M :=
          𝟙_ X.Modules) (toUnitSection V 1) (toUnitSection V 1) := by
    have h := leftUnitor_hom_app_tensorSections (N := 𝟙_ X.Modules) (U := V) (1 : Γ(X,
        V)) (toUnitSection V 1)
    rw [one_smul] at h
    have hid : ∀ z : Γ(𝟙_ X.Modules ⊗ 𝟙_ X.Modules, V),
        (λ_ (𝟙_ X.Modules)).inv.app V ((λ_ (𝟙_ X.Modules)).hom.app V z) = z := fun z =>
      CategoryTheory.ConcreteCategory.congr_hom
        (congrArg (fun k => Scheme.Modules.Hom.app k V) ((λ_ (𝟙_ X.Modules)).hom_inv_id)) z
    conv_lhs => rw [← h]
    exact hid _
  change (s ⊗ₘ s').app V ((λ_ (𝟙_ X.Modules)).inv.app V (toUnitSection V 1)) = _
  rw [h1, tensorHom_app_tensorSections]

theorem τL_app_restrictSection :
    (τL U eL).hom.app ⊤ (restrictSection s U.1)
      = eL.hom.app ⊤ (((Scheme.Modules.pullback U.1.ι).obj L).presheaf.map
          (eqToHom (U.1.ι.preimage_image_eq ⊤).symm).op (localPullback U.1.ι _ _ (s.app (U.1.ι
              ''ᵁ ⊤) (toUnitSection _ 1)))) := by
  change eL.hom.app ⊤ (((restrictFunctorIsoPullback U.1.ι).hom.app L).app ⊤ (restrictSection s
      U.1)) = _
  exact congrArg _ (restrictFunctorIsoPullback_hom_app_app U.1.ι L ⊤ _)

theorem τT_app_restrictSection :
    (τT U eL eM).hom.app ⊤ (restrictSection (tens s s') U.1)
      = (show Γ((U.1 : Scheme.{u}), (⊤ : (U.1 : Scheme.{u}).Opens)) from
            eL.hom.app ⊤ (((Scheme.Modules.pullback U.1.ι).obj L).presheaf.map
              (eqToHom (U.1.ι.preimage_image_eq ⊤).symm).op (localPullback U.1.ι _ _ (s.app
                  (U.1.ι ''ᵁ ⊤) (toUnitSection _ 1))))) •
        eM.hom.app ⊤ (((Scheme.Modules.pullback U.1.ι).obj M).presheaf.map
              (eqToHom (U.1.ι.preimage_image_eq ⊤).symm).op (localPullback U.1.ι _ _ (s'.app
                  (U.1.ι ''ᵁ ⊤) (toUnitSection _ 1)))) := by
  change (λ_ (𝟙_ (U.1 : Scheme.{u}).Modules)).hom.app ⊤ ((eL.hom ⊗ₘ eM.hom).app ⊤
      ((pullbackTensorObjIso U.1.ι L M).hom.app ⊤
    (((restrictFunctorIsoPullback U.1.ι).hom.app (L ⊗ M)).app ⊤ (restrictSection (tens s s')
        U.1)))) = _
  have h0 : restrictSection (tens s s') U.1
      = (show Γ((L ⊗ M).restrict U.1.ι, ⊤) from
          tensorSections (s.app (U.1.ι ''ᵁ ⊤) (toUnitSection _ 1)) (s'.app (U.1.ι ''ᵁ ⊤)
              (toUnitSection _ 1))) :=
    tens_app_one s s' _
  rw [h0]
  erw [restrictFunctorIsoPullback_hom_app_app U.1.ι (L ⊗ M) ⊤]
  rw [app_naturality, pullbackTensorObjIso_hom_app_localPullback, map_tensorSections,
    tensorHom_app_tensorSections, leftUnitor_hom_app_tensorSections]

theorem coeff_tens :
    coeff (tens s s') U.1 (τT U eL eM).hom =
        coeff s U.1 (τL U eL).hom * coeff s' U.1 (τL U eM).hom := by
  simp only [coeff]
  rw [τT_app_restrictSection, τL_app_restrictSection, τL_app_restrictSection]
  rw [← map_mul]
  rfl

include eL eM in
theorem ideal_eq (hL : IsLineBundle L) (hM : IsLineBundle M) :
    (zeroSchemeIdeal (tens s s')).ideal U =
        (zeroSchemeIdeal s).ideal U * (zeroSchemeIdeal s').ideal U := by
  obtain ⟨h1,
      -⟩ := ((hL.tensor hM).coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq (tens s s')).2 U (τT U eL eM)
  obtain ⟨h2, -⟩ := (hL.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U (τL U eL)
  obtain ⟨h3, -⟩ := (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s').2 U (τL U eM)
  rw [h1, h2, h3, Ideal.span_singleton_mul_span_singleton, coeff_tens]

end local_computation

noncomputable def restrictTriv {L : X.Modules} {U₀ : X.Opens} {U : X.Opens} (h : U ≤ U₀)
    (e : (Scheme.Modules.pullback U₀.ι).obj L ≅ 𝟙_ (U₀ : Scheme.{u}).Modules) :
    (Scheme.Modules.pullback U.ι).obj L ≅ 𝟙_ (U : Scheme.{u}).Modules :=
  (pullbackCongr (X.homOfLE_ι h).symm).app L ≪≫
    ((pullbackComp (X.homOfLE h) U₀.ι).app L).symm ≪≫
    (Scheme.Modules.pullback (X.homOfLE h)).mapIso e ≪≫
    pullbackTensorUnitObjIso (X.homOfLE h)

theorem main {L M : X.Modules} (hL : IsLineBundle L) (hM : IsLineBundle M)
    (s : 𝟙_ X.Modules ⟶ L) (s' : 𝟙_ X.Modules ⟶ M) :
    zeroSchemeIdeal ((λ_ (𝟙_ X.Modules)).inv ≫
        (s ⊗ₘ s')) = zeroSchemeIdeal s * zeroSchemeIdeal s' := by
  have key : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      (zeroSchemeIdeal ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s'))).ideal U
        = (zeroSchemeIdeal s).ideal U * (zeroSchemeIdeal s').ideal U := by
    intro x
    obtain ⟨UL, hxL, ⟨eL0⟩⟩ := hL x
    obtain ⟨UM, hxM, ⟨eM0⟩⟩ := hM x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUle⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ UL ⊓ UM from ⟨hxL,
          hxM⟩) (UL ⊓ UM).isOpen
    refine ⟨⟨U, hU⟩, hxU, ?_⟩
    exact ideal_eq ⟨U, hU⟩ (restrictTriv (fun y hy => (hUle hy).1) eL0)
      (restrictTriv (fun y hy => (hUle hy).2) eM0) s s' hL hM
  choose U hxU hU using key
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U ?_ (fun x => ?_)
  · exact top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
  · rw [hU, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]

end ZeroSchemeTensor

end AlgebraicGeometry.Scheme.Modules

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

/-- For line bundles `L` and `M`, the zero ideal sheaf of the tensor product of sections `s` and
`s'` is the product of their zero ideal sheaves. -/
public theorem IsLineBundle.zeroSchemeIdeal_tensorHom
    {X : Scheme.{u}} {L M : X.Modules} (hL : IsLineBundle L) (hM :
        IsLineBundle M)
    (s : 𝟙_ X.Modules ⟶ L) (s' : 𝟙_ X.Modules ⟶ M) :
    Scheme.Modules.zeroSchemeIdeal ((λ_ (𝟙_ X.Modules)).inv ≫ (s ⊗ₘ s')) =
      Scheme.Modules.zeroSchemeIdeal s * Scheme.Modules.zeroSchemeIdeal s' :=
  ZeroSchemeTensor.main hL hM s s'

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

namespace AlgebraicGeometry.Scheme.Modules

set_option autoImplicit false
section translate_product
open scoped CategoryTheory.MonObj

namespace TranslateProduct

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj
    (Over.mk t)]

noncomputable abbrev T (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : X ⟶ X :=
  (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left

theorem T_inv_mul (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : T t (y⁻¹ * y) =
    𝟙 X := by
  have h1 : (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)) = 𝟙 (Over.mk t) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
      mul_assoc, GrpObj.comp_inv, inv_mul_cancel, mul_one]
  have h2 : (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)) =
      𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (y⁻¹ * y)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
      mul_assoc]
    congr 1
    exact (MonObj.comp_mul (CartesianMonoidalCategory.toUnit (Over.mk t)) y⁻¹ y).symm
  exact congrArg CommaMorphism.left (h2.symm.trans h1)

theorem support_zeroSchemeIdeal_pullbackSection {X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules}
    (hM : IsLineBundle M) (s : 𝟙_ X.Modules ⟶ M) :
    ((Scheme.Modules.zeroSchemeIdeal (pullbackSection F s)).support : Set X') =
      F.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by
  rw [← hM.comap_zeroSchemeIdeal F s, Scheme.IdealSheafData.support_comap]
  rfl

-- `SchemeModulesTensor.power L 3` is the monoidal cube `((𝟙_ ⊗ L) ⊗ L) ⊗ L`: both iterate the
-- sheafified tensor product, and `moduleTensorIso` compares the two at each step.
open MathlibExt.AlgebraicGeometry in
private def powerThreeIso (L : X.Modules) :
    SchemeModulesTensor.power L 3 ≅ ((𝟙_ X.Modules ⊗ L) ⊗ L) ⊗ L :=
  moduleTensorIso (SchemeModulesTensor.power L 2) L ≪≫
    whiskerRightIso (moduleTensorIso (SchemeModulesTensor.power L 1) L ≪≫
      whiskerRightIso (moduleTensorIso (SchemeModulesTensor.power L 0) L) L) L

end TranslateProduct

open TranslateProduct in
private theorem exists_hom_tensorPow_three_aux
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : IsLineBundle L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    ∃ s : 𝟙_ X.Modules ⟶ MathlibExt.AlgebraicGeometry.SchemeModulesTensor.power L 3,
      ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) =
        (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) := by
  classical
  let c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t := (a * b)⁻¹
  let Lp : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) → X.Modules := fun x =>
    (Scheme.Modules.pullback (T t x)).obj L
  have hLp : ∀ x, IsLineBundle (Lp x) := fun x => hL.pullback _
  let θp : ∀ x, 𝟙_ X.Modules ⟶ Lp x := fun x => pullbackSection (T t x) θ
  let sab : 𝟙_ X.Modules ⟶ Lp a ⊗ Lp b := (λ_ (𝟙_ X.Modules)).inv ≫ (θp a ⊗ₘ θp b)
  let s₀ : 𝟙_ X.Modules ⟶ Lp c ⊗ (Lp a ⊗ Lp b) := (λ_ (𝟙_ X.Modules)).inv ≫ (θp c ⊗ₘ sab)
  have hT1 : T t (c * (a * b)) = 𝟙 X := T_inv_mul t (a * b)
  have e1 : Lp (c * (a * b)) ≅ L :=
    (Scheme.Modules.pullbackCongr hT1).app L ≪≫ (Scheme.Modules.pullbackId X).app L
  have Φ₁ : Lp c ⊗ (Lp a ⊗ Lp b) ≅ Lp c ⊗ (Lp (a * b) ⊗ L) := whiskerLeftIso (Lp c) (hsq a b).some
  have Φ₂ : Lp c ⊗ (Lp (a * b) ⊗ L) ≅ (Lp c ⊗ Lp (a * b)) ⊗ L := (α_ (Lp c) (Lp (a * b)) L).symm
  have Φ₃ : (Lp c ⊗ Lp (a * b)) ⊗ L ≅ (Lp (c * (a * b)) ⊗ L) ⊗ L :=
      whiskerRightIso (hsq c (a * b)).some L
  have Φ₄ : (Lp (c * (a * b)) ⊗ L) ⊗ L ≅ ((𝟙_ X.Modules ⊗ L) ⊗ L) ⊗ L :=
    whiskerRightIso (whiskerRightIso (e1 ≪≫ (λ_ L).symm) L) L
  have Φ : Lp c ⊗ (Lp a ⊗ Lp b) ≅ MathlibExt.AlgebraicGeometry.SchemeModulesTensor.power L 3 :=
    Φ₁ ≪≫ Φ₂ ≪≫ Φ₃ ≪≫ Φ₄ ≪≫ (powerThreeIso L).symm
  refine ⟨s₀ ≫ Φ.hom, ?_⟩
  rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso]
  have hZ : Scheme.Modules.zeroSchemeIdeal s₀ =
      Scheme.Modules.zeroSchemeIdeal (θp c) *
        (Scheme.Modules.zeroSchemeIdeal (θp a) * Scheme.Modules.zeroSchemeIdeal (θp b)) := by
    rw [(hLp c).zeroSchemeIdeal_tensorHom ((hLp a).tensor (hLp b)),
      (hLp a).zeroSchemeIdeal_tensorHom (hLp b)]
  rw [hZ, Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_mul]
  simp only [TopologicalSpace.Closeds.coe_sup]
  rw [support_zeroSchemeIdeal_pullbackSection (T t c) hL θ,
      support_zeroSchemeIdeal_pullbackSection (T t a) hL θ,
    support_zeroSchemeIdeal_pullbackSection (T t b) hL θ]
  exact Set.union_comm _ _

end translate_product

end AlgebraicGeometry.Scheme.Modules

open scoped CategoryTheory.MonObj in
/-- For a commutative group scheme `t : X ⟶ Spec k` over a field and an invertible sheaf `L` with
the theorem-of-the-square isomorphisms `hsq`, every section `θ` of `L` gives a section of the
tensor cube `SchemeModulesTensor.power L 3` whose zero support is the union of the preimages of
the zero support of `θ` under the translations `g ↦ g * a`, `g ↦ g * b` and `g ↦ g * (a * b)⁻¹`,
that is, of the zero supports of the pullbacks of `θ` along these translations. -/
public theorem
    AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : IsLineBundle L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫
            (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    ∃ s : 𝟙_ X.Modules ⟶ MathlibExt.AlgebraicGeometry.SchemeModulesTensor.power L 3,
      ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) =
        (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) :=
  AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_aux k t L hL hsq θ a b

end
