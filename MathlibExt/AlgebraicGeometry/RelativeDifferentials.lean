/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# The sheaf of relative differentials of a scheme over a ring

Let `X` be a scheme and `φ : R ⟶ Γ(X, ⊤)` a ring map (equivalently, a morphism `X ⟶ Spec R`).

* `AlgebraicGeometry.Scheme.relativeDifferentialsPresheaf φ` is the presheaf of
  `𝒪_X`-modules `U ↦ Ω[𝒪_X(U)⁄R]`, i.e. Mathlib's
  `PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'` applied to the
  morphism `constToPresheaf φ` from the constant presheaf of rings `R` to `𝒪_X`.
* `AlgebraicGeometry.Scheme.relativeDifferentials φ : X.Modules` is its sheafification.
* `AlgebraicGeometry.Scheme.relativeDifferentialsHomEquiv` is its universal property:
  morphisms `relativeDifferentials φ ⟶ F` of `𝒪_X`-modules are in bijection with derivations
  `𝒪_X → F` vanishing on the image of `R`.

For a ring map `f : R ⟶ A` and `X = Spec A` (with `φ = f ≫ (ΓSpecIso A).inv`):

* `AlgebraicGeometry.Scheme.relativeDifferentialsSpecIso f` is an isomorphism of
  `𝒪_{Spec A}`-modules between `relativeDifferentials φ` and `Ω[A⁄R]^~`
  (`tilde (CommRingCat.KaehlerDifferential f)`); in particular the sheaf is quasi-coherent.
* `AlgebraicGeometry.Scheme.relativeDifferentialsSpecΓIso f` is the resulting isomorphism of
  `A`-modules `Γ(Spec A, Ω) ≅ Ω[A⁄R]`, and `relativeDifferentialsSpecΓIso_hom_d` says that it
  sends the universal derivation of `a ∈ A` to `d a`.
* `relativeDifferentialsSpecIsoFree`, `relativeDifferentialsSpecIsoUnit`: a basis of `Ω[A⁄R]`
  (resp. an isomorphism `Ω[A⁄R] ≅ A`) gives an isomorphism of the sheaf with a free
  `𝒪_{Spec A}`-module (resp. with `𝒪_{Spec A}`), and
  `exists_iso_free_of_isStandardSmoothOfRelativeDimension`: if `A` is standard smooth of
  relative dimension `n` over `R`, the sheaf is free on a set of cardinality `n`.

## Comparison with the reference

The Stacks Project, Tags 01UM and 01UQ, defines `Ω_{X/S}`
for `f : X → S` using the inverse image `f⁻¹𝒪_S`. Here the base is the constant presheaf `R`
instead; for `S = Spec R` both have the universal property of Tag 01UR with
respect to derivations vanishing on `R` (a derivation vanishing on `R` vanishes on local
fractions of `R`). This file treats the base `R` only: it does not compare the construction with
the one through `f⁻¹𝒪_S`, and it does not treat a general base scheme `S`. The affine
computation is Tag 01UT for `U = X = Spec A` and `V = S = Spec R`, upgraded to an
isomorphism of sheaves with `Ω[A⁄R]^~`; the restriction to an arbitrary affine open of an
arbitrary `X` (Tag 01US) is outside its scope.

The proof follows the idea of Tag 01UO: on a basic open `D(g)`, the
isomorphism `Ω[A_g⁄R] ≅ (Ω[A⁄R])_g` (`KaehlerDifferential.isLocalizedModule_map`) defines a
derivation `𝒪(D(g)) → Ω[A⁄R]^~(D(g))`; these glue along the basis of basic opens to a
derivation `𝒪_{Spec A} → Ω[A⁄R]^~`, whose induced morphism from the presheaf of relative
differentials is bijective on basic opens, hence locally bijective, hence becomes an
isomorphism after sheafification.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace PresheafOfModulesOfCommRing


namespace KaehlerDifferential.LocalizationAux

variable {R A S N : Type u} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
  [Algebra A S] [IsScalarTower R A S] (g : A) [IsLocalization.Away g S]
  [AddCommGroup N] [Module A N] [Module S N] [IsScalarTower A S N]
  (t : Ω[A⁄R] →ₗ[A] N) [ht : IsLocalizedModule.Away g t]

/-- Let `R → A → S` with `S` a localization of `A` away from `g`, and let `t : Ω[A⁄R] → N` be a
localization of `A`-modules away from `g`, where `N` is also an `S`-module. This is the
`S`-linear map `Ω[S⁄R] → N` extending `t` along `Ω[A⁄R] → Ω[S⁄R]`; it is bijective
(`liftOfLocalization_bijective`). -/
noncomputable def liftOfLocalization : Ω[S⁄R] →ₗ[S] N :=
  haveI := KaehlerDifferential.isLocalizedModule_map R A S (.powers g)
  LinearMap.extendScalarsOfIsLocalization (.powers g) S
    (IsLocalizedModule.linearEquiv (.powers g) (KaehlerDifferential.map R R A S) t).toLinearMap

/-- `liftOfLocalization` is bijective. -/
lemma liftOfLocalization_bijective : Function.Bijective (liftOfLocalization (S := S) g t) :=
  haveI := KaehlerDifferential.isLocalizedModule_map R A S (.powers g)
  (IsLocalizedModule.linearEquiv (.powers g) (KaehlerDifferential.map R R A S) t).bijective

/-- `liftOfLocalization` extends `t`. -/
lemma liftOfLocalization_map (x : Ω[A⁄R]) :
    liftOfLocalization (S := S) g t (KaehlerDifferential.map R R A S x) = t x :=
  haveI := KaehlerDifferential.isLocalizedModule_map R A S (.powers g)
  IsLocalizedModule.linearEquiv_apply (.powers g) (KaehlerDifferential.map R R A S) t x

lemma liftOfLocalization_D_algebraMap (a : A) :
    liftOfLocalization (S := S) g t (KaehlerDifferential.D R S (algebraMap A S a)) =
      t (KaehlerDifferential.D R A a) := by
  rw [← KaehlerDifferential.map_D R R A S, liftOfLocalization_map]

/-- The additive map `S → N`, `s ↦ e (d s)`, where `e : Ω[S⁄R] → N` is `liftOfLocalization`. -/
noncomputable def dOfLocalization : S →+ N :=
  (liftOfLocalization (S := S) g t).toAddMonoidHom.comp
    (KaehlerDifferential.D R S).toLinearMap.toAddMonoidHom

lemma dOfLocalization_apply (s : S) :
    dOfLocalization g t s = liftOfLocalization (S := S) g t (KaehlerDifferential.D R S s) := rfl

lemma dOfLocalization_mul (s s' : S) :
    dOfLocalization g t (s * s') = s • dOfLocalization g t s' + s' • dOfLocalization g t s := by
  simp only [dOfLocalization_apply, Derivation.leibniz, map_add, map_smul]

lemma dOfLocalization_algebraMap_base (r : R) :
    dOfLocalization (S := S) g t (algebraMap R S r) = 0 := by
  simp only [dOfLocalization_apply, Derivation.map_algebraMap, map_zero]

lemma dOfLocalization_algebraMap (a : A) :
    dOfLocalization (S := S) g t (algebraMap A S a) = t (KaehlerDifferential.D R A a) :=
  liftOfLocalization_D_algebraMap g t a

/-- Compatibility of `dOfLocalization` with a ring map `ρ : S → S'` under `A` and a compatible
additive map `ρN : N → N'` sending `t` to `t'`, provided `g` is a non-zero-divisor on `N'`. -/
lemma dOfLocalization_naturality {g' : A} {S' N' : Type u} [CommRing S'] [Algebra R S']
    [Algebra A S'] [IsScalarTower R A S'] [IsLocalization.Away g' S'] [AddCommGroup N']
    [Module A N'] [Module S' N'] [IsScalarTower A S' N'] (t' : Ω[A⁄R] →ₗ[A] N')
    [ht' : IsLocalizedModule.Away g' t'] (ρ : S →+* S')
    (hρ : ∀ a, ρ (algebraMap A S a) = algebraMap A S' a)
    (ρN : N →+ N') (hρN : ∀ (s : S) (n : N), ρN (s • n) = ρ s • ρN n)
    (htt : ∀ x, ρN (t x) = t' x) (hreg : IsSMulRegular N' g) (s : S) :
    ρN (dOfLocalization g t s) = dOfLocalization g' t' (ρ s) := by
  obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) s
  dsimp only at h
  have h' := congr(ρ $h)
  rw [map_mul, hρ, hρ] at h'
  have e1 := congr(ρN (dOfLocalization g t $h))
  rw [dOfLocalization_mul, map_add, hρN, hρN, hρ, dOfLocalization_algebraMap,
    dOfLocalization_algebraMap, htt, htt] at e1
  have e2 := congr(dOfLocalization g' t' $h')
  rw [dOfLocalization_mul, dOfLocalization_algebraMap, dOfLocalization_algebraMap] at e2
  rw [← e2] at e1
  have e3 := add_left_cancel e1
  rw [algebraMap_smul, algebraMap_smul] at e3
  exact (hreg.pow n) e3

end KaehlerDifferential.LocalizationAux

namespace AlgebraicGeometry.Scheme

section General

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (φ : R ⟶ Γ(X, ⊤))

/-- The morphism from the constant presheaf of rings with value `R` to `𝒪_X` induced by a ring
map `φ : R ⟶ Γ(X, ⊤)`: on an open `U` it is `φ` followed by restriction to `U`. -/
@[simps]
def constToPresheaf : (Functor.const X.Opensᵒᵖ).obj R ⟶ X.presheaf where
  app U := φ ≫ X.presheaf.map (homOfLE le_top).op
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    rfl

/-- The presheaf of `𝒪_X`-modules of relative differentials `U ↦ Ω[𝒪_X(U)⁄R]` of a scheme `X`
over a ring `R` given by `φ : R ⟶ Γ(X, ⊤)`, with restriction maps induced by functoriality of
Kähler differentials. -/
noncomputable def relativeDifferentialsPresheaf : PresheafOfModulesOfCommRing.{u} X.presheaf :=
  DifferentialsConstruction.relativeDifferentials' (constToPresheaf φ)

/-- The sheaf of relative differentials `Ω_{X/R}` of a scheme `X` over a ring `R` given by
`φ : R ⟶ Γ(X, ⊤)`: the sheafification of `relativeDifferentialsPresheaf φ`. Compare Stacks
Project, Tag 01UQ, where the base is `f⁻¹𝒪_S`; here it is the constant
ring `R` (see the module docstring). -/
noncomputable def relativeDifferentials : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (relativeDifferentialsPresheaf φ)

/-- The presheaf of `𝒪_X`-modules (over the presheaf of commutative rings `𝒪_X`) underlying an
`𝒪_X`-module. -/
noncomputable abbrev Modules.presheafOfModulesOfCommRing (F : X.Modules) :
    PresheafOfModulesOfCommRing.{u} X.presheaf :=
  (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj ((SheafOfModules.forget _).obj F)

/-- Morphisms out of the presheaf of relative differentials correspond to derivations vanishing
on `R` (the universal property of Mathlib's `relativeDifferentials'`). -/
noncomputable def relativeDifferentialsPresheafHomEquiv
    (M : PresheafOfModulesOfCommRing.{u} X.presheaf) :
    (relativeDifferentialsPresheaf φ ⟶ M) ≃ M.Derivation' (constToPresheaf φ) where
  toFun g := (DifferentialsConstruction.derivation' (constToPresheaf φ)).postcomp g
  invFun d := (DifferentialsConstruction.isUniversal' (constToPresheaf φ)).desc d
  left_inv g := (DifferentialsConstruction.isUniversal' (constToPresheaf φ)).postcomp_injective
    _ _ (by simp)
  right_inv d := (DifferentialsConstruction.isUniversal' (constToPresheaf φ)).fac d

/-- **Universal property of the sheaf of relative differentials.** Morphisms of `𝒪_X`-modules
`relativeDifferentials φ ⟶ F` correspond bijectively to derivations `𝒪_X → F` vanishing on the
image of `R`. Stacks Project, Tag 01UR, with `S`-derivations replaced by
derivations vanishing on the constant ring `R`. -/
noncomputable def relativeDifferentialsHomEquiv (F : X.Modules) :
    (relativeDifferentials φ ⟶ F) ≃ F.presheafOfModulesOfCommRing.Derivation' (constToPresheaf φ) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    (relativeDifferentialsPresheafHomEquiv φ F.presheafOfModulesOfCommRing)

/-- The universal derivation `𝒪_X → Ω_{X/R}`. -/
noncomputable def relativeDifferentialsDerivation :
    (relativeDifferentials φ).presheafOfModulesOfCommRing.Derivation' (constToPresheaf φ) :=
  relativeDifferentialsHomEquiv φ _ (𝟙 _)

end General

section Spec

variable {R A : CommRingCat.{u}} (f : R ⟶ A)

namespace RelativeDifferentialsSpec

/-- (Implementation) The map from the constant presheaf `R` to `𝒪_{Spec A}` induced by `f`. -/
noncomputable abbrev structMap : (Functor.const (Spec A).Opensᵒᵖ).obj R ⟶ (Spec A).presheaf :=
  constToPresheaf (X := Spec A) (f ≫ (ΓSpecIso A).inv)

/-- (Implementation) The quasi-coherent sheaf `Ω[A⁄R]^~` on `Spec A`. -/
noncomputable abbrev tildeΩ : (Spec A).Modules := tilde (CommRingCat.KaehlerDifferential f)

/-- (Implementation) The basic open `D(g)` of `Spec A`, as an open of the scheme. -/
abbrev bo (g : A) : (Spec A).Opens := PrimeSpectrum.basicOpen g

instance isLocalization_bo (g : A) : IsLocalization.Away g Γ(Spec A, bo g) :=
  StructureSheaf.IsLocalization.to_basicOpen A g

instance isLocalizedModule_toOpen_bo (M : ModuleCat.{u} A) (g : A) :
    IsLocalizedModule.Away g (tilde.toOpen M (bo g)).hom :=
  inferInstance

/-- (Implementation) The localization map `Ω[A⁄R] → Γ(Ω[A⁄R]^~, D(g))`. -/
noncomputable def toOpenₗ (g : A) : CommRingCat.KaehlerDifferential f →ₗ[A] Γ(tildeΩ f, bo g) :=
  (tilde.toOpen (CommRingCat.KaehlerDifferential f) (bo g)).hom

instance isLocalizedModule_toOpenₗ (g : A) : IsLocalizedModule.Away g (toOpenₗ f g) :=
  inferInstanceAs (IsLocalizedModule.Away g (tilde.toOpen _ (bo g)).hom)

/-- (Implementation) The derivation `Γ(Spec A, D(g)) → Γ(Ω[A⁄R]^~, D(g))` obtained from
`Ω[A_g⁄R] ≅ (Ω[A⁄R])_g`. -/
noncomputable def dBasic (g : A) : Γ(Spec A, bo g) →+ Γ(tildeΩ f, bo g) :=
  letI := f.hom.toAlgebra
  letI : Algebra R Γ(Spec A, bo g) := ((structMap f).app (op (bo g))).hom.toAlgebra
  haveI : IsScalarTower R A Γ(Spec A, bo g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  KaehlerDifferential.LocalizationAux.dOfLocalization (R := R)
    (ht := (inferInstance : IsLocalizedModule.Away g (toOpenₗ f g))) g (toOpenₗ f g)

lemma dBasic_mul (g : A) (s s' : Γ(Spec A, bo g)) :
    dBasic f g (s * s') = s • dBasic f g s' + s' • dBasic f g s := by
  let := f.hom.toAlgebra
  let _ : Algebra R Γ(Spec A, bo g) := ((structMap f).app (op (bo g))).hom.toAlgebra
  have : IsScalarTower R A Γ(Spec A, bo g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact KaehlerDifferential.LocalizationAux.dOfLocalization_mul (R := R)
    (ht := (inferInstance : IsLocalizedModule.Away g (toOpenₗ f g))) g (toOpenₗ f g) s s'

lemma dBasic_structMap (g : A) (r : R) :
    dBasic f g ((structMap f).app (op (bo g)) r) = 0 := by
  let := f.hom.toAlgebra
  let _ : Algebra R Γ(Spec A, bo g) := ((structMap f).app (op (bo g))).hom.toAlgebra
  have : IsScalarTower R A Γ(Spec A, bo g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact KaehlerDifferential.LocalizationAux.dOfLocalization_algebraMap_base (R := R)
    (ht := (inferInstance : IsLocalizedModule.Away g (toOpenₗ f g))) g (toOpenₗ f g) r

lemma dBasic_algebraMap (g : A) (a : A) :
    dBasic f g (algebraMap A Γ(Spec A, bo g) a) =
      toOpenₗ f g (CommRingCat.KaehlerDifferential.d (f := f) a) := by
  let := f.hom.toAlgebra
  let _ : Algebra R Γ(Spec A, bo g) := ((structMap f).app (op (bo g))).hom.toAlgebra
  have : IsScalarTower R A Γ(Spec A, bo g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact KaehlerDifferential.LocalizationAux.dOfLocalization_algebraMap (R := R)
    (ht := (inferInstance : IsLocalizedModule.Away g (toOpenₗ f g))) g (toOpenₗ f g) a

lemma dBasic_naturality {g g' : A} (j : bo g' ⟶ bo g) (s : Γ(Spec A, bo g)) :
    (tildeΩ f).presheaf.map j.op (dBasic f g s) = dBasic f g' ((Spec A).presheaf.map j.op s) := by
  let := f.hom.toAlgebra
  let _ : Algebra R Γ(Spec A, bo g) := ((structMap f).app (op (bo g))).hom.toAlgebra
  have : IsScalarTower R A Γ(Spec A, bo g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let _ : Algebra R Γ(Spec A, bo g') := ((structMap f).app (op (bo g'))).hom.toAlgebra
  have : IsScalarTower R A Γ(Spec A, bo g') :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine KaehlerDifferential.LocalizationAux.dOfLocalization_naturality (R := R)
    (ht := (inferInstance : IsLocalizedModule.Away g (toOpenₗ f g)))
    (ht' := (inferInstance : IsLocalizedModule.Away g' (toOpenₗ f g'))) g (toOpenₗ f g)
    (toOpenₗ f g') ((Spec A).presheaf.map j.op).hom ?_ ((tildeΩ f).presheaf.map j.op).hom ?_ ?_
    (Scheme.Modules.isSMulRegular_of_le_basicOpen j.le) s
  · intro a
    change (((ΓSpecIso A).inv ≫ (Spec A).presheaf.map (homOfLE le_top).op) ≫
      (Spec A).presheaf.map j.op) a =
        ((ΓSpecIso A).inv ≫ (Spec A).presheaf.map (homOfLE le_top).op) a
    rw [Category.assoc, ← Functor.map_comp]
    rfl
  · intro s n
    exact (tildeΩ f).val.map_smul j.op s n
  · intro x
    exact congr($(tilde.toOpen_res (CommRingCat.KaehlerDifferential f) _ _ j).hom x)

lemma isBasis_bo : Opens.IsBasis (Set.range (bo (A := A))) := PrimeSpectrum.isBasis_basic_opens

/-- (Implementation) The structure sheaf of `Spec A` as a presheaf of abelian groups. -/
noncomputable abbrev structureSheafAb : TopCat.Presheaf AddCommGrpCat.{u} (Spec A) :=
  (Spec A).ringCatSheaf.obj ⋙ forget₂ RingCat AddCommGrpCat

/-- (Implementation) The sheaf of abelian groups underlying `tildeΩ f`. -/
noncomputable abbrev tildeΩAb : TopCat.Sheaf AddCommGrpCat.{u} (Spec A) :=
  (SheafOfModules.toSheaf _).obj (tildeΩ f)

/-- (Implementation) The derivations on basic opens, as a natural transformation on the basis
of basic opens. -/
noncomputable def dBasis :
    (inducedFunctor (bo (A := A))).op ⋙ structureSheafAb ⟶
      (inducedFunctor (bo (A := A))).op ⋙ (tildeΩAb f).obj where
  app g := AddCommGrpCat.ofHom (dBasic f g.unop)
  naturality g g' i := by
    ext s
    exact (dBasic_naturality f ((inducedFunctor (bo (A := A))).map i.unop) s).symm

/-- (Implementation) The derivation `𝒪_{Spec A} → Ω[A⁄R]^~` as a morphism of presheaves of
abelian groups, extended from the basis of basic opens. -/
noncomputable def dSheaf : (structureSheafAb (A := A)) ⟶ (tildeΩAb f).obj :=
  TopCat.Sheaf.restrictHomEquivHom structureSheafAb (tildeΩAb f) isBasis_bo (dBasis f)

lemma dSheaf_app_bo (g : A) (s : Γ(Spec A, bo g)) :
    (dSheaf f).app (op (bo g)) s = dBasic f g s := by
  rw [dSheaf, TopCat.Sheaf.extend_hom_app]
  rfl

lemma dSheaf_restrict (U : (Spec A).Opens) (g : A) (h : bo g ≤ U) (s : Γ(Spec A, U)) :
    (tildeΩ f).presheaf.map (homOfLE h).op ((dSheaf f).app (op U) s) =
      dBasic f g ((Spec A).presheaf.map (homOfLE h).op s) := by
  rw [← dSheaf_app_bo]
  exact (congr($((dSheaf f).naturality (homOfLE h).op).hom s)).symm

lemma tildeΩ_ext {U : (Spec A).Opens} {x y : Γ(tildeΩ f, U)}
    (h : ∀ (g : A) (hg : bo g ≤ U), (tildeΩ f).presheaf.map (homOfLE hg).op x =
      (tildeΩ f).presheaf.map (homOfLE hg).op y) : x = y := by
  apply TopCat.Presheaf.IsSheaf.section_ext (tildeΩ f).isSheaf
  intro p hp
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hgU : bo g ≤ U⟩ :=
    isBasis_bo.exists_subset_of_mem_open hp U.2
  exact ⟨bo g, hgU, hpg, h g hgU⟩

/-- (Implementation) The derivation `𝒪_{Spec A} → Ω[A⁄R]^~`, vanishing on `R`. -/
noncomputable def derivationT :
    (tildeΩ f).presheafOfModulesOfCommRing.Derivation' (structMap f) where
  d {U} := ((dSheaf f).app U).hom
  d_mul {U} a b := by
    apply tildeΩ_ext
    intro g hg
    have h1 := (tildeΩ f).val.map_smul (homOfLE hg).op a (((dSheaf f).app U).hom b)
    have h2 := (tildeΩ f).val.map_smul (homOfLE hg).op b (((dSheaf f).app U).hom a)
    erw [dSheaf_restrict, map_add, h1, h2, dSheaf_restrict, dSheaf_restrict, map_mul, dBasic_mul]
    rfl
  d_map {U V} i x := congr($((dSheaf f).naturality i).hom x)
  d_app {U} r := by
    apply tildeΩ_ext
    intro g hg
    erw [dSheaf_restrict, map_zero]
    convert dBasic_structMap f g r using 2
    change (((structMap f).app U) ≫ (Spec A).presheaf.map (homOfLE hg).op) r = _
    rw [← (structMap f).naturality]
    rfl

/-- (Implementation) The comparison morphism from the presheaf `U ↦ Ω[𝒪(U)⁄R]` to
`Ω[A⁄R]^~`. -/
noncomputable def mT : relativeDifferentialsPresheaf (f ≫ (ΓSpecIso A).inv) ⟶
    (tildeΩ f).presheafOfModulesOfCommRing :=
  (relativeDifferentialsPresheafHomEquiv _ _).symm (derivationT f)

lemma mT_app_d (U : (Spec A).Opens) (s : Γ(Spec A, U)) :
    (mT f).app (op U) (CommRingCat.KaehlerDifferential.d s) = (dSheaf f).app (op U) s :=
  Derivation.congr_d ((DifferentialsConstruction.isUniversal' (structMap f)).fac (derivationT f)) s

/-- (Implementation) The bijective linear map `Ω[Γ(D(g))⁄R] → Γ(Ω[A⁄R]^~, D(g))`. -/
noncomputable def eBasic (g : A) : CommRingCat.KaehlerDifferential ((structMap f).app (op (bo g)))
    →ₗ[Γ(Spec A, bo g)] Γ(tildeΩ f, bo g) :=
  letI := f.hom.toAlgebra
  letI : Algebra R Γ(Spec A, bo g) := ((structMap f).app (op (bo g))).hom.toAlgebra
  haveI : IsScalarTower R A Γ(Spec A, bo g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  KaehlerDifferential.LocalizationAux.liftOfLocalization (R := R)
    (ht := (inferInstance : IsLocalizedModule.Away g (toOpenₗ f g))) g (toOpenₗ f g)

lemma eBasic_bijective (g : A) : Function.Bijective (eBasic f g) := by
  let := f.hom.toAlgebra
  let _ : Algebra R Γ(Spec A, bo g) := ((structMap f).app (op (bo g))).hom.toAlgebra
  have : IsScalarTower R A Γ(Spec A, bo g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact KaehlerDifferential.LocalizationAux.liftOfLocalization_bijective (R := R)
    (ht := (inferInstance : IsLocalizedModule.Away g (toOpenₗ f g))) g (toOpenₗ f g)

lemma eBasic_d (g : A) (s : Γ(Spec A, bo g)) :
    eBasic f g (CommRingCat.KaehlerDifferential.d s) = dBasic f g s := rfl

lemma mT_app_bo (g : A) (x : CommRingCat.KaehlerDifferential ((structMap f).app (op (bo g)))) :
    (mT f).app (op (bo g)) x = eBasic f g x := by
  let := f.hom.toAlgebra
  let _ : Algebra R Γ(Spec A, bo g) := ((structMap f).app (op (bo g))).hom.toAlgebra
  have hx : x ∈ Submodule.span Γ(Spec A, bo g)
      (Set.range (KaehlerDifferential.D R Γ(Spec A, bo g))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    exact (mT_app_d f (bo g) s).trans ((dSheaf_app_bo f g s).trans (eBasic_d f g s).symm)
  | zero => exact ((mT f).app _).hom.map_zero.trans (eBasic f g).map_zero.symm
  | add y z _ _ hy hz =>
    refine (((mT f).app _).hom.map_add y z).trans ?_
    rw [hy, hz]
    exact ((eBasic f g).map_add y z).symm
  | smul c y _ hy =>
    rw [map_smul, ← hy]
    exact ((mT f).app (op (bo g))).hom.map_smul c y

lemma mT_app_bo_bijective (g : A) : Function.Bijective ((mT f).app (op (bo g))) := by
  have : ⇑((mT f).app (op (bo g))) = eBasic f g := funext (mT_app_bo f g)
  rw [this]
  exact eBasic_bijective f g

instance isLocallyInjective_mT :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology (Spec A)) (mT f) where
  equalizerSieve_mem {U} x y hxy := by
    rw [Opens.mem_grothendieckTopology]
    intro p hp
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hgU : bo g ≤ U.unop⟩ :=
      isBasis_bo.exists_subset_of_mem_open hp U.unop.2
    refine ⟨bo g, homOfLE hgU, ?_, hpg⟩
    apply (mT_app_bo_bijective f g).1
    have h1 := PresheafOfModules.naturality_apply (mT f) (homOfLE hgU).op x
    have h2 := PresheafOfModules.naturality_apply (mT f) (homOfLE hgU).op y
    have h3 : (mT f).app U x = (mT f).app U y := hxy
    exact h1.trans ((congrArg _ h3).trans h2.symm)

instance isLocallySurjective_mT :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology (Spec A)) (mT f) where
  imageSieve_mem {U} t := by
    rw [Opens.mem_grothendieckTopology]
    intro p hp
    obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hgU : bo g ≤ U⟩ :=
      isBasis_bo.exists_subset_of_mem_open hp U.2
    refine ⟨bo g, homOfLE hgU, ?_, hpg⟩
    obtain ⟨s, hs⟩ := (mT_app_bo_bijective f g).2 ((tildeΩ f).presheafOfModulesOfCommRing.map
      (homOfLE hgU).op t)
    exact ⟨s, hs⟩

/-- (Implementation) The forgetful functor right adjoint to sheafification. -/
noncomputable abbrev forgetR (A : CommRingCat.{u}) : (Spec A).Modules ⥤
    _root_.PresheafOfModules.{u} (Spec A).ringCatSheaf.obj :=
  SheafOfModules.forget _ ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 (Spec A).ringCatSheaf.obj)

instance full_forgetR : (forgetR A).Full :=
  inferInstanceAs (SheafOfModules.forget _ ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 (Spec A).ringCatSheaf.obj)).Full

instance faithful_forgetR : (forgetR A).Faithful :=
  inferInstanceAs (SheafOfModules.forget _ ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 (Spec A).ringCatSheaf.obj)).Faithful

/-- (Implementation) The sheafification adjunction for `𝒪_{Spec A}`-modules. -/
noncomputable abbrev sheafAdj (A : CommRingCat.{u}) :=
  _root_.PresheafOfModules.sheafificationAdjunction (𝟙 (Spec A).ringCatSheaf.obj)

/-- (Implementation) The comparison morphism `Ω_{Spec A/R} ⟶ Ω[A⁄R]^~`. -/
noncomputable def compHom : relativeDifferentials (f ≫ (ΓSpecIso A).inv) ⟶ tildeΩ f :=
  ((sheafAdj A).homEquiv _ _).symm (mT f)

/-- (Implementation) The unit of sheafification at the presheaf of relative differentials. -/
noncomputable abbrev unitη : relativeDifferentialsPresheaf (f ≫ (ΓSpecIso A).inv) ⟶
    (forgetR A).obj (relativeDifferentials (f ≫ (ΓSpecIso A).inv)) :=
  (sheafAdj A).homEquiv _ _ (𝟙 (relativeDifferentials (f ≫ (ΓSpecIso A).inv)))

/-- (Implementation) The presheaf-level inverse of `mT`, up to sheafification. -/
noncomputable def nT :
    (forgetR A).obj (tildeΩ f) ⟶ (forgetR A).obj (relativeDifferentials (f ≫ (ΓSpecIso A).inv)) :=
  (_root_.PresheafOfModules.homEquivOfIsLocallyBijective (mT f)
    (relativeDifferentials (f ≫ (ΓSpecIso A).inv)).isSheaf).symm (unitη f)

lemma mT_comp_nT : mT f ≫ nT f = unitη f :=
  (_root_.PresheafOfModules.homEquivOfIsLocallyBijective_apply (mT f) _ (nT f)).symm.trans
    (Equiv.apply_symm_apply _ _)

/-- (Implementation) The inverse of `compHom`. -/
noncomputable def compInv : tildeΩ f ⟶ relativeDifferentials (f ≫ (ΓSpecIso A).inv) :=
  (forgetR A).preimage (nT f)

lemma compHom_compInv : compHom f ≫ compInv f = 𝟙 _ := by
  apply ((sheafAdj A).homEquiv _ _).injective
  refine ((sheafAdj A).homEquiv_naturality_right (compHom f) (compInv f)).trans ?_
  have h1 : (sheafAdj A).homEquiv _ _ (compHom f) = mT f := Equiv.apply_symm_apply _ _
  have h2 : (forgetR A).map (compInv f) = nT f := (forgetR A).map_preimage _
  rw [h1]
  exact (congrArg (mT f ≫ ·) h2).trans (mT_comp_nT f)

lemma eta_comp_compHom : unitη f ≫ (forgetR A).map (compHom f) = mT f :=
  ((sheafAdj A).homEquiv_naturality_right (𝟙 _) (compHom f)).symm.trans
    ((congrArg ((sheafAdj A).homEquiv _ _) (Category.id_comp (compHom f))).trans
      (Equiv.apply_symm_apply _ _))

lemma compInv_compHom : compInv f ≫ compHom f = 𝟙 _ := by
  apply (forgetR A).map_injective
  apply (_root_.PresheafOfModules.homEquivOfIsLocallyBijective (mT f) (tildeΩ f).isSheaf).injective
  refine (_root_.PresheafOfModules.homEquivOfIsLocallyBijective_apply (mT f) _ _).trans ?_
  refine Eq.trans ?_ (_root_.PresheafOfModules.homEquivOfIsLocallyBijective_apply (mT f) _ _).symm
  have h2 : (forgetR A).map (compInv f) = nT f := (forgetR A).map_preimage _
  calc mT f ≫ (forgetR A).map (compInv f ≫ compHom f)
      = (mT f ≫ nT f) ≫ (forgetR A).map (compHom f) := by
        rw [Functor.map_comp, h2, Category.assoc]
    _ = mT f := by rw [mT_comp_nT, eta_comp_compHom]
    _ = mT f ≫ (forgetR A).map (𝟙 _) := by
      rw [CategoryTheory.Functor.map_id]; exact (Category.comp_id _).symm

lemma dSheaf_top_algebraMap (a : A) :
    (dSheaf f).app (op ⊤) (algebraMap A Γ(Spec A, ⊤) a) =
      tilde.toOpen (CommRingCat.KaehlerDifferential f) ⊤ (CommRingCat.KaehlerDifferential.d a) := by
  apply tildeΩ_ext
  intro g hg
  rw [dSheaf_restrict]
  have : (Spec A).presheaf.map (homOfLE hg).op (algebraMap A Γ(Spec A, ⊤) a) =
      algebraMap A Γ(Spec A, bo g) a := by
    change (((ΓSpecIso A).inv ≫ (Spec A).presheaf.map (homOfLE le_top).op) ≫
      (Spec A).presheaf.map (homOfLE hg).op) a =
        ((ΓSpecIso A).inv ≫ (Spec A).presheaf.map (homOfLE le_top).op) a
    rw [Category.assoc, ← Functor.map_comp]
    rfl
  rw [this, dBasic_algebraMap]
  exact (congr($(tilde.toOpen_res (CommRingCat.KaehlerDifferential f) _ _ (homOfLE hg)).hom
    (CommRingCat.KaehlerDifferential.d a))).symm

end RelativeDifferentialsSpec

open RelativeDifferentialsSpec in
/-- **Affine computation of the sheaf of relative differentials.** For a ring map `f : R ⟶ A`,
the sheaf of relative differentials of `Spec A` over `R` (`relativeDifferentials` for the
structure map `f ≫ (ΓSpecIso A).inv`) is isomorphic, as an `𝒪_{Spec A}`-module, to the
quasi-coherent sheaf `Ω[A⁄R]^~` associated with the `A`-module of Kähler differentials.
This upgrades Stacks Project, Tag 01UT, in the case `U = X = Spec A`,
`V = S = Spec R`, to an isomorphism of sheaves; the base is the constant ring `R` (see the module
docstring). -/
noncomputable def relativeDifferentialsSpecIso :
    relativeDifferentials (f ≫ (ΓSpecIso A).inv) ≅ tilde (CommRingCat.KaehlerDifferential f) where
  hom := compHom f
  inv := compInv f
  hom_inv_id := compHom_compInv f
  inv_hom_id := compInv_compHom f

/-- The sheaf of relative differentials of `Spec A` over `R` is quasi-coherent. -/
instance isQuasicoherent_relativeDifferentials_Spec :
    (relativeDifferentials (f ≫ (ΓSpecIso A).inv)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    (relativeDifferentialsSpecIso f).symm
    (inferInstance : (tilde (CommRingCat.KaehlerDifferential f)).IsQuasicoherent)

/-- **Global sections of the sheaf of relative differentials of `Spec A` over `R`.** For a ring
map `f : R ⟶ A`, the `A`-module of global sections of `relativeDifferentials` (for the structure
map `f ≫ (ΓSpecIso A).inv`) is isomorphic to `Ω[A⁄R]`; by
`relativeDifferentialsSpecΓIso_hom_d` the isomorphism is compatible with the universal
derivations. Stacks Project, Tag 01UT, for `U = X = Spec A`, `V = S = Spec R`,
with the base taken as the constant ring `R`. -/
noncomputable def relativeDifferentialsSpecΓIso :
    moduleSpecΓFunctor.obj (relativeDifferentials (f ≫ (ΓSpecIso A).inv)) ≅
      CommRingCat.KaehlerDifferential f :=
  moduleSpecΓFunctor.mapIso (relativeDifferentialsSpecIso f) ≪≫ (tilde.isoTop _).symm

open RelativeDifferentialsSpec in
/-- The isomorphism `relativeDifferentialsSpecΓIso f` sends the universal derivation of the
global section `a ∈ A` (viewed in `Γ(Spec A, ⊤)` via `ΓSpecIso`) to `d a ∈ Ω[A⁄R]`
(the compatibility with derivations in Stacks Project, Tag 01UT). -/
lemma relativeDifferentialsSpecΓIso_hom_d (a : A) :
    (relativeDifferentialsSpecΓIso f).hom
      ((relativeDifferentialsDerivation (f ≫ (ΓSpecIso A).inv)).d (X := op ⊤)
        ((ΓSpecIso A).inv a)) = CommRingCat.KaehlerDifferential.d (f := f) a := by
  have h1 : (ΓSpecIso A).inv a = algebraMap A Γ(Spec A, ⊤) a := by
    rw [IsAffineOpen.algebraMap_Spec_obj]
    change _ = ((Spec A).presheaf.map (𝟙 _)) _
    rw [CategoryTheory.Functor.map_id]
    rfl
  have h2 : (relativeDifferentialsDerivation (f ≫ (ΓSpecIso A).inv)).d (X := op ⊤)
      ((ΓSpecIso A).inv a) = (unitη f).app (op ⊤)
        (CommRingCat.KaehlerDifferential.d ((ΓSpecIso A).inv a)) := rfl
  have h3 : (compHom f).val.app (op ⊤) ((unitη f).app (op ⊤)
      (CommRingCat.KaehlerDifferential.d ((ΓSpecIso A).inv a))) =
        (mT f).app (op ⊤) (CommRingCat.KaehlerDifferential.d ((ΓSpecIso A).inv a)) :=
    congr($(eta_comp_compHom f).app (op ⊤) (CommRingCat.KaehlerDifferential.d ((ΓSpecIso A).inv a)))
  rw [h2]
  change (tilde.isoTop _).inv ((compHom f).val.app (op ⊤) _) = _
  rw [h3, mT_app_d, h1, dSheaf_top_algebraMap]
  exact (tilde.isoTop _).hom_inv_id_apply _

/-- If `Ω[A⁄R]` has a basis indexed by `ι`, then the sheaf of relative differentials of `Spec A`
over `R` is isomorphic to the free `𝒪_{Spec A}`-module on `ι`. -/
noncomputable def relativeDifferentialsSpecIsoFree {ι : Type u}
    (b : Module.Basis ι A (CommRingCat.KaehlerDifferential f)) :
    relativeDifferentials (f ≫ (ΓSpecIso A).inv) ≅ SheafOfModules.free ι :=
  relativeDifferentialsSpecIso f ≪≫ (tilde.functor A).mapIso b.repr.toModuleIso ≪≫
    tildeFinsupp ι

/-- If `Ω[A⁄R] ≅ A` as `A`-modules (i.e. `Ω[A⁄R]` is free of rank one, generated by
`e.symm 1`), then the sheaf of relative differentials of `Spec A` over `R` is isomorphic to
`𝒪_{Spec A}`. -/
noncomputable def relativeDifferentialsSpecIsoUnit
    (e : CommRingCat.KaehlerDifferential f ≃ₗ[A] A) :
    relativeDifferentials (f ≫ (ΓSpecIso A).inv) ≅ SheafOfModules.unit (Spec A).ringCatSheaf :=
  relativeDifferentialsSpecIso f ≪≫ (tilde.functor A).mapIso e.toModuleIso ≪≫ tildeSelf

/-- If `A` is a (nontrivial) standard smooth `R`-algebra of relative dimension `n` (via `f`), then
the sheaf of relative differentials of `Spec A` over `R` is isomorphic to a free
`𝒪_{Spec A}`-module on a set of cardinality `n`. -/
theorem exists_iso_free_of_isStandardSmoothOfRelativeDimension (n : ℕ) [Nontrivial A]
    (h : letI := f.hom.toAlgebra; Algebra.IsStandardSmoothOfRelativeDimension n R A) :
    ∃ (ι : Type u), Cardinal.mk ι = n ∧
      Nonempty (relativeDifferentials (f ≫ (ΓSpecIso A).inv) ≅ SheafOfModules.free ι) := by
  let := f.hom.toAlgebra
  have := h
  have : Algebra.IsStandardSmooth R A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  let b := Module.Free.chooseBasis A Ω[A⁄R]
  exact ⟨_, b.mk_eq_rank''.trans
    (Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n),
    ⟨relativeDifferentialsSpecIsoFree f b⟩⟩

end Spec

end AlgebraicGeometry.Scheme
