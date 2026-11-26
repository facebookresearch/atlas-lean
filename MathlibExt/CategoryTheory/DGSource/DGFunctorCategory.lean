/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed source port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Functor/Category.lean
Only module/namespace paths are adapted for Atlas; source operations and hypotheses are retained.
-/

public import MathlibExt.CategoryTheory.DGSource.DGFunctorHomComplex
public import MathlibExt.CategoryTheory.DGSource.DGNaturalTransformation

/-!
# The differential graded category of DG functors

For differential graded categories `C` and `D` over `R`, with `C` small, the DG functors
`C ⥤ D` form a differential graded category.  A morphism `F ⟶ G` of degree `n` is a family of
degree-`n` morphisms `η X : F X ⟶ G X` which is natural up to the Koszul sign: for every
morphism `f : X ⟶ Y` of degree `p`,

`F f ≫ η Y = (-1) ^ (p * n) • (η X ≫ G f)`,

in Mathlib's enriched factor order.  In Keller's order this is the familiar condition
`G f ∘ η X = (-1) ^ (p * n) • η Y ∘ F f`.  The differential, composition and identity are
computed objectwise: `(d η) X = d (η X)`, `(η ≫ θ) X = η X ≫ θ X` and `(𝟙 F) X = 𝟙 (F X)`.  The
Leibniz rule shows that the differential of a natural family is natural with the sign of the
next degree.

This is the DG category in which modules over a DG category live: a right DG module over `C` is
a DG functor `Cᵒᵖ ⥤ C(R)` to cochain complexes, and the morphism complexes of modules are the
Hom complexes constructed here.

The objects are those of `MathlibExt.DGSource.DGFunctor R C D`, whose ordinary morphisms are the closed
degree-zero DG natural transformations; these are exactly the closed degree-zero morphisms of the
DG category constructed here.  The source `C` lives in the universe of the ground ring, so that a
natural family, a family indexed by the objects of `C`, is again a module in that universe.

## Main definitions

* `MathlibExt.DGSource.DGFunctor.IsNatural`: a family of homogeneous morphisms is natural up to the Koszul
  sign.
* `MathlibExt.DGSource.DGFunctor.natTransSubmodule`: the natural families of degree `n`.
* `MathlibExt.DGSource.DGFunctor.homComplexData`: the Hom-complex data of DG functors.
* `MathlibExt.DGSource.DGFunctor.instDGCategory`: DG functors `C ⥤ D` form a differential graded category.
* `MathlibExt.DGSource.DGFunctor.dgHomEquiv`: a morphism of degree `n` is a natural family of degree `n`.
* `MathlibExt.DGSource.DGFunctor.dgApp`: the component of a morphism of DG functors at an object.
* `MathlibExt.DGSource.DGFunctor.homEquivDGCycles`: DG natural transformations `F ⟶ G` are the closed
  degree-zero morphisms `F ⟶ G` of the DG category of DG functors.

## Main results

* `MathlibExt.DGSource.DGFunctor.IsNatural.dgDifferential`: the differential of a natural family is
  natural.
* `MathlibExt.DGSource.DGFunctor.IsNatural.dgComp`: composites of natural families are natural.
* `MathlibExt.DGSource.DGFunctor.dgComp_dgMap_dgApp`: morphisms of DG functors are natural up to the
  Koszul sign.
* `MathlibExt.DGSource.DGFunctor.dgApp_dgDifferential`, `MathlibExt.DGSource.DGFunctor.dgApp_dgComp` and
  `MathlibExt.DGSource.DGFunctor.dgApp_dgId`: the differential, composition and identity are objectwise.
* `MathlibExt.DGSource.DGFunctor.homEquivDGCycles_id` and `MathlibExt.DGSource.DGFunctor.homEquivDGCycles_comp`: the
  identification of DG natural transformations with closed morphisms respects identities and
  composition.

## References

* `MathlibExt.CategoryTheory.DGSourceMore.DGAdditiveClosure`, whose explicit construction through
  `DGCategoryData.toDGCategory` is followed here.
* B. Keller, *Deriving DG categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.
-/

public section

open CategoryTheory MonoidalCategory

namespace MathlibExt.DGSource

universe v u₁ u₂

namespace DGFunctor

variable (R : Type v) [CommRing R]

/-! ### Natural families of homogeneous morphisms -/

section IsNatural

variable {R} {C : Type u₁} {D : Type u₂} [DGCategory R C] [DGCategory R D]

/-- A family `η X : F X ⟶ G X` of morphisms of degree `n` is **natural** when it commutes with
every homogeneous morphism up to the Koszul sign: for `f : X ⟶ Y` of degree `p`, the composite
`F f ≫ η Y` is `(-1) ^ (p * n)` times `η X ≫ G f`.  The degree `m` of both composites is left
free, so that the condition can be used without transporting degrees. -/
def IsNatural {F G : DGFunctor R C D} {n : ℤ}
    (η : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)) : Prop :=
  ∀ ⦃X Y : C⦄ ⦃p m : ℤ⦄ (f : DGHom R p X Y) (h₁ : p + n = m) (h₂ : n + p = m),
    dgComp R (F.toEnrichedFunctor.dgMap p f) (η Y) h₁ =
      (p * n).negOnePow • dgComp R (η X) (G.toEnrichedFunctor.dgMap p f) h₂

variable {F G H : DGFunctor R C D}

/-- The defining condition of a natural family. -/
theorem isNatural_def {n : ℤ}
    {η : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)} :
    IsNatural η ↔ ∀ ⦃X Y : C⦄ ⦃p m : ℤ⦄ (f : DGHom R p X Y) (h₁ : p + n = m) (h₂ : n + p = m),
      dgComp R (F.toEnrichedFunctor.dgMap p f) (η Y) h₁ =
        (p * n).negOnePow • dgComp R (η X) (G.toEnrichedFunctor.dgMap p f) h₂ :=
  Iff.rfl

/-- A natural family commutes with a homogeneous morphism `f` of degree `p` up to the Koszul
sign: `F f ≫ η Y = (-1) ^ (p * n) • (η X ≫ G f)`. -/
theorem IsNatural.dgComp_dgMap {n : ℤ}
    {η : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)}
    (hη : IsNatural η) {X Y : C} {p m : ℤ} (f : DGHom R p X Y) (h₁ : p + n = m)
    (h₂ : n + p = m) :
    dgComp R (F.toEnrichedFunctor.dgMap p f) (η Y) h₁ =
      (p * n).negOnePow • dgComp R (η X) (G.toEnrichedFunctor.dgMap p f) h₂ :=
  hη f h₁ h₂

/-- Naturality may be checked with the degree of the two composites fixed to be `p + n`. -/
theorem isNatural_iff {n : ℤ}
    {η : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)} :
    IsNatural η ↔ ∀ ⦃X Y : C⦄ (p : ℤ) (f : DGHom R p X Y),
      dgComp R (F.toEnrichedFunctor.dgMap p f) (η Y) rfl =
        (p * n).negOnePow • dgComp R (η X) (G.toEnrichedFunctor.dgMap p f) (add_comm n p) := by
  refine ⟨fun hη X Y p f ↦ hη f rfl (add_comm n p), fun hη X Y p m f h₁ h₂ ↦ ?_⟩
  subst h₁
  exact hη p f

/-- The zero family is natural. -/
theorem isNatural_zero (n : ℤ) :
    IsNatural (F := F) (G := G) (n := n) fun _ ↦ 0 := by
  intro X Y p m f h₁ h₂
  simp

/-- A sum of natural families is natural. -/
theorem IsNatural.add {n : ℤ}
    {η θ : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)}
    (hη : IsNatural η) (hθ : IsNatural θ) : IsNatural (η + θ) := by
  intro X Y p m f h₁ h₂
  simp only [Pi.add_apply, dgComp_add, add_dgComp, smul_add, hη f h₁ h₂, hθ f h₁ h₂]

/-- A scalar multiple of a natural family is natural. -/
theorem IsNatural.smul {n : ℤ}
    {η : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)}
    (hη : IsNatural η) (r : R) : IsNatural (r • η) := by
  intro X Y p m f h₁ h₂
  simp only [Pi.smul_apply, dgComp_smul, smul_dgComp, hη f h₁ h₂, smul_comm r]

/-- **The differential of a natural family is natural**, with the Koszul sign of the next
degree `n + 1`. -/
theorem IsNatural.dgDifferential {n : ℤ}
    {η : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)}
    (hη : IsNatural η) : IsNatural fun X ↦ dgDifferential R n (η X) := by
  rw [isNatural_iff]
  intro X Y p f
  -- The Koszul sign exponents: naturality of `η` against `d f`, of degree `p + 1`, carries the
  -- exponent `(p + 1) * n`, and the Leibniz sign `p` combines with `p * n` into the exponent
  -- `p * (n + 1)` for the next degree.
  have hd : (p + 1) * n = p * n + n := by ring
  have hnext : p + p * n = p * (n + 1) := by ring
  have key := congrArg
    ((dgHomComplex R (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj Y)).d (p + n)
      (p + (n + 1))).hom (hη f rfl (add_comm n p))
  rw [map_zsmul_unit, dgHomComplex_d_dgComp R rfl rfl (by omega),
    dgHomComplex_d_dgComp R rfl rfl (by omega)] at key
  simp only [← EnrichedFunctor.dgMap_dgDifferential] at key
  rw [hη (MathlibExt.DGSource.dgDifferential R p f) (by omega) (by omega), smul_add, smul_smul,
    ← Int.negOnePow_add, hd] at key
  have key' := congrArg (p.negOnePow • ·) (add_left_cancel (key.trans (add_comm _ _)))
  simp only [smul_smul, Int.units_mul_self, one_smul] at key'
  refine key'.trans ?_
  rw [← Int.negOnePow_add, hnext]

/-- The differentials of a Hom complex between arbitrary indices preserve natural families. -/
theorem IsNatural.d {n : ℤ}
    {η : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)}
    (hη : IsNatural η) (m : ℤ) :
    IsNatural fun X ↦
      ((dgHomComplex R (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)).d n m).hom
        (η X) := by
  by_cases hnm : n + 1 = m
  · subst hnm
    exact hη.dgDifferential
  · have hz (X : C) :
        (dgHomComplex R (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)).d n m = 0 :=
      HomologicalComplex.shape _ n m hnm
    simp only [hz, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact isNatural_zero m

/-- **Composites of natural families are natural.** -/
theorem IsNatural.dgComp {p q n : ℤ}
    {η : ∀ X : C, DGHom R p (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)}
    {θ : ∀ X : C, DGHom R q (G.toEnrichedFunctor.obj X) (H.toEnrichedFunctor.obj X)}
    (hη : IsNatural η) (hθ : IsNatural θ) (h : p + q = n) :
    IsNatural fun X ↦ MathlibExt.DGSource.dgComp R (η X) (θ X) h := by
  intro X Y r m f h₁ h₂
  subst h
  rw [← dgComp_assoc R (F.toEnrichedFunctor.dgMap r f) (η Y) (θ Y) rfl rfl (n := m) (by omega),
    hη f rfl (add_comm p r), units_smul_dgComp,
    dgComp_assoc R (η X) (G.toEnrichedFunctor.dgMap r f) (θ Y) (add_comm p r) rfl (n := m)
      (by omega),
    hθ f rfl (add_comm q r), dgComp_units_smul,
    ← dgComp_assoc R (η X) (θ X) (H.toEnrichedFunctor.dgMap r f) rfl (add_comm q r) (n := m)
      (by omega), smul_smul, ← Int.negOnePow_add, ← mul_add]

/-- The family of identities is natural. -/
theorem isNatural_dgId (F : DGFunctor R C D) :
    IsNatural (F := F) (G := F) fun X ↦ dgId R (F.toEnrichedFunctor.obj X) := by
  intro X Y p m f h₁ h₂
  obtain rfl : p = m := by omega
  rw [dgComp_dgId, dgId_dgComp, mul_zero, Int.negOnePow_zero, one_smul]

variable (F G) in
/-- The `R`-module of natural families of morphisms `F X ⟶ G X` of degree `n`: the degree-`n`
morphisms `F ⟶ G` of the DG category of DG functors. -/
def natTransSubmodule (n : ℤ) :
    Submodule R (∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)) where
  carrier := {η | IsNatural η}
  add_mem' hη hθ := hη.add hθ
  zero_mem' := isNatural_zero n
  smul_mem' r _ hη := hη.smul r

@[simp]
theorem mem_natTransSubmodule {n : ℤ}
    {η : ∀ X : C, DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)} :
    η ∈ natTransSubmodule F G n ↔ IsNatural η :=
  Iff.rfl

end IsNatural

/-! ### The Hom complexes -/

section HomComplex

variable {C : Type v} {D : Type u₂} [DGCategory R C] [DGCategory R D]

/-- The differential of the Hom complex of DG functors between arbitrary indices, objectwise. -/
private noncomputable def dNat (F G : DGFunctor R C D) (n m : ℤ) :
    natTransSubmodule F G n →ₗ[R] natTransSubmodule F G m :=
  (LinearMap.piMap fun X ↦
    ((dgHomComplex R (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)).d n m).hom).restrict
    fun _ hη ↦ IsNatural.d hη m

private theorem dNat_apply (F G : DGFunctor R C D) (n m : ℤ) (η : natTransSubmodule F G n)
    (X : C) :
    (dNat R F G n m η).1 X =
      ((dgHomComplex R (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X)).d n m).hom
        (η.1 X) :=
  (rfl)

private theorem dNat_eq_zero (F G : DGFunctor R C D) {n m : ℤ}
    (h : ¬(ComplexShape.up ℤ).Rel n m) : dNat R F G n m = 0 :=
  LinearMap.ext fun η ↦ Subtype.ext <| funext fun X ↦ by
    rw [dNat_apply, HomologicalComplex.shape _ n m h]
    rfl

private theorem dNat_comp_dNat (F G : DGFunctor R C D) (n m l : ℤ) :
    dNat R F G m l ∘ₗ dNat R F G n m = 0 :=
  LinearMap.ext fun η ↦ Subtype.ext <| funext fun X ↦ by
    rw [LinearMap.comp_apply, dNat_apply, dNat_apply, ← LinearMap.comp_apply,
      ← ModuleCat.hom_comp, HomologicalComplex.d_comp_d]
    rfl

/-- The Hom complex of DG functors `F ⟶ G`: in degree `n` the natural families of degree `n`,
with the objectwise differential. -/
private noncomputable def homComplex (F G : DGFunctor R C D) :
    CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (natTransSubmodule F G n)
  d n m := ModuleCat.ofHom (dNat R F G n m)
  shape n m h := by rw [dNat_eq_zero R F G h]; rfl
  d_comp_d' n m l _ _ := by rw [← ModuleCat.ofHom_comp, dNat_comp_dNat]; rfl

/-- Composition of natural families, objectwise. -/
private noncomputable def comp {F G H : DGFunctor R C D} (p q n : ℤ) (h : p + q = n) :
    natTransSubmodule F G p →ₗ[R] natTransSubmodule G H q →ₗ[R] natTransSubmodule F H n :=
  LinearMap.mk₂ R (fun η θ ↦ ⟨fun X ↦ dgComp R (η.1 X) (θ.1 X) h, η.2.dgComp θ.2 h⟩)
    (fun η η' θ ↦ by ext X; simp)
    (fun r η θ ↦ by ext X; simp)
    (fun η θ θ' ↦ by ext X; simp)
    (fun r η θ ↦ by ext X; simp)

/-- The **Hom-complex data of DG functors** `C ⥤ D`: natural families of homogeneous morphisms
with the objectwise differential, composition and identities. -/
noncomputable def homComplexData : DGCategoryData R (DGFunctor R C D) where
  hom := homComplex R
  comp := comp R
  id F := ⟨fun X ↦ dgId R (F.toEnrichedFunctor.obj X), isNatural_dgId F⟩
  d_comp h η θ := Subtype.ext <| funext fun X ↦ dgDifferential_dgComp R (η.1 X) (θ.1 X) h
  comp_assoc hpq hqr h η θ κ := Subtype.ext <| funext fun X ↦
    dgComp_assoc R (η.1 X) (θ.1 X) (κ.1 X) hpq hqr h
  id_comp θ := Subtype.ext <| funext fun X ↦ dgId_dgComp R (θ.1 X)
  comp_id η := Subtype.ext <| funext fun X ↦ dgComp_dgId R (η.1 X)

/-- **DG functors `C ⥤ D` form a differential graded category**, whose morphisms of degree `n`
are the natural families of degree `n`. -/
noncomputable instance instDGCategory : DGCategory R (DGFunctor R C D) :=
  (homComplexData R).toDGCategory

/-! ### Morphisms, differential, composition and identity -/

/-- A morphism `F ⟶ G` of degree `n` of DG functors is a natural family of degree-`n` morphisms
`F X ⟶ G X`. -/
noncomputable def dgHomEquiv (F G : DGFunctor R C D) (n : ℤ) :
    DGHom R n F G ≃ₗ[R] natTransSubmodule F G n :=
  LinearEquiv.refl R _

/-- The component at `X` of a morphism of DG functors of degree `n`. -/
noncomputable def dgApp {F G : DGFunctor R C D} (n : ℤ) (X : C) :
    DGHom R n F G →ₗ[R] DGHom R n (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X) :=
  (LinearMap.proj X ∘ₗ (natTransSubmodule F G n).subtype) ∘ₗ (dgHomEquiv R F G n).toLinearMap

/-- The components of a morphism of DG functors are its underlying natural family. -/
theorem dgApp_apply {F G : DGFunctor R C D} {n : ℤ} (η : DGHom R n F G) (X : C) :
    dgApp R n X η = (dgHomEquiv R F G n η).1 X :=
  (rfl)

/-- The components of the morphism determined by a natural family are the members of the
family. -/
@[simp]
theorem dgApp_dgHomEquiv_symm_apply {F G : DGFunctor R C D} {n : ℤ}
    (η : natTransSubmodule F G n) (X : C) :
    dgApp R n X ((dgHomEquiv R F G n).symm η) = η.1 X :=
  (rfl)

/-- The components of a morphism of DG functors form a natural family. -/
theorem isNatural_dgApp {F G : DGFunctor R C D} {n : ℤ} (η : DGHom R n F G) :
    IsNatural fun X ↦ dgApp R n X η :=
  (dgHomEquiv R F G n η).2

/-- **Naturality of a morphism of DG functors**: for `f : X ⟶ Y` of degree `p` and `η : F ⟶ G`
of degree `n`, `F f ≫ η Y = (-1) ^ (p * n) • (η X ≫ G f)`. -/
theorem dgComp_dgMap_dgApp {F G : DGFunctor R C D} {n p m : ℤ} (η : DGHom R n F G) {X Y : C}
    (f : DGHom R p X Y) (h₁ : p + n = m) (h₂ : n + p = m) :
    dgComp R (F.toEnrichedFunctor.dgMap p f) (dgApp R n Y η) h₁ =
      (p * n).negOnePow • dgComp R (dgApp R n X η) (G.toEnrichedFunctor.dgMap p f) h₂ :=
  (isNatural_dgApp R η).dgComp_dgMap f h₁ h₂

/-- Morphisms of DG functors are determined by their components. -/
theorem dgHom_ext {F G : DGFunctor R C D} {n : ℤ} {η θ : DGHom R n F G}
    (h : ∀ X, dgApp R n X η = dgApp R n X θ) : η = θ :=
  (dgHomEquiv R F G n).injective (Subtype.ext (funext h))

/-- **The differential of DG functors is objectwise**: `(d η) X = d (η X)`. -/
@[simp↓]
theorem dgApp_dgDifferential {F G : DGFunctor R C D} {n : ℤ} (η : DGHom R n F G) (X : C) :
    dgApp R (n + 1) X (dgDifferential R n η) = dgDifferential R n (dgApp R n X η) :=
  congrFun (congrArg Subtype.val ((homComplexData R).dgDifferential_toDGCategory n η)) X

/-- **Composition of DG functors is objectwise**: `(η ≫ θ) X = η X ≫ θ X`. -/
@[simp↓]
theorem dgApp_dgComp {F G H : DGFunctor R C D} {p q n : ℤ} (η : DGHom R p F G)
    (θ : DGHom R q G H) (h : p + q = n) (X : C) :
    dgApp R n X (dgComp R η θ h) = dgComp R (dgApp R p X η) (dgApp R q X θ) h :=
  congrFun (congrArg Subtype.val ((homComplexData R).dgComp_toDGCategory η θ h)) X

/-- **The identity of a DG functor is objectwise**: `𝟙 F X = 𝟙 (F X)`. -/
@[simp↓]
theorem dgApp_dgId (F : DGFunctor R C D) (X : C) :
    dgApp R 0 X (dgId R F) = dgId R (F.toEnrichedFunctor.obj X) :=
  congrFun (congrArg Subtype.val ((homComplexData R).dgId_toDGCategory F)) X

/-! ### Closed degree-zero morphisms

The closed degree-zero morphisms `F ⟶ G` of this DG category are the morphisms of the ordinary
category of DG functors, whose components are maps from the tensor unit to the Hom complexes.
-/

/-- The closed components of a closed degree-zero DG natural transformation form a natural
family: graded naturality at the tensor unit, evaluated in degree `p`. -/
private theorem isNatural_dgClosedHom_app {F G : DGFunctor R C D} (α : F ⟶ G) :
    IsNatural (F := F) (G := G) (n := 0) fun X ↦
      dgClosedHom R
        (ForgetEnrichment.homOf (CochainComplex (ModuleCat.{v} R) ℤ) (α.app X)) := by
  intro X Y p m f h₁ h₂
  obtain rfl : p = m := by omega
  rw [mul_zero, Int.negOnePow_zero, one_smul]
  have hs : ((eHomWhiskerLeft (CochainComplex (ModuleCat.{v} R) ℤ)
      (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) (F.toEnrichedFunctor.obj X))
      (ForgetEnrichment.homOf (CochainComplex (ModuleCat.{v} R) ℤ) (α.app Y))).f p).hom
        (((F.toEnrichedFunctor.map X Y).f p).hom f) =
      ((eHomWhiskerRight (CochainComplex (ModuleCat.{v} R) ℤ)
        (ForgetEnrichment.homOf (CochainComplex (ModuleCat.{v} R) ℤ) (α.app X))
        (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ)
          (G.toEnrichedFunctor.obj Y))).f p).hom
          (((G.toEnrichedFunctor.map X Y).f p).hom f) :=
    congrArg (fun φ ↦ (φ.f p).hom f)
      ((unitGradedNaturality_iff F.toEnrichedFunctor G.toEnrichedFunctor X Y (α.app X)
        (α.app Y)).mp (α.naturality X Y))
  have hl := eHomWhiskerLeft_f_apply R _
    (ForgetEnrichment.homOf (CochainComplex (ModuleCat.{v} R) ℤ) (α.app Y)) p
    (((F.toEnrichedFunctor.map X Y).f p).hom f)
  have hr := eHomWhiskerRight_f_apply R
    (ForgetEnrichment.homOf (CochainComplex (ModuleCat.{v} R) ℤ) (α.app X)) _ p
    (((G.toEnrichedFunctor.map X Y).f p).hom f)
  rw [EnrichedFunctor.dgMap_apply, EnrichedFunctor.dgMap_apply]
  exact hl.symm.trans (hs.trans hr)

/-- The components of a closed morphism of DG functors are closed. -/
theorem dgApp_mem_dgCycles {F G : DGFunctor R C D} {η : DGHom R 0 F G}
    (hη : η ∈ dgCycles R F G) (X : C) :
    dgApp R 0 X η ∈ dgCycles R (F.toEnrichedFunctor.obj X) (G.toEnrichedFunctor.obj X) := by
  rw [mem_dgCycles] at hη ⊢
  rw [← dgApp_dgDifferential, hη, map_zero]

variable (F G : DGFunctor R C D)

/-- **Closed degree-zero morphisms of DG functors are DG natural transformations**: the
morphisms `F ⟶ G` of the category of DG functors correspond to the closed degree-zero morphisms
`F ⟶ G` of the DG category of DG functors, componentwise. -/
noncomputable def homEquivDGCycles : (F ⟶ G) ≃ dgCycles R F G where
  toFun α :=
    ⟨(dgHomEquiv R F G 0).symm
        ⟨fun X ↦ dgClosedHom R (ForgetEnrichment.homOf _ (α.app X)),
          isNatural_dgClosedHom_app R α⟩,
      (mem_dgCycles R).mpr (dgHom_ext R fun X ↦ by
        rw [dgApp_dgDifferential, dgApp_dgHomEquiv_symm_apply, map_zero]
        exact (mem_dgCycles R).mp (dgClosedHom_mem_dgCycles R _))⟩
  invFun η :=
    { app X := ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ)
        (dgClosedHomOf R (dgApp R 0 X η.1) (dgApp_mem_dgCycles R η.2 X))
      naturality X Y := by
        apply (unitGradedNaturality_iff F.toEnrichedFunctor G.toEnrichedFunctor X Y _ _).mpr
        ext p f
        have hl := eHomWhiskerLeft_f_apply R _
          (dgClosedHomOf R (dgApp R 0 Y η.1) (dgApp_mem_dgCycles R η.2 Y)) p
          (((F.toEnrichedFunctor.map X Y).f p).hom f)
        have hr := eHomWhiskerRight_f_apply R
          (dgClosedHomOf R (dgApp R 0 X η.1) (dgApp_mem_dgCycles R η.2 X)) _ p
          (((G.toEnrichedFunctor.map X Y).f p).hom f)
        rw [dgClosedHom_dgClosedHomOf] at hl hr
        refine hl.trans (Eq.trans ?_ hr.symm)
        rw [← EnrichedFunctor.dgMap_apply, ← EnrichedFunctor.dgMap_apply,
          dgComp_dgMap_dgApp R η.1 f (add_zero p) (zero_add p), mul_zero, Int.negOnePow_zero,
          one_smul] }
  left_inv α := GradedNatTrans.ext <| funext fun X ↦ by
    -- Reducing the equivalence application and its subtype coercions exposes the two canonical
    -- conversions from an enriched component to a closed DG morphism and back.
    change ForgetEnrichment.homTo _ (dgClosedHomOf R
      (dgClosedHom R (ForgetEnrichment.homOf _ (α.app X))) _) = α.app X
    exact (congrArg (ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ))
      (dgClosedHomOf_dgClosedHom R (ForgetEnrichment.homOf _ (α.app X)))).trans
        (ForgetEnrichment.homTo_homOf _ _)
  right_inv η := Subtype.ext <| dgHom_ext R fun X ↦ by
    -- Componentwise extensionality reduces the equivalence wrappers to the reverse round trip:
    -- first `homTo`/`homOf`, then `dgClosedHomOf`/`dgClosedHom`.
    change dgClosedHom R (ForgetEnrichment.homOf _
      (ForgetEnrichment.homTo _ (dgClosedHomOf R (dgApp R 0 X η.1) _))) = dgApp R 0 X η.1
    exact (congrArg (dgClosedHom R)
      (ForgetEnrichment.homOf_homTo _ (dgClosedHomOf R (dgApp R 0 X η.1)
        (dgApp_mem_dgCycles R η.2 X)))).trans
          (dgClosedHom_dgClosedHomOf R _ _)

variable {F G}

/-- The components of the closed morphism determined by a DG natural transformation `α` are the
closed morphisms underlying the components of `α`. -/
@[simp]
theorem dgApp_homEquivDGCycles_apply (α : F ⟶ G) (X : C) :
    dgApp R 0 X (homEquivDGCycles R F G α : DGHom R 0 F G) =
      dgClosedHom R (ForgetEnrichment.homOf (CochainComplex (ModuleCat.{v} R) ℤ) (α.app X)) :=
  dgApp_dgHomEquiv_symm_apply R _ X

/-- The components of the DG natural transformation determined by a closed morphism `η` are the
components of `η`, regarded as maps from the tensor unit. -/
@[simp]
theorem homEquivDGCycles_symm_app (η : dgCycles R F G) (X : C) :
    ((homEquivDGCycles R F G).symm η).app X =
      ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ)
        (dgClosedHomOf R (dgApp R 0 X η.1) (dgApp_mem_dgCycles R η.2 X)) :=
  (rfl)

/-- The identity DG natural transformation is the identity of the DG category of DG
functors. -/
@[simp]
theorem homEquivDGCycles_id :
    (homEquivDGCycles R F F (𝟙 F) : DGHom R 0 F F) = dgId R F :=
  dgHom_ext R fun X ↦ by
    rw [dgApp_homEquivDGCycles_apply, dgApp_dgId]
    exact (congrArg (fun a ↦ dgClosedHom R (ForgetEnrichment.homOf _ a))
      (DGNatTrans.id_app F.toEnrichedFunctor X)).trans
      ((congrArg (dgClosedHom R) (ForgetEnrichment.homOf_eId _ _)).trans (dgClosedHom_id R _))

/-- Composition of DG natural transformations is composition in the DG category of DG
functors. -/
@[simp]
theorem homEquivDGCycles_comp {H : DGFunctor R C D} (α : F ⟶ G) (β : G ⟶ H) :
    (homEquivDGCycles R F H (α ≫ β) : DGHom R 0 F H) =
      dgCompZero R (homEquivDGCycles R F G α : DGHom R 0 F G)
        (homEquivDGCycles R G H β : DGHom R 0 G H) :=
  dgHom_ext R fun X ↦ by
    rw [dgCompZero_def, dgApp_dgComp, dgApp_homEquivDGCycles_apply,
      dgApp_homEquivDGCycles_apply, dgApp_homEquivDGCycles_apply]
    exact (congrArg (fun a ↦ dgClosedHom R (ForgetEnrichment.homOf _ a))
      (DGNatTrans.comp_app α β X)).trans ((dgClosedHom_comp R _ _).trans (dgCompZero_def R _ _))

end HomComplex

end DGFunctor

end MathlibExt.DGSource
