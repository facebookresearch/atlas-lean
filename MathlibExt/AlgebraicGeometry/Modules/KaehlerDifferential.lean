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

`Definitions/Def_AlgebraicGeometry_KaehlerModule.lean`
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

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.RingTheory.Kaehler.Polynomial
public import MathlibExt.AlgebraicGeometry.Modules.ExteriorPower
public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.Cech

/-!
# The sheaf of relative Kähler differentials over an affine base

For a morphism of schemes `f : X ⟶ Spec A` to an affine base, `kaehlerPresheaf` is the presheaf
of relative differentials `U ↦ Ω[Γ(X, U)⁄A]`, pointwise the Kähler differentials of the section
rings over `A`, and `kaehler` is its sheafification. For a degree `d` chosen by the caller,
`topDifferentials d` is the `d`-th exterior power of `kaehler`; it is the top exterior power only
when `kaehler` is locally free of rank `d`, which nothing here assumes.

`topPresheaf d` is the sectionwise `d`-th exterior power of the presheaf `kaehlerPresheaf`, while
`topDifferentials d` sheafifies the exterior power of the sheaf `kaehler`. The comparison maps
`kaehlerToSectionsₗ` and `topToSectionsₗ`, built from the sheafification unit, send sections of
`kaehlerPresheaf` and of `topPresheaf d` to sections of `kaehler` and of `topDifferentials d`.

`MathlibExt.AlgebraicGeometry.AlgebraicDifferentialSheaves`,
`MathlibExt.AlgebraicGeometry.RelativeDifferentialForms` and
`MathlibExt.AlgebraicGeometry.PrimeFieldDeRham` construct sheaves of differential forms for
schemes in universe `0`; the declarations here are universe polymorphic.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- **The base ring on sections.** For `f : X ⟶ Spec A`, the morphism from the constant presheaf
of rings `A` to the structure presheaf of `X` whose component at `U` is
`A ≅ Γ(Spec A, ⊤) ⟶ Γ(X, U)`, the map `f.appLE ⊤ U`. -/
def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of A) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop (by simp)
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]

/-- **The presheaf of relative Kähler differentials.** For `f : X ⟶ Spec A`, the presheaf of
`𝒪_X`-modules whose sections over `U` are the Kähler differentials `Ω[Γ(X, U)⁄A]`, for the
`A`-algebra structure on `Γ(X, U)` given by `constToPresheaf`. -/
@[reducible] def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf

instance (U : X.Opens) :
    Module Γ(X, U) (f.kaehlerPresheaf.obj (op U) : Type u) :=
  inferInstanceAs (Module Γ(X, U)
    (CommRingCat.KaehlerDifferential (f.constToPresheaf.app (op U)) : Type u))

/-- **The sheaf of relative Kähler differentials.** For `f : X ⟶ Spec A`, the sheafification of
`kaehlerPresheaf`. -/
def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.kaehlerPresheaf

/-- **Exterior power of the relative Kähler sheaf in a chosen degree.** For `f : X ⟶ Spec A`, the
`d`-th exterior power `Scheme.Modules.det d f.kaehler` of `kaehler`. The degree `d` is chosen by
the caller, not inferred from a rank: this is the top exterior power of `kaehler` only when
`kaehler` is locally free of rank `d`. -/
def topDifferentials (d : ℕ) : X.Modules :=
  Scheme.Modules.det d f.kaehler

/-- **Sectionwise exterior power of the relative Kähler presheaf.** For `f : X ⟶ Spec A` and a
degree `d` chosen by the caller, the sectionwise `d`-th exterior power of the presheaf
`kaehlerPresheaf`. Its sheafification is not `topDifferentials d` by definition, since
`topDifferentials d` sheafifies the exterior power of the sheaf `kaehler`; `topToSectionsₗ` sends
its sections to sections of `topDifferentials d`. -/
abbrev topPresheaf (d : ℕ) : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj f.kaehlerPresheaf

@[simp] lemma kaehlerPresheaf_obj (U : (X.Opens)ᵒᵖ) :
    f.kaehlerPresheaf.obj U = CommRingCat.KaehlerDifferential (f.constToPresheaf.app U) := rfl

/-- **Differentials to sections of the Kähler sheaf, as a linear map.** For `f : X ⟶ Spec A`, the
`Γ(X, U)`-linear map from `Ω[Γ(X, U)⁄A]`, the sections of `kaehlerPresheaf` over `U`, to the
sections of `kaehler` over `U`: the component at `U` of the sheafification unit. -/
def kaehlerToSectionsₗ (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U)) →ₗ[Γ(X, U)] (Γ(f.kaehler, U) : Type u) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom

/-- **Differentials to sections of the Kähler sheaf.** For `f : X ⟶ Spec A`, the function
underlying the linear map `kaehlerToSectionsₗ`, the component at `U` of the sheafification
unit. -/
def kaehlerToSections (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U) : Type u) → (Γ(f.kaehler, U) : Type u) :=
  ⇑(f.kaehlerToSectionsₗ U)

/-- **Wedges of differentials to sections of `topDifferentials`, as a linear map.** For
`f : X ⟶ Spec A` and a degree `d` chosen by the caller, the `Γ(X, U)`-linear map sending
`ω₁ ∧ ⋯ ∧ ω_d` to the image of `kaehlerToSectionsₗ ω₁ ∧ ⋯ ∧ kaehlerToSectionsₗ ω_d` under the
component at `U` of the sheafification unit of the sectionwise exterior power of `kaehler`. -/
def topToSectionsₗ (d : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U)) : Type u) →ₗ[Γ(X, U)]
      (Γ(f.topDifferentials d, U) : Type u) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom ∘ₗ
    exteriorPower.map d (f.kaehlerToSectionsₗ U)

/-- **Wedges of differentials to sections of `topDifferentials`.** For `f : X ⟶ Spec A`, the
function underlying the linear map `topToSectionsₗ`. -/
def topToSections (d : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U)) : Type u) →
      (Γ(f.topDifferentials d, U) : Type u) :=
  ⇑(f.topToSectionsₗ d U)

theorem kaehlerToSections_add (U : X.Opens) (s t : f.kaehlerPresheaf.obj (op U)) :
    f.kaehlerToSections U (s + t) = f.kaehlerToSections U s + f.kaehlerToSections U t :=
  map_add (kaehlerToSectionsₗ f U) s t

/-- **Nontrivial global differentials of a polynomial ring.** For `Spec A[X] ⟶ Spec A` with `A`
nontrivial, the module of sections of the presheaf `kaehlerPresheaf` over the whole space, that
is `Ω[Γ(Spec A[X], ⊤)⁄A]` before sheafification, is nontrivial. The statement is about the
presheaf on the top open, not about the sheafified `kaehler`. -/
theorem kaehlerPresheaf_nontrivial_polynomial (A : Type u) [CommRing A] [Nontrivial A] :
    letI f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    Nontrivial (f.kaehlerPresheaf.obj (op ⊤)) := by
  set f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A))) with hf
  let Γ' : Type u := Γ(Spec (CommRingCat.of (Polynomial A)), ⊤)
  let algA : Algebra A Γ' := f.sectionsAlgebra ⊤
  let e : Γ' ≃+* Polynomial A :=
    (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).commRingCatIsoToRingEquiv
  let : Algebra Γ' (Polynomial A) := e.toRingHom.toAlgebra
  have hcomp : (algebraMap Γ' (Polynomial A)).comp (algebraMap A Γ') =
      algebraMap A (Polynomial A) := by
    refine RingHom.ext fun a => ?_
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).hom.hom
      ((f.appLE ⊤ ⊤ (by simp)).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) =
        algebraMap A (Polynomial A) a
    have h1 : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
      simp only [appLE, TopologicalSpace.Opens.map_top, homOfLE_refl, op_id,
        CategoryTheory.Functor.map_id, appTop]
      exact Category.comp_id _
    rw [h1]
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    rw [← hf] at h2
    have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    rw [h3]
    change algebraMap A (Polynomial A) (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom a) = _
    rw [Iso.inv_hom_id]; rfl
  have : IsScalarTower A Γ' (Polynomial A) := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hsurj : Function.Surjective (KaehlerDifferential.map A A Γ' (Polynomial A)) :=
    KaehlerDifferential.map_surjective_of_surjective A A (h := e.surjective)
  have : Nontrivial (Ω[Polynomial A⁄A]) :=
    (KaehlerDifferential.polynomialEquiv A).toEquiv.nontrivial
  exact hsurj.nontrivial

end AlgebraicGeometry.Scheme.Hom

end
