/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.Algebra.Homology.TwistingHomComplex
public import MathlibExt.RingTheory.DifferentialGraded.TwistingCochain
public import MathlibExt.Algebra.Homology.TwistingMaurerCartanFunctoriality

/-!
# Functorial map between twisted Hom complexes

This file constructs the combined functorial map between two-sided twisted Hom
cochain complexes defined in `TwistingHomComplex`, with Maurer–Cartan
functoriality from `TwistingMaurerCartanFunctoriality`. It packages
the smallest combined functorial map between two-sided twisted Hom cochain
complexes: postcomposition by a monoid morphism and precomposition by a
comonoid morphism.

For `x : MaurerCartan C A`, `ψ : C' ⟶ C` with `[IsComonHom ψ]`, and
`φ : A ⟶ B` with `[IsMonHom φ]`, a degree-`n` cochain `f : Cochain C A n` is
sent by postcomposing with `φ` and then precomposing with `ψ`, targeting the
twisted complex for `x.map ψ φ`.

## Variance and orientation

Covariant in the algebra morphism `φ` by postcomposition with `add_zero`
transports, and contravariant in the coalgebra morphism `ψ` by precomposition
with `zero_add` transports, exactly as in `MaurerCartan.map`. The chain
orientation is unchanged: a forward cochain `C → A` in degree `n` maps to a
forward cochain `C' → B` in the same degree `n`; the differential compatibility
is with `twistedDifferential` landing in `n + 1` on both sides.

## Primary source

No external source beyond the pinned Mathlib `HomComplex` API and the imported
modules `TwistingHomComplex`, `TwistingCochain`, and
`TwistingMaurerCartanFunctoriality` is used;
no Loday–Vallette section match is claimed here.

## Declaration inventory

* `twistedHomComplexMapCochain`: degreewise cochain function.
* `twistedHomComplexMapCochain_twistedDifferential`: it commutes with
  `twistedDifferential`, from the pinned `HomComplex.δ_comp_ofHom`,
  `HomComplex.δ_ofHom_comp`, `conv_postcomp`, and `conv_precomp`.
* `twistedHomComplexMapHom`: each degree as an `AddMonoidHom`.
* `twistedHomComplexMap`: bundled cochain-complex morphism from
  `twistedHomComplex x.tau x.isMC` to the complex for `x.map ψ φ`.
* `twistedHomComplexMapCochain_id` and `twistedHomComplexMapCochain_comp`:
  degreewise identity and composition laws for the cochain map.
* `twistedHomComplexMap_id_f` and `twistedHomComplexMap_comp_f`:
  degree-component identity and composition laws for the bundled map.

## Nonclaims

Identity and composition laws `twistedHomComplexMapCochain_id`,
`twistedHomComplexMapCochain_comp`, `twistedHomComplexMap_id_f`, and
`twistedHomComplexMap_comp_f` are proved here; the dedicated public consumer
is `MathlibExtTest/Algebra/Homology/TwistingHomComplexMapTests.lean`.
No separate pre/post APIs, no roots, no totalization, no adjunction,
no Koszul, no operadic, and no homotopical claim is made here. Only the
combined map stated above is constructed.

## Import justification

`TwistingHomComplex` supplies `twistedDifferential`, `twistedDifferentialHom`,
and `twistedHomComplex` with the `add_comm 1 n` cast convention preserved
exactly. `TwistingCochain` supplies `conv` with the `conv_postcomp`/`conv_precomp`
compatibility lemmas. `TwistingMaurerCartanFunctoriality` supplies
`MaurerCartan.map` with its `map_tau` rule. No further MathlibExt import is
needed.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [MonObj A] [ComonObj C]

variable {B : CochainComplex (ModuleCat R) ℤ} [MonObj B]
variable {C' : CochainComplex (ModuleCat R) ℤ} [ComonObj C']

/-- Degreewise cochain function of the combined twisted Hom-complex map:
postcompose with a monoid morphism `φ` (via `add_zero`), then precompose with
a comonoid morphism `ψ` (via `zero_add`). Covariant in `φ`, contravariant in
`ψ`; the degree `n` and forward orientation are unchanged. -/
noncomputable def twistedHomComplexMapCochain {n : ℤ}
    (_x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ]
    (f : HomComplex.Cochain C A n) : HomComplex.Cochain C' B n :=
  (HomComplex.Cochain.ofHom ψ).comp
    (f.comp (HomComplex.Cochain.ofHom φ) (add_zero n)) (zero_add n)

/-- The degreewise map commutes with the two-sided twisting differential,
from the pinned differential pre/postcomposition rules and the imported
convolution pre/postcomposition laws. -/
theorem twistedHomComplexMapCochain_twistedDifferential {n : ℤ}
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ]
    (f : HomComplex.Cochain C A n) :
    twistedHomComplexMapCochain x ψ φ (twistedDifferential x.tau f) =
      twistedDifferential (x.map ψ φ).tau
        (twistedHomComplexMapCochain x ψ φ f) := by
  have hδ : ∀ (g : HomComplex.Cochain C A n),
      twistedHomComplexMapCochain x ψ φ (HomComplex.δ n (n + 1) g) =
        HomComplex.δ n (n + 1) (twistedHomComplexMapCochain x ψ φ g) := by
    intro g
    unfold twistedHomComplexMapCochain
    rw [← HomComplex.δ_comp_ofHom, ← HomComplex.δ_ofHom_comp]
  have hconv : ∀ {m k : ℤ} (a : HomComplex.Cochain C A m)
      (b : HomComplex.Cochain C A k),
      twistedHomComplexMapCochain x ψ φ (conv a b) =
        conv (twistedHomComplexMapCochain x ψ φ a)
          (twistedHomComplexMapCochain x ψ φ b) := by
    intro m k a b
    unfold twistedHomComplexMapCochain
    rw [conv_postcomp, conv_precomp]
  have hcast : ∀ {a b : ℤ} (hab : a = b) (y : HomComplex.Cochain C A a),
      twistedHomComplexMapCochain x ψ φ
          (cast (congrArg (HomComplex.Cochain C A) hab) y) =
        cast (congrArg (HomComplex.Cochain C' B) hab)
          (twistedHomComplexMapCochain x ψ φ y) := by
    intro a b hab y
    cases hab
    rfl
  have hadd : ∀ (a b : HomComplex.Cochain C A (n + 1)),
      twistedHomComplexMapCochain x ψ φ (a + b) =
        twistedHomComplexMapCochain x ψ φ a +
          twistedHomComplexMapCochain x ψ φ b := by
    intro a b
    unfold twistedHomComplexMapCochain
    rw [HomComplex.Cochain.add_comp, HomComplex.Cochain.comp_add]
  have hsub : ∀ (a b : HomComplex.Cochain C A (n + 1)),
      twistedHomComplexMapCochain x ψ φ (a - b) =
        twistedHomComplexMapCochain x ψ φ a -
          twistedHomComplexMapCochain x ψ φ b := by
    intro a b
    rw [sub_eq_add_neg, hadd, sub_eq_add_neg]
    congr 1
    unfold twistedHomComplexMapCochain
    rw [HomComplex.Cochain.neg_comp, HomComplex.Cochain.comp_neg]
  have hsmul : ∀ (k : ℤˣ) (y : HomComplex.Cochain C A (n + 1)),
      twistedHomComplexMapCochain x ψ φ (k • y) =
        k • twistedHomComplexMapCochain x ψ φ y := by
    intro k y
    unfold twistedHomComplexMapCochain
    rcases Int.units_eq_one_or k with rfl | rfl
    · simp only [one_smul]
    · simp only [Units.neg_smul, one_smul,
        HomComplex.Cochain.neg_comp, HomComplex.Cochain.comp_neg]
  have htau : twistedHomComplexMapCochain x ψ φ x.tau = (x.map ψ φ).tau :=
    rfl
  unfold twistedDifferential
  simp only [MaurerCartan.map_tau]
  rw [hsub, hadd, hδ, hcast (add_comm 1 n), hsmul, hconv, hconv, htau,
    MaurerCartan.map_tau]

/-- Each degree of the combined twisted Hom-complex map as an additive
homomorphism, from the pinned cochain additivity and zero laws. -/
noncomputable def twistedHomComplexMapHom {n : ℤ}
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ] :
    HomComplex.Cochain C A n →+ HomComplex.Cochain C' B n where
  toFun := twistedHomComplexMapCochain x ψ φ
  map_zero' := by
    unfold twistedHomComplexMapCochain
    simp only [HomComplex.Cochain.zero_comp, HomComplex.Cochain.comp_zero]
  map_add' := by
    intro f g
    unfold twistedHomComplexMapCochain
    simp only [HomComplex.Cochain.add_comp, HomComplex.Cochain.comp_add]

/-- The bundled combined map as a cochain-complex morphism from
`twistedHomComplex x.tau x.isMC` to the twisted complex for `x.map ψ φ`.
The commutativity is discharged by
`twistedHomComplexMapCochain_twistedDifferential`. -/
noncomputable def twistedHomComplexMap
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ : C' ⟶ C) [IsComonHom ψ] (φ : A ⟶ B) [IsMonHom φ] :
    twistedHomComplex x.tau x.isMC ⟶
      twistedHomComplex (x.map ψ φ).tau (x.map ψ φ).isMC where
  f n := AddCommGrpCat.ofHom (twistedHomComplexMapHom x ψ φ (n := n))
  comm' := by
    intro i j hij
    have h1 : i + 1 = j := by simpa [ComplexShape.up_Rel] using hij
    subst h1
    change (AddCommGrpCat.ofHom (twistedHomComplexMapHom (n := i) x ψ φ) ≫
        AddCommGrpCat.ofHom
          (twistedDifferentialHom (x.map ψ φ).tau i (i + 1))) =
      (AddCommGrpCat.ofHom (twistedDifferentialHom x.tau i (i + 1)) ≫
        AddCommGrpCat.ofHom (twistedHomComplexMapHom (n := i + 1) x ψ φ))
    ext g p q hpq z
    rw [← AddCommGrpCat.ofHom_comp, AddCommGrpCat.ofHom_apply,
      AddMonoidHom.comp_apply, ← AddCommGrpCat.ofHom_comp,
      AddCommGrpCat.ofHom_apply, AddMonoidHom.comp_apply]
    have e1 : (twistedDifferentialHom (x.map ψ φ).tau i (i + 1))
          ((twistedHomComplexMapHom (n := i) x ψ φ) g) =
        twistedDifferential (x.map ψ φ).tau
          (twistedHomComplexMapCochain x ψ φ g) := by
      simp [twistedDifferentialHom, twistedHomComplexMapHom]
    have e2 : (twistedHomComplexMapHom (n := i + 1) x ψ φ)
          ((twistedDifferentialHom x.tau i (i + 1)) g) =
        twistedHomComplexMapCochain x ψ φ (twistedDifferential x.tau g) := by
      simp [twistedDifferentialHom, twistedHomComplexMapHom]
    rw [e1, e2]
    have hC := twistedHomComplexMapCochain_twistedDifferential x ψ φ g
    have hW := congrArg
      (fun h : HomComplex.Cochain C' B (i + 1) =>
        ModuleCat.Hom.hom (h.v p q hpq) z) hC
    exact hW.symm

variable {B' : CochainComplex (ModuleCat R) ℤ} [MonObj B']
variable {C'' : CochainComplex (ModuleCat R) ℤ} [ComonObj C'']

/-- Identity law for the degreewise twisted Hom-complex map: mapping along both
identity morphisms is the identity, from the pinned cochain identity laws. -/
theorem twistedHomComplexMapCochain_id
    (x : MaurerCartan (R := R) (C := C) (A := A))
    {n : ℤ} (f : HomComplex.Cochain C A n) :
    twistedHomComplexMapCochain x (𝟙 C) (𝟙 A) f = f := by
  unfold twistedHomComplexMapCochain
  simp only [HomComplex.Cochain.comp_id, HomComplex.Cochain.id_comp]

/-- Composition law for the degreewise twisted Hom-complex map: coalgebra
morphisms compose contravariantly as `ψ₁ ≫ ψ₂` while algebra morphisms compose
covariantly as `φ₂ ≫ φ₁`, from `ofHom_comp` and the degree-zero cochain
associativity lemmas. -/
theorem twistedHomComplexMapCochain_comp
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ₂ : C' ⟶ C) [IsComonHom ψ₂] (φ₂ : A ⟶ B) [IsMonHom φ₂]
    (ψ₁ : C'' ⟶ C') [IsComonHom ψ₁] (φ₁ : B ⟶ B') [IsMonHom φ₁]
    {n : ℤ} (f : HomComplex.Cochain C A n) :
    twistedHomComplexMapCochain (x.map ψ₂ φ₂) ψ₁ φ₁
        (twistedHomComplexMapCochain x ψ₂ φ₂ f) =
      twistedHomComplexMapCochain x (ψ₁ ≫ ψ₂) (φ₂ ≫ φ₁) f := by
  unfold twistedHomComplexMapCochain
  simp only [HomComplex.Cochain.ofHom_comp,
    HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
    HomComplex.Cochain.comp_assoc_of_second_is_zero_cochain]

/-- Degree-component identity law for the bundled twisted Hom-complex map.
Stated at degree components because the source/target complexes differ
propositionally through `MaurerCartan.map_id`. -/
theorem twistedHomComplexMap_id_f
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (n : ℤ) (f : HomComplex.Cochain C A n) :
    ((twistedHomComplexMap x (𝟙 C) (𝟙 A)).f n) f = f := by
  change twistedHomComplexMapCochain x (𝟙 C) (𝟙 A) f = f
  exact twistedHomComplexMapCochain_id x f

/-- Degree-component composition law for the bundled twisted Hom-complex map.
Stated at degree components because the source/target complexes differ
propositionally through `MaurerCartan.map_comp`. -/
theorem twistedHomComplexMap_comp_f
    (x : MaurerCartan (R := R) (C := C) (A := A))
    (ψ₂ : C' ⟶ C) [IsComonHom ψ₂] (φ₂ : A ⟶ B) [IsMonHom φ₂]
    (ψ₁ : C'' ⟶ C') [IsComonHom ψ₁] (φ₁ : B ⟶ B') [IsMonHom φ₁]
    (n : ℤ) (f : HomComplex.Cochain C A n) :
    (((twistedHomComplexMap x ψ₂ φ₂) ≫
        (twistedHomComplexMap (x.map ψ₂ φ₂) ψ₁ φ₁)).f n) f =
      ((twistedHomComplexMap x (ψ₁ ≫ ψ₂) (φ₂ ≫ φ₁)).f n) f := by
  rw [HomologicalComplex.comp_f]
  change twistedHomComplexMapCochain (x.map ψ₂ φ₂) ψ₁ φ₁
        (twistedHomComplexMapCochain x ψ₂ φ₂ f) =
      twistedHomComplexMapCochain x (ψ₁ ≫ ψ₂) (φ₂ ≫ φ₁) f
  exact twistedHomComplexMapCochain_comp x ψ₂ φ₂ ψ₁ φ₁ f

end CochainComplex
