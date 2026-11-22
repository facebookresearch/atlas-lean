/-
Copyright (c) 2025 Julian Komaromy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
See NOTICE in the repository root for the original Mathlib attribution.
-/
module

-- BACKPORT: Extracted from PR #42435 head `e09070f786c9fc0a688e6239d71230b618b045ff`,
-- path `Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean`,
-- blob `df6a12d695696a4f38858636c66f28d856a71dd4`.
-- See `BACKPORTS.md` for adaptations and upgrade-removal steps.

public import Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated

/-!
# Two-truncated quasicategory compatibility backport for Lean 4.33

This file backports witness-level and functor-construction APIs introduced in
Mathlib PR #42435 which are absent from the pinned Mathlib `v4.33.0` (`db584cd`)
but required for the simplicial weak-equivalence and fundamental-groupoid constructions.

## Source

* PR: `leanprover-community/mathlib4#42435`
* PR head: `e09070f786c9fc0a688e6239d71230b618b045ff`
* Upstream file: `Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean`
* Blob: `df6a12d695696a4f38858636c66f28d856a71dd4`
* Pinned Mathlib: `v4.33.0` `db584cd6d46c92f209a44c0f1c829460d327499d` containing
  `Mathlib/AlgebraicTopology/Quasicategory/TwoTruncated.lean` with only Prop-level
  `HomotopicL`/`HomotopicR`, `comp_unique`, `comp`, `compStruct`, `HomotopyCategory₂`,
  `Setoid`, `CategoryStruct`/`Category`, `homMk` etc.

## Ported declarations

This module provides exactly the declarations absent from the pin and required
downstream, preserving namespaces, universes, attributes, theorem statements,
and proof semantics verbatim from the PR head where they elaborate on the pin:

* witness-level edge types:
  `SSet.Truncated.Edge.HomotopyL`, `SSet.Truncated.Edge.HomotopyR`
* witness-level homotopy witnesses:
  `SSet.Truncated.Edge.HomotopyL.refl`, `SSet.Truncated.Edge.HomotopyR.refl`,
  `SSet.Truncated.Edge.HomotopyL.symm`, `SSet.Truncated.Edge.HomotopyR.symm`,
  `SSet.Truncated.Edge.HomotopyL.trans`, `SSet.Truncated.Edge.HomotopyR.trans`
* witness-level edge associativity:
  `SSet.Truncated.Edge.assoc`, `SSet.Truncated.Edge.assoc'`
* homotopy conversions (left ↔ right):
  `SSet.Truncated.Edge.HomotopyL.homotopyR`,
  `SSet.Truncated.Edge.HomotopyR.homotopyL`
* composition uniqueness at witness level:
  `SSet.Truncated.Edge.CompStruct.unique`
* homotopy category functor construction:
  `SSet.Truncated.HomotopyCategory₂.descMap`,
  `SSet.Truncated.HomotopyCategory₂.descMap_homMk`,
  `SSet.Truncated.HomotopyCategory₂.desc`,
  `SSet.Truncated.HomotopyCategory₂.desc_map_homMk`,
  `SSet.Truncated.HomotopyCategory₂.functor_ext`
* homotopy category morphism equality:
  `SSet.Truncated.HomotopyCategory₂.homMk_eq_iff_homotopicL`,
  `SSet.Truncated.HomotopyCategory₂.homMk_eq_iff_homotopicR`

Existing pinned declarations are not duplicated:
`Quasicategory₂`, Prop-level `HomotopicL`/`HomotopicR`, `HomotopicL.refl`/`symm`/`trans`,
`homotopicL_iff_homotopicR`, `Edge.CompStruct.comp_unique`, `Edge.comp`,
`Edge.compStruct`, `HomotopyCategory₂` structure, `instSetoidEdge`, `Hom`,
`CategoryStruct` instance, `mk_surjective`, `homMk`, `homMk_surjective`,
`homMk_id`, `congr_homotopyCategory₂HomMk`, `homotopyCategory₂_fac`,
`ofHomotopyCategory₂Fac`, `nonempty_iff`, `Category` instance.

All proofs use only `Quasicategory₂.fill21`, `fill31`, `fill32`, `Edge.id`,
`Edge.compId`, `idComp`, `idCompId`, `compStruct`, `homotopyCategory₂_fac`,
`homMk_surjective`, `Quot.lift`, `Quotient.sound`, `Functor.ext`, etc., present on
the pin. Attributes `@[no_expose]`, `@[implicit_reducible]`, `@[simp]` are retained
exactly as in upstream.

## Adaptations for 4.33

* Imports the pinned `Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated` rather than
  re-importing `Basic`/`CompStructTruncated` directly; transitive imports supply
  `Edge`, `CompStruct`, `Quasicategory₂`.
* No signature changes. No additional `simp` or `aesop` premises beyond upstream.

## Removal rule

Delete this file `MathlibExt/AlgebraicTopology/Quasicategory/TwoTruncatedCompat.lean`
and switch any imports of it to `Mathlib.AlgebraicTopology.Quasicategory.TwoTruncated`
once the pinned Mathlib provides all declarations listed in Ported declarations above.
Do not retain local copies that would collide with upstream.
-/

@[expose] public section

open CategoryTheory SimplicialObject.Truncated

namespace SSet.Truncated
open Edge CompStruct

/-- The public proof that degree zero lies in the two-truncation. -/
theorem zero_le_two : 0 ≤ 2 := Nat.zero_le 2

variable {X : Truncated 2} {x₀ x₁ x₂ x₃ : X _⦋0,zero_le_two⦌₂}

/--
A left homotopy between two edges `f` and `g` is a `CompStruct f (id _) g`.
(See `HomotopicL` for the `Prop`-valued version.)
-/
abbrev Edge.HomotopyL (f g : Edge x₀ x₁) := CompStruct f (id x₁) g

/--
A right homotopy between two edges `f` and `g` is a `CompStruct (id _) f g`.
(See `HomotopicL` for the `Prop`-valued version.)
-/
abbrev Edge.HomotopyR (f g : Edge x₀ x₁) := CompStruct (id x₀) f g

/-- The left homotopy relation on the edges of a `2`-truncated simplicial set is reflexive. -/
abbrev Edge.HomotopyL.refl (f : Edge x₀ x₁) : HomotopyL f f := .compId _

/-- The right homotopy relation on the edges of a `2`-truncated simplicial set is reflexive. -/
abbrev Edge.HomotopyR.refl (f : Edge x₀ x₁) : HomotopyR f f := .idComp _

/-- The associativity of the composition in a `2`-truncated quasicategory. -/
@[no_expose]
noncomputable def Edge.assoc [Quasicategory₂ X]
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂) (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₁ e₁₃ e₀₃) :
    CompStruct e₀₂ e₂₃ e₀₃ :=
  (Quasicategory₂.fill31 h₀₂ h₁₃ h).some

/-- The associativity of the composition in a `2`-truncated quasicategory. -/
@[no_expose]
noncomputable def Edge.assoc' [Quasicategory₂ X]
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₂₃ : Edge x₂ x₃}
    {e₀₂ : Edge x₀ x₂} {e₁₃ : Edge x₁ x₃} {e₀₃ : Edge x₀ x₃}
    (h₀₂ : CompStruct e₀₁ e₁₂ e₀₂) (h₁₃ : CompStruct e₁₂ e₂₃ e₁₃)
    (h : CompStruct e₀₂ e₂₃ e₀₃) :
    CompStruct e₀₁ e₁₃ e₀₃ :=
  (Quasicategory₂.fill32 h₀₂ h₁₃ h).some

/-- In a `2`-truncated quasicategory, the left homotopy relation on edges
is symmetric. -/
@[no_expose]
noncomputable def Edge.HomotopyL.symm [Quasicategory₂ X]
    {f g : Edge x₀ x₁} (h : HomotopyL f g) : HomotopyL g f :=
  assoc h (idComp _) (compId _)

/-- In a `2`-truncated quasicategory, the right homotopy relation on edges
is symmetric. -/
@[no_expose]
noncomputable def Edge.HomotopyR.symm [Quasicategory₂ X]
    {f g : Edge x₀ x₁} (h : HomotopyR f g) : HomotopyR g f :=
  assoc' (compId _) h (idComp _)

/-- In a `2`-truncated quasicategory, the left homotopy relation on edges
is transitive. -/
@[no_expose]
noncomputable def Edge.HomotopyL.trans [Quasicategory₂ X]
    {f g h : Edge x₀ x₁} (h₁ : HomotopyL f g) (h₂ : HomotopyL g h) :
    HomotopyL f h :=
  assoc' h₁ (.idCompId _) h₂

/-- In a `2`-truncated quasicategory, the right homotopy relation on edges
is transitive. -/
@[no_expose]
noncomputable def Edge.HomotopyR.trans [Quasicategory₂ X]
    {f g h : Edge x₀ x₁} (h₁ : HomotopyR f g) (h₂ : HomotopyR g h) :
    HomotopyR f h :=
  assoc (.idCompId _) h₁ h₂

/-- In a `2`-truncated quasicategory, two left homotopic edges are
also right homotopic. -/
@[no_expose]
noncomputable def Edge.HomotopyL.homotopyR [Quasicategory₂ X]
    {f g : Edge x₀ x₁} (h : HomotopyL f g) :
    HomotopyR f g :=
  assoc' (.idComp f) (.compId f) h

/-- In a `2`-truncated quasicategory, two right homotopic edges are
also left homotopic. -/
@[no_expose]
noncomputable def Edge.HomotopyR.homotopyL [Quasicategory₂ X]
    {f g : Edge x₀ x₁} (h : HomotopyR f g) :
    HomotopyL f g :=
  assoc (.idComp _) (.compId _) h

section homotopy_category

variable [Quasicategory₂ X]

/--
Assume we have structures `CompStruct f g h` and `CompStruct f' g' h'`.
If `f` and `f'` are left homotopic, and `g` and `g'` are left homotopic,
then `h` and `h'` are left homotopic.
-/
@[no_expose]
noncomputable def Edge.CompStruct.unique
    {f f' : Edge x₀ x₁} {g g' : Edge x₁ x₂} {h h' : Edge x₀ x₂}
    (s : CompStruct f g h) (s' : CompStruct f' g' h')
    (hf : HomotopyL f f') (hg : HomotopyL g g') : HomotopyL h h' :=
  assoc s (compId g) (assoc (compId f) hg.homotopyR (assoc' hf (idComp g') s'))

namespace HomotopyCategory₂

variable {D : Type*} [Category D]

section

variable (obj : X _⦋0,zero_le_two⦌₂ → D)
  (map : ∀ {x y : X _⦋0,zero_le_two⦌₂}, Edge x y → (obj x ⟶ obj y))
  (map_id : ∀ (x : X _⦋0,zero_le_two⦌₂), map (.id x) = 𝟙 (obj x))
  (map_comp : ∀ {x₀ x₁ x₂ : X _⦋0,zero_le_two⦌₂}
    {e₀₁ : Edge x₀ x₁} {e₁₂ : Edge x₁ x₂} {e₀₂ : Edge x₀ x₂},
    Edge.CompStruct e₀₁ e₁₂ e₀₂ → map e₀₁ ≫ map e₁₂ = map e₀₂)

/-- Auxiliary definition for `SSet.Truncated.HomotopyCategory₂.desc`. -/
@[no_expose]
def descMap {x y : HomotopyCategory₂ X} (f : x ⟶ y) : obj x.pt ⟶ obj y.pt :=
  Quot.lift map (fun _ _ ⟨h⟩ ↦ by simpa [map_id] using map_comp h) f

@[simp]
lemma descMap_homMk {x y : X _⦋0,zero_le_two⦌₂} (e : Edge x y) :
    descMap obj map map_id map_comp (homMk e) = map e := by rfl

/-- Constructor for functors from `SSet.Truncated.HomotopyCategory₂`. -/
@[implicit_reducible]
def desc : HomotopyCategory₂ X ⥤ D where
  obj x := obj x.pt
  map := descMap obj map map_id map_comp
  map_id x := by exact map_id x.pt
  map_comp {x y z} f g := by
    obtain ⟨f, rfl⟩ := homMk_surjective f
    obtain ⟨g, rfl⟩ := homMk_surjective g
    simp [(compStruct f g).homotopyCategory₂_fac, ← map_comp (compStruct f g)]

@[simp]
lemma desc_map_homMk {x y : X _⦋0,zero_le_two⦌₂} (e : Edge x y) :
    (desc obj map map_id map_comp).map (homMk e) = map e := by rfl

end

lemma functor_ext {F G : HomotopyCategory₂ X ⥤ D}
    (h₁ : ∀ (x : X _⦋0,zero_le_two⦌₂), F.obj (mk x) = G.obj (mk x) := by cat_disch)
    (h₂ : ∀ {x y : X _⦋0,zero_le_two⦌₂} (e : Edge x y),
      F.map (homMk e) = eqToHom (h₁ x) ≫ G.map (homMk e) ≫ eqToHom (h₁ y).symm := by cat_disch) :
    F = G :=
  CategoryTheory.Functor.ext (fun x ↦ h₁ x.pt) (fun x y f ↦ by
    obtain ⟨e, rfl⟩ := homMk_surjective f
    exact h₂ e)

lemma homMk_eq_iff_homotopicL {f g : Edge x₀ x₁} :
    homMk f = homMk g ↔ HomotopicL f g :=
  ⟨Quotient.exact, fun h ↦ Quotient.sound h⟩

lemma homMk_eq_iff_homotopicR {f g : Edge x₀ x₁} :
    homMk f = homMk g ↔ HomotopicR f g := by
  rw [homMk_eq_iff_homotopicL, homotopicL_iff_homotopicR]

end HomotopyCategory₂

end homotopy_category

end SSet.Truncated
