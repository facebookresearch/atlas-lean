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

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects


/-!
# Exact categories
Definitions and basic properties of exact structures on additive categories in the sense of Quillen,
following Weibel's `K-book` definitions.

Every admissible exact sequence is a kernel-cokernel pair: for `S : ShortComplex C` with
`IsAdmissibleExact S`, `S.f` is a kernel of `S.g` and `S.g` is a cokernel of `S.f`,
witnessed by `Nonempty (IsLimit (KernelFork.ofι S.f S.zero))` and
`Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero))` (existence, data-independent).

## Main definitions
* `CategoryTheory.ExactCategory`
* `CategoryTheory.ExactCategory.IsAdmissibleMono`
* `CategoryTheory.ExactCategory.IsAdmissibleEpi`

## Main results
* `CategoryTheory.ExactCategory.IsAdmissibleMono.mono`
* `CategoryTheory.ExactCategory.IsAdmissibleEpi.epi`
* `isAdmissibleMono_id` / `IsAdmissibleMono.id` — identities are admissible monos
* `isAdmissibleMono_of_isIso` / `of_isIso` — isomorphisms are admissible monos
* `IsAdmissibleMono.fromZero` — every `0 ⟶ X` is an admissible mono
* `instIsMultiplicativeAdmissibleMonos` / `instRespectsIsoAdmissibleMonos` — admissible monos
  are multiplicative and respect isos

## Implementation notes
* Mathlib encodes an additive category by `[Preadditive C]`, `[HasZeroObject C]`,
  and `[HasBinaryBiproducts C]`.
* An additive category may support more than one exact structure,
  encoded by `[ExactCategory C]` structure.
* `admissibleMono_pushout` and `admissibleEpi_pullback` assert the existence and admissibility.
* Admissible exact sequences are kernel-cokernel pairs in the sense of Quillen:
  existence of `S.f` as kernel of `S.g` and `S.g` as cokernel of `S.f`
  (`Nonempty (IsLimit ...)` / `Nonempty (IsColimit ...)`), data-independent.

## References
* [C. Weibel, *The K-book: Chapter II.7*][weibel-k-book]
* [D. Quillen, *Higher algebraic K-theory: I*][quillen-higher-algk-I]
-/

@[expose] public section

open CategoryTheory Limits Preadditive ZeroObject

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]
variable (C)

/-- For a predicate `P` on short complexes in an additive category `C`, this
property holds of `i : X ⟶ Y` if there exist `Z` and `p : Y ⟶ Z` such that
`i ≫ p = 0` and `P` holds of the short complex `X ⟶ Y ⟶ Z` with legs `i, p`.
For arbitrary `P`, this asserts neither monicity nor exactness. -/
def admissibleMonosOf (P : ShortComplex C → Prop) : MorphismProperty C :=
  fun _ Y i => ∃ (Z : C) (p : Y ⟶ Z) (w : i ≫ p = 0), P (ShortComplex.mk i p w)

/-- For a predicate `P` on short complexes in an additive category `C`, this
property holds of `p : Y ⟶ Z` if there exist `X` and `i : X ⟶ Y` such that
`i ≫ p = 0` and `P` holds of the short complex `X ⟶ Y ⟶ Z` with legs `i, p`.
For arbitrary `P`, this asserts neither epicity nor exactness. -/
def admissibleEpisOf (P : ShortComplex C → Prop) : MorphismProperty C :=
  fun Y _ p => ∃ (X : C) (i : X ⟶ Y) (w : i ≫ p = 0), P (ShortComplex.mk i p w)

/-- Exact structure on an additive category in the sense of Quillen -/
class ExactCategory (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] where
  /-- The class of admissible exact sequences -/
  IsAdmissibleExact : ShortComplex C → Prop
  /-- Admissible exact sequences are SES -/
  shortExact_of_isAdmissibleExact : ∀ ⦃S : ShortComplex C⦄, IsAdmissibleExact S → S.ShortExact
  /-- Every admissible exact sequence is a kernel: `S.f` is a kernel of `S.g` (existence). -/
  isLimit_kernelFork : ∀ ⦃S : ShortComplex C⦄, IsAdmissibleExact S →
    Nonempty (IsLimit (KernelFork.ofι S.f S.zero))
  /-- Every admissible exact sequence is a cokernel: `S.g` is a cokernel of `S.f` (existence). -/
  isColimit_cokernelCofork : ∀ ⦃S : ShortComplex C⦄, IsAdmissibleExact S →
    Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero))
  /-- Admissible exact sequences are closed under isomorphisms -/
  isAdmissibleExact_of_iso : ∀ ⦃S T : ShortComplex C⦄, (S ≅ T) → IsAdmissibleExact S →
    IsAdmissibleExact T
  /-- Split exact sequences are admissible -/
  isAdmissibleExact_split : ∀ (X Y : C),
    IsAdmissibleExact (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd (by simp))
  /-- Admissible monomorphisms are closed under composition -/
  admissibleMono_comp : (admissibleMonosOf C IsAdmissibleExact).IsStableUnderComposition
  /-- Admissible epimorphisms are closed under composition -/
  admissibleEpi_comp : (admissibleEpisOf C IsAdmissibleExact).IsStableUnderComposition
  /-- Admissible monomorphisms are closed under pushouts along any morphisms -/
  admissibleMono_pushout : ∀ (X Y : C) (i : X ⟶ Y), admissibleMonosOf C IsAdmissibleExact i →
    ∀ (X' : C) (f : X ⟶ X'), ∃ (P : C) (inl : X' ⟶ P) (inr : Y ⟶ P),
      IsPushout f i inl inr ∧ admissibleMonosOf C IsAdmissibleExact inl
  /-- Admissible epimorphisms are closed under pullbacks along any morphisms -/
  admissibleEpi_pullback : ∀ (Y Z : C) (p : Y ⟶ Z), admissibleEpisOf C IsAdmissibleExact p →
    ∀ (Z' : C) (g : Z' ⟶ Z), ∃ (P : C) (fst : P ⟶ Z') (snd : P ⟶ Y),
      IsPullback fst snd g p ∧ admissibleEpisOf C IsAdmissibleExact fst

namespace ExactCategory

variable {C} [ExactCategory C]

/-- In an additive category `C` with an exact structure, `i : X ⟶ Y` is an
admissible monomorphism if there exist `Z` and `p : Y ⟶ Z` such that
`i ≫ p = 0` and the short complex with legs `i, p` is admissible exact. -/
def IsAdmissibleMono {X Y : C} (i : X ⟶ Y) : Prop := admissibleMonosOf C IsAdmissibleExact i

/-- In an additive category `C` with an exact structure, `p : Y ⟶ Z` is an
admissible epimorphism if there exist `X` and `i : X ⟶ Y` such that
`i ≫ p = 0` and the short complex with legs `i, p` is admissible exact. -/
def IsAdmissibleEpi {Y Z : C} (p : Y ⟶ Z) : Prop := admissibleEpisOf C IsAdmissibleExact p

/-- The first map of an admissible exact short complex is an admissible mono. -/
lemma isAdmissibleMono_f {S : ShortComplex C} (hS : IsAdmissibleExact S) :
    IsAdmissibleMono S.f :=
  ⟨S.X₃, S.g, S.zero, hS⟩

/-- The second map of an admissible exact short complex is an admissible epi. -/
lemma isAdmissibleEpi_g {S : ShortComplex C} (hS : IsAdmissibleExact S) :
    IsAdmissibleEpi S.g :=
  ⟨S.X₁, S.f, S.zero, hS⟩

/-- Kernel universal property of an admissible exact sequence (chosen witness). -/
noncomputable def isLimit_kernelFork_of_isAdmissibleExact {S : ShortComplex C}
    (hS : IsAdmissibleExact S) : IsLimit (KernelFork.ofι S.f S.zero) :=
  (ExactCategory.isLimit_kernelFork hS).some

/-- Cokernel universal property of an admissible exact sequence (chosen witness). -/
noncomputable def isColimit_cokernelCofork_of_isAdmissibleExact {S : ShortComplex C}
    (hS : IsAdmissibleExact S) : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  (ExactCategory.isColimit_cokernelCofork hS).some

/-- In an additive category `C` with an exact structure, a short complex `S`
is admissible exact if `S.f` is an admissible monomorphism and `S.g` exhibits
a cokernel of `S.f`, i.e. `CokernelCofork.ofπ S.g S.zero` is a colimit cofork. -/
theorem isAdmissibleExact_of_isAdmissibleMono_isColimit {S : ShortComplex C}
    (hf : IsAdmissibleMono S.f)
    (hc : IsColimit (CokernelCofork.ofπ S.g S.zero)) :
    IsAdmissibleExact S := by
  obtain ⟨W, p, w, hS'⟩ := hf
  have hc' := isColimit_cokernelCofork_of_isAdmissibleExact hS'
  let e : W ≅ S.X₃ := hc'.coconePointUniqueUpToIso hc
  have h_e_hom : p ≫ e.hom = S.g := by
    have h := IsColimit.comp_coconePointUniqueUpToIso_hom hc' hc WalkingParallelPair.one
    simpa [Cofork.app_one_eq_π, CokernelCofork.π_ofπ] using h
  have h_iso : ShortComplex.mk S.f p w ≅ S :=
    ShortComplex.isoMk (Iso.refl S.X₁) (Iso.refl S.X₂) e (by simp) (by simpa using h_e_hom.symm)
  exact isAdmissibleExact_of_iso h_iso hS'

/-- In an additive category with an exact structure, a morphism `i` satisfying
`IsAdmissibleMono i` is a monomorphism (`Mono i`). -/
lemma IsAdmissibleMono.mono {X Y : C} {i : X ⟶ Y} (hi : IsAdmissibleMono i) : Mono i := by
  obtain ⟨Z, g, w, hS⟩ := hi
  exact (shortExact_of_isAdmissibleExact hS).mono_f

/-- In an additive category with an exact structure, a morphism `p` satisfying
`IsAdmissibleEpi p` is an epimorphism (`Epi p`). -/
lemma IsAdmissibleEpi.epi {Y Z : C} {p : Y ⟶ Z} (hp : IsAdmissibleEpi p) : Epi p := by
  obtain ⟨X, f, w, hS⟩ := hp
  exact (shortExact_of_isAdmissibleExact hS).epi_g

section AdmissibleMonoCalculus

private lemma isAdmissibleExact_id (X : C) :
    IsAdmissibleExact (ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : C)) (by simp)) := by
  let S_split : ShortComplex C :=
    ShortComplex.mk (biprod.inl : X ⟶ X ⊞ (0 : C)) (biprod.snd : X ⊞ (0 : C) ⟶ (0 : C)) (by simp)
  have h_split : IsAdmissibleExact S_split := isAdmissibleExact_split X (0 : C)
  have h_iso : ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : C)) (by simp) ≅ S_split :=
    ShortComplex.isoMk (Iso.refl X) (isoBiprodZero (isZero_zero C)) (Iso.refl (0 : C))
      (by dsimp [S_split]; simp) (by dsimp [S_split]; simp)
  exact isAdmissibleExact_of_iso h_iso.symm h_split

/-- In an additive category with an exact structure, the identity morphism
`𝟙 X` on any object `X` is an admissible monomorphism. -/
lemma isAdmissibleMono_id (X : C) : IsAdmissibleMono (𝟙 X) :=
  ⟨(0 : C), (0 : X ⟶ (0 : C)), by simp, isAdmissibleExact_id X⟩

/-- In an additive category with an exact structure, a morphism `f : X ⟶ Y`
with `[IsIso f]` is an admissible monomorphism. -/
lemma isAdmissibleMono_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsAdmissibleMono f := by
  have h_id : IsAdmissibleExact (ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : C)) (by simp)) :=
    isAdmissibleExact_id X
  let S_id : ShortComplex C := ShortComplex.mk (𝟙 X) (0 : X ⟶ (0 : C)) (by simp)
  let S_f : ShortComplex C := ShortComplex.mk f (0 : Y ⟶ (0 : C)) (by simp)
  have h_iso : S_id ≅ S_f :=
    ShortComplex.isoMk (Iso.refl X) (asIso f) (Iso.refl (0 : C))
      (by dsimp [S_id, S_f]) (by dsimp [S_id, S_f]; simp)
  have h_f : IsAdmissibleExact S_f := isAdmissibleExact_of_iso h_iso h_id
  exact ⟨(0 : C), (0 : Y ⟶ (0 : C)), by simp, h_f⟩

/-- Admissible monos are multiplicative: identities are admissible and admissible monos compose. -/
instance instIsMultiplicativeAdmissibleMonos :
    (admissibleMonosOf C IsAdmissibleExact).IsMultiplicative where
  id_mem X := isAdmissibleMono_id X
  comp_mem f g hf hg := admissibleMono_comp.comp_mem f g hf hg

/-- Admissible monos respect isomorphisms, via `respectsIso_of_isStableUnderComposition`. -/
instance instRespectsIsoAdmissibleMonos :
    (admissibleMonosOf C IsAdmissibleExact).RespectsIso := by
  have h : (admissibleMonosOf C IsAdmissibleExact).IsStableUnderComposition :=
    admissibleMono_comp
  exact MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f hf => isAdmissibleMono_of_isIso f)

namespace IsAdmissibleMono

/-- In an additive category with an exact structure, `𝟙 X` is an admissible
monomorphism for every object `X`. -/
lemma id (X : C) : IsAdmissibleMono (𝟙 X) := isAdmissibleMono_id X

/-- In an additive category with an exact structure, every morphism `f : X ⟶ Y`
with `[IsIso f]` is an admissible monomorphism. -/
lemma of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsAdmissibleMono f :=
  isAdmissibleMono_of_isIso f

/-- In an additive category with an exact structure, every morphism
from the zero object `0` to an object `X` is an admissible monomorphism. -/
lemma fromZero {X : C} (f : (0 : C) ⟶ X) : IsAdmissibleMono f := by
  have h_inl : IsAdmissibleMono (biprod.inl : (0 : C) ⟶ (0 : C) ⊞ X) :=
    ⟨X, biprod.snd, by simp, isAdmissibleExact_split (0 : C) X⟩
  let e : X ≅ (0 : C) ⊞ X := isoZeroBiprod (isZero_zero C)
  have h_snd : IsAdmissibleMono e.symm.hom :=
    isAdmissibleMono_of_isIso e.symm.hom
  have h_comp : IsAdmissibleMono (biprod.inl ≫ e.symm.hom : (0 : C) ⟶ X) :=
    admissibleMono_comp.comp_mem _ _ h_inl h_snd
  have h_eq : f = biprod.inl ≫ e.symm.hom := (isZero_zero C).eq_of_src _ _
  exact h_eq ▸ h_comp

end IsAdmissibleMono

end AdmissibleMonoCalculus

end ExactCategory
end CategoryTheory
