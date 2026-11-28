/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects


/- The exact-structure axioms retain kernel and cokernel universal properties as
Nonempty witnesses; the corresponding helper definitions choose these witnesses. -/

/-!
# Quillen exact structures

An additive category `C` has a zero object and binary biproducts. A Quillen
exact structure selects admissible kernel–cokernel short complexes, contains
split exact sequences, and is closed under isomorphisms. Its admissible
monomorphisms and epimorphisms are closed under composition; pushout of an
admissible mono and pullback of an admissible epi exist and remain admissible.

All admissibility statements refer to the chosen exact structure on `C`.
An additive category can have more than one such structure.

For an admissible exact sequence `X → Y → Z`, the first map is a kernel
of the second and the second is a cokernel of the first.

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

/-- For a preadditive category `C` and a predicate `P` on its short
complexes, this morphism property consists of the maps occurring as
the first leg of a short complex satisfying `P`. -/
def admissibleMonosOf (P : ShortComplex C → Prop) : MorphismProperty C :=
  fun _ Y i => ∃ (Z : C) (p : Y ⟶ Z) (w : i ≫ p = 0), P (ShortComplex.mk i p w)

/-- For a preadditive category `C` and a predicate `P` on its short
complexes, this morphism property consists of the maps occurring as
the second leg of a short complex satisfying `P`. -/
def admissibleEpisOf (P : ShortComplex C → Prop) : MorphismProperty C :=
  fun Y _ p => ∃ (X : C) (i : X ⟶ Y) (w : i ≫ p = 0), P (ShortComplex.mk i p w)

/-- A Quillen exact structure on a preadditive category `C` with a zero
object and binary biproducts specifies admissible kernel–cokernel
short complexes, including split pairs, with closure under isomorphism,
composition, and the admissible pushout and pullback axioms. -/
class ExactCategory (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] where
  /-- In an additive category `C` with a chosen Quillen exact structure, the
admissible-exact predicate selects short complexes `S : X → Y → Z`
whose two maps form an admissible kernel–cokernel pair. -/
  IsAdmissibleExact : ShortComplex C → Prop
  /-- In an additive category `C` with a chosen Quillen exact structure, every
admissible exact short complex `S` is short exact: its first map is
monic, its second map epic, and their composite is zero with exact
middle term. -/
  shortExact_of_isAdmissibleExact : ∀ ⦃S : ShortComplex C⦄, IsAdmissibleExact S → S.ShortExact
  /-- In an additive category `C` with a chosen Quillen exact structure, if `S` is
admissible exact, `S.f : S.X₁ → S.X₂` is a kernel of
`S.g : S.X₂ → S.X₃`. Every morphism killed by `S.g` factors uniquely through `S.f`. -/
  isLimit_kernelFork : ∀ ⦃S : ShortComplex C⦄, IsAdmissibleExact S →
    Nonempty (IsLimit (KernelFork.ofι S.f S.zero))
  /-- In an additive category `C` with a chosen Quillen exact structure, if `S` is
admissible exact, `S.g : S.X₂ → S.X₃` is a cokernel of
`S.f : S.X₁ → S.X₂`. Every morphism killing `S.f` factors uniquely through `S.g`. -/
  isColimit_cokernelCofork : ∀ ⦃S : ShortComplex C⦄, IsAdmissibleExact S →
    Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero))
  /-- In an additive category `C` with a chosen Quillen exact structure, an
isomorphism of short complexes `S ≅ T` carries admissible exactness
of `S` to admissible exactness of `T`. -/
  isAdmissibleExact_of_iso : ∀ ⦃S T : ShortComplex C⦄, (S ≅ T) → IsAdmissibleExact S →
    IsAdmissibleExact T
  /-- In an additive category `C` with a chosen Quillen exact structure, the split
sequence `X → X ⊞ Y → Y`, with maps `biprod.inl` and `biprod.snd`,
is admissible exact for every pair of objects `X`, `Y`. -/
  isAdmissibleExact_split : ∀ (X Y : C),
    IsAdmissibleExact (ShortComplex.mk (biprod.inl : X ⟶ X ⊞ Y) biprod.snd (by simp))
  /-- In an additive category `C` with a chosen Quillen exact structure, the
composite of two composable admissible monomorphisms is again
an admissible monomorphism. -/
  admissibleMono_comp : (admissibleMonosOf C IsAdmissibleExact).IsStableUnderComposition
  /-- In an additive category `C` with a chosen Quillen exact structure, the
composite of two composable admissible epimorphisms is again
an admissible epimorphism. -/
  admissibleEpi_comp : (admissibleEpisOf C IsAdmissibleExact).IsStableUnderComposition
  /-- In an additive category `C` with a chosen Quillen exact structure, every
admissible mono `i : X → Y` and arbitrary `f : X → X′` admit
a pushout `Y → P ← X′`; the resulting map `X′ → P` is admissible monic. -/
  admissibleMono_pushout : ∀ (X Y : C) (i : X ⟶ Y), admissibleMonosOf C IsAdmissibleExact i →
    ∀ (X' : C) (f : X ⟶ X'), ∃ (P : C) (inl : X' ⟶ P) (inr : Y ⟶ P),
      IsPushout f i inl inr ∧ admissibleMonosOf C IsAdmissibleExact inl
  /-- In an additive category `C` with a chosen Quillen exact structure, every
admissible epi `p : Y → Z` and arbitrary `g : Z′ → Z` admit
a pullback `Y ← P → Z′`; the resulting map `P → Z′` is admissible epic. -/
  admissibleEpi_pullback : ∀ (Y Z : C) (p : Y ⟶ Z), admissibleEpisOf C IsAdmissibleExact p →
    ∀ (Z' : C) (g : Z' ⟶ Z), ∃ (P : C) (fst : P ⟶ Z') (snd : P ⟶ Y),
      IsPullback fst snd g p ∧ admissibleEpisOf C IsAdmissibleExact fst

namespace ExactCategory

variable {C} [ExactCategory C]

/-- In an additive category `C` with a chosen Quillen exact structure, a map
`i : X → Y` is admissible monic when it is the first map of an
admissible exact short complex `X → Y → Z` for some `Z`. -/
def IsAdmissibleMono {X Y : C} (i : X ⟶ Y) : Prop := admissibleMonosOf C IsAdmissibleExact i

/-- In an additive category `C` with a chosen Quillen exact structure, a map
`p : Y → Z` is admissible epic when it is the second map of an
admissible exact short complex `X → Y → Z` for some `X`. -/
def IsAdmissibleEpi {Y Z : C} (p : Y ⟶ Z) : Prop := admissibleEpisOf C IsAdmissibleExact p

/-- In an additive category `C` with a chosen Quillen exact structure, the
first map `S.f` of an admissible exact short complex `S` is an
admissible monomorphism. -/
lemma isAdmissibleMono_f {S : ShortComplex C} (hS : IsAdmissibleExact S) :
    IsAdmissibleMono S.f :=
  ⟨S.X₃, S.g, S.zero, hS⟩

/-- In an additive category `C` with a chosen Quillen exact structure, the
second map `S.g` of an admissible exact short complex `S` is an
admissible epimorphism. -/
lemma isAdmissibleEpi_g {S : ShortComplex C} (hS : IsAdmissibleExact S) :
    IsAdmissibleEpi S.g :=
  ⟨S.X₁, S.f, S.zero, hS⟩

/-- In an additive category `C` with a chosen Quillen exact structure, an
admissible exact short complex `S` determines a kernel universal
property for `S.f` against `S.g`, with the given zero composite. -/
noncomputable def isLimit_kernelFork_of_isAdmissibleExact {S : ShortComplex C}
    (hS : IsAdmissibleExact S) : IsLimit (KernelFork.ofι S.f S.zero) :=
  (ExactCategory.isLimit_kernelFork hS).some

/-- In an additive category `C` with a chosen Quillen exact structure, an
admissible exact short complex `S` determines a cokernel universal
property for `S.g` against `S.f`, with the given zero composite. -/
noncomputable def isColimit_cokernelCofork_of_isAdmissibleExact {S : ShortComplex C}
    (hS : IsAdmissibleExact S) : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
  (ExactCategory.isColimit_cokernelCofork hS).some

/- Proof implementation note.
An admissible-mono first leg plus a cokernel colimit second leg imply admissible exactness.

For `S : ShortComplex C`, `hf : IsAdmissibleMono S.f` and
`hc : IsColimit (CokernelCofork.ofπ S.g S.zero)` suffice for `IsAdmissibleExact S`.
Unpacks `hf` to `W, p, w, hS'`, reuses the canonical cokernel comparison
`hc'.coconePointUniqueUpToIso hc`, derives the second-leg equation with
`IsColimit.comp_coconePointUniqueUpToIso_hom`, then transports with
`ShortComplex.isoMk` and `isAdmissibleExact_of_iso`.
-/

/-- In an additive category `C` with a chosen Quillen exact structure, let
`S : X → Y → Z` be a short complex. If `S.f` is admissible
monic and `S.g` is a cokernel of `S.f`, then `S` is admissible exact. -/
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

/-- In an additive category `C` with a chosen Quillen exact structure, every
admissible monomorphism `i : X → Y` is a monomorphism in the
underlying category `C`. -/
lemma IsAdmissibleMono.mono {X Y : C} {i : X ⟶ Y} (hi : IsAdmissibleMono i) : Mono i := by
  obtain ⟨Z, g, w, hS⟩ := hi
  exact (shortExact_of_isAdmissibleExact hS).mono_f

/-- In an additive category `C` with a chosen Quillen exact structure, every
admissible epimorphism `p : Y → Z` is an epimorphism in the
underlying category `C`. -/
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

/- Proof implementation note.
Identities are admissible monos via `X ⟶ X ⊞ 0` and `isAdmissibleExact_of_iso`.
-/

/-- In an additive category `C` with a chosen Quillen exact structure, the
identity of any object `X` is an admissible monomorphism, as
the first map of a split admissible sequence. -/
lemma isAdmissibleMono_id (X : C) : IsAdmissibleMono (𝟙 X) :=
  ⟨(0 : C), (0 : X ⟶ (0 : C)), by simp, isAdmissibleExact_id X⟩

/-- In an additive category `C` with a chosen Quillen exact structure, every
isomorphism `f : X → Y` is an admissible monomorphism; admissible
kernel maps are stable under isomorphism of arrows. -/
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

/-- In an additive category `C` with a chosen Quillen exact structure, the
admissible-monomorphism property is multiplicative: identities
and composites of admissible monomorphisms are admissible. -/
instance instIsMultiplicativeAdmissibleMonos :
    (admissibleMonosOf C IsAdmissibleExact).IsMultiplicative where
  id_mem X := isAdmissibleMono_id X
  comp_mem f g hf hg := admissibleMono_comp.comp_mem f g hf hg

/- Proof implementation note.
Admissible monos respect isomorphisms, via `respectsIso_of_isStableUnderComposition`.
-/

/-- In an additive category `C` with a chosen Quillen exact structure, the
admissible-monomorphism property is invariant under isomorphisms
of arrows, including changes of either endpoint by an isomorphism. -/
instance instRespectsIsoAdmissibleMonos :
    (admissibleMonosOf C IsAdmissibleExact).RespectsIso := by
  have h : (admissibleMonosOf C IsAdmissibleExact).IsStableUnderComposition :=
    admissibleMono_comp
  exact MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f hf => isAdmissibleMono_of_isIso f)

namespace IsAdmissibleMono

/- Proof implementation note.
Identity is an admissible mono (ergonomic alias).
-/

/-- In an additive category `C` with a chosen Quillen exact structure, the
identity `𝟙 X` of each object `X` is an admissible monomorphism
coming from its split kernel–cokernel sequence. -/
lemma id (X : C) : IsAdmissibleMono (𝟙 X) := isAdmissibleMono_id X

/- Proof implementation note.
Isomorphism is an admissible mono (ergonomic alias).
-/

/-- In an additive category `C` with a chosen Quillen exact structure, an
isomorphism `f : X → Y` is an admissible monomorphism, obtained
by transporting the identity kernel map. -/
lemma of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsAdmissibleMono f :=
  isAdmissibleMono_of_isIso f

/- Proof implementation note.
Every map `0 ⟶ X` is an admissible mono, via `0 ⟶ 0 ⊞ X` and the zero biproduct iso.
-/

/-- In an additive category `C` with a chosen Quillen exact structure, every
morphism `0 → X` from a zero object is an admissible monomorphism,
as in the split admissible sequence `0 → X → X`. -/
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
