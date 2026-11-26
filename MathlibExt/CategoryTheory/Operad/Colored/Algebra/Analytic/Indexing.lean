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

public import MathlibExt.CategoryTheory.Operad.Colored.Collection
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteTensor
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Data.Fintype.Option

/-!
# Analytic indexing for a fixed colored symmetric collection

For a fixed output color `d`, this file packages the KQ-independent indexing layer used by the
analytic algebra monad: fixed-output profiles reusing `ColoredProfile`, the finite input
family of a varying carrier family `A`, the combined family containing the operation object
`O(P)` and all carrier objects `A (P.inputColor i)`, and its finite-tensor analytic summand.
Carrier and collection maps induce natural transformations with identity, composition, and
mixed laws; summand maps are obtained by whiskering with the finite tensor.

Provenance (verified 2026-09-09): the summand is the profilewise
operation-tensor-carriers piece of the classical one-colored Schur/analytic-functor
archetype, before symmetric-group coinvariants: J. P. May, _The Geometry of Iterated
Loop Spaces_, opening sections "Operads and C-spaces" and "Operads and Monads"
(stable DOI https://doi.org/10.1007/BFb0067491; author PDF
https://www.math.uchicago.edu/~may/BOOKS/gils.pdf), and J.-L. Loday and B. Vallette,
_Algebraic Operads_, Chapter 5, §5.1 "S-module and Schur functor" (stable DOI
https://doi.org/10.1007/978-3-642-30362-3; author PDF
https://www.math.univ-paris13.fr/~vallette/Operads.pdf). Colored indexing via
`ColoredProfile` and O7B shapes is local. Local engineering
only: `FiniteFamily` packaging, the fixed-output `AnalyticIndex` fiber, and tensor
whiskering. The cited uncolored formula does not itself prove the colored
construction. O7G fixes one operad and indexes its algebras; O7E's free colored-operad
monad has operads as algebras instead.

Variance: morphisms are color-preserving input relabellings inside that fixed-output fiber
and everything is covariant under them; the input family, combined family, and summand are
separately covariant in pointwise carrier maps and in maps of the fixed colored symmetric
collection.

Nonclaims: no colimit, orbit quotient, analytic endofunctor, unit, multiplication, monad,
algebra, Eilenberg--Moore, bar-construction, Kan--Quillen, or homotopical claim is made.
No change-of-output-color or change-of-colors action is provided here.
Operad substitution and unit laws are unused at this indexing layer. The enriched
fixed-carrier algebra interface in `Algebra/Basic.lean` is neither used nor modified.
No nested substitution bridge is constructed here; it belongs in a later one-file bridge.
-/

@[expose] public section

namespace CategoryTheory.Operad

open CategoryTheory

universe u v w

/-- Input profiles with a fixed output color `d`.

This is the fixed-output fiber (not a categorical slice) of `ColoredProfile` at the
definitionally fixed output `d`: an unordered finite input type with an
input-color function. -/
structure AnalyticIndex (Color : Type u) (d : Color) where
  /-- The finite type indexing the inputs. -/
  inputs : FintypeCat.{0}
  /-- The color of each input. -/
  inputColor : inputs → Color

namespace AnalyticIndex

variable {Color : Type u} {d : Color}

/-- The underlying colored profile with fixed output color. -/
def toColoredProfile (P : AnalyticIndex Color d) : ColoredProfile Color :=
  ⟨P.inputs, P.inputColor, d⟩

/-- A fixed-output profile with input type `Fin n`. -/
def ofFin {n : ℕ} (inputColor : Fin n → Color) : AnalyticIndex Color d :=
  ⟨FintypeCat.of (Fin n), inputColor⟩

/-- The nullary fixed-output profile. -/
def nullary : AnalyticIndex Color d :=
  ofFin Fin.elim0

/-- The unary fixed-output profile with the given input color. -/
def unary (c : Color) : AnalyticIndex Color d :=
  ⟨FintypeCat.of PUnit, fun _ => c⟩

@[simp]
theorem toColoredProfile_inputs (P : AnalyticIndex Color d) :
    P.toColoredProfile.inputs = P.inputs :=
  rfl

@[simp]
theorem toColoredProfile_inputColor (P : AnalyticIndex Color d) (i : P.inputs) :
    P.toColoredProfile.inputColor i = P.inputColor i :=
  rfl

@[simp]
theorem toColoredProfile_outputColor (P : AnalyticIndex Color d) :
    P.toColoredProfile.outputColor = d :=
  rfl

/-- A color-preserving input relabelling inside the fixed-output fiber,
reusing `ColoredProfile.Hom`. -/
abbrev Hom (P Q : AnalyticIndex Color d) : Type _ :=
  P.toColoredProfile ⟶ Q.toColoredProfile

/-- Fixed-output profiles form a groupoid inheriting the `ColoredProfile` groupoid. -/
instance instGroupoid : Groupoid (AnalyticIndex Color d) where
  Hom := Hom
  id P := 𝟙 P.toColoredProfile
  comp f g := f ≫ g
  inv f := Groupoid.inv f
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h
  inv_comp f := Groupoid.inv_comp f
  comp_inv f := Groupoid.comp_inv f

/-- The input equivalence of the identity morphism is the identity. -/
@[simp]
theorem id_inputEquiv (P : AnalyticIndex Color d) :
    (𝟙 P : P ⟶ P).inputEquiv = Equiv.refl _ :=
  rfl

/-- The input equivalence of a composite is the composite of input equivalences. -/
@[simp]
theorem comp_inputEquiv {P Q R : AnalyticIndex Color d} (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).inputEquiv = f.inputEquiv.trans g.inputEquiv :=
  rfl

/-- The input equivalence of the inverse is the symmetric equivalence. -/
@[simp]
theorem inv_inputEquiv {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    (Groupoid.inv f).inputEquiv = f.inputEquiv.symm :=
  rfl

end AnalyticIndex

/-- Inclusion of fixed-output profiles into all colored profiles. -/
def analyticToProfileFunctor (Color : Type u) (d : Color) :
    AnalyticIndex Color d ⥤ ColoredProfile Color where
  obj P := P.toColoredProfile
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The profile of a fixed-output index has the fixed output color. -/
@[simp]
theorem analyticToProfileFunctor_obj_outputColor (Color : Type u) (d : Color)
    (P : AnalyticIndex Color d) :
    ((analyticToProfileFunctor Color d).obj P).outputColor = d :=
  rfl

/-- The input equivalence is preserved by inclusion into colored profiles. -/
@[simp]
theorem analyticToProfileFunctor_map_inputEquiv (Color : Type u) (d : Color)
    {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    ((analyticToProfileFunctor Color d).map f).inputEquiv = f.inputEquiv :=
  rfl

/-- Inclusion of fixed-output profiles is full: every profile map lifts. -/
instance analyticToProfileFunctor_full (Color : Type u) (d : Color) :
    Functor.Full (analyticToProfileFunctor Color d) where
  map_surjective g := ⟨g, rfl⟩

/-- Inclusion of fixed-output profiles is faithful. -/
instance analyticToProfileFunctor_faithful (Color : Type u) (d : Color) :
    Functor.Faithful (analyticToProfileFunctor Color d) where
  map_injective h := h

variable {Color : Type u} {d : Color} {V : Type w} [Category.{v} V]

/-- Transport of a carrier component across a color equality commutes with the component. -/
private theorem eqToHom_congrArg_comm {A B : Color → V} (φ : ∀ c, A c ⟶ B c)
    {a b : Color} (h : a = b) :
    eqToHom (congrArg A h) ≫ φ b = φ a ≫ eqToHom (congrArg B h) := by
  cases h
  simp

/-- Transport across a composite color equality splits. -/
private theorem eqToHom_congrArg_trans (A : Color → V)
    {a b c : Color} (h1 : a = b) (h2 : b = c) :
    eqToHom (congrArg A (h1.trans h2)) =
      eqToHom (congrArg A h1) ≫ eqToHom (congrArg A h2) := by
  cases h1
  cases h2
  simp

/-- The finite input family of a varying carrier family `A` over a fixed-output profile.

Covariant in fixed-output profiles via relabelling with color transport. -/
def analyticInputFamily (A : Color → V) :
    AnalyticIndex Color d ⥤ FiniteFamily V where
  obj P := ⟨P.inputs, fun i => A (P.inputColor i)⟩
  map f :=
    { equiv := f.inputEquiv
      hom := fun i => eqToHom (congrArg A (f.inputColor_eq i)) }
  map_id P := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      rfl
    · intro i
      exact heq_of_eq rfl
  map_comp f g := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      rfl
    · intro i
      exact heq_of_eq
        (eqToHom_congrArg_trans A (f.inputColor_eq i)
          (g.inputColor_eq (f.inputEquiv i)))

/-- The carrier object at an input of the input family. -/
@[simp]
theorem analyticInputFamily_obj (A : Color → V) (P : AnalyticIndex Color d)
    (i : P.inputs) :
    ((analyticInputFamily (d := d) A).obj P).obj i = A (P.inputColor i) :=
  rfl

/-- The relabelling map of the input family is color transport. -/
@[simp]
theorem analyticInputFamily_map_hom (A : Color → V)
    {P Q : AnalyticIndex Color d} (f : P ⟶ Q) (i : P.inputs) :
    ((analyticInputFamily (d := d) A).map f).hom i =
      eqToHom (congrArg A (f.inputColor_eq i)) :=
  rfl

/-- The index equivalence of the input-family relabelling. -/
@[simp]
theorem analyticInputFamily_map_equiv (A : Color → V)
    {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    ((analyticInputFamily (d := d) A).map f).equiv = f.inputEquiv :=
  rfl

/-- The finite index type of the combined family: `none` for the operation slot. -/
def analyticFactorsIndex (P : AnalyticIndex Color d) : FintypeCat.{0} :=
  FintypeCat.of (Option P.inputs)

/-- The combined finite family containing the operation object and all carrier objects.

The index `none` carries the operation object `O(P)`; each index `some i` carries the carrier
object `A (P.inputColor i)`. Covariant in fixed-output profiles: the operation slot uses the
collection relabelling, the carrier slots use color transport. -/
def analyticFactors (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    AnalyticIndex Color d ⥤ FiniteFamily V where
  obj P :=
    { index := analyticFactorsIndex P
      obj := fun o => match o with
        | none => O.obj P.toColoredProfile
        | some i => A (P.inputColor i) }
  map f :=
    { equiv := Equiv.optionCongr f.inputEquiv
      hom := fun o => match o with
        | none => O.map ((analyticToProfileFunctor Color d).map f)
        | some i => eqToHom (congrArg A (f.inputColor_eq i)) }
  map_id P := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro o
      cases o <;> rfl
    · intro o
      cases o with
      | none =>
        have h0 : (analyticToProfileFunctor Color d).map (𝟙 P) = 𝟙 _ :=
          (analyticToProfileFunctor Color d).map_id P
        have h1 : O.map ((analyticToProfileFunctor Color d).map (𝟙 P)) = 𝟙 _ := by
          rw [h0, O.map_id]
        exact heq_of_eq h1
      | some i =>
        exact heq_of_eq rfl
  map_comp f g := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro o
      cases o <;> rfl
    · intro o
      cases o with
      | none =>
        have h0 : (analyticToProfileFunctor Color d).map (f ≫ g) =
            (analyticToProfileFunctor Color d).map f ≫
              (analyticToProfileFunctor Color d).map g :=
          (analyticToProfileFunctor Color d).map_comp f g
        have h1 : O.map ((analyticToProfileFunctor Color d).map (f ≫ g)) =
            O.map ((analyticToProfileFunctor Color d).map f) ≫
              O.map ((analyticToProfileFunctor Color d).map g) := by
          rw [h0, O.map_comp]
        exact heq_of_eq h1
      | some i =>
        exact heq_of_eq
          (eqToHom_congrArg_trans A (f.inputColor_eq i)
            (g.inputColor_eq (f.inputEquiv i)))

/-- The index of the operation object in `analyticFactors`. -/
def analyticFactorsOuterIndex (O : ColoredSymmetricCollection Color V) (A : Color → V)
    (P : AnalyticIndex Color d) : ((analyticFactors (d := d) O A).obj P).index :=
  none

/-- The index of a carrier object in `analyticFactors`. -/
def analyticFactorsInnerIndex (O : ColoredSymmetricCollection Color V) (A : Color → V)
    (P : AnalyticIndex Color d) (i : P.inputs) :
    ((analyticFactors (d := d) O A).obj P).index :=
  some i

/-- The operation slot of the combined family is evaluation of `O`. -/
@[simp]
theorem analyticFactors_obj_outer (O : ColoredSymmetricCollection Color V) (A : Color → V)
    (P : AnalyticIndex Color d) :
    ((analyticFactors (d := d) O A).obj P).obj
        (analyticFactorsOuterIndex O A P) =
      O.obj P.toColoredProfile :=
  rfl

/-- A carrier slot of the combined family is the carrier object at that input color. -/
@[simp]
theorem analyticFactors_obj_inner (O : ColoredSymmetricCollection Color V) (A : Color → V)
    (P : AnalyticIndex Color d) (i : P.inputs) :
    ((analyticFactors (d := d) O A).obj P).obj
        (analyticFactorsInnerIndex O A P i) = A (P.inputColor i) :=
  rfl

/-- The index equivalence of the combined-family relabelling. -/
@[simp]
theorem analyticFactors_map_equiv (O : ColoredSymmetricCollection Color V) (A : Color → V)
    {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    ((analyticFactors (d := d) O A).map f).equiv =
      Equiv.optionCongr f.inputEquiv :=
  rfl

/-- The operation component of the combined-family relabelling. -/
@[simp]
theorem analyticFactors_map_outer (O : ColoredSymmetricCollection Color V) (A : Color → V)
    {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    ((analyticFactors (d := d) O A).map f).hom
        (analyticFactorsOuterIndex O A P) =
      O.map ((analyticToProfileFunctor Color d).map f) :=
  rfl

/-- A carrier component of the combined-family relabelling is color transport. -/
@[simp]
theorem analyticFactors_map_inner (O : ColoredSymmetricCollection Color V) (A : Color → V)
    {P Q : AnalyticIndex Color d} (f : P ⟶ Q) (i : P.inputs) :
    ((analyticFactors (d := d) O A).map f).hom
        (analyticFactorsInnerIndex O A P i) =
      eqToHom (congrArg A (f.inputColor_eq i)) :=
  rfl

/-- Finite-tensor analytic summand at a fixed-output profile: the tensor of the combined family.

This is the profilewise summand of the analytic functor, before any colimit or quotient.
No endofunctor on carrier families is constructed here. -/
def analyticSummand [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V) (A : Color → V) :
    AnalyticIndex Color d ⥤ V :=
  analyticFactors O A ⋙ FiniteTensor.tensor

/-- The analytic summand is the tensor of the combined family. -/
@[simp]
theorem analyticSummand_obj [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V) (A : Color → V)
    (P : AnalyticIndex Color d) :
    (analyticSummand (d := d) O A).obj P =
      (FiniteTensor.tensor (V := V)).obj
        ((analyticFactors (d := d) O A).obj P) :=
  rfl

/-- The analytic-summand relabelling is the tensor of the combined-family relabelling. -/
@[simp]
theorem analyticSummand_map [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V) (A : Color → V)
    {P Q : AnalyticIndex Color d} (f : P ⟶ Q) :
    (analyticSummand (d := d) O A).map f =
      (FiniteTensor.tensor (V := V)).map
        ((analyticFactors (d := d) O A).map f) :=
  rfl

/-- Pointwise carrier maps induce a natural transformation of input families.

Covariant in carrier maps; the component at `P` reindexes by the identity with components
`φ (P.inputColor i)`. -/
def analyticInputCarrierMap {A B : Color → V} (φ : ∀ c, A c ⟶ B c) :
    analyticInputFamily (d := d) A ⟶ analyticInputFamily (d := d) B where
  app P :=
    { equiv := Equiv.refl _
      hom := fun i => φ (P.inputColor i) }
  naturality P Q f := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro i
      rfl
    · intro i
      exact heq_of_eq (eqToHom_congrArg_comm φ (f.inputColor_eq i))

/-- The identity carrier map induces the identity transformation of input families. -/
@[simp]
theorem analyticInputCarrierMap_id {A : Color → V} :
    analyticInputCarrierMap (d := d) (V := V) (A := A) (B := A)
        (fun _ => 𝟙 _) = 𝟙 _ := by
  ext P
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    exact heq_of_eq rfl

/-- Composition of carrier maps induces composition of input-family transformations. -/
@[simp]
theorem analyticInputCarrierMap_comp {A B C : Color → V}
    (φ : ∀ c, A c ⟶ B c) (ψ : ∀ c, B c ⟶ C c) :
    analyticInputCarrierMap (d := d) (fun c => φ c ≫ ψ c) =
      analyticInputCarrierMap φ ≫ analyticInputCarrierMap ψ := by
  ext P
  apply FiniteFamily.Hom_ext
  · rfl
  · intro i
    exact heq_of_eq rfl

/-- The index equivalence of an input-family carrier component is the identity. -/
@[simp]
theorem analyticInputCarrierMap_app_equiv {A B : Color → V}
    (φ : ∀ c, A c ⟶ B c) (P : AnalyticIndex Color d) :
    ((analyticInputCarrierMap (d := d) φ).app P).equiv = Equiv.refl _ :=
  rfl

/-- A component of an input-family carrier map. -/
@[simp]
theorem analyticInputCarrierMap_app_hom {A B : Color → V}
    (φ : ∀ c, A c ⟶ B c) (P : AnalyticIndex Color d) (i : P.inputs) :
    ((analyticInputCarrierMap (d := d) φ).app P).hom i = φ (P.inputColor i) :=
  rfl

/-- Pointwise carrier maps induce a natural transformation of combined families.

The operation slot uses the identity; each carrier slot uses the corresponding component of
`φ`. -/
def analyticFactorsCarrierMap (O : ColoredSymmetricCollection Color V)
    {A B : Color → V} (φ : ∀ c, A c ⟶ B c) :
    analyticFactors (d := d) O A ⟶ analyticFactors (d := d) O B where
  app P :=
    { equiv := Equiv.refl _
      hom := fun o => match o with
        | none => 𝟙 _
        | some i => φ (P.inputColor i) }
  naturality P Q f := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro o
      cases o <;> rfl
    · intro o
      cases o with
      | none =>
        have h : O.map ((analyticToProfileFunctor Color d).map f) ≫ 𝟙 _ =
            𝟙 _ ≫ O.map ((analyticToProfileFunctor Color d).map f) :=
          (Category.comp_id _).trans (Category.id_comp _).symm
        exact heq_of_eq h
      | some i =>
        exact heq_of_eq (eqToHom_congrArg_comm φ (f.inputColor_eq i))

/-- The identity carrier map induces the identity transformation of combined families. -/
@[simp]
theorem analyticFactorsCarrierMap_id (O : ColoredSymmetricCollection Color V)
    {A : Color → V} :
    analyticFactorsCarrierMap (d := d) O (A := A) (B := A) (fun _ => 𝟙 _) = 𝟙 _ := by
  ext P
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq rfl
    | some i =>
      exact heq_of_eq rfl

/-- Composition of carrier maps induces composition of combined-family transformations. -/
@[simp]
theorem analyticFactorsCarrierMap_comp (O : ColoredSymmetricCollection Color V)
    {A B C : Color → V} (φ : ∀ c, A c ⟶ B c) (ψ : ∀ c, B c ⟶ C c) :
    analyticFactorsCarrierMap (d := d) O (fun c => φ c ≫ ψ c) =
      analyticFactorsCarrierMap O φ ≫ analyticFactorsCarrierMap O ψ := by
  ext P
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq (Category.id_comp _).symm
    | some i =>
      exact heq_of_eq rfl

/-- The index equivalence of a combined-family carrier component is the identity. -/
@[simp]
theorem analyticFactorsCarrierMap_app_equiv (O : ColoredSymmetricCollection Color V)
    {A B : Color → V} (φ : ∀ c, A c ⟶ B c) (P : AnalyticIndex Color d) :
    ((analyticFactorsCarrierMap (d := d) O φ).app P).equiv = Equiv.refl _ :=
  rfl

/-- The operation component of a combined-family carrier map is the identity. -/
@[simp]
theorem analyticFactorsCarrierMap_app_outer (O : ColoredSymmetricCollection Color V)
    {A B : Color → V} (φ : ∀ c, A c ⟶ B c) (P : AnalyticIndex Color d) :
    ((analyticFactorsCarrierMap (d := d) O φ).app P).hom
        (analyticFactorsOuterIndex O A P) = 𝟙 _ :=
  rfl

/-- A carrier component of a combined-family carrier map. -/
@[simp]
theorem analyticFactorsCarrierMap_app_inner (O : ColoredSymmetricCollection Color V)
    {A B : Color → V} (φ : ∀ c, A c ⟶ B c) (P : AnalyticIndex Color d)
    (i : P.inputs) :
    ((analyticFactorsCarrierMap (d := d) O φ).app P).hom
        (analyticFactorsInnerIndex O A P i) = φ (P.inputColor i) :=
  rfl

/-- Pointwise carrier maps induce a natural transformation of analytic summands.

Defined by whiskering the combined-family carrier transformation with the finite tensor. -/
def analyticSummandCarrierMap [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V)
    {A B : Color → V} (φ : ∀ c, A c ⟶ B c) :
    analyticSummand (d := d) O A ⟶ analyticSummand (d := d) O B :=
  Functor.whiskerRight
    (analyticFactorsCarrierMap (d := d) O φ) (FiniteTensor.tensor (V := V))

/-- The summand carrier component is the tensor of the combined-family component. -/
@[simp]
theorem analyticSummandCarrierMap_app [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V)
    {A B : Color → V} (φ : ∀ c, A c ⟶ B c) (P : AnalyticIndex Color d) :
    (analyticSummandCarrierMap (d := d) O φ).app P =
      (FiniteTensor.tensor (V := V)).map
        ((analyticFactorsCarrierMap (d := d) O φ).app P) :=
  rfl

/-- The identity carrier map induces the identity transformation of analytic summands. -/
@[simp]
theorem analyticSummandCarrierMap_id [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V) {A : Color → V} :
    analyticSummandCarrierMap (d := d) O (A := A) (B := A) (fun _ => 𝟙 _) = 𝟙 _ := by
  unfold analyticSummandCarrierMap analyticSummand
  rw [analyticFactorsCarrierMap_id, Functor.whiskerRight_id']

/-- Composition of carrier maps induces composition of analytic-summand transformations. -/
@[simp]
theorem analyticSummandCarrierMap_comp [FiniteTensor V]
    (O : ColoredSymmetricCollection Color V)
    {A B C : Color → V} (φ : ∀ c, A c ⟶ B c) (ψ : ∀ c, B c ⟶ C c) :
    analyticSummandCarrierMap (d := d) O (fun c => φ c ≫ ψ c) =
      analyticSummandCarrierMap O φ ≫ analyticSummandCarrierMap O ψ := by
  unfold analyticSummandCarrierMap analyticSummand
  rw [analyticFactorsCarrierMap_comp, Functor.whiskerRight_comp]

/-- A map of collections induces a natural transformation of combined families.

The operation slot uses the collection map; each carrier slot uses the identity. -/
def analyticFactorsCollectionMap (A : Color → V)
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O') :
    analyticFactors (d := d) O A ⟶ analyticFactors (d := d) O' A where
  app P :=
    { equiv := Equiv.refl _
      hom := fun o => match o with
        | none => α.app P.toColoredProfile
        | some _ => 𝟙 _ }
  naturality P Q f := by
    apply FiniteFamily.Hom_ext
    · apply Equiv.ext
      intro o
      cases o <;> rfl
    · intro o
      cases o with
      | none =>
        exact heq_of_eq (α.naturality ((analyticToProfileFunctor Color d).map f))
      | some i =>
        exact heq_of_eq
          ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The index equivalence of a combined-family collection component is the identity. -/
@[simp]
theorem analyticFactorsCollectionMap_app_equiv (A : Color → V)
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (P : AnalyticIndex Color d) :
    ((analyticFactorsCollectionMap (d := d) A α).app P).equiv = Equiv.refl _ :=
  rfl

/-- The operation component of a combined-family collection map. -/
@[simp]
theorem analyticFactorsCollectionMap_app_outer (A : Color → V)
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (P : AnalyticIndex Color d) :
    ((analyticFactorsCollectionMap (d := d) A α).app P).hom
        (analyticFactorsOuterIndex O A P) = α.app P.toColoredProfile :=
  rfl

/-- A carrier component of a combined-family collection map is the identity. -/
@[simp]
theorem analyticFactorsCollectionMap_app_inner (A : Color → V)
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (P : AnalyticIndex Color d) (i : P.inputs) :
    ((analyticFactorsCollectionMap (d := d) A α).app P).hom
        (analyticFactorsInnerIndex O A P i) = 𝟙 _ :=
  rfl

/-- The identity collection map induces the identity transformation. -/
@[simp]
theorem analyticFactorsCollectionMap_id (A : Color → V)
    (O : ColoredSymmetricCollection Color V) :
    analyticFactorsCollectionMap (d := d) A (O := O) (O' := O) (𝟙 O) = 𝟙 _ := by
  ext P
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      exact heq_of_eq rfl
    | some i =>
      exact heq_of_eq rfl

/-- Composition of collection maps induces composition of combined-family transformations. -/
@[simp]
theorem analyticFactorsCollectionMap_comp (A : Color → V)
    {O O' O'' : ColoredSymmetricCollection Color V}
    (α : O ⟶ O') (β : O' ⟶ O'') :
    analyticFactorsCollectionMap (d := d) A (α ≫ β) =
      analyticFactorsCollectionMap A α ≫ analyticFactorsCollectionMap A β := by
  ext P
  apply FiniteFamily.Hom_ext
  · exact (Equiv.refl_trans _).symm
  · intro o
    cases o with
    | none =>
      exact heq_of_eq rfl
    | some i =>
      exact heq_of_eq (Category.id_comp _).symm

/-- Collection maps commute with carrier maps on combined families. -/
theorem analyticFactorsCollectionCarrier_mixed (A : Color → V)
    {B : Color → V}
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (φ : ∀ c, A c ⟶ B c) :
    analyticFactorsCollectionMap (d := d) A α ≫
        analyticFactorsCarrierMap (d := d) O' φ =
      analyticFactorsCarrierMap (d := d) O φ ≫
        analyticFactorsCollectionMap (d := d) B α := by
  ext P
  apply FiniteFamily.Hom_ext
  · rfl
  · intro o
    cases o with
    | none =>
      have h1 : α.app P.toColoredProfile ≫
          (𝟙 _ : O'.obj P.toColoredProfile ⟶ O'.obj P.toColoredProfile) =
          α.app P.toColoredProfile :=
        Category.comp_id _
      have h2 : (𝟙 _ : O.obj P.toColoredProfile ⟶ O.obj P.toColoredProfile) ≫
          α.app P.toColoredProfile = α.app P.toColoredProfile :=
        Category.id_comp _
      exact heq_of_eq (h1.trans h2.symm)
    | some i =>
      have h1 : (𝟙 _ : A (P.inputColor i) ⟶ A (P.inputColor i)) ≫
          φ (P.inputColor i) = φ (P.inputColor i) :=
        Category.id_comp _
      have h2 : φ (P.inputColor i) ≫
          (𝟙 _ : B (P.inputColor i) ⟶ B (P.inputColor i)) =
          φ (P.inputColor i) :=
        Category.comp_id _
      exact heq_of_eq (h1.trans h2.symm)

/-- A map of collections induces a natural transformation of analytic summands. -/
def analyticSummandCollectionMap [FiniteTensor V] (A : Color → V)
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O') :
    analyticSummand (d := d) O A ⟶ analyticSummand (d := d) O' A :=
  Functor.whiskerRight
    (analyticFactorsCollectionMap (d := d) A α) (FiniteTensor.tensor (V := V))

/-- The summand collection component is the tensor of the combined-family component. -/
@[simp]
theorem analyticSummandCollectionMap_app [FiniteTensor V] (A : Color → V)
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (P : AnalyticIndex Color d) :
    (analyticSummandCollectionMap (d := d) A α).app P =
      (FiniteTensor.tensor (V := V)).map
        ((analyticFactorsCollectionMap (d := d) A α).app P) :=
  rfl

/-- The identity collection map induces the identity transformation of analytic summands. -/
@[simp]
theorem analyticSummandCollectionMap_id [FiniteTensor V] (A : Color → V)
    (O : ColoredSymmetricCollection Color V) :
    analyticSummandCollectionMap (d := d) A (O := O) (O' := O) (𝟙 O) = 𝟙 _ := by
  unfold analyticSummandCollectionMap analyticSummand
  rw [analyticFactorsCollectionMap_id, Functor.whiskerRight_id']

/-- Composition of collection maps induces composition of analytic-summand transformations. -/
@[simp]
theorem analyticSummandCollectionMap_comp [FiniteTensor V] (A : Color → V)
    {O O' O'' : ColoredSymmetricCollection Color V}
    (α : O ⟶ O') (β : O' ⟶ O'') :
    analyticSummandCollectionMap (d := d) A (α ≫ β) =
      analyticSummandCollectionMap A α ≫ analyticSummandCollectionMap A β := by
  unfold analyticSummandCollectionMap analyticSummand
  rw [analyticFactorsCollectionMap_comp, Functor.whiskerRight_comp]

/-- Collection maps commute with carrier maps on analytic summands. -/
theorem analyticSummandCollectionCarrier_mixed [FiniteTensor V] (A : Color → V)
    {B : Color → V}
    {O O' : ColoredSymmetricCollection Color V} (α : O ⟶ O')
    (φ : ∀ c, A c ⟶ B c) :
    analyticSummandCollectionMap (d := d) A α ≫
        analyticSummandCarrierMap (d := d) O' φ =
      analyticSummandCarrierMap (d := d) O φ ≫
        analyticSummandCollectionMap (d := d) B α := by
  unfold analyticSummandCollectionMap analyticSummandCarrierMap analyticSummand
  rw [← Functor.whiskerRight_comp, ← Functor.whiskerRight_comp,
    analyticFactorsCollectionCarrier_mixed]

end CategoryTheory.Operad
