/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGeneratedFactorization
public import MathlibExt.CategoryTheory.MorphismProperty.FunctorCategory
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Original coefficient factories with fixed isomorphism endpoints

A framing degree construction operates in the category of coefficient functors `C ⥤ C`.
The parameter naturality is internal to that category. Its factorization factory therefore
need not itself be functorial on arbitrary arrows of `C ⥤ C`.

At a whole coefficient isomorphism, normalization keeps the actual source or target as
the middle object and uses the original coefficient arrow with an identity factor. At
every other coefficient arrow, the complete original factor record is unchanged. The
ordinary C factories extend pointwise, including their maps on all original parameter
morphisms. No extra limits, colimits, or model structure on `C ⥤ C` are required.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v v' u u'

open CategoryTheory MorphismProperty

namespace CategoryTheory.MorphismProperty.FactorizationData

variable {C : Type u} [Category.{v} C] {P Q : MorphismProperty C}

/-- Pointwise classes retain original identity maps without a diagram model structure. -/
instance functorCategory_containsIdentities (P : MorphismProperty C) [P.ContainsIdentities]
    (J : Type u') [Category.{v'} J] : (P.functorCategory J).ContainsIdentities where
  id_mem X j := P.id_mem (X.obj j)

section Source

variable [P.ContainsIdentities] [Q.ContainsIdentities] [Q.RespectsIso]

/-- At an original isomorphism, the factor record keeps its exact source as middle object. -/
def sourceIdentity {X Y : C} (f : X ⟶ Y) [IsIso f] : MapFactorizationData P Q f where
  Z := X
  i := 𝟙 X
  p := f
  hi := P.id_mem X
  hp := Q.of_isIso f

/-- Source normalization changes only actual whole-isomorphism coefficient arrows. -/
def normalizeSource (F : FactorizationData P Q) : FactorizationData P Q := fun f ↦ by
  classical
  exact if h : IsIso f then letI := h; sourceIdentity f else F f

/-- A whole-isomorphism coefficient retains the complete exact identity-at-source record. -/
theorem normalizeSource_of_isIso (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y)
    [IsIso f] : normalizeSource F f = sourceIdentity f := by
  classical
  simp only [normalizeSource, dite_eq_left (inferInstance : IsIso f)]

/-- Every other coefficient retains the entire original factor record. -/
theorem normalizeSource_of_not_isIso (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y)
    (h : ¬ IsIso f) : normalizeSource F f = F f := by
  classical
  simp only [normalizeSource, dite_eq_right h]

/-- The normalized whole-isomorphism coefficient has exactly its original source as middle. -/
theorem normalizeSource_Z (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    (normalizeSource F f).Z = X := by
  rw [normalizeSource_of_isIso]
  rfl

/-- The normalized source factor is the original identity, with its exact endpoint retained. -/
theorem normalizeSource_i_heq (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    HEq (normalizeSource F f).i (𝟙 X) := by
  rw [normalizeSource_of_isIso]
  rfl

/-- The normalized target factor is the original coefficient arrow. -/
theorem normalizeSource_p_heq (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    HEq (normalizeSource F f).p f := by
  rw [normalizeSource_of_isIso]
  rfl

/-- The same original source factor is an isomorphism at a whole coefficient isomorphism. -/
instance normalizeSource_i_isIso (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y)
    [IsIso f] : IsIso (normalizeSource F f).i := by
  rw [normalizeSource_of_isIso]
  change IsIso (𝟙 X)
  infer_instance

end Source

section Target

variable [P.ContainsIdentities] [P.RespectsIso] [Q.ContainsIdentities]

/-- At an original isomorphism, the factor record keeps its exact target as middle object. -/
def targetIdentity {X Y : C} (f : X ⟶ Y) [IsIso f] : MapFactorizationData P Q f where
  Z := Y
  i := f
  p := 𝟙 Y
  hi := P.of_isIso f
  hp := Q.id_mem Y

/-- Target normalization changes only actual whole-isomorphism coefficient arrows. -/
def normalizeTarget (F : FactorizationData P Q) : FactorizationData P Q := fun f ↦ by
  classical
  exact if h : IsIso f then letI := h; targetIdentity f else F f

/-- A whole-isomorphism coefficient retains the complete exact identity-at-target record. -/
theorem normalizeTarget_of_isIso (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y)
    [IsIso f] : normalizeTarget F f = targetIdentity f := by
  classical
  simp only [normalizeTarget, dite_eq_left (inferInstance : IsIso f)]

/-- Every other coefficient retains the entire original factor record. -/
theorem normalizeTarget_of_not_isIso (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y)
    (h : ¬ IsIso f) : normalizeTarget F f = F f := by
  classical
  simp only [normalizeTarget, dite_eq_right h]

/-- The normalized whole-isomorphism coefficient has exactly its original target as middle. -/
theorem normalizeTarget_Z (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    (normalizeTarget F f).Z = Y := by
  rw [normalizeTarget_of_isIso]
  rfl

/-- The normalized source factor is the original coefficient arrow. -/
theorem normalizeTarget_i_heq (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    HEq (normalizeTarget F f).i f := by
  rw [normalizeTarget_of_isIso]
  rfl

/-- The normalized target factor is the original identity, with its exact endpoint retained. -/
theorem normalizeTarget_p_heq (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    HEq (normalizeTarget F f).p (𝟙 Y) := by
  rw [normalizeTarget_of_isIso]
  rfl

/-- The same original target factor is an isomorphism at a whole coefficient isomorphism. -/
instance normalizeTarget_p_isIso (F : FactorizationData P Q) {X Y : C} (f : X ⟶ Y)
    [IsIso f] : IsIso (normalizeTarget F f).p := by
  rw [normalizeTarget_of_isIso]
  change IsIso (𝟙 Y)
  infer_instance

end Target

end CategoryTheory.MorphismProperty.FactorizationData

namespace HomotopicalAlgebra.FramingCoefficientFactory

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-- The original I factory on parameter functors, with an exact target at isomorphisms. -/
def cofibrant (F : FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    FactorizationData ((cofibrations C).functorCategory C)
      ((trivialFibrations C).functorCategory C) :=
  fun {_ _} f ↦ FactorizationData.normalizeTarget
    (fun {_ _} g ↦ (F.functorCategory C).factorizationData g) f

/-- The original J factory on parameter functors, with an exact source at isomorphisms. -/
def fibrant (F : FunctorialFactorizationData (trivialCofibrations C) (fibrations C)) :
    FactorizationData ((trivialCofibrations C).functorCategory C)
      ((fibrations C).functorCategory C) :=
  fun {_ _} f ↦ FactorizationData.normalizeSource
    (fun {_ _} g ↦ (F.functorCategory C).factorizationData g) f

/-- At every non-isomorphism coefficient, the complete original pointwise I record is retained. -/
theorem cofibrant_of_not_isIso
    (F : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    {X Y : C ⥤ C} (f : X ⟶ Y) (h : ¬ IsIso f) :
    cofibrant F f = (F.functorCategory C).factorizationData f :=
  FactorizationData.normalizeTarget_of_not_isIso _ f h

/-- At every non-isomorphism coefficient, the complete original pointwise J record is retained. -/
theorem fibrant_of_not_isIso
    (F : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X Y : C ⥤ C} (f : X ⟶ Y) (h : ¬ IsIso f) :
    fibrant F f = (F.functorCategory C).factorizationData f :=
  FactorizationData.normalizeSource_of_not_isIso _ f h

/-- The normalized I coefficient has an isomorphic original right factor at an isomorphism. -/
instance cofibrant_p_isIso
    (F : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    {X Y : C ⥤ C} (f : X ⟶ Y) [IsIso f] : IsIso (cofibrant F f).p :=
  FactorizationData.normalizeTarget_p_isIso _ f

/-- The normalized J coefficient has an isomorphic original left factor at an isomorphism. -/
instance fibrant_i_isIso
    (F : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X Y : C ⥤ C} (f : X ⟶ Y) [IsIso f] : IsIso (fibrant F f).i :=
  FactorizationData.normalizeSource_i_isIso _ f

/-- Each original parameter square uses the same original I factory middle map. -/
theorem cofibrant_map_heq
    (F : FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
    {X Y : C ⥤ C} (f : X ⟶ Y) (h : ¬ IsIso f) {U V : C} (g : U ⟶ V) :
    HEq ((cofibrant F f).Z.map g)
      (F.mapZ (Arrow.homMk (X.map g) (Y.map g) (f.naturality g))) := by
  rw [cofibrant_of_not_isIso F f h]
  rfl

/-- Each original parameter square uses the same original J factory middle map. -/
theorem fibrant_map_heq
    (F : FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    {X Y : C ⥤ C} (f : X ⟶ Y) (h : ¬ IsIso f) {U V : C} (g : U ⟶ V) :
    HEq ((fibrant F f).Z.map g)
      (F.mapZ (Arrow.homMk (X.map g) (Y.map g) (f.naturality g))) := by
  rw [fibrant_of_not_isIso F f h]
  rfl

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]

/-- The actual original I generation supplies the normalized framing coefficient factory. -/
abbrev generatedCofibrant (d : CofibrantGenerationData C κ) :
    FactorizationData ((cofibrations C).functorCategory C)
      ((trivialFibrations C).functorCategory C) :=
  fun {_ _} f ↦ cofibrant d.cofibrantFactorizationData f

/-- The actual original J generation supplies the normalized framing coefficient factory. -/
abbrev generatedFibrant (d : CofibrantGenerationData C κ) :
    FactorizationData ((trivialCofibrations C).functorCategory C)
      ((fibrations C).functorCategory C) :=
  fun {_ _} f ↦ fibrant d.fibrantFactorizationData f

end HomotopicalAlgebra.FramingCoefficientFactory
