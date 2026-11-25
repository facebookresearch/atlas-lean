/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: Tsutomu Okano <toskua@meta.com>
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoReplacement
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Yoneda

/-!
# Quillen right functors and the original replacement counit in ordinary Ho

For a genuine self Quillen adjunction whose original model category has
fibrant objects everywhere, Brown's lemma allows its actual right functor
to descend to the original localization. Its object and represented-map
formulas retain the literal original right functor.

Mathlib's natural-transformation extension transports the existing
ordinary Ho Hom equivalence through every morphism of the localization.
An explicit weak cofibrant replacement then gives the same complete Hom
functions with the caller's original replacement map. The full counit
word is left-map of that same replacement at the right object, followed
by the actual adjunction counit. Its Ho adjunct after every target Ho map
is the descended right functor's complete map.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.QuillenOrdinaryHoFunctorTransport

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {L R : C ⥤ C} (adj : L ⊣ R) [Adjunction.IsQuillenAdjunction adj]
  (hF : ∀ X : C, IsFibrant X)

local notation "H" => (MorphismProperty.Q (weakEquivalences C))

include adj hF in
/-- Brown's actual right Quillen law inverts all original weak maps when all objects are fibrant. -/
theorem rightFunctor_inverts :
    (weakEquivalences C).IsInvertedBy (R ⋙ (H)) := by
  intro X Y f hf
  let _ : IsFibrant X := hF X
  let _ : IsFibrant Y := hF Y
  let _ : WeakEquivalence f := (weakEquivalence_iff f).mpr hf
  have hw : WeakEquivalence (R.map f) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) f
  exact Localization.inverts (H) (weakEquivalences C) (R.map f) hw.mem

/-- The literal original right functor descends through the canonical ordinary Ho localization. -/
def rightHoFunctor : ((weakEquivalences C).Localization) ⥤ ((weakEquivalences C).Localization) :=
  Localization.Construction.lift (R ⋙ (H)) (rightFunctor_inverts adj hF)

/-- The whole composite with the original localization is the unchanged right functor. -/
theorem rightHoFunctor_fac : (H) ⋙ rightHoFunctor adj hF = R ⋙ (H) :=
  Localization.Construction.fac (R ⋙ (H)) (rightFunctor_inverts adj hF)

/-- The descended right functor keeps the literal original object without a replacement. -/
theorem rightHoFunctor_obj (X : C) :
    (rightHoFunctor adj hF).obj ((H).obj X) = (H).obj (R.obj X) := rfl

/-- Every original represented map is the entire actual mapped right-functor arrow. -/
theorem rightHoFunctor_map {X Y : C} (f : X ⟶ Y) :
    (rightHoFunctor adj hF).map ((H).map f) = (H).map (R.map f) := by
  exact Functor.congr_hom (rightHoFunctor_fac adj hF) f

/-- The full Ho right-map function has the literal original right objects as its endpoints. -/
def rightHoMap {X Y : C} (g : (H).obj X ⟶ (H).obj Y) :
    (H).obj (R.obj X) ⟶ (H).obj (R.obj Y) := (rightHoFunctor adj hF).map g

/-- The entire original-object map is exactly the descended right functor map. -/
theorem rightHoMap_eq {X Y : C} (g : (H).obj X ⟶ (H).obj Y) :
    rightHoMap adj hF g = (rightHoFunctor adj hF).map g := rfl

/-- The existing complete ordinary Ho Hom equivalence uses the proved fibrancy of its target. -/
abbrev homEquiv (X : C) [IsCofibrant X] (Y : C) :
    ((H).obj (L.obj X) ⟶ (H).obj Y) ≃ ((H).obj X ⟶ (H).obj (R.obj Y)) := by
  let _ : IsFibrant Y := hF Y
  exact QuillenOrdinaryHoHom.homEquiv adj X Y

/-- The original complete Ho adjunct functions are natural on every actual target arrow. -/
def originalHomNatTrans (X : C) [IsCofibrant X] :
    (H) ⋙ coyoneda.obj (Opposite.op ((H).obj (L.obj X))) ⟶
      (H) ⋙ (rightHoFunctor adj hF ⋙ coyoneda.obj (Opposite.op ((H).obj X))) where
  app Y := TypeCat.ofHom (homEquiv adj hF X Y)
  naturality Y Y' f := by
    ext a
    change homEquiv adj hF X Y' (a ≫ (H).map f) =
      homEquiv adj hF X Y a ≫ (rightHoFunctor adj hF).map ((H).map f)
    rw [rightHoFunctor_map]
    let _ : IsFibrant Y := hF Y
    let _ : IsFibrant Y' := hF Y'
    exact QuillenOrdinaryHoHom.homEquiv_naturality_right adj X a f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every target map in ordinary Ho preserves the full original forward Hom function. -/
theorem homEquiv_targetHo (X : C) [IsCofibrant X] {Y Y' : C}
    (a : (H).obj (L.obj X) ⟶ (H).obj Y) (g : (H).obj Y ⟶ (H).obj Y') :
    homEquiv adj hF X Y' (a ≫ g) =
      homEquiv adj hF X Y a ≫ (rightHoFunctor adj hF).map g := by
  have h :=
    (Localization.Construction.natTransExtension
      (originalHomNatTrans adj hF X)).naturality_apply g a
  simp only [Localization.Construction.natTransExtension_app,
    Localization.Construction.NatTransExtension.app_eq] at h
  change homEquiv adj hF X Y' (a ≫ g) =
    homEquiv adj hF X Y a ≫ (rightHoFunctor adj hF).map g at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every target map in ordinary Ho also preserves the entire original inverse Hom function. -/
theorem homEquiv_symm_targetHo (X : C) [IsCofibrant X] {Y Y' : C}
    (a : (H).obj X ⟶ (H).obj (R.obj Y)) (g : (H).obj Y ⟶ (H).obj Y') :
    (homEquiv adj hF X Y').symm (a ≫ (rightHoFunctor adj hF).map g) =
      (homEquiv adj hF X Y).symm a ≫ g := by
  apply (homEquiv adj hF X Y').injective
  rw [Equiv.apply_symm_apply, homEquiv_targetHo, Equiv.apply_symm_apply]

section OriginalReplacement

variable (Q : C ⥤ C) (ε : Q ⟶ 𝟭 C)
  (hQ : ∀ X : C, IsCofibrant (Q.obj X))
  (hε : ∀ X : C, weakEquivalences C (ε.app X))

/-- The actual original replacement map determines its isomorphism in ordinary Ho. -/
def originalQHoIso (X : C) : (H).obj (Q.obj X) ≅ (H).obj X := by
  let _ : WeakEquivalence (ε.app X) := (weakEquivalence_iff _).mpr (hε X)
  exact QuillenOrdinaryHoReplacement.replacementHoIso (ε.app X)

/-- The original replacement Iso has the unchanged entire mapped ε as its forward function. -/
theorem originalQHoIso_hom (X : C) :
    (originalQHoIso Q ε hε X).hom = (H).map (ε.app X) := rfl

/-- The complete original replacement Hom equivalence retains the caller's same Q and ε. -/
def originalQHomEquiv (X Y : C) :
    ((H).obj (L.obj (Q.obj X)) ⟶ (H).obj Y) ≃
      ((H).obj X ⟶ (H).obj (R.obj Y)) := by
  let _ : IsCofibrant (Q.obj X) := hQ X
  let _ : IsFibrant Y := hF Y
  let _ : WeakEquivalence (ε.app X) := (weakEquivalence_iff _).mpr (hε X)
  exact QuillenOrdinaryHoReplacement.homEquiv adj (ε.app X) Y

/-- The whole forward function is the original inverse ε
followed by the complete old adjunct. -/
theorem originalQHomEquiv_apply (X Y : C)
    (f : (H).obj (L.obj (Q.obj X)) ⟶ (H).obj Y) :
    originalQHomEquiv adj hF Q ε hQ hε X Y f =
      (originalQHoIso Q ε hε X).inv ≫
        (letI : IsCofibrant (Q.obj X) := hQ X
         homEquiv adj hF (Q.obj X) Y f) := by
  let _ : IsCofibrant (Q.obj X) := hQ X
  let _ : IsFibrant Y := hF Y
  let _ : WeakEquivalence (ε.app X) := (weakEquivalence_iff _).mpr (hε X)
  let _ : IsIso ((H).map (ε.app X)) := Localization.inverts (H) (weakEquivalences C) _ (hε X)
  exact QuillenOrdinaryHoReplacement.homEquiv_apply adj (ε.app X) Y f

/-- The complete inverse function keeps the original mapped ε before the actual inverse adjunct. -/
theorem originalQHomEquiv_symm_apply (X Y : C)
    (f : (H).obj X ⟶ (H).obj (R.obj Y)) :
    (originalQHomEquiv adj hF Q ε hQ hε X Y).symm f =
      (letI : IsCofibrant (Q.obj X) := hQ X
       (homEquiv adj hF (Q.obj X) Y).symm ((H).map (ε.app X) ≫ f)) := by
  let _ : IsCofibrant (Q.obj X) := hQ X
  let _ : IsFibrant Y := hF Y
  let _ : WeakEquivalence (ε.app X) := (weakEquivalence_iff _).mpr (hε X)
  exact QuillenOrdinaryHoReplacement.homEquiv_symm_apply adj (ε.app X) Y f

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All ordinary Ho target maps retain the same original inverse ε and the full forward adjunct. -/
theorem originalQHomEquiv_targetHo (X : C) {Y Y' : C}
    (a : (H).obj (L.obj (Q.obj X)) ⟶ (H).obj Y) (g : (H).obj Y ⟶ (H).obj Y') :
    originalQHomEquiv adj hF Q ε hQ hε X Y' (a ≫ g) =
      originalQHomEquiv adj hF Q ε hQ hε X Y a ≫ (rightHoFunctor adj hF).map g := by
  let _ : IsCofibrant (Q.obj X) := hQ X
  rw [originalQHomEquiv_apply, originalQHomEquiv_apply, homEquiv_targetHo, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All ordinary Ho target maps also retain the same original inverse adjunct function. -/
theorem originalQHomEquiv_symm_targetHo (X : C) {Y Y' : C}
    (a : (H).obj X ⟶ (H).obj (R.obj Y)) (g : (H).obj Y ⟶ (H).obj Y') :
    (originalQHomEquiv adj hF Q ε hQ hε X Y').symm
        (a ≫ (rightHoFunctor adj hF).map g) =
      (originalQHomEquiv adj hF Q ε hQ hε X Y).symm a ≫ g := by
  apply (originalQHomEquiv adj hF Q ε hQ hε X Y').injective
  rw [Equiv.apply_symm_apply, originalQHomEquiv_targetHo, Equiv.apply_symm_apply]

/-- The counit word uses the same Q at the original right object
and the actual adjunction counit. -/
def originalQCounit (W : C) : L.obj (Q.obj (R.obj W)) ⟶ W :=
  L.map (ε.app (R.obj W)) ≫ adj.counit.app W

omit [ModelCategory C] [Adjunction.IsQuillenAdjunction adj] in
/-- The full original same-Q counit word is natural on every actual input map. -/
theorem originalQCounit_naturality {W E : C} (f : W ⟶ E) :
    L.map (Q.map (R.map f)) ≫ originalQCounit adj Q ε E =
      originalQCounit adj Q ε W ≫ f := by
  rw [originalQCounit, originalQCounit, ← Category.assoc, ← L.map_comp,
    ε.naturality, L.map_comp, Category.assoc]
  change L.map (ε.app (R.obj W)) ≫ (L.map (R.map f) ≫ adj.counit.app E) = _
  have hf := adj.counit.naturality f
  change L.map (R.map f) ≫ adj.counit.app E = adj.counit.app W ≫ f at hf
  rw [hf]
  exact (Category.assoc _ _ _).symm

/-- All original same-Q counit components form the whole natural transformation. -/
def originalQCounitNatTrans : R ⋙ Q ⋙ L ⟶ 𝟭 C where
  app W := originalQCounit adj Q ε W
  naturality _W _E f := originalQCounit_naturality adj Q ε f

omit [ModelCategory C] [Adjunction.IsQuillenAdjunction adj] in
/-- The raw original adjunct of the complete same-Q counit
is the unchanged ε at the right object. -/
theorem originalQCounit_adjunct (W : C) :
    adj.homEquiv (Q.obj (R.obj W)) W (originalQCounit adj Q ε W) = ε.app (R.obj W) := by
  rw [originalQCounit, adj.homEquiv_naturality_left, ← adj.homEquiv_symm_id W]
  simp only [Functor.id_obj, Equiv.apply_symm_apply, Category.comp_id]

/-- The full same-Q counit has the original identity
as its entire transported ordinary Ho adjunct. -/
theorem originalQCounit_Ho_adjunct (W : C) :
    originalQHomEquiv adj hF Q ε hQ hε (R.obj W) W
        ((H).map (originalQCounit adj Q ε W)) = 𝟙 ((H).obj (R.obj W)) := by
  let _ : IsCofibrant (Q.obj (R.obj W)) := hQ (R.obj W)
  let _ : IsFibrant W := hF W
  let _ : WeakEquivalence (ε.app (R.obj W)) := (weakEquivalence_iff _).mpr (hε _)
  let _ : IsIso ((H).map (ε.app (R.obj W))) :=
    Localization.inverts (H) (weakEquivalences C) _ (hε _)
  rw [originalQHomEquiv_apply]
  change (originalQHoIso Q ε hε (R.obj W)).inv ≫
      QuillenOrdinaryHoHom.homEquiv adj (Q.obj (R.obj W)) W
        ((H).map (originalQCounit adj Q ε W)) = _
  rw [QuillenOrdinaryHoHom.homEquiv_map, originalQCounit_adjunct]
  exact (originalQHoIso Q ε hε (R.obj W)).inv_hom_id

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- After every original ordinary Ho target map, the full same-Q counit adjunct is the right map. -/
theorem originalQCounit_Ho_adjunct_comp (W E : C) (g : (H).obj W ⟶ (H).obj E) :
    originalQHomEquiv adj hF Q ε hQ hε (R.obj W) E
        ((H).map (originalQCounit adj Q ε W) ≫ g) = (rightHoFunctor adj hF).map g := by
  rw [originalQHomEquiv_targetHo, originalQCounit_Ho_adjunct, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The complete inverse function recovers the same original counit followed by that Ho map. -/
theorem originalQCounit_Ho_inverse (W E : C) (g : (H).obj W ⟶ (H).obj E) :
    (originalQHomEquiv adj hF Q ε hQ hε (R.obj W) E).symm
        ((rightHoFunctor adj hF).map g) = (H).map (originalQCounit adj Q ε W) ≫ g := by
  apply (originalQHomEquiv adj hF Q ε hQ hε (R.obj W) E).injective
  rw [Equiv.apply_symm_apply, originalQCounit_Ho_adjunct_comp]

end OriginalReplacement

end HomotopicalAlgebra.QuillenOrdinaryHoFunctorTransport
