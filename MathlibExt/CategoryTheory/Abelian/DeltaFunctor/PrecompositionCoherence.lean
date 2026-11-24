/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Authors: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.Precomposition
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaComparison

/-!
# Identity, composition and naturality of exact cohomological precomposition
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe uA vA uB vB uD vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

namespace CohomologicalDeltaFunctor

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/-- Change the exact input functor by its natural transformation. -/
def precomposeChangeHom (R R' : A ⥤ B) [R.Additive] [R'.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hR' : ∀ S : ShortComplex A, S.ShortExact → (S.map R').ShortExact)
    (τ : R ⟶ R') (T : CohomologicalDeltaFunctor B D) :
    precompose R hR T ⟶ precompose R' hR' T :=
  homMk A D (fun n => Functor.whiskerRight τ (T.T n)) (fun n S => by
    let f : (⟨S.obj.map R, hR S.obj S.property⟩ : ShortComplex.ShortExactSequences B) ⟶
        ⟨S.obj.map R', hR' S.obj S.property⟩ :=
      ObjectProperty.homMk (S.obj.mapNatTrans τ)
    exact ((T.connecting n).naturality f).symm)

@[simp] theorem precomposeChangeHom_app (R R' : A ⥤ B) [R.Additive] [R'.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hR' : ∀ S : ShortComplex A, S.ShortExact → (S.map R').ShortExact)
    (τ : R ⟶ R') (T : CohomologicalDeltaFunctor B D) (n : ℕ) :
    Hom.app (precomposeChangeHom R R' hR hR' τ T) n = Functor.whiskerRight τ (T.T n) := rfl

end CohomologicalDeltaFunctor
end CategoryTheory

end


section

universe uA vA uB vB uD vD
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Preadditive B]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

universe uC vC
variable {C : Type uC} [Category.{vC} C] [Preadditive C]

/-- Exactness of a composite uses the two exactness providers. -/
theorem precomposeCompShortExact (R : A ⥤ B) (R' : B ⥤ C) [R.Additive] [R'.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hR' : ∀ S : ShortComplex B, S.ShortExact → (S.map R').ShortExact)
    (S : ShortComplex A) (hS : S.ShortExact) : (S.map (R ⋙ R')).ShortExact :=
  hR' (S.map R) (hR S hS)

set_option backward.isDefEq.respectTransparency false in
-- V3 recorded implicit projection mismatches in the same short-complex object aliases.
/-- Associativity of the same exact precomposition, preserving all original connectors. -/
def precomposeCompIso (R : A ⥤ B) (R' : B ⥤ C) [R.Additive] [R'.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hR' : ∀ S : ShortComplex B, S.ShortExact → (S.map R').ShortExact)
    (T : CohomologicalDeltaFunctor C D) :
    precompose R hR (precompose R' hR' T) ≅
      precompose (R ⋙ R') (precomposeCompShortExact R R' hR hR') T :=
  isoOfComponents _ _ (fun n => (Functor.associator R R' (T.T n)).symm) (by
    intro n S
    let Z : ShortComplex.ShortExactSequences C :=
      ⟨(S.obj.map R).map R', hR' (S.obj.map R) (hR S.obj S.property)⟩
    change (T.connecting n).app Z ≫ 𝟙 _ = 𝟙 _ ≫ (T.connecting n).app Z
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

@[simp] theorem precomposeCompIso_hom_app
    (R : A ⥤ B) (R' : B ⥤ C) [R.Additive] [R'.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (hR' : ∀ S : ShortComplex B, S.ShortExact → (S.map R').ShortExact)
    (T : CohomologicalDeltaFunctor C D) (n : ℕ) :
    Hom.app (precomposeCompIso R R' hR hR' T).hom n =
      (Functor.associator R R' (T.T n)).inv := rfl

end CategoryTheory.CohomologicalDeltaFunctor

end


section

universe uA vA uD vD
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]

/-- The identity input preserves the same literal short exact sequence. -/
theorem precomposeIdentityShortExact (S : ShortComplex A) (hS : S.ShortExact) :
    (S.map (𝟭 A)).ShortExact := by
  change S.ShortExact
  exact hS

/-- Exact identity precomposition has the left-unitor components. -/
def precomposeIdentityIso (T : CohomologicalDeltaFunctor A D) :
    precompose (𝟭 A) precomposeIdentityShortExact T ≅ T :=
  isoOfComponents (precompose (𝟭 A) precomposeIdentityShortExact T) T
    (fun q => Functor.leftUnitor (T.T q)) (by
      intro q S
      change (T.connecting q).app S ≫ 𝟙 _ = 𝟙 _ ≫ (T.connecting q).app S
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

@[simp] theorem precomposeIdentityIso_hom_app (T : CohomologicalDeltaFunctor A D) (q : ℕ) :
    Hom.app (precomposeIdentityIso T).hom q = (Functor.leftUnitor (T.T q)).hom := rfl

@[simp] theorem precomposeIdentityIso_inv_app (T : CohomologicalDeltaFunctor A D) (q : ℕ) :
    Hom.app (precomposeIdentityIso T).inv q = (Functor.leftUnitor (T.T q)).inv := rfl

end CategoryTheory.CohomologicalDeltaFunctor

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
namespace CohomologicalDeltaFunctor
/-- Evaluate the existing exact-input precomposition functor on its map. -/
theorem delta_precompose_map_app {A B D : Type*} [Category A] [Preadditive A]
    [Category B] [Preadditive B] [Category D] [Preadditive D]
    (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    {S T : CohomologicalDeltaFunctor B D} (f : S ⟶ T) (q : ℕ) :
    Hom.app ((precomposeFunctor R hR).map f) q = Functor.whiskerLeft R (Hom.app f q) := rfl
end CohomologicalDeltaFunctor
end CategoryTheory

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.CohomologicalDeltaFunctor
variable {A B D : Type*} [Category A] [Preadditive A] [Category B] [Preadditive B]
variable [Category D] [Preadditive D]

/-- Generic equality elimination compares connecting components without rebuilding degree types. -/
theorem equal_system_connecting {S T : CohomologicalDeltaFunctor A D} (h : S = T)
    (q : ℕ) (Z : ShortComplex.ShortExactSequences A) :
    HEq ((S.connecting q).app Z) ((T.connecting q).app Z) := by
  cases h
  rfl
/-- Literal evaluation of original exact-input precomposition. -/
theorem original_precompose_connector (R : A ⥤ B) [R.Additive]
    (hR : ∀ S : ShortComplex A, S.ShortExact → (S.map R).ShortExact)
    (T : CohomologicalDeltaFunctor B D) (q : ℕ) (S : ShortComplex.ShortExactSequences A) :
    ((precompose R hR T).connecting q).app S =
      (T.connecting q).app ⟨S.obj.map R, hR S.obj S.property⟩ := rfl

end CategoryTheory.CohomologicalDeltaFunctor

end
