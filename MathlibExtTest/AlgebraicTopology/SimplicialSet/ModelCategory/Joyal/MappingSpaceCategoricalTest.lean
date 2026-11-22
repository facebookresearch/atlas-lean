/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceCategorical
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWTwoOfThree

/-!
# Mapping-space full faithfulness of categorical equivalences: tests

These tests exercise the public API of
`MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.MappingSpaceCategorical`:
the `π₀`-level predicate `SSet.dwyerKanFullyFaithfulPiZero` and its
unconditional proof for categorical equivalences, in fully-faithful,
hom-equivalence, bijection and edge forms; the simplex formula for
the induced mapping-space map; two-out-of-six for
`SSet.KanComplex.W` (`SSet.KanComplex.W.left_of_comp_comp`, in
`KanComplexWTwoOfThree.lean`) and for
`SSet.dwyerKanFullyFaithful` (`of_comp_comp`), with the resulting
conditional Dwyer–Kan conclusion; and the Whitehead assembly
`SSet.dwyerKanFullyFaithful.of_kan_bijective_piMap`. Tested at an
arbitrary universe and at universe `0`, including identity maps and
nerves of category isomorphisms.

The full mapping-space statement
`SSet.KanComplex.W (SSet.mappingSpaceRight.map X a b f)` for a
categorical equivalence between quasicategories is not tested here:
it is blocked on the additional comparison obligation and
the additional comparison obligation in the main file header
(the additional comparison obligation and the additional comparison obligation are closed downstream
by `SSet.kanComplex_mappingSpaceRight` and
`SSet.mappingSpaceRight.piZeroEquiv`).
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal
namespace MappingSpaceCategoricalTest

section PiZeroLevel

variable {X Y : SSet.{u}} {f : X ⟶ Y}

example : SSet.dwyerKanFullyFaithfulPiZero f ↔
    ∀ x y : X _⦋0⦌, Function.Bijective
      ((SSet.mapHomotopyCategory f).map :
        (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) →
          (SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) x) ⟶
            SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) y))) :=
  Iff.rfl

example (hf : SSet.categoricalEquivalences f) :
    (SSet.mapHomotopyCategory f).FullyFaithful :=
  hf.fullyFaithful_mapHomotopyCategory

example (hf : SSet.categoricalEquivalences f) :
    SSet.dwyerKanFullyFaithfulPiZero f :=
  hf.dwyerKanFullyFaithfulPiZero

example (hf : SSet.categoricalEquivalences f) (x y : X _⦋0⦌) :
    (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) ≃
      (SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) x) ⟶
        SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) y)) :=
  hf.homEquiv_mapHomotopyCategory_mk x y

example (hf : SSet.categoricalEquivalences f) (x y : X _⦋0⦌) :
    Function.Bijective
      ((SSet.mapHomotopyCategory f).map :
        (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) →
          (SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) x) ⟶
            SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) y))) :=
  hf.dwyerKanFullyFaithfulPiZero x y

example : SSet.dwyerKanFullyFaithfulPiZero (𝟙 X) :=
  (SSet.categoricalEquivalences.of_isIso (𝟙 X))
    |>.dwyerKanFullyFaithfulPiZero

example {C D : Type u} [Category.{u} C] [Category.{u} D]
    (e : Cat.of C ≅ Cat.of D) :
    SSet.dwyerKanFullyFaithfulPiZero
      (CategoryTheory.nerveMap e.hom.toFunctor) :=
  (SSet.categoricalEquivalences.nerveMap_catIso_hom e)
    |>.dwyerKanFullyFaithfulPiZero

end PiZeroLevel

section EdgeForms

variable {X Y : SSet.{u}} {f : X ⟶ Y}

example [SSet.Quasicategory X] (hf : SSet.categoricalEquivalences f)
    {x y : X _⦋0⦌}
    (e' : SSet.Edge (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) :
    ∃ e : SSet.Edge x y, (e.map f).toHoHom = e'.toHoHom :=
  hf.dwyerKanFullyFaithfulPiZero.exists_edge_map_toHoHom_eq e'

example (hf : SSet.categoricalEquivalences f) {x y : X _⦋0⦌}
    {e₁ e₂ : SSet.Edge x y}
    (h : (e₁.map f).toHoHom = (e₂.map f).toHoHom) :
    e₁.toHoHom = e₂.toHoHom :=
  hf.dwyerKanFullyFaithfulPiZero.edge_map_toHoHom_injective h

example (hf : SSet.dwyerKanFullyFaithfulPiZero f) {x y : X _⦋0⦌}
    {e₁ e₂ : SSet.Edge x y}
    (h : (e₁.map f).toHoHom = (e₂.map f).toHoHom) :
    e₁.toHoHom = e₂.toHoHom :=
  hf.edge_map_toHoHom_injective h

end EdgeForms

section MappingSpaceSimplices

variable {X Y : SSet.{u}} {f : X ⟶ Y} (a b : (Δ[0] : SSet.{u}) ⟶ X)

example (n : ℕ) (σ : (SSet.mappingSpaceRight X a b).obj (op ⦋n⦌)) :
    ((SSet.mappingSpaceRight.simplexEquivSucc Y (a ≫ f) (b ≫ f) n)
        ((SSet.mappingSpaceRight.map X a b f).app (op ⦋n⦌) σ)).1 =
      ((SSet.mappingSpaceRight.simplexEquivSucc X a b n) σ).1 ≫ f :=
  SSet.mappingSpaceRight.simplexEquivSucc_map_app_val X a b f n σ

example (σ : (SSet.mappingSpaceRight X a b).obj (op ⦋0⦌)) :
    ((SSet.mappingSpaceRight.simplexEquivSucc Y (a ≫ f) (b ≫ f) 0)
        ((SSet.mappingSpaceRight.map X a b f).app (op ⦋0⦌) σ)).1 =
      ((SSet.mappingSpaceRight.simplexEquivSucc X a b 0) σ).1 ≫ f :=
  SSet.mappingSpaceRight.simplexEquivSucc_map_app_val X a b f 0 σ

example (x y : X _⦋0⦌) :
    SSet.mappingSpaceRight X (SSet.const x) (SSet.const y) ⟶
      SSet.mappingSpaceRight Y ((SSet.const x) ≫ f)
        ((SSet.const y) ≫ f) :=
  SSet.mappingSpaceRight.map X (SSet.const x) (SSet.const y) f

end MappingSpaceSimplices

section TwoOutOfSix

variable {A B C D X Y : SSet.{u}} {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D}
  {f : X ⟶ Y} {g : Y ⟶ X}

example (hab : SSet.KanComplex.W (a ≫ b))
    (hbc : SSet.KanComplex.W (b ≫ c)) :
    SSet.KanComplex.W a :=
  SSet.KanComplex.W.left_of_comp_comp hab hbc

example (hab : SSet.KanComplex.W (a ≫ b))
    (hbc : SSet.KanComplex.W (b ≫ c)) :
    SSet.KanComplex A ∧ SSet.KanComplex B :=
  ⟨(SSet.KanComplex.W.left_of_comp_comp hab hbc).kanComplex_source,
    (SSet.KanComplex.W.left_of_comp_comp hab hbc).kanComplex_target⟩

example [SSet.KanComplex A] :
    SSet.KanComplex.W (𝟙 A) :=
  SSet.KanComplex.W.left_of_comp_comp
    (a := 𝟙 A) (b := 𝟙 A) (c := 𝟙 A)
    (by simpa using (SSet.KanComplex.W.id (X := A)))
    (by simpa using (SSet.KanComplex.W.id (X := A)))

example (hfg : SSet.dwyerKanFullyFaithful (f ≫ g))
    (hgf : SSet.dwyerKanFullyFaithful (g ≫ f)) :
    SSet.dwyerKanFullyFaithful f :=
  SSet.dwyerKanFullyFaithful.of_comp_comp hfg hgf

example (hfg : SSet.dwyerKanFullyFaithful (f ≫ g))
    (hgf : SSet.dwyerKanFullyFaithful (g ≫ f)) :
    SSet.dwyerKanFullyFaithful g :=
  SSet.dwyerKanFullyFaithful.of_comp_comp hgf hfg

example (hfg : SSet.dwyerKanFullyFaithful (f ≫ g))
    (hgf : SSet.dwyerKanFullyFaithful (g ≫ f)) (x y : X _⦋0⦌) :
    SSet.realizationWeakEquivalences
      (SSet.mappingSpaceRight.map X (SSet.const x) (SSet.const y) f) :=
  (SSet.dwyerKanFullyFaithful.of_comp_comp hfg hgf).vertex x y

example (hf : SSet.categoricalEquivalences f)
    (hfg : SSet.dwyerKanFullyFaithful (f ≫ g))
    (hgf : SSet.dwyerKanFullyFaithful (g ≫ f)) :
    SSet.isDwyerKanEquivalence f :=
  hf.isDwyerKanEquivalence_of_comp_comp hfg hgf

example (hf : SSet.categoricalEquivalences f)
    (hfg : SSet.dwyerKanFullyFaithful (f ≫ g))
    (hgf : SSet.dwyerKanFullyFaithful (g ≫ f)) :
    SSet.dwyerKanEssentiallySurjective f ∧
      SSet.dwyerKanFullyFaithful f :=
  ⟨(hf.isDwyerKanEquivalence_of_comp_comp hfg hgf)
      |>.dwyerKanEssentiallySurjective,
    (hf.isDwyerKanEquivalence_of_comp_comp hfg hgf)
      |>.dwyerKanFullyFaithful⟩

end TwoOutOfSix

section WhiteheadAssembly

variable {X Y : SSet.{u}} {f : X ⟶ Y}

example (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (hFG : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      (SSet.mapFundamentalGroupoid
        (SSet.mappingSpaceRight.map X a b f)).IsEquivalence)
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (SSet.mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (SSet.KanComplex.π.map (SSet.mappingSpaceRight.map X a b f)
          rfl (n := n) (x := σ))) :
    SSet.dwyerKanFullyFaithful f :=
  SSet.dwyerKanFullyFaithful.of_kan_bijective_piMap hKanX hKanY hFG hπ

example (hKan : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      SSet.KanComplex (SSet.mappingSpaceRight X a b)) :
    SSet.dwyerKanFullyFaithful (𝟙 X) := by
  apply SSet.dwyerKanFullyFaithful.of_kan_bijective_piMap hKan
  · simpa using hKan
  · intro a b
    rw [SSet.mappingSpaceRight.map_id]
    exact (SSet.KanComplex.W.id
      (X := SSet.mappingSpaceRight X a b)).isEquivalence_mapFundamentalGroupoid
  · intro a b n σ
    rw [SSet.mappingSpaceRight.map_id]
    exact (SSet.KanComplex.W.id
      (X := SSet.mappingSpaceRight X a b)).bijective_piMap n σ

end WhiteheadAssembly

section UniverseZero

variable {X Y : SSet.{0}} [SSet.Quasicategory X] {f : X ⟶ Y} {g : Y ⟶ X}

example (hf : SSet.categoricalEquivalences.{0} f) :
    SSet.dwyerKanFullyFaithfulPiZero f :=
  hf.dwyerKanFullyFaithfulPiZero

example (hf : SSet.categoricalEquivalences.{0} f) (x y : X _⦋0⦌) :
    (SSet.HomotopyCategory.mk x ⟶ SSet.HomotopyCategory.mk y) ≃
      (SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) x) ⟶
        SSet.HomotopyCategory.mk (f.app (op ⦋0⦌) y)) :=
  hf.homEquiv_mapHomotopyCategory_mk x y

example (hf : SSet.categoricalEquivalences.{0} f)
    {x y : X _⦋0⦌}
    (e' : SSet.Edge (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) :
    ∃ e : SSet.Edge x y, (e.map f).toHoHom = e'.toHoHom :=
  hf.dwyerKanFullyFaithfulPiZero.exists_edge_map_toHoHom_eq e'

example (hf : SSet.categoricalEquivalences.{0} f)
    (hfg : SSet.dwyerKanFullyFaithful (f ≫ g))
    (hgf : SSet.dwyerKanFullyFaithful (g ≫ f)) :
    SSet.isDwyerKanEquivalence f :=
  hf.isDwyerKanEquivalence_of_comp_comp hfg hgf

end UniverseZero

end MappingSpaceCategoricalTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal

end
