/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.DwyerKan
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexWTwoOfThree
public import Mathlib.CategoryTheory.Whiskering

/-!
# Homotopy-category full faithfulness and right mapping-space comparisons

For f:X→Y of simplicial sets in universe u, categorical equivalence means that precomposition
gives an equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. Such a map
induces bijections ho(X)([x],[y])→ho(Y)([f(x)],[f(y)]) for every pair of vertices. For a
quasicategory source, target edges between image vertices have image-edge representatives with
the same homotopy-category morphism.

For vertex maps a,b:Δ[0]→X, write r_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) for the induced map of right
mapping spaces. Two reverse composites f≫g and g≫f fully faithful on these mapping spaces imply
full faithfulness of f. A separate criterion obtains full faithfulness from Kan right mapping
spaces, equivalences of their fundamental groupoids, and bijectivity on all based homotopy
groups.

Reference: D. Stevenson, Notes on the Joyal model structure, arXiv:1810.05233, for the
mapping-space framework.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed Limits Opposite

open scoped Simplicial

universe u

namespace SSet

variable {X Y Z : SSet.{u}} {f : X ⟶ Y}

/-!
## Homotopy-category morphism sets

For arbitrary simplicial X,Y, the homotopy-category condition is bijectivity of ho(f) on all
hom-sets between vertex objects. Categorical equivalence supplies this condition and the
corresponding hom-set equivalences.
-/

/-- For f:X→Y in universe u, define the homotopy-category full-faithfulness condition by requiring
ho(f):ho(X)([x],[y])→ho(Y)([f(x)],[f(y)]) to be bijective for every x,y∈X₀. This condition is
stated using homotopy-category morphisms. -/
def dwyerKanFullyFaithfulPiZero (f : X ⟶ Y) : Prop :=
  ∀ x y : X _⦋0⦌, Function.Bijective
    ((mapHomotopyCategory f).map :
      (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) →
        (HomotopyCategory.mk (f.app (op ⦋0⦌) x) ⟶
          HomotopyCategory.mk (f.app (op ⦋0⦌) y)))

/-- For f:X→Y of simplicial sets in universe u, categorical equivalence means that precomposition
gives an equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. The induced
functor ho(f):ho(X)→ho(Y) has a full-and-faithful structure, giving bijections on every hom-set. -/
noncomputable def categoricalEquivalences.fullyFaithful_mapHomotopyCategory
    (hf : categoricalEquivalences f) :
    (mapHomotopyCategory f).FullyFaithful := by
  have : (mapHomotopyCategory f).IsEquivalence :=
    hf.isEquivalence_mapHomotopyCategory
  exact Functor.FullyFaithful.ofFullyFaithful _

/-- For f:X→Y of simplicial sets in universe u, categorical equivalence means that precomposition
gives an equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. For x,y∈X₀,
ho(f) gives an equivalence ho(X)([x],[y])≃ho(Y)([f(x)],[f(y)]). Its forward map is the functor's
action on morphisms. -/
noncomputable def categoricalEquivalences.homEquiv_mapHomotopyCategory_mk
    (hf : categoricalEquivalences f) (x y : X _⦋0⦌) :
    (HomotopyCategory.mk x ⟶ HomotopyCategory.mk y) ≃
      (HomotopyCategory.mk (f.app (op ⦋0⦌) x) ⟶
        HomotopyCategory.mk (f.app (op ⦋0⦌) y)) :=
  hf.fullyFaithful_mapHomotopyCategory.homEquiv

/-- For f:X→Y of simplicial sets in universe u, categorical equivalence means that precomposition
gives an equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. For all x,y∈X₀,
the map ho(X)([x],[y])→ho(Y)([f(x)],[f(y)]) is bijective. -/
theorem categoricalEquivalences.dwyerKanFullyFaithfulPiZero
    (hf : categoricalEquivalences f) :
    dwyerKanFullyFaithfulPiZero f :=
  fun _ _ ↦ hf.fullyFaithful_mapHomotopyCategory.map_bijective _ _

/-- For f:X→Y in universe u, assume ho(f) is bijective on all vertex hom-sets and X is a
quasicategory. For any edge e′:f(x)→f(y) in Y, there is e:x→y in X with [f(e)]=[e′] in ho(Y). -/
theorem dwyerKanFullyFaithfulPiZero.exists_edge_map_toHoHom_eq
    [Quasicategory X] (hf : dwyerKanFullyFaithfulPiZero f)
    {x y : X _⦋0⦌} (e' : Edge (f.app (op ⦋0⦌) x) (f.app (op ⦋0⦌) y)) :
    ∃ e : Edge x y, (e.map f).toHoHom = e'.toHoHom := by
  obtain ⟨φ, hφ⟩ := (hf x y).surjective e'.toHoHom
  obtain ⟨e, rfl⟩ := Edge.exists_toHoHom_eq φ
  refine ⟨e, ?_⟩
  rw [Edge.toHoHom_map]
  exact hφ

/-- For f:X→Y in universe u, assume ho(f) is bijective on all vertex hom-sets. If e₁,e₂:x→y in X
have equal image-edge morphisms in ho(Y), then [e₁]=[e₂] in ho(X). -/
theorem dwyerKanFullyFaithfulPiZero.edge_map_toHoHom_injective
    (hf : dwyerKanFullyFaithfulPiZero f) {x y : X _⦋0⦌}
    {e₁ e₂ : Edge x y}
    (h : (e₁.map f).toHoHom = (e₂.map f).toHoHom) :
    e₁.toHoHom = e₂.toHoHom := by
  rw [Edge.toHoHom_map, Edge.toHoHom_map] at h
  exact (hf x y).injective h

/-!
## Simplices of the right mapping space

An n-simplex of R_X(a,b) is represented by an (n+1)-simplex of X with its specified endpoints.
Postcomposition by f sends that representing simplex σ to σ≫f.
-/

namespace mappingSpaceRight

variable (X : SSet.{u}) (a b : (Δ[0] : SSet.{u}) ⟶ X)

/-- For f:X→Y in universe u, a,b:Δ[0]→X and n∈ℕ, let σ be an n-simplex of R_X(a,b). Under the
successor-simplex presentation, the representing (n+1)-simplex of r_{a,b}(σ) is the representing
simplex of σ followed by f. -/
theorem simplexEquivSucc_map_app_val {Y : SSet.{u}} (F : X ⟶ Y)
    (n : ℕ) (σ : (mappingSpaceRight X a b).obj (op ⦋n⦌)) :
    ((simplexEquivSucc Y (a ≫ F) (b ≫ F) n)
        ((map X a b F).app (op ⦋n⦌) σ)).1 =
      ((simplexEquivSucc X a b n) σ).1 ≫ F := by
  change (SSet.joinStdSimplexIso n 0).inv ≫ (σ.1 ≫ F) =
    ((SSet.joinStdSimplexIso n 0).inv ≫ σ.1) ≫ F
  rw [Category.assoc]

end mappingSpaceRight

/-!
## Full faithfulness from two reverse composites

If f:X→Y and g:Y→X have both f≫g and g≫f fully faithful on realized right mapping spaces, then f
is fully faithful on those spaces. Combining this with categorical equivalence of f gives its
Dwyer–Kan condition.
-/

/-- For f:X→Y and g:Y→X in universe u, suppose every realized right mapping-space map of f≫g and of
g≫f is a weak homotopy equivalence. Then the same holds for f; thus f is Dwyer–Kan fully
faithful. -/
theorem dwyerKanFullyFaithful.of_comp_comp {g : Y ⟶ X}
    (hfg : dwyerKanFullyFaithful (f ≫ g))
    (hgf : dwyerKanFullyFaithful (g ≫ f)) :
    dwyerKanFullyFaithful f := by
  intro a b
  have hab : realizationWeakEquivalences (mappingSpaceRight.map X a b f ≫
      mappingSpaceRight.map Y (a ≫ f) (b ≫ f) g) := by
    rw [← mappingSpaceRight.map_comp]
    exact hfg a b
  have hbc : realizationWeakEquivalences (mappingSpaceRight.map Y (a ≫ f) (b ≫ f) g ≫
      mappingSpaceRight.map X ((a ≫ f) ≫ g) ((b ≫ f) ≫ g) f) := by
    rw [← mappingSpaceRight.map_comp]
    exact hgf (a ≫ f) (b ≫ f)
  exact realizationWeakEquivalences.left_of_comp_comp hab hbc

/-- For f:X→Y of simplicial sets in universe u, categorical equivalence means that precomposition
gives an equivalence ho(Q^Y)→ho(Q^X) for every quasicategory Q in that universe. If there is
g:Y→X such that f≫g and g≫f are fully faithful on realized right mapping spaces, then f is a
Dwyer–Kan equivalence: ho(f) is essentially surjective and all |r_{a,b}| are weak homotopy
equivalences. -/
theorem categoricalEquivalences.isDwyerKanEquivalence_of_comp_comp
    (hf : categoricalEquivalences f) {g : Y ⟶ X}
    (hfg : dwyerKanFullyFaithful (f ≫ g))
    (hgf : dwyerKanFullyFaithful (g ≫ f)) :
    isDwyerKanEquivalence f :=
  ⟨hf.dwyerKanEssentiallySurjective,
    dwyerKanFullyFaithful.of_comp_comp hfg hgf⟩

/-!
## A Kan mapping-space criterion

If each r_{a,b} has Kan source and target, induces an equivalence of fundamental groupoids, and
induces bijections on π_n at every source basepoint for every n≥0, then all |r_{a,b}| are weak
homotopy equivalences.
-/

/-- For f:X→Y in universe u, For vertex maps a,b:Δ[0]→X, write r_{a,b}:R_X(a,b)→R_Y(a≫f,b≫f) for the
induced map of right mapping spaces. Suppose these source and target mapping spaces are Kan for
every a,b, each induced fundamental-groupoid functor is an equivalence, and for every source
vertex σ and n∈ℕ the map π_n(R_X(a,b),σ)→π_n(R_Y(a≫f,b≫f),r_{a,b}(σ)) is bijective. Then f is
Dwyer–Kan fully faithful. -/
theorem dwyerKanFullyFaithful.of_kan_bijective_piMap
    (hKanX : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight X a b))
    (hKanY : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      KanComplex (mappingSpaceRight Y (a ≫ f) (b ≫ f)))
    (hFG : ∀ a b : (Δ[0] : SSet.{u}) ⟶ X,
      (SSet.mapFundamentalGroupoid
        (mappingSpaceRight.map X a b f)).IsEquivalence)
    (hπ : ∀ (a b : (Δ[0] : SSet.{u}) ⟶ X) (n : ℕ)
      (σ : (mappingSpaceRight X a b) _⦋0⦌),
      Function.Bijective
        (KanComplex.π.map (mappingSpaceRight.map X a b f) rfl
          (n := n) (x := σ))) :
    dwyerKanFullyFaithful f :=
  dwyerKanFullyFaithful.of_kanComplexW hKanX hKanY
    (fun a b => KanComplex.W.mk _ (hKanX a b) (hKanY a b) (hFG a b) (hπ a b))

end SSet

end
