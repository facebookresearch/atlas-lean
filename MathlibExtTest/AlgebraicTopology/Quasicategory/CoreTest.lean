/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.Core
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
# Tests for the equivalence-edge core of a simplicial set

Public clients exercise `SSet.core`, its membership
characterizations, maximality, functoriality, the Kan-complex
computation, the unconditional horn-lifting property of the core
inclusion with its inner-fibration and quasicategory consequences,
the coherent-isomorphism edge, and both forms of the nerve gate.
Only public declarations are used.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe v u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory
namespace CoreTest

open SSet

section Signatures

#check @SSet.Edge.IsEquivalence.of_edge_eq
#check @SSet.Edge.isEquivalence_iff_of_edge_eq
#check @SSet.Edge.isEquivalence_of_kanComplex
#check @SSet.core
#check @SSet.mem_core_obj_iff
#check @SSet.mem_core_obj_zero
#check @SSet.core_obj_zero
#check @SSet.mem_core_obj_one_iff
#check @SSet.mem_core_obj_iff_forall_edge
#check @SSet.le_core_iff
#check @SSet.core_le_preimage
#check @SSet.core.map
#check @SSet.core.map_ι
#check @SSet.core_eq_top_of_kanComplex
#check @SSet.hasLiftingProperty_horn_core_ι
#check @SSet.mem_core_nerve_iff_forall_map'_isIso
#check @SSet.mem_core_nerve_iff_forall_succ_map'_isIso
#check @SSet.mem_core_nerve_mk₁_iff
#check @SSet.mem_core_nerve_mk₂_iff

end Signatures

section Basic

variable {X Y : SSet.{u}} {x₀ x₁ : X _⦋0⦌}

/-- The core is a subcomplex of its ambient simplicial set. -/
example : X.Subcomplex := core X

/-- Membership in the core unfolds to the defining edge condition. -/
example {Δ : SimplexCategoryᵒᵖ} {x : X.obj Δ} :
    x ∈ (core X).obj Δ ↔
      ∀ φ : ⦋1⦌ ⟶ Δ.unop, (Edge.mk' (X.map φ.op x)).IsEquivalence :=
  mem_core_obj_iff

/-- Every vertex lies in the core. -/
example (x : X _⦋0⦌) : x ∈ (core X).obj (op ⦋0⦌) :=
  mem_core_obj_zero x

/-- The core has all vertices of the ambient simplicial set. -/
example : (core X).obj (op ⦋0⦌) = Set.univ :=
  core_obj_zero X

/-- A `1`-simplex is in the core exactly when its edge is an
equivalence. -/
example {s : X _⦋1⦌} : s ∈ (core X).obj (op ⦋1⦌) ↔ (Edge.mk' s).IsEquivalence :=
  mem_core_obj_one_iff

/-- The degenerate `1`-simplex underlying an identity edge lies
in the core. -/
example (x : X _⦋0⦌) : (Edge.id x).edge ∈ (core X).obj (op ⦋1⦌) :=
  mem_core_obj_one_iff.mpr ((Edge.isEquivalence_id x).of_edge_eq rfl)

/-- The edge `Edge.mk' e.edge` recovered from the `1`-simplex of an
edge is an equivalence if and only if `e` is. -/
example (e : Edge x₀ x₁) :
    (Edge.mk' e.edge).IsEquivalence ↔ e.IsEquivalence :=
  (Edge.isEquivalence_iff_of_edge_eq (show
    (Edge.mk' e.edge).edge = e.edge from rfl))

/-- Membership can be tested on the vertex pairs given by
`stdSimplex.edge`. -/
example {n : ℕ} {x : X _⦋n⦌} :
    x ∈ (core X).obj (op ⦋n⦌) ↔ ∀ (a b : Fin (n + 1)) (hab : a ≤ b),
      (Edge.mk' (X.map
        (stdSimplex.objEquiv (stdSimplex.edge.{u} n a b hab)).op x)).IsEquivalence :=
  mem_core_obj_iff_forall_edge

/-- Simplices of the core are stable under simplicial operators,
because the core is a subcomplex. -/
example {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') {x : X.obj Δ}
    (hx : x ∈ (core X).obj Δ) : X.map f x ∈ (core X).obj Δ' :=
  (core X).map f hx

/-- Maximality: a subcomplex is contained in the core if and only
if all of its `1`-simplices are equivalences. -/
example (A : X.Subcomplex) :
    A ≤ core X ↔ ∀ s ∈ A.obj (op ⦋1⦌), (Edge.mk' s).IsEquivalence :=
  le_core_iff A

/-- In particular the core is contained in itself through the
maximality characterization. -/
example : core X ≤ core X :=
  (le_core_iff _).mpr fun _s hs ↦ mem_core_obj_one_iff.mp hs

/-- Functoriality at the level of preimages. -/
example (f : X ⟶ Y) : core X ≤ (core Y).preimage f :=
  core_le_preimage f

/-- A map of simplicial sets restricts to a map of cores. -/
example (f : X ⟶ Y) : (core X : SSet.{u}) ⟶ (core Y : SSet.{u}) :=
  core.map f

/-- The restricted map is compatible with the inclusions. -/
example (f : X ⟶ Y) : core.map f ≫ (core Y).ι = (core X).ι ≫ f :=
  core.map_ι f

end Basic

section KanAndQuasicategory

variable {X : SSet.{u}} {x₀ x₁ : X _⦋0⦌}

/-- Every edge of a Kan complex is an equivalence. -/
example [KanComplex X] (e : Edge x₀ x₁) : e.IsEquivalence :=
  Edge.isEquivalence_of_kanComplex e

/-- The core of a Kan complex is the whole simplicial set. -/
example [KanComplex X] : core X = ⊤ :=
  core_eq_top_of_kanComplex X

/-- Hence every simplex of a Kan complex lies in its core. -/
example [KanComplex X] {Δ : SimplexCategoryᵒᵖ} (x : X.obj Δ) :
    x ∈ (core X).obj Δ := by
  simp [core_eq_top_of_kanComplex X]

/-- The core inclusion is an inner fibration with no hypothesis
on `X`. -/
example : InnerFibration (core X).ι := inferInstance

/-- The core inclusion has the right lifting property against
every horn in dimension at least `2`, including outer horns. -/
example {n : ℕ} (i : Fin (n + 3)) :
    HasLiftingProperty Λ[n + 2, i].ι (core X).ι :=
  hasLiftingProperty_horn_core_ι i

/-- The core of a quasicategory is a quasicategory. -/
example [Quasicategory X] : Quasicategory (core X : SSet.{u}) :=
  inferInstance

/-- In particular, the core of a Kan complex is a quasicategory. -/
example [KanComplex X] : Quasicategory (core X : SSet.{u}) :=
  inferInstance

end KanAndQuasicategory

section CoherentIsoTests

variable {X : SSet.{u}}

/-- The forward edge of the walking coherent isomorphism lies in
its core. -/
example : (coherentIso.hom.{u}).edge ∈
    (core coherentIso.{u}).obj (op ⦋1⦌) :=
  mem_core_obj_one_iff.mpr
    (Edge.isEquivalence_coherentIso_hom.of_edge_eq rfl)

/-- Any map out of the coherent isomorphism restricts to cores. -/
example (g : coherentIso.{u} ⟶ X) :
    (core coherentIso.{u} : SSet.{u}) ⟶ (core X : SSet.{u}) :=
  core.map g

end CoherentIsoTests

section NerveTests

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Nerve gate in all-pairs form, as an if-and-only-if. -/
example {n : ℕ} (F : ComposableArrows C n) :
    F ∈ (core (nerve C)).obj (op ⦋n⦌) ↔
      ∀ (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n), IsIso (F.map' i j) :=
  mem_core_nerve_iff_forall_map'_isIso F

/-- Nerve gate in successive form: the simplices in the core of a
nerve are chains of isomorphisms. -/
example {n : ℕ} (F : ComposableArrows C n) :
    F ∈ (core (nerve C)).obj (op ⦋n⦌) ↔
      ∀ (i : ℕ) (hi : i + 1 ≤ n), IsIso (F.map' i (i + 1)) :=
  mem_core_nerve_iff_forall_succ_map'_isIso F

/-- A chain of isomorphisms in `C` lies in the core of the
nerve. -/
example {n : ℕ} (F : ComposableArrows C n)
    (h : ∀ (i : ℕ) (hi : i + 1 ≤ n), IsIso (F.map' i (i + 1))) :
    F ∈ (core (nerve C)).obj (op ⦋n⦌) :=
  (mem_core_nerve_iff_forall_succ_map'_isIso F).mpr h

/-- Every successive morphism of a chain in the core of a nerve
is an isomorphism. -/
example {n : ℕ} (F : ComposableArrows C n)
    (hF : F ∈ (core (nerve C)).obj (op ⦋n⦌))
    (i : ℕ) (hi : i + 1 ≤ n) : IsIso (F.map' i (i + 1)) :=
  (mem_core_nerve_iff_forall_succ_map'_isIso F).mp hF i hi

/-- Every composite `F.map' i j` of a chain in the core of a
nerve is an isomorphism. -/
example {n : ℕ} (F : ComposableArrows C n)
    (hF : F ∈ (core (nerve C)).obj (op ⦋n⦌))
    (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) : IsIso (F.map' i j) :=
  (mem_core_nerve_iff_forall_map'_isIso F).mp hF i j hij hjn

/-- The unique `0`-simplex shape in a nerve lies in the core:
the successive condition is vacuous in dimension `0`. -/
example (a : C) :
    ComposableArrows.mk₀ a ∈ (core (nerve C)).obj (op ⦋0⦌) :=
  (mem_core_nerve_iff_forall_succ_map'_isIso _).mpr
    fun i hi ↦ (Nat.not_succ_le_zero i hi).elim

/-- A `1`-simplex of a nerve is in the core exactly when the
morphism is an isomorphism. -/
example {a b : C} (f : a ⟶ b) :
    ComposableArrows.mk₁ f ∈ (core (nerve C)).obj (op ⦋1⦌) ↔ IsIso f :=
  mem_core_nerve_mk₁_iff f

/-- The identity `1`-simplex of a nerve lies in the core. -/
example (a : C) :
    ComposableArrows.mk₁ (𝟙 a) ∈ (core (nerve C)).obj (op ⦋1⦌) :=
  (mem_core_nerve_mk₁_iff (𝟙 a)).mpr inferInstance

/-- A `1`-simplex of the core of a nerve comes from an isomorphism
in `C`. -/
example {a b : C} (f : a ⟶ b)
    (h : ComposableArrows.mk₁ f ∈ (core (nerve C)).obj (op ⦋1⦌)) :
    IsIso f :=
  (mem_core_nerve_mk₁_iff f).mp h

/-- A `2`-simplex of a nerve is in the core exactly when both
morphisms are isomorphisms. -/
example {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    ComposableArrows.mk₂ f g ∈ (core (nerve C)).obj (op ⦋2⦌) ↔
      IsIso f ∧ IsIso g :=
  mem_core_nerve_mk₂_iff f g

/-- A composable pair of isomorphisms gives a `2`-simplex of the
core of the nerve. -/
example {a b c : C} (f : a ⟶ b) (g : b ⟶ c) [IsIso f] [IsIso g] :
    ComposableArrows.mk₂ f g ∈ (core (nerve C)).obj (op ⦋2⦌) :=
  (mem_core_nerve_mk₂_iff f g).mpr ⟨inferInstance, inferInstance⟩

/-- The first morphism of a `2`-simplex in the core of a nerve is
an isomorphism. -/
example {a b c : C} (f : a ⟶ b) (g : b ⟶ c)
    (h : ComposableArrows.mk₂ f g ∈ (core (nerve C)).obj (op ⦋2⦌)) :
    IsIso f :=
  ((mem_core_nerve_mk₂_iff f g).mp h).1

/-- Functors induce maps between the cores of nerves. -/
example (F : C ⥤ D) :
    (core (nerve C) : SSet) ⟶ (core (nerve D) : SSet) :=
  core.map (nerveMap F)

end NerveTests

section ConservativeMaps

/-- An equivalence of homotopy categories supplies the required reflection instance. -/
example {X Y : SSet.{u}} (f : X ⟶ Y)
    [(mapHomotopyCategory f).IsEquivalence] :
    core X = (core Y).preimage f :=
  core_eq_preimage_of_reflectsIsomorphisms f

/-- The literal pullback square transfers lifting properties to the core map. -/
example {A B X Y : SSet.{u}} (i : A ⟶ B) (f : X ⟶ Y)
    [(mapHomotopyCategory f).ReflectsIsomorphisms] [HasLiftingProperty i f] :
    HasLiftingProperty i (core.map f) :=
  (core.isPullback_of_reflectsIsomorphisms f).hasLiftingProperty i

end ConservativeMaps

end CoreTest
end MathlibExtTest.AlgebraicTopology.Quasicategory
