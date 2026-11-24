/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.Basic.Countable.Basic

/-!
# Natural-number models of simplicial sets

Sets of natural-number codes and their simplicial operators realize in
any value universe. Supplied degreewise injective encodings give a coded
model and an actual natural isomorphism to the original simplicial set.
The full data and proofs are retained from the general recoding unit in
`ModelCategory.Joyal.TwoVertexJ`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-!
## Simplicial sets coded on subsets of `ℕ`

A `SSet.NatModel` is the raw data of a simplicial set whose type of
`x`-simplices is a subset of `ℕ` for every `x : SimplexCategoryᵒᵖ`, with
the simplicial operators given as bare functions. The type of these data
is a `Type 0`, which is what makes Stevenson's "set of representatives"
small in every universe `u` after realization at `SSet.{u}`.
-/

/-- The data of a simplicial set coded on subsets of `ℕ`: for each
`x : SimplexCategoryᵒᵖ` a set of codes `obj x ⊆ ℕ`, and for each
`φ : x ⟶ y` a function `map φ : obj x → obj y`, satisfying the functor
laws. This is the `Type 0` data type underlying the small representative
family for Stevenson's `𝒥`. -/
structure NatModel where
  /-- The set of `ℕ`-codes of simplices in degree `x`. -/
  obj : SimplexCategoryᵒᵖ → Set ℕ
  /-- The simplicial operators, as functions between code sets. -/
  map : ∀ {x y : SimplexCategoryᵒᵖ}, (x ⟶ y) → obj x → obj y
  /-- Identity operators act as the identity. -/
  map_id : ∀ {x : SimplexCategoryᵒᵖ} (a : obj x), map (𝟙 x) a = a
  /-- Simplicial operators compose functorially. -/
  map_comp : ∀ {x y z : SimplexCategoryᵒᵖ} (f : x ⟶ y) (g : y ⟶ z)
    (a : obj x), map (f ≫ g) a = map g (map f a)

namespace NatModel

variable (d : NatModel)

/-- The simplicial set at universe `u` realized from coded data: its
type of `x`-simplices is `ULift (d.obj x)` and its simplicial operators
are the lifts of the coded functions. -/
def toSSet : SSet.{u} where
  obj x := ULift.{u} (d.obj x)
  map {x y} φ :=
    ↾fun (a : ULift.{u} (d.obj x)) =>
      (ULift.up.{u} (d.map φ a.down) : ULift.{u} (d.obj y))
  map_id _ := by
    ext a
    exact congrArg Subtype.val (d.map_id a.down)
  map_comp φ ψ := by
    ext a
    exact congrArg Subtype.val (d.map_comp φ ψ a.down)

/-- A coded model has countably many non-degenerate simplices, Stevenson's
boundedness condition in Notation 6.1: a non-degenerate simplex is
determined by the pair of its dimension and its `ℕ`-code. -/
theorem countable_N_toSSet : Countable (d.toSSet.{u}).N := by
  refine Function.Injective.countable (f := fun s : (d.toSSet.{u}).N ↦
    (s.dim, s.simplex.down.1)) ?_
  intro s t h
  obtain ⟨n, ⟨s, hs⟩, rfl⟩ := s.mk_surjective
  obtain ⟨m, ⟨t, ht⟩, rfl⟩ := t.mk_surjective
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  rw [N.ext_iff, S.ext_iff']
  exact ⟨rfl, ULift.ext (Subtype.ext h2)⟩

end NatModel


namespace NatModel

variable (B : SSet.{u}) (e : ∀ x : SimplexCategoryᵒᵖ, B.obj x → ℕ)
  (he : ∀ x, Function.Injective (e x))

/-- The coded model of a simplicial set `B` with respect to a chosen
encoding `e` of its simplex types into `ℕ`: the codes in degree `x` are
the range of `e x`, and the simplicial operators are transported from
`B` along the encoding (decoded by choice from the range proof). -/
noncomputable def of : NatModel where
  obj x := Set.range (e x)
  map {x y} φ a := ⟨e y (B.map φ a.2.choose), ⟨_, rfl⟩⟩
  map_id {x} a := by
    apply Subtype.ext
    change e x (B.map (𝟙 x) a.2.choose) = a.1
    rw [show B.map (𝟙 x) a.2.choose = a.2.choose by simp, a.2.choose_spec]
  map_comp {x y z} f g a := by
    apply Subtype.ext
    have key : ∀ b : B.obj y,
        (⟨e y b, ⟨b, rfl⟩⟩ : Set.range (e y)).2.choose = b :=
      fun b ↦ he y (⟨b, rfl⟩ : ∃ a, e y a = e y b).choose_spec
    change e z (B.map (f ≫ g) a.2.choose)
      = e z (B.map g
        (⟨e y (B.map f a.2.choose), ⟨B.map f a.2.choose, rfl⟩⟩ :
          Set.range (e y)).2.choose)
    rw [key]
    congr 1
    simp

/-- The degreewise bijection between the realization of the coded model
of `B` and `B` itself: a coded simplex decodes (by choice) to the simplex
of `B` it came from, which is independent of choices by injectivity of
the encoding. -/
noncomputable def ofEquiv (x : SimplexCategoryᵒᵖ) :
    (NatModel.of B e he).toSSet.{u}.obj x ≃ B.obj x where
  toFun a := a.down.2.choose
  invFun b := ⟨⟨e x b, ⟨b, rfl⟩⟩⟩
  left_inv a := by
    apply ULift.ext
    apply Subtype.ext
    exact a.down.2.choose_spec
  right_inv b := he x (⟨b, rfl⟩ : ∃ a, e x a = e x b).choose_spec

/-- The realization of the coded model of `B` is isomorphic to `B`:
recoding a simplicial set on subsets of `ℕ` does not change its
isomorphism class. This is the representative-existence step behind
Stevenson's passage from the (proper class of) all two-vertex countable
categorical `B` to the small set `𝒥` of Notation 6.1. -/
noncomputable def isoOf : (NatModel.of B e he).toSSet.{u} ≅ B :=
  NatIso.ofComponents (fun x ↦ (NatModel.ofEquiv B e he x).toIso) (by
    intro x y φ
    ext a
    apply he y
    exact ((NatModel.of B e he).toSSet.{u}.map φ a).down.2.choose_spec)

end NatModel

end SSet
