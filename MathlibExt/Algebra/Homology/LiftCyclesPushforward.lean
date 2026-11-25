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

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Pushforward of lifted cycles along a chain map

`Mathlib`'s `HomologicalComplex.liftCycles_comp_cyclesMap` pushes a lifted
cycle forward along a chain map, but bakes in one specific cycle proof for
the pushed-forward chain. These restatements accept an arbitrary proof
(definitionally irrelevant), and the class-level corollary.
-/

@[expose] public section

noncomputable section

universe uC vC w

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}

/-- Pushing a bundled cycle forward along a chain map, for any cycle proof:
the reverse of `HomologicalComplex.liftCycles_comp_cyclesMap`, whose baked-in
proof is definitionally irrelevant. -/
theorem liftCycles_pushforward {K L : HomologicalComplex C c} (φ : K ⟶ L)
    {A : C} {i j : ι} (k : A ⟶ K.X i) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (hkφ : (k ≫ φ.f i) ≫ L.d i j = 0)
    [K.HasHomology i] [L.HasHomology i] :
    L.liftCycles (k ≫ φ.f i) j hj hkφ
      = K.liftCycles k j hj hk ≫ cyclesMap φ i :=
  (liftCycles_comp_cyclesMap k j hj hk φ).symm

/-- The class of a pushed-forward chain is the pushforward of the class. -/
theorem classHom_pushforward {K L : HomologicalComplex C c} (φ : K ⟶ L)
    {A : C} {i j : ι} (k : A ⟶ K.X i) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (hkφ : (k ≫ φ.f i) ≫ L.d i j = 0)
    [K.HasHomology i] [L.HasHomology i] :
    L.liftCycles (k ≫ φ.f i) j hj hkφ ≫ L.homologyπ i
      = (K.liftCycles k j hj hk ≫ K.homologyπ i) ≫
        homologyMap φ i := by
  have h1 := liftCycles_pushforward φ k hj hk hkφ
  have h2 := homologyπ_naturality φ (K := K) (L := L) (i := i)
  calc L.liftCycles (k ≫ φ.f i) j hj hkφ ≫ L.homologyπ i
        = (K.liftCycles k j hj hk ≫ cyclesMap φ i) ≫ L.homologyπ i := by
          rw [h1]
      _ = K.liftCycles k j hj hk ≫ (cyclesMap φ i ≫ L.homologyπ i) := by
          rw [Category.assoc]
      _ = K.liftCycles k j hj hk ≫ (K.homologyπ i ≫ homologyMap φ i) := by
          rw [← h2]
      _ = (K.liftCycles k j hj hk ≫ K.homologyπ i) ≫ homologyMap φ i := by
          rw [← Category.assoc]

end HomologicalComplex
