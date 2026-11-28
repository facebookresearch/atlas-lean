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
# Lifted cycles under a complex morphism

Let C be a category with zero morphisms and c a complex shape on an independent index type. For
a morphism φ:K→L of c-shaped complexes, a map k:A→K_i with k≫d_K=0 lifts to a map A→Z_i(K).

Pushing k forward to k≫φ_i and lifting its cycle gives the composite of the lift of k with
Z_i(φ). Taking the homology class then gives the composite with H_i(φ). The statements apply
whenever K and L have homology at the selected index.
-/

@[expose] public section

noncomputable section

universe uC vC w

open CategoryTheory Limits

namespace HomologicalComplex

variable {C : Type uC} [Category.{vC} C] [HasZeroMorphisms C]
variable {ι : Type w} {c : ComplexShape ι}

/-- Let C be a category with zero morphisms, with independent object and morphism universes uC,vC.
Let c be a complex shape on an index type I in universe w. Let φ:K→L, k:A→K_i, and c.next(i)=j.
Assume K,L have homology at i and k≫d_K(i,j)=0, (k≫φ_i)≫d_L(i,j)=0. Then
lift_L(k≫φ_i)=lift_K(k)≫Z_i(φ) as morphisms A→Z_i(L), for the indicated lifts to cycles. -/
theorem liftCycles_pushforward {K L : HomologicalComplex C c} (φ : K ⟶ L)
    {A : C} {i j : ι} (k : A ⟶ K.X i) (hj : c.next i = j)
    (hk : k ≫ K.d i j = 0) (hkφ : (k ≫ φ.f i) ≫ L.d i j = 0)
    [K.HasHomology i] [L.HasHomology i] :
    L.liftCycles (k ≫ φ.f i) j hj hkφ
      = K.liftCycles k j hj hk ≫ cyclesMap φ i :=
  (liftCycles_comp_cyclesMap k j hj hk φ).symm

/-- Let C be a category with zero morphisms, with independent object and morphism universes uC,vC.
Let c be a complex shape on an index type I in universe w. For φ:K→L, k:A→K_i, c.next(i)=j, and
homology at i in both complexes, assume k≫d_K(i,j)=0 and (k≫φ_i)≫d_L(i,j)=0. With π_i the cycle
class projections, lift_L(k≫φ_i)≫π_i^L=(lift_K(k)≫π_i^K)≫H_i(φ) as maps A→H_i(L). -/
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
