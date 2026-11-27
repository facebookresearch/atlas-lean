/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Data.ZMod.Basic
public import MathlibExt.Algebra.Homology.Embedding.RestrictionHomology

/-! # Tests for functorial restriction-homology comparisons -/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex.RestrictionHomologyNaturalityTests

section Generic

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (e : c.Embedding c') [e.IsRelIff]
variable {K L M : HomologicalComplex C c'}
variable (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k)
variable {i' j' k' : ι'}
  (hi' : e.f i = i') (hj' : e.f j = j') (hk' : e.f k = k')
  (hi'' : c'.prev j' = i') (hk'' : c'.next j' = k')
variable [K.HasHomology j'] [L.HasHomology j'] [M.HasHomology j']
variable [(K.restriction e).HasHomology j]
  [(L.restriction e).HasHomology j]
  [(M.restriction e).HasHomology j]

#check restrictionHomologyIso_inv_naturality
#check restrictionHomologyIso_naturality
#check restrictionCyclesIso_naturality
#check restrictionOpcyclesIso_naturality

example (φ : K ⟶ L) :
    homologyMap φ j' ≫
        (L.restrictionHomologyIso e i j k hi hk
          hi' hj' hk' hi'' hk'').inv =
      (K.restrictionHomologyIso e i j k hi hk
        hi' hj' hk' hi'' hk'').inv ≫
        homologyMap (restrictionMap φ e) j :=
  restrictionHomologyIso_inv_naturality φ e i j k hi hk
    hi' hj' hk' hi'' hk''

example :
    homologyMap (𝟙 K) j' ≫
        (K.restrictionHomologyIso e i j k hi hk
          hi' hj' hk' hi'' hk'').inv =
      (K.restrictionHomologyIso e i j k hi hk
        hi' hj' hk' hi'' hk'').inv ≫
        homologyMap (restrictionMap (𝟙 K) e) j :=
  restrictionHomologyIso_inv_naturality (𝟙 K) e i j k hi hk
    hi' hj' hk' hi'' hk''

example (φ : K ⟶ L) (ψ : L ⟶ M) :
    homologyMap (φ ≫ ψ) j' ≫
        (M.restrictionHomologyIso e i j k hi hk
          hi' hj' hk' hi'' hk'').inv =
      (K.restrictionHomologyIso e i j k hi hk
        hi' hj' hk' hi'' hk'').inv ≫
        homologyMap (restrictionMap (φ ≫ ψ) e) j :=
  restrictionHomologyIso_inv_naturality (φ ≫ ψ) e i j k hi hk
    hi' hj' hk' hi'' hk''

example (φ : K ⟶ L)
    (hi₂ : c.prev j = i) (hk₂ : c.next j = k)
    (hi₂' : e.f i = i') (hj₂' : e.f j = j') (hk₂' : e.f k = k')
    (hi₂'' : c'.prev j' = i') (hk₂'' : c'.next j' = k') :
    homologyMap φ j' ≫
        (L.restrictionHomologyIso e i j k hi₂ hk₂
          hi₂' hj₂' hk₂' hi₂'' hk₂'').inv =
      (K.restrictionHomologyIso e i j k hi₂ hk₂
        hi₂' hj₂' hk₂' hi₂'' hk₂'').inv ≫
        homologyMap (restrictionMap φ e) j :=
  restrictionHomologyIso_inv_naturality φ e i j k hi₂ hk₂
    hi₂' hj₂' hk₂' hi₂'' hk₂''

end Generic

section NeighborCompatible

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (e : c.Embedding c') [e.IsRelIff]
variable {K L : HomologicalComplex C c'} (j : ι)
variable (hprev : c'.prev (e.f j) = e.f (c.prev j))
  (hnext : c'.next (e.f j) = e.f (c.next j))
variable [K.HasHomology (e.f j)] [L.HasHomology (e.f j)]
  [(K.restriction e).HasHomology j]
  [(L.restriction e).HasHomology j]

example : (K.restriction e).homology j ≅ K.homology (e.f j) :=
  K.restrictionHomologyIsoAt e j hprev hnext

example (φ : K ⟶ L) :
    homologyMap (restrictionMap φ e) j ≫
        (L.restrictionHomologyIsoAt e j hprev hnext).hom =
      (K.restrictionHomologyIsoAt e j hprev hnext).hom ≫
        homologyMap φ (e.f j) :=
  restrictionHomologyIsoAt_hom_naturality e φ j hprev hnext

example (φ : K ⟶ L) :
    homologyMap φ (e.f j) ≫
        (L.restrictionHomologyIsoAt e j hprev hnext).inv =
      (K.restrictionHomologyIsoAt e j hprev hnext).inv ≫
        homologyMap (restrictionMap φ e) j :=
  restrictionHomologyIsoAt_inv_naturality e φ j hprev hnext

example (φ : K ⟶ L) :
    QuasiIsoAt (restrictionMap φ e) j ↔ QuasiIsoAt φ (e.f j) :=
  quasiIsoAt_restrictionMap_iff φ e j hprev hnext

end NeighborCompatible

section FunctorComparison

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  [HasZeroObject C] [CategoryWithHomology C]
variable (e : c.Embedding c') [e.IsRelIff] (j : ι)
variable (hprev : c'.prev (e.f j) = e.f (c.prev j))
  (hnext : c'.next (e.f j) = e.f (c.next j))

example :
    e.restrictionFunctor C ⋙ cyclesFunctor C c j ≅
      cyclesFunctor C c' (e.f j) :=
  restrictionCyclesFunctorIsoAt e j hnext

example :
    e.restrictionFunctor C ⋙ opcyclesFunctor C c j ≅
      opcyclesFunctor C c' (e.f j) :=
  restrictionOpcyclesFunctorIsoAt e j hprev

example :
    e.restrictionFunctor C ⋙ homologyFunctor C c j ≅
      homologyFunctor C c' (e.f j) :=
  restrictionHomologyFunctorIsoAt e j hprev hnext

end FunctorComparison

section IntegerBoundary

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : ChainComplex C ℤ}

example (f : K ⟶ L) (z : ℤ) :=
  restrictionHomologyIso_inv_naturality
    (K := K) (L := L) f ComplexShape.embeddingUpIntDownInt
    (z - 1) z (z + 1)
    (by simp) (by simp)
    (i' := ComplexShape.embeddingUpIntDownInt.f (z - 1))
    (j' := ComplexShape.embeddingUpIntDownInt.f z)
    (k' := ComplexShape.embeddingUpIntDownInt.f (z + 1))
    rfl rfl rfl
    (by simp [ComplexShape.embeddingUpIntDownInt]; omega)
    (by simp [ComplexShape.embeddingUpIntDownInt]; omega)

example (z : ℤ) :=
  let Z : ChainComplex C ℤ := HomologicalComplex.zero
  restrictionHomologyIso_inv_naturality
    (K := Z) (L := Z) (𝟙 Z) ComplexShape.embeddingUpIntDownInt
    (z - 1) z (z + 1)
    (by simp) (by simp)
    (i' := ComplexShape.embeddingUpIntDownInt.f (z - 1))
    (j' := ComplexShape.embeddingUpIntDownInt.f z)
    (k' := ComplexShape.embeddingUpIntDownInt.f (z + 1))
    rfl rfl rfl
    (by simp [ComplexShape.embeddingUpIntDownInt]; omega)
    (by simp [ComplexShape.embeddingUpIntDownInt]; omega)

end IntegerBoundary

section ZeroRing

variable {K L : ChainComplex (ModuleCat.{0} (ZMod 1)) ℤ}

example (f : K ⟶ L) (z : ℤ) :=
  restrictionHomologyIso_inv_naturality
    (K := K) (L := L) f ComplexShape.embeddingUpIntDownInt
    (z - 1) z (z + 1)
    (by simp) (by simp)
    (i' := ComplexShape.embeddingUpIntDownInt.f (z - 1))
    (j' := ComplexShape.embeddingUpIntDownInt.f z)
    (k' := ComplexShape.embeddingUpIntDownInt.f (z + 1))
    rfl rfl rfl
    (by simp [ComplexShape.embeddingUpIntDownInt]; omega)
    (by simp [ComplexShape.embeddingUpIntDownInt]; omega)

end ZeroRing

#print axioms restrictionCyclesIso_naturality
#print axioms restrictionHomologyIso_naturality
#print axioms restrictionHomologyIso_inv_naturality
#print axioms restrictionHomologyFunctorIsoAt
#print axioms quasiIsoAt_restrictionMap_iff

end HomologicalComplex.RestrictionHomologyNaturalityTests

end
