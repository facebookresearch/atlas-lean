/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.CommAlgCat.CotangentSimplicial
public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Homology of the normalized cotangent model with coefficients

Tensor the normalized polynomial cotangent chain model with an `A`-module
`M` and take homology. This defines the canonical coefficient homology
functor, with coefficient maps induced by tensor natural transformations
and homology maps.

The convention is `M ⊗[A] L`; the tensor commutor gives the opposite
factor order. The coefficient universe is independent and `M` need not be
flat or projective. This module defines the specified model and its
functorial coefficient maps.

References: Stacks Project, Definition 92.3.2; Loday, *Cyclic Homology*,
second edition, Definition 3.5.4.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v t

namespace CommAlgCat

variable (k : Type u) [CommRing k] (A : CommAlgCat.{max u v} k)

/-- The actual coefficient chain complex, functorial in arbitrary `A`-modules.
The coefficient height `t` is independent of the ground and algebra heights. -/
def cotangentCoefficientComplexFunctor :
    ModuleCat.{t} A ⥤ ChainComplex (ModuleCat.{max u v t} A) ℕ where
  obj M := (((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).obj M).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (cotangentComplex k A)
  map f := (NatTrans.mapHomologicalComplex
    ((ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map f)
    (ComplexShape.down ℕ)).app (cotangentComplex k A)
  map_id M := by
    rw [(ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map_id M,
      NatTrans.mapHomologicalComplex_id]
    rfl
  map_comp f g := by
    rw [(ModuleCat.tensorBifunctorAt.{max u v, t, max u v} A).map_comp f g,
      NatTrans.mapHomologicalComplex_comp]
    rfl

/-- Degreewise canonical André–Quillen homology of the actual standard
polynomial cotangent model. Its coefficient maps are the genuine induced
homology maps, rather than fields of a supplied data structure. -/
def andreQuillenHomologyFunctor (n : ℕ) :
    ModuleCat.{t} A ⥤ ModuleCat.{max u v t} A :=
  cotangentCoefficientComplexFunctor k A ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u v t} A) (ComplexShape.down ℕ) n

/-- Canonical André–Quillen homology with arbitrary coefficients. -/
def andreQuillenHomology (M : ModuleCat.{t} A) (n : ℕ) : ModuleCat.{max u v t} A :=
  (andreQuillenHomologyFunctor k A n).obj M

/-- The canonical coefficient map induced from the actual module morphism. -/
def andreQuillenHomologyMap {M N : ModuleCat.{t} A} (f : M ⟶ N) (n : ℕ) :
    andreQuillenHomology k A M n ⟶ andreQuillenHomology k A N n :=
  (andreQuillenHomologyFunctor k A n).map f

@[simp]
theorem andreQuillenHomologyMap_id (M : ModuleCat.{t} A) (n : ℕ) :
    andreQuillenHomologyMap k A (𝟙 M) n = 𝟙 (andreQuillenHomology k A M n) :=
  (andreQuillenHomologyFunctor k A n).map_id M

theorem andreQuillenHomologyMap_comp {M N T : ModuleCat.{t} A}
    (f : M ⟶ N) (g : N ⟶ T) (n : ℕ) :
    andreQuillenHomologyMap k A (f ≫ g) n =
      andreQuillenHomologyMap k A f n ≫ andreQuillenHomologyMap k A g n :=
  (andreQuillenHomologyFunctor k A n).map_comp f g

end CommAlgCat

end
