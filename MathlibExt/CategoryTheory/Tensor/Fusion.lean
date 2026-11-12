/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Andres Barei Bueno
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import MathlibExt.CategoryTheory.Semisimple

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Algebra 477, Algebra 478

/-!
# Fusion Category; Rank of a fusion category

## References

* The definition appears directly in Wikipedia: https://en.wikipedia.org/wiki/Fusion_category
  (dated Oct 5 2026), An actual reference is Introduction to Fusion Categories by Kyle Kawagoe,
  where the definition of fusion category appears as Definition 6.1. This definition however, is
  with the idea that \mathbb C is algebraically closed, in which case the monoidal unit is simple
  if and only if its endomorphism space is one-dimensional. For the equivalence, see Theorem 4.21
  from the reference. (for `Fusion`)
* This definition appears in the first page of the paper Rank-Finiteness for Modular Categories,
  by Bruillard, Ng, Rowell and Wang: https://arxiv.org/pdf/1310.7050 (dated Oct 6, 2026) (for
  `Fusion.Rank`)
-/

namespace MetaMathlibExt

-- Algebra 477: Fusion Category

/-- Let k be a field. A k-linear monoidal and abelian category is called a fusion category if it is
rigid, it has only a finite number of isoclasses of simple objects, and the monoidal identity is a
simple object.
-/
class Fusion.{u,v,w} (k : Type w) [Field k] (C : Type u) [CategoryTheory.Category.{v} C]
  extends CategoryTheory.Abelian C, CategoryTheory.Linear k C,
          CategoryTheory.MonoidalCategory C, CategoryTheory.MonoidalPreadditive C,
          CategoryTheory.MonoidalLinear k C, CategoryTheory.RigidCategory C,
          SemisimpleCategory C
          where
            [finite_simples : ∃ (n : ℕ) (S : Fin n → C),
              (∀ (i : Fin n), CategoryTheory.Simple (S i))  ∧
              (∀ (T : C), CategoryTheory.Simple T → (∃! (i : Fin n), Nonempty (T ≅ (S i))))]
            [hom_finite : ∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
            [simple_monoidal_unit : CategoryTheory.Simple tensorUnit]

-- Algebra 478: Rank of a fusion category

/-- The rank of a fusion category 𝒞 is the number of isoclasses of simple objects in 𝒞. -/
noncomputable def Fusion.Rank.{u,v,w} (k : Type w) [Field k]
  (C : Type u) [CategoryTheory.Category.{v} C]
  [Fusion k C] : ℕ :=
    Exists.choose (Fusion.finite_simples (k := k) (C := C))

end MetaMathlibExt

end
