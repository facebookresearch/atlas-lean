/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.InfiniteDenominatorRoots

/-!
# Actual finite-root transition and infinite-root stack construction

These requests construct root restriction by the literal quotient exponent,
the coherent global finite-root tower and its actual groupoid 2-limit stack.
The finite fibres, monoid power embeddings, root module maps, stack 2-cells,
parameter restrictions and projection comparisons are fixed by their types.

Source: Mattia Talpo and Angelo Vistoli,
https://arxiv.org/abs/1410.1164v2, §§3--4. Theorem 5.24 concerns
universal-infinite-root-preserving morphisms, and Theorem 6.16 concerns an
independently defined Kummer-flat site; those interfaces continue separately.
-/

open CategoryTheory AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.DeligneFaltingsSheaves
open MathlibExt.AlgebraicGeometry.DenominatorRootStacks
open MathlibExt.AlgebraicGeometry.FiniteRootTowers
open MathlibExt.AlgebraicGeometry.InfiniteDenominatorRoots
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage

universe u

/-- Restrict actual m-th roots to n-th roots by the literal exponent m/n. -/
def_wanted finiteRootRestriction
    [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{u}) (X : Scheme.{u})
    (A : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A)
    (T : Over X) (n m : Exponent) (h : n.val ∣ m.val) : RootRestriction I D T n m h

/-- Construct the actual coherent stack transition maps from normalized finite root models. -/
def_wanted finiteRootTower
    [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{u}) (X : Scheme.{u})
    (A : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A)
    (hA : FiniteRootTowers.IsFineSaturated A)
    (R : FiniteModels I D) : GlobalTower I D R

/-- The infinite-root stack has the actual compatible-root fibres and native projections. -/
def_wanted infiniteRootStack
    [∀ (T Z : Scheme.{u}) (f : T ⟶ Z), HasInverseImage f]
    (I : NativeDFImages.{u}) (X : Scheme.{u})
    (A : DeligneFaltingsSheaves.MonoidSheaf X) (D : Structure A)
    (hA : FiniteRootTowers.IsFineSaturated A)
    (R : FiniteModels I D) (K : GlobalTower I D R) : InfiniteModel I D K
