/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SmoothKrullDim

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

example {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (n : ℕ) [SmoothOfRelativeDimension n f] : topologicalKrullDim X ≤ n :=
  AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_le f n

example (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : ringKrullDim R ≤ ringKrullDim S :=
  ringKrullDim_le_of_faithfullyFlat R S

example {K : Type*} [Field K] {B : Type*} [CommRing B] [Algebra K B] (n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension n K B] : ringKrullDim B ≤ n :=
  ringKrullDim_le_of_isStandardSmoothOfRelativeDimension (K := K) (B := B) n
