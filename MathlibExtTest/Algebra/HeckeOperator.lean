/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.HeckeOperator

@[expose] public section

open MulAction AbstractHeckeOperator
open scoped Pointwise

noncomputable example (G : Type*) [Group G] (U V : Subgroup G) (g : G)
    (h : (QuotientGroup.mk '' (U * ({g} : Set G)) : Set (G ⧸ V)).Finite)
    (A : Type*) [AddCommMonoid A] [DistribMulAction G A] :
    fixedPoints V A →+ fixedPoints U A :=
  HeckeOperator_addMonoidHom h

noncomputable example (G : Type*) [Group G] (U V : Subgroup G) (g : G)
    (h : (QuotientGroup.mk '' (U * ({g} : Set G)) : Set (G ⧸ V)).Finite)
    (A : Type*) [AddCommMonoid A] [DistribMulAction G A]
    (R : Type*) [Ring R] [Module R A] [SMulCommClass G R A] :
    fixedPoints V A →ₗ[R] fixedPoints U A :=
  HeckeOperator (R := R) g U V h
