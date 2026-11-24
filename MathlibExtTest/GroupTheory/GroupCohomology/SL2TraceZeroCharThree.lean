/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.GroupCohomology.SL2TraceZeroCharThree

@[expose] public section

universe v

set_option autoImplicit false

open Matrix MatrixGroups groupCohomology

-- `exactSource` consumer with the original binders.
example {F : Type} [Field F] [Finite F] [CharP F 3]
    (A : Rep F SL(2, F)) (e : A →ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (he_inj : Function.Injective e)
    (he_range : LinearMap.range e = LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F))
    (he_act : ∀ (g : SL(2, F)) (a : A),
      e (A.ρ g a) = (g : Matrix (Fin 2) (Fin 2) F) * e a *
        ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :
    Subsingleton (H1 A) :=
  groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three
    A e he_inj he_range he_act

-- Higher-universe consumer: the field may live in any universe.
example {F : Type v} [Field F] [Finite F] [CharP F 3]
    (A : Rep F SL(2, F)) (e : A →ₗ[F] Matrix (Fin 2) (Fin 2) F)
    (he_inj : Function.Injective e)
    (he_range : LinearMap.range e = LinearMap.ker (Matrix.traceLinearMap (Fin 2) F F))
    (he_act : ∀ (g : SL(2, F)) (a : A),
      e (A.ρ g a) = (g : Matrix (Fin 2) (Fin 2) F) * e a *
        ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F)) :
    Subsingleton (H1 A) :=
  groupCohomology.subsingleton_H1_specialLinearGroup_fin_two_traceZero_of_charP_three
    A e he_inj he_range he_act

-- Boundary: characteristic `3` matters. Over `ZMod 3` itself the field
-- hypothesis package is satisfiable, so this is the smallest case the
-- theorem covers; dropping `CharP F 3` is not asserted here.
example : CharP (ZMod 3) 3 := ZMod.charP 3
