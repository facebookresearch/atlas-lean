/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.CotangentScalarExtension

set_option autoImplicit false

/-! Tests for maps out of scalar extensions of modules of Kähler differentials. -/

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings TensorProduct

namespace MathlibExtTest.CotangentScalarExtension

universe u

section FromExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  {X : ModuleCat.{u} R} {Y : ModuleCat.{u} S} (g : X ⟶ (ModuleCat.restrictScalars f).obj Y)

-- The pure-tensor formula for the `S`-linear map adjoint to `g`.
example (s : S) (x : X) :
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f g (s ⊗ₜ[R,f] x) =
      s • (g x : Y) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul f g s x

-- A single `rw` evaluates the adjoint map on `1 ⊗ x`.
example (x : X) :
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f g ((1 : S) ⊗ₜ[R,f] x) =
      (g x : Y) := by
  rw [ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul, one_smul]

end FromExtendScalars

section KaehlerDifferential

variable {A P S : Type u} [CommRing A] [CommRing P] [CommRing S] [Algebra A P]

/-- `d a = 0` in `Ω[A⁄A]`. -/
theorem D_self (a : A) : KaehlerDifferential.D A A a = 0 :=
  (KaehlerDifferential.D A A).map_algebraMap a

-- A nondegenerate pair: the `S`-linear extension of `ω ↦ 1 ⊗ ω` is the identity of
-- `S ⊗[P] Ω[P⁄A]`, as both agree on every `1 ⊗ d p`.
example (f : P →+* S) :
    ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars f
        ((ModuleCat.extendRestrictScalarsAdj f).unit.app
          (ModuleCat.of P (KaehlerDifferential A P))) =
      𝟙 _ := by
  refine ModuleCat.extendScalars_kaehlerDifferential_hom_ext f _ _ fun p => ?_
  refine (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul f _ 1 _).trans ?_
  exact one_smul S _

-- The pair `(𝟙, 0)`: the scalar extension of `Ω[A⁄A]` is zero, since `d a = 0`.
example (f : A →+* S) :
    IsZero ((ModuleCat.extendScalars f).obj (ModuleCat.of A (KaehlerDifferential A A))) := by
  rw [IsZero.iff_id_eq_zero]
  refine ModuleCat.extendScalars_kaehlerDifferential_hom_ext f _ _ fun a => ?_
  rw [D_self]
  exact TensorProduct.tmul_zero _ _

-- The same for the base change written directly as `C ⊗[A] Ω[A⁄A]`.
example (C : Type u) [CommRing C] [Algebra A C] :
    IsZero (ModuleCat.of C (C ⊗[A] KaehlerDifferential A A)) := by
  rw [IsZero.iff_id_eq_zero]
  refine ModuleCat.baseChange_kaehlerDifferential_hom_ext (A := A) (R := A) _ _ fun a => ?_
  rw [D_self, TensorProduct.tmul_zero, map_zero, map_zero]

-- The same for the iterated scalar extension `C ⊗[B] (B ⊗[A] Ω[A⁄A])`.
example (B C : Type u) [CommRing B] [CommRing C] [Algebra A B] (g : B →+* C) :
    IsZero ((ModuleCat.extendScalars g).obj
      (ModuleCat.of B (B ⊗[A] KaehlerDifferential A A))) := by
  rw [IsZero.iff_id_eq_zero]
  refine ModuleCat.extendScalars_baseChange_kaehlerDifferential_hom_ext (A := A) (P := A) g
    _ _ fun a => ?_
  rw [D_self, TensorProduct.tmul_zero]
  exact TensorProduct.tmul_zero _ _

end KaehlerDifferential

end MathlibExtTest.CotangentScalarExtension
