/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.RingHom

/-!
# Scalar compatibility of an algebra representation

Let `R` be a commutative semiring, `E` an `R`-algebra, `M` an `R`-semimodule, and `ρ : E →ₐ[R]
End_R(M)`. The action `e • m=ρ(e)(m)` makes `M` an `E`-semimodule.

Its scalar compatibility is `(r • e) • m=r • (e • m)`, giving the tower `R → E → M`.
-/

@[expose] public section
noncomputable section

universe u v w

namespace AlgHom

variable {R : Type u} {E : Type v} {M : Type w}
  [CommSemiring R] [Semiring E] [Algebra R E]
  [AddCommMonoid M] [Module R M]

/-- Let `R` be a commutative semiring, `E` an `R`-algebra, `M` an `R`-semimodule, and `ρ : E →ₐ[R]
Module.End R M`. For the pulled-back action `e • m=ρ(e)(m)`, `IsScalarTower R E M` holds: `(r
• e) • m=r • (e • m)`. -/
theorem moduleEnd_compHom_isScalarTower (ρ : E →ₐ[R] Module.End R M) :
    letI : Module E M := Module.compHom M ρ.toRingHom
    IsScalarTower R E M := by
  let : Module E M := Module.compHom M ρ.toRingHom
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change ρ (algebraMap R E r) m = r • m
  simpa only [Module.algebraMap_end_apply] using
    congrArg (fun f : Module.End R M => f m) (ρ.commutes r)

end AlgHom
