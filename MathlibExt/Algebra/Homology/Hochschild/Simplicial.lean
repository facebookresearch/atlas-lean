/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.Basic

/-!
# Simplicial degeneracies in Hochschild coefficient coordinates

Let k be a commutative ring, A an associative k-algebra and M a compatible A-bimodule. In
degree n, Hochschild chains are M ⊗[k] A⊗n. The degeneracy sᵢ retains the coefficient and
inserts 1_A at tensor position i, for 0≤i≤n. The chain isomorphism with the coefficient bar
uses its degreewise tensor coordinate isomorphisms.

See J.-L. Loday, Cyclic Homology, 2nd ed., Chapter 1, for the Hochschild simplicial module.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Simplicial ModuleCat.Algebra

universe u v w

namespace ModuleCat.Algebra.Hochschild

attribute [local instance] uliftSMulCommClass

variable (k : Type u) (A : Type v) (M : Type w)
  [CommRing k] [Ring A] [Algebra k A] [AddCommGroup M]
  [Module A M] [Module Aᵐᵒᵖ M] [Module k M]
  [SMulCommClass A Aᵐᵒᵖ M] [SMulCommClass k A M]
  [SMulCommClass k Aᵐᵒᵖ M] [IsScalarTower k A M] [IsScalarTower k Aᵐᵒᵖ M]

/-- The unit-inserting degeneracy of a Hochschild tensor word.

For a commutative ring k, an associative k-algebra A, a compatible A-bimodule M and i ∈
Fin(n+1), sᵢ maps M ⊗ A⊗n to M ⊗ A⊗(n+1), retaining M and inserting 1_A at position i. -/
def degeneracy (n : ℕ) (i : Fin (n + 1)) :
    chainLevel k A M n ⟶ chainLevel k A M (n + 1) :=
  (coefficientBarObjIso k A M n).inv ≫ (coefficientBar k A M).σ i ≫
    (coefficientBarObjIso k A M (n + 1)).hom

/-- The pure-tensor formula for a Hochschild degeneracy.

For a commutative ring k, an associative k-algebra A, a compatible A-bimodule M and a : Fin n
→ A, sᵢ(m ⊗ tprod(a)) = m ⊗ tprod(hochschildInsertOne(i,a)). -/
theorem degeneracy_tprod (n : ℕ) (i : Fin (n + 1)) (m : M) (a : Fin n → A) :
    (degeneracy k A M n i).hom (m ⊗ₜ[k] PiTensorProduct.tprod k a) =
      m ⊗ₜ[k] PiTensorProduct.tprod k (hochschildInsertOne i a) := by
  change TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k (n + 1) A))
      ((barObjIso k A (ULift.{max u v w} M) (n + 1)).hom.hom
        (((barK k A (ULift.{max u v w} M)).σ i).hom
          ((barObjIso k A (ULift.{max u v w} M) n).inv.hom
            (ULift.up m ⊗ₜ[k] PiTensorProduct.tprod k a)))) = _
  exact (congrArg
    (TensorProduct.congr
      (ULift.moduleEquiv : ULift.{max u v w} M ≃ₗ[k] M)
      (LinearEquiv.refl k (TensorPower k (n + 1) A)))
    (bar_degen_insert k A (ULift.{max u v w} M) n i (ULift.up m) a)).trans (by rfl)

/-- The forward coefficient-bar comparison in degree n.

For a commutative ring k, an associative k-algebra A and a compatible A-bimodule M, the nth
component of chainComplexIso.hom is the inverse coefficientBarObjIso tensor-coordinate map. -/
theorem chainComplexIso_hom_f (n : ℕ) :
    (chainComplexIso k A M).hom.f n = (coefficientBarObjIso k A M n).inv := rfl

/-- The inverse coefficient-bar comparison in degree n.

For a commutative ring k, an associative k-algebra A and a compatible A-bimodule M, the nth
component of chainComplexIso.inv is coefficientBarObjIso, recovering the coefficient bar from
its tensor coordinates. -/
theorem chainComplexIso_inv_f (n : ℕ) :
    (chainComplexIso k A M).inv.f n = (coefficientBarObjIso k A M n).hom := rfl

end ModuleCat.Algebra.Hochschild
