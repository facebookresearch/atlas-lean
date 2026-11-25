/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Kaehler.CoefficientRingSquare
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Extended differentials in an actual algebra pushout

The square k → K, P → Q is an actual native algebra pushout.  The coefficient
square P → A, Q → B is any compatible original square.  Cancelling the actual
coefficient tensor twice and using the native Kähler pushout equivalence gives
the B-linear equivalence

  B ⊗[A] (A ⊗[P] Ω[P/k]) ≃ B ⊗[Q] Ω[Q/K].

The coefficient square need not be a pushout, and no coefficient flatness,
polynomial structure, finite generation, or module projectivity is used.  All
six ring universes are independent.  The forward map agrees with the existing
original CoefficientRingSquare map, rather than taking that agreement as data.

Native elaboration and kernel checks are unexecuted for this source proposal.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe uk uK uP uQ uA uB

namespace KaehlerDifferential

variable (k : Type uk) (K : Type uK) (P : Type uP) (Q : Type uQ)
  (A : Type uA) (B : Type uB)
  [CommRing k] [CommRing K] [CommRing P] [CommRing Q] [CommRing A] [CommRing B]
  [Algebra k K] [Algebra k P] [Algebra k Q] [Algebra K Q] [Algebra P Q]
  [IsScalarTower k K Q] [IsScalarTower k P Q]
  [Algebra P A] [Algebra P B] [Algebra A B] [Algebra Q B]
  [IsScalarTower P A B] [IsScalarTower P Q B]

attribute [local instance] SMulCommClass.of_commMonoid

/-- The original coefficient ring square supplied by the actual structural maps. -/
def coefficientPushoutRingSquare : CoefficientRingSquare k K P Q A B where
  ground := algebraMap k K
  algebra := algebraMap P Q
  coefficient := algebraMap A B
  ground_commutes := by
    rw [← IsScalarTower.algebraMap_eq k P Q,
      ← IsScalarTower.algebraMap_eq k K Q]
  augmentation_commutes := by
    rw [← IsScalarTower.algebraMap_eq P A B,
      ← IsScalarTower.algebraMap_eq P Q B]

variable [Algebra.IsPushout k K P Q]

/-- The existing ring-square map in the original coefficient-module action.
The native algebra-instance equality supplies the source alignment. -/
def coefficientBaseChangeMapOfRingSquareOfAlgebra
    (s : CoefficientRingSquare k K P Q A B) (hs : s.coefficient = algebraMap A B) :
    B ⊗[A] Coefficient k P A →ₗ[B] Coefficient K Q B := by
  have hAlg : s.coefficient.toAlgebra = ‹Algebra A B› :=
    (congrArg RingHom.toAlgebra hs).trans toAlgebra_algebraMap
  exact hAlg ▸ coefficientBaseChangeMapOfRingSquare s

/-- Source alignment preserves the actual native coefficient and differential formula. -/
theorem coefficientBaseChangeMapOfRingSquareOfAlgebra_tmul_D
    (s : CoefficientRingSquare k K P Q A B) (hs : s.coefficient = algebraMap A B)
    (b : B) (a : A) (p : P) :
    coefficientBaseChangeMapOfRingSquareOfAlgebra k K P Q A B s hs
        (b ⊗ₜ[A] (a ⊗ₜ[P] D k P p)) =
      (b * s.coefficient a) ⊗ₜ[Q] D K Q (s.algebra p) := by
  have hAlg : s.coefficient.toAlgebra = ‹Algebra A B› :=
    (congrArg RingHom.toAlgebra hs).trans toAlgebra_algebraMap
  exact hAlg ▸ coefficientBaseChangeMapOfRingSquare_tmul_D s b a p

/-- An actual pushout earns the full coefficient linear equivalence.
Only the structural algebra pushout is assumed; no desired comparison is input. -/
def coefficientPushoutEquiv :
    B ⊗[A] Coefficient k P A ≃ₗ[B] Coefficient K Q B :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange
      P A B B (KaehlerDifferential k P)).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
      P Q B B (KaehlerDifferential k P)).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
        (KaehlerDifferential.tensorKaehlerEquiv k K P Q)))

/-- Its literal map on original differential tensors, with both coefficient factors. -/
@[simp]
theorem coefficientPushoutEquiv_tmul_D (b : B) (a : A) (p : P) :
    coefficientPushoutEquiv k K P Q A B
        (b ⊗ₜ[A] (a ⊗ₜ[P] KaehlerDifferential.D k P p)) =
      (b * algebraMap A B a) ⊗ₜ[Q]
        KaehlerDifferential.D K Q (algebraMap P Q p) := by
  simp only [coefficientPushoutEquiv, LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul,
    LinearEquiv.refl_apply, KaehlerDifferential.tensorKaehlerEquiv_tmul_D,
    one_smul]
  rw [Algebra.smul_def, mul_comm]

/-- The actual inverse retains the original differential class. -/
@[simp]
theorem coefficientPushoutEquiv_symm_tmul_D (b : B) (p : P) :
    (coefficientPushoutEquiv k K P Q A B).symm
        (b ⊗ₜ[Q] KaehlerDifferential.D K Q (algebraMap P Q p)) =
      b ⊗ₜ[A] ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p) := by
  have h := (coefficientPushoutEquiv k K P Q A B).symm_apply_apply
    (b ⊗ₜ[A] ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p))
  simpa only [coefficientPushoutEquiv_tmul_D, map_one, mul_one] using h

/-- On the literal generating tensors, the native equivalence is the existing
base-change map of the original coefficient ring square. -/
theorem coefficientPushoutEquiv_tmul_D_eq_ringSquare (b : B) (a : A) (p : P) :
    coefficientPushoutEquiv k K P Q A B
        (b ⊗ₜ[A] (a ⊗ₜ[P] KaehlerDifferential.D k P p)) =
      coefficientBaseChangeMapOfRingSquareOfAlgebra k K P Q A B
        (coefficientPushoutRingSquare k K P Q A B) rfl
        (b ⊗ₜ[A] (a ⊗ₜ[P] KaehlerDifferential.D k P p)) := by
  exact (coefficientPushoutEquiv_tmul_D k K P Q A B b a p).trans
    (coefficientBaseChangeMapOfRingSquareOfAlgebra_tmul_D k K P Q A B
      (coefficientPushoutRingSquare k K P Q A B) rfl b a p).symm

/-- Equality with the existing actual ring-square map, earned by its universal generators. -/
theorem coefficientPushoutEquiv_toLinearMap_eq_ringSquare :
    (coefficientPushoutEquiv k K P Q A B).toLinearMap =
      coefficientBaseChangeMapOfRingSquareOfAlgebra k K P Q A B
        (coefficientPushoutRingSquare k K P Q A B) rfl := by
  letI : Algebra k A :=
    ((algebraMap P A).comp (algebraMap k P)).toAlgebra
  letI : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' rfl
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  let f : Coefficient k P A →ₗ[A] Coefficient K Q B :=
    (coefficientPushoutEquiv k K P Q A B).toLinearMap.restrictScalars A ∘ₗ
      TensorProduct.mk A B (Coefficient k P A) b
  let g : Coefficient k P A →ₗ[A] Coefficient K Q B :=
    (coefficientBaseChangeMapOfRingSquareOfAlgebra k K P Q A B
      (coefficientPushoutRingSquare k K P Q A B) rfl).restrictScalars A ∘ₗ
        TensorProduct.mk A B (Coefficient k P A) b
  have hfg : f = g := by
    apply coefficient_hom_ext k P A
    intro p
    exact coefficientPushoutEquiv_tmul_D_eq_ringSquare k K P Q A B b 1 p
  exact LinearMap.congr_fun hfg x

/-- The original ring-square map is bijective when its algebra square is a pushout. -/
theorem coefficientBaseChangeMapOfRingSquare_bijective_of_pushout :
    Function.Bijective (coefficientBaseChangeMapOfRingSquare
      (coefficientPushoutRingSquare k K P Q A B)) := by
  let φ : A →+* B := algebraMap A B
  have hPAB : algebraMap P B = φ.comp (algebraMap P A) :=
    IsScalarTower.algebraMap_eq P A B
  letI : Algebra A B := φ.toAlgebra
  letI : IsScalarTower P A B := IsScalarTower.of_algebraMap_eq' hPAB
  have h : Function.Bijective
      (coefficientBaseChangeMapOfRingSquareOfAlgebra k K P Q A B
        (coefficientPushoutRingSquare k K P Q A B) rfl) := by
    rw [← coefficientPushoutEquiv_toLinearMap_eq_ringSquare]
    exact (coefficientPushoutEquiv k K P Q A B).bijective
  exact h

end KaehlerDifferential

end
