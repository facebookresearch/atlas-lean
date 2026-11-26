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
# Extended differentials in an algebra pushout

Let k → K and P → Q form a pushout square of commutative algebras, with the two k-actions on Q
compatible. Let P → A → B and P → Q → B be compatible coefficient towers. Then tensor-tower
cancellation and the Kähler pushout equivalence give a B-linear isomorphism
B⊗[A](A⊗[P]Ω_{P/k}) ≃ B⊗[Q]Ω_{Q/K}.

The map sends b⊗(a⊗d p) to (b·algebraMap(A,B)(a))⊗d(algebraMap(P,Q)(p)). Its inverse sends
b⊗d(algebraMap(P,Q)(p)) to b⊗(1_A⊗d p). The forward map equals the scalar extension of the
structural coefficient ring-square map. Only the structural k,K,P,Q square is required to be a
pushout; all six ring universes are independent.
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

/-- Structural coefficient ring square from compatible algebra maps.

For the given compatible algebra towers, use algebraMap(k,K), algebraMap(P,Q) and
algebraMap(A,B) as the three row maps. The scalar-tower equations give the two commuting
squares. -/
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

/-- Coefficient differential map aligned with an ambient algebra action.

For a coefficient square s with s.coefficient = algebraMap(A,B), its scalar-extended map can
be viewed using the given A-algebra structure on B. The equality identifies the induced and
ambient coefficient actions. -/
def coefficientBaseChangeMapOfRingSquareOfAlgebra
    (s : CoefficientRingSquare k K P Q A B) (hs : s.coefficient = algebraMap A B) :
    B ⊗[A] Coefficient k P A →ₗ[B] Coefficient K Q B := by
  have hAlg : s.coefficient.toAlgebra = ‹Algebra A B› :=
    (congrArg RingHom.toAlgebra hs).trans toAlgebra_algebraMap
  exact hAlg ▸ coefficientBaseChangeMapOfRingSquare s

/-- Generator formula after coefficient-action alignment.

If s.coefficient = algebraMap(A,B), the aligned B-linear map sends b⊗[A](a⊗[P]d p) to
(b·s.coefficient(a))⊗[Q]d(s.algebra(p)). -/
theorem coefficientBaseChangeMapOfRingSquareOfAlgebra_tmul_D
    (s : CoefficientRingSquare k K P Q A B) (hs : s.coefficient = algebraMap A B)
    (b : B) (a : A) (p : P) :
    coefficientBaseChangeMapOfRingSquareOfAlgebra k K P Q A B s hs
        (b ⊗ₜ[A] (a ⊗ₜ[P] D k P p)) =
      (b * s.coefficient a) ⊗ₜ[Q] D K Q (s.algebra p) := by
  have hAlg : s.coefficient.toAlgebra = ‹Algebra A B› :=
    (congrArg RingHom.toAlgebra hs).trans toAlgebra_algebraMap
  exact hAlg ▸ coefficientBaseChangeMapOfRingSquare_tmul_D s b a p

/-- Coefficient Kähler equivalence from a structural algebra pushout.

For the pushout square k,K,P,Q and compatible coefficient towers through A,B, tensor
cancellation and Ω_{Q/K} ≃ Q⊗[P]Ω_{P/k} give B⊗[A](A⊗[P]Ω_{P/k}) ≃ₗ[B] B⊗[Q]Ω_{Q/K}. -/
def coefficientPushoutEquiv :
    B ⊗[A] Coefficient k P A ≃ₗ[B] Coefficient K Q B :=
  (TensorProduct.AlgebraTensorModule.cancelBaseChange
      P A B B (KaehlerDifferential k P)).trans
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange
      P Q B B (KaehlerDifferential k P)).symm.trans
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
        (KaehlerDifferential.tensorKaehlerEquiv k K P Q)))

/-- Forward generator value of the coefficient pushout equivalence.

The equivalence sends b⊗[A](a⊗[P]d_{P/k}p) to
(b·algebraMap(A,B)(a))⊗[Q]d_{Q/K}(algebraMap(P,Q)(p)). -/
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

/-- Inverse generator value of the coefficient pushout equivalence.

For p ∈ P, the inverse sends b⊗[Q]d_{Q/K}(algebraMap(P,Q)(p)) to b⊗[A](1_A⊗[P]d_{P/k}p). -/
@[simp]
theorem coefficientPushoutEquiv_symm_tmul_D (b : B) (p : P) :
    (coefficientPushoutEquiv k K P Q A B).symm
        (b ⊗ₜ[Q] KaehlerDifferential.D K Q (algebraMap P Q p)) =
      b ⊗ₜ[A] ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p) := by
  have h := (coefficientPushoutEquiv k K P Q A B).symm_apply_apply
    (b ⊗ₜ[A] ((1 : A) ⊗ₜ[P] KaehlerDifferential.D k P p))
  simpa only [coefficientPushoutEquiv_tmul_D, map_one, mul_one] using h

/-- Generator agreement with the structural coefficient-square map.

On b⊗[A](a⊗[P]d p), the coefficient pushout equivalence equals the scalar-extended map of
coefficientPushoutRingSquare, aligned with the ambient A-action on B. -/
theorem coefficientPushoutEquiv_tmul_D_eq_ringSquare (b : B) (a : A) (p : P) :
    coefficientPushoutEquiv k K P Q A B
        (b ⊗ₜ[A] (a ⊗ₜ[P] KaehlerDifferential.D k P p)) =
      coefficientBaseChangeMapOfRingSquareOfAlgebra k K P Q A B
        (coefficientPushoutRingSquare k K P Q A B) rfl
        (b ⊗ₜ[A] (a ⊗ₜ[P] KaehlerDifferential.D k P p)) := by
  exact (coefficientPushoutEquiv_tmul_D k K P Q A B b a p).trans
    (coefficientBaseChangeMapOfRingSquareOfAlgebra_tmul_D k K P Q A B
      (coefficientPushoutRingSquare k K P Q A B) rfl b a p).symm

/-- Linear-map agreement of the coefficient pushout comparison.

The B-linear map underlying coefficientPushoutEquiv equals
coefficientBaseChangeMapOfRingSquareOfAlgebra for the structural coefficient square. Equality
is determined by the differential tensor generators. -/
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

/-- Bijectivity of structural coefficient differential base change.

Under the algebra pushout k,K,P,Q and compatible coefficient towers, the scalar-extended
differential map of coefficientPushoutRingSquare is bijective. Its value agrees with
coefficientPushoutEquiv. -/
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
