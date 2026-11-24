/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.PolynomialDiagonalCoefficients
public import MathlibExt.LinearAlgebra.ExteriorPower.BalancedBaseChange
public import MathlibExt.RingTheory.Kaehler.PolynomialExterior

/-!
# polynomial diagonal coefficients in exterior coordinates

The original free enveloping coordinate module is the scalar extension of
the original ground generator module. Exterior base change and balanced cancellation identify every diagonal coefficient degree with
the original coefficient tensor the ground exterior power.

For arbitrary bimodules the differential keeps the original right-minus-left
variable action. Only the symmetric action makes it zero. The
resulting symmetric Hochschild homology comparison with polynomial
differential forms uses the diagonal resolution and arbitrary
coefficient modules over arbitrary commutative ground rings.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct
open MulOpposite

universe u v w

namespace ModuleCat.Algebra.Hochschild.PolynomialDiagonal

variable (k : Type u) [CommRing k] (σ : Type v)

local notation "A" => MvPolynomial σ k
local notation "E" => MvPolynomial.PolynomialEnveloping k σ
local notation "V" => (σ →₀ k)
local notation "VE" => (σ →₀ E)

section Bimodule

variable (M : Type w) [AddCommGroup M] [Module k M]
  [Module (MvPolynomial σ k) M] [Module (MvPolynomial σ k)ᵐᵒᵖ M]
  [SMulCommClass (MvPolynomial σ k) (MvPolynomial σ k)ᵐᵒᵖ M]
  [SMulCommClass k (MvPolynomial σ k) M] [SMulCommClass k (MvPolynomial σ k)ᵐᵒᵖ M]
  [IsScalarTower k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k)ᵐᵒᵖ M]

/-- Actual diagonal coefficient degrees have the original free exterior generator
coordinates, retaining arbitrary original bimodule coefficients. -/
def coefficientFreeExteriorEquiv (n : ℕ) :
    (coefficientComplex k σ M).X n ≃ₗ[k] M ⊗[k] (⋀[k]^n V) := by
  letI nativeRight : Module Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI nativeTower : IsScalarTower k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarTower k A M
  letI nativeComm : SMulCommClass k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarComm k A M
  letI groundSource : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
  letI groundTarget : Module k (⋀[E]^n (E ⊗[k] V)) := Module.compHom _ (algebraMap k E)
  letI : IsScalarTower k E (⋀[E]^n VE) := IsScalarTower.of_compHom k E (⋀[E]^n VE)
  letI : IsScalarTower k E (⋀[E]^n (E ⊗[k] V)) := IsScalarTower.of_compHom k E (⋀[E]^n (E ⊗[k] V))
  letI nativeCompat : LinearMap.CompatibleSMul (⋀[E]^n VE) (⋀[E]^n (E ⊗[k] V)) k E :=
    ⟨fun f c z => f.map_smul (algebraMap k E c) z⟩
  let e : (⋀[E]^n VE) ≃ₗ[E] (⋀[E]^n (E ⊗[k] V)) :=
    exteriorPower.mapEquiv E VE n (Finsupp.scalarExtensionCoordinates k E σ).symm
  let g : (⋀[E]^n VE) ≃ₗ[k] (⋀[E]^n (E ⊗[k] V)) :=
    @LinearEquiv.restrictScalars k E (⋀[E]^n VE) (⋀[E]^n (E ⊗[k] V))
      inferInstance inferInstance inferInstance inferInstance groundSource groundTarget
      inferInstance inferInstance nativeCompat e
  exact (TensorProduct.Balanced.congr (LinearEquiv.refl k M) g
    (fun _ _ => rfl) (fun r z => e.map_smul r z)).trans
      (exteriorPower.balancedBaseChangeEquiv k E M V n)

/-- Each original enveloping exterior scalar is absorbed by the original right
enveloping action while every original ground variable is preserved. -/
theorem coefficientFreeExteriorEquiv_mk_smul_basis
    (n : ℕ) (m : M) (e : E) (f : Fin n → σ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
    coefficientFreeExteriorEquiv k σ M n
      (TensorProduct.Balanced.mk k E M (⋀[E]^n VE) m
        (e • exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E)))) =
      (op e • m) ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k)) := by
  letI nativeRight : Module Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI nativeTower : IsScalarTower k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarTower k A M
  letI nativeComm : SMulCommClass k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarComm k A M
  letI groundSource : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
  letI groundTarget : Module k (⋀[E]^n (E ⊗[k] V)) := Module.compHom _ (algebraMap k E)
  letI : IsScalarTower k E (⋀[E]^n VE) := IsScalarTower.of_compHom k E (⋀[E]^n VE)
  letI : IsScalarTower k E (⋀[E]^n (E ⊗[k] V)) := IsScalarTower.of_compHom k E (⋀[E]^n (E ⊗[k] V))
  letI nativeCompat : LinearMap.CompatibleSMul (⋀[E]^n VE) (⋀[E]^n (E ⊗[k] V)) k E :=
    ⟨fun f c z => f.map_smul (algebraMap k E c) z⟩
  let p : (⋀[E]^n VE) ≃ₗ[E] (⋀[E]^n (E ⊗[k] V)) :=
    exteriorPower.mapEquiv E VE n (Finsupp.scalarExtensionCoordinates k E σ).symm
  let g : (⋀[E]^n VE) ≃ₗ[k] (⋀[E]^n (E ⊗[k] V)) :=
    @LinearEquiv.restrictScalars k E (⋀[E]^n VE) (⋀[E]^n (E ⊗[k] V))
      inferInstance inferInstance inferInstance inferInstance groundSource groundTarget
      inferInstance inferInstance nativeCompat p
  let B : TensorProduct.Balanced k E M (⋀[E]^n VE) ≃ₗ[k]
      TensorProduct.Balanced k E M (⋀[E]^n (E ⊗[k] V)) :=
    TensorProduct.Balanced.congr (LinearEquiv.refl k M) g
      (fun _ _ => rfl) (fun r z => p.map_smul r z)
  let T := exteriorPower.balancedBaseChangeEquiv k E M V n
  let a : ⋀[E]^n VE := e • exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E))
  let a' : ⋀[E]^n (E ⊗[k] V) :=
    e • exteriorPower.ιMulti E n (fun j => (1 : E) ⊗ₜ[k] Finsupp.single (f j) (1 : k))
  have hdef : coefficientFreeExteriorEquiv k σ M n
      (TensorProduct.Balanced.mk k E M (⋀[E]^n VE) m a) =
    T (B (TensorProduct.Balanced.mk k E M (⋀[E]^n VE) m a)) := rfl
  have hB : B (TensorProduct.Balanced.mk k E M (⋀[E]^n VE) m a) =
      TensorProduct.Balanced.mk k E M (⋀[E]^n (E ⊗[k] V)) m (g a) :=
    TensorProduct.Balanced.congr_mk (LinearEquiv.refl k M) g
      (fun _ _ => rfl) (fun r z => p.map_smul r z) m a
  have hw : p (exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E))) =
      exteriorPower.ιMulti E n (fun j => (1 : E) ⊗ₜ[k] Finsupp.single (f j) (1 : k)) := by
    have h := exteriorPower.mapEquiv_apply_ιMulti E VE n (N := E ⊗[k] V)
      (Finsupp.scalarExtensionCoordinates k E σ).symm (fun j => Finsupp.single (f j) (1 : E))
    refine h.trans ?_
    apply congrArg (exteriorPower.ιMulti E n)
    funext j
    exact Finsupp.scalarExtensionCoordinates_symm_single k E σ (f j) (1 : E)
  have hp : g a = p a := rfl
  have ha : g a = a' :=
    hp.trans ((p.map_smul e (exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E)))).trans
      (congrArg (fun z : ⋀[E]^n (E ⊗[k] V) => e • z) hw))
  have hmk := congrArg (TensorProduct.Balanced.mk k E M (⋀[E]^n (E ⊗[k] V)) m) ha
  have hT : T (TensorProduct.Balanced.mk k E M (⋀[E]^n (E ⊗[k] V)) m a') =
      (op e • m) ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k)) :=
    exteriorPower.balancedBaseChangeEquiv_mk_smul_ιMulti k E M V n m e
      (fun j => Finsupp.single (f j) (1 : k))
  exact hdef.trans ((congrArg T (hB.trans hmk)).trans hT)

/-- Original unscaled variable wedges retain the original coefficient unchanged. -/
theorem coefficientFreeExteriorEquiv_mk_basis (n : ℕ) (m : M) (f : Fin n → σ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
    coefficientFreeExteriorEquiv k σ M n
      (TensorProduct.Balanced.mk k E M (⋀[E]^n VE) m
        (exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E)))) =
      m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k)) := by
  simpa only [op_one, one_smul] using
    coefficientFreeExteriorEquiv_mk_smul_basis k σ M n m (1 : E) f

/-- The inverse free coordinate recovers the original balanced variable wedge. -/
theorem coefficientFreeExteriorEquiv_symm_tmul_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    letI := EnvelopingCoefficient.rightEnvelopingModule k A M
    letI : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
    (coefficientFreeExteriorEquiv k σ M n).symm
      (m ⊗ₜ[k] exteriorPower.ιMulti k n (fun j => Finsupp.single (f j) (1 : k))) =
      TensorProduct.Balanced.mk k E M (⋀[E]^n VE) m
        (exteriorPower.ιMulti E n (fun j => Finsupp.single (f j) (1 : E))) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
  apply (coefficientFreeExteriorEquiv k σ M n).injective
  rw [LinearEquiv.apply_symm_apply, coefficientFreeExteriorEquiv_mk_basis]

/-- The original variable differential in free exterior coordinates has the right-minus-left coefficient actions, with all original deletion signs. -/
theorem coefficientFreeExteriorEquiv_boundary_basis
    (n : ℕ) (m : M) (f : Fin (n + 1) → σ) :
    coefficientFreeExteriorEquiv k σ M n
      (((coefficientComplex k σ M).d (n + 1) n).hom
        ((coefficientFreeExteriorEquiv k σ M (n + 1)).symm
          (m ⊗ₜ[k] exteriorPower.ιMulti k (n + 1)
            (fun j => Finsupp.single (f j) (1 : k))))) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
        ((op (MvPolynomial.X (f j) : A) • m - (MvPolynomial.X (f j) : A) • m) ⊗ₜ[k]
          exteriorPower.ιMulti k n (fun q => Finsupp.single (f (j.succAbove q)) (1 : k))) := by
  letI := EnvelopingCoefficient.rightEnvelopingModule k A M
  letI : IsScalarTower k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarTower k A M
  letI : SMulCommClass k Eᵐᵒᵖ M := EnvelopingCoefficient.rightEnvelopingScalarComm k A M
  letI : Module k (⋀[E]^(n + 1) VE) := Module.compHom _ (algebraMap k E)
  letI : Module k (⋀[E]^n VE) := Module.compHom _ (algebraMap k E)
  let z : (coefficientComplex k σ M).X (n + 1) :=
    TensorProduct.Balanced.mk k E M (⋀[E]^(n + 1) VE) m
      (exteriorPower.ιMulti E (n + 1) (fun j => Finsupp.single (f j) (1 : E)))
  have hz : (coefficientFreeExteriorEquiv k σ M (n + 1)).symm
      (m ⊗ₜ[k] exteriorPower.ιMulti k (n + 1) (fun j => Finsupp.single (f j) (1 : k))) = z :=
    coefficientFreeExteriorEquiv_symm_tmul_basis k σ M (n + 1) m f
  let s (j : Fin (n + 1)) : (coefficientComplex k σ M).X n :=
    TensorProduct.Balanced.mk k E M (⋀[E]^n VE)
      (op (((-1 : E) ^ j.val) * MvPolynomial.diagonalDifference k σ (f j)) • m)
      (exteriorPower.ιMulti E n (fun q => Finsupp.single (f (j.succAbove q)) (1 : E)))
  have hd : ((coefficientComplex k σ M).d (n + 1) n).hom z = ∑ j, s j :=
    coefficientComplex_d_mk_basis k σ M n m f
  have htransport := congrArg (coefficientFreeExteriorEquiv k σ M n)
    ((congrArg ((coefficientComplex k σ M).d (n + 1) n).hom hz).trans hd)
  have hsum : coefficientFreeExteriorEquiv k σ M n (∑ j, s j) =
      ∑ j, coefficientFreeExteriorEquiv k σ M n (s j) :=
    map_sum (coefficientFreeExteriorEquiv k σ M n) s Finset.univ
  have hterms : (∑ j, coefficientFreeExteriorEquiv k σ M n (s j)) =
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
        ((op (MvPolynomial.X (f j) : A) • m - (MvPolynomial.X (f j) : A) • m) ⊗ₜ[k]
          exteriorPower.ιMulti k n (fun q => Finsupp.single (f (j.succAbove q)) (1 : k))) := by
    apply Finset.sum_congr rfl
    intro j _
    have hm : coefficientFreeExteriorEquiv k σ M n (s j) =
        (op (((-1 : E) ^ j.val) * MvPolynomial.diagonalDifference k σ (f j)) • m) ⊗ₜ[k]
          exteriorPower.ιMulti k n (fun q => Finsupp.single (f (j.succAbove q)) (1 : k)) :=
      coefficientFreeExteriorEquiv_mk_basis k σ M n
        (op (((-1 : E) ^ j.val) * MvPolynomial.diagonalDifference k σ (f j)) • m)
        (fun q => f (j.succAbove q))
    have hs : op (((-1 : E) ^ j.val) * MvPolynomial.diagonalDifference k σ (f j)) • m =
        (-1 : ℤ) ^ j.val • (op (MvPolynomial.diagonalDifference k σ (f j)) • m) := by
      rw [MulOpposite.op_mul, mul_smul, ← smul_comm]
      simpa only [MulOpposite.op_pow, MulOpposite.op_neg, op_one,
        Int.cast_pow, Int.cast_neg, Int.cast_one] using
        Int.cast_smul_eq_zsmul (R := Eᵐᵒᵖ) ((-1 : ℤ) ^ j.val)
          (op (MvPolynomial.diagonalDifference k σ (f j)) • m)
    have hc := hs.trans (congrArg (fun b : M => (-1 : ℤ) ^ j.val • b)
      (rightDiagonalDifference_action k σ M (f j) m))
    let t : M →ₗ[k] M ⊗[k] (⋀[k]^n V) :=
      (TensorProduct.mk k M (⋀[k]^n V)).flip
        (exteriorPower.ιMulti k n (fun q => Finsupp.single (f (j.succAbove q)) (1 : k)))
    exact hm.trans ((congrArg t hc).trans (map_zsmul t ((-1 : ℤ) ^ j.val)
      (op (MvPolynomial.X (f j) : A) • m - (MvPolynomial.X (f j) : A) • m)))
  exact htransport.trans (hsum.trans hterms)

end Bimodule

section Symmetric

variable (M : Type w) [AddCommGroup M] [Module k M] [Module (MvPolynomial σ k) M]
  [SMulCommClass k (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]

/-- The symmetric coefficient degree has the canonical original free exterior coordinates. -/
def symmetricFreeExteriorEquiv (n : ℕ) :
    (symmetricCoefficientComplex k σ M).X n ≃ₗ[k] M ⊗[k] (⋀[k]^n V) := by
  letI := Symmetric.opModule A M
  letI := Symmetric.actionsComm A M
  letI := Symmetric.kOpComm k A M
  letI := Symmetric.kOpTower k A M
  exact coefficientFreeExteriorEquiv k σ M n

/-- The polynomial diagonal resolution computes all original symmetric
coefficient Hochschild homology in the original free exterior model. -/
def symmetricHochschildFreeExteriorEquiv (n : ℕ) :
    (Symmetric.chainComplex k A M).homology n ≃ₗ[k] M ⊗[k] (⋀[k]^n V) :=
  (symmetricCoefficientHomologyIsoDegree k σ M n).toLinearEquiv.trans
    (symmetricFreeExteriorEquiv k σ M n)

/-- Canonical polynomial cotangent coordinates identify the computed homology
with the original coefficient-first exterior differential-form module. -/
def symmetricHochschildDifferentialFormEquiv (n : ℕ) :
    (Symmetric.chainComplex k A M).homology n ≃ₗ[k]
      M ⊗[A] (⋀[A]^n (KaehlerDifferential k A)) :=
  (symmetricHochschildFreeExteriorEquiv k σ M n).trans
    ((KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n).restrictScalars k)

/-- The coefficient diagonal class has its independently specified original
free exterior coordinates. -/
def symmetricHochschildFreeExteriorClass (n : ℕ) :
    M ⊗[k] (⋀[k]^n V) →ₗ[k] (Symmetric.chainComplex k A M).homology n :=
  (symmetricHochschildClassFromDiagonal k σ M n).hom.comp
    (symmetricFreeExteriorEquiv k σ M n).symm.toLinearMap


/-- The diagonal class is detected by its independently specified
original free exterior element. -/
theorem symmetricHochschildFreeExteriorClass_coordinates (n : ℕ)
    (x : M ⊗[k] (⋀[k]^n V)) :
    symmetricHochschildFreeExteriorEquiv k σ M n
      (symmetricHochschildFreeExteriorClass k σ M n x) = x := by
  let z : (symmetricCoefficientComplex k σ M).X n := (symmetricFreeExteriorEquiv k σ M n).symm x
  have hc : (symmetricCoefficientHomologyIsoDegree k σ M n).hom.hom
      ((symmetricHochschildClassFromDiagonal k σ M n).hom z) = z :=
    (ModuleCat.comp_apply (symmetricHochschildClassFromDiagonal k σ M n)
      (symmetricCoefficientHomologyIsoDegree k σ M n).hom z).symm.trans
        ((ConcreteCategory.congr_hom (symmetricHochschildClassFromDiagonal_coordinates k σ M n) z).trans
          (ModuleCat.id_apply ((symmetricCoefficientComplex k σ M).X n) z))
  have he : symmetricHochschildFreeExteriorEquiv k σ M n
      (symmetricHochschildFreeExteriorClass k σ M n x) =
    symmetricFreeExteriorEquiv k σ M n
      ((symmetricCoefficientHomologyIsoDegree k σ M n).hom.hom
        ((symmetricHochschildClassFromDiagonal k σ M n).hom z)) := rfl
  exact he.trans ((congrArg (symmetricFreeExteriorEquiv k σ M n) hc).trans
    ((symmetricFreeExteriorEquiv k σ M n).apply_symm_apply x))

/-- The original variable class gives its coefficient differential word
under the full polynomial diagonal homology comparison. -/
theorem symmetricHochschildFreeExteriorClass_differentialForm_basis
    (n : ℕ) (m : M) (f : Fin n → σ) :
    symmetricHochschildDifferentialFormEquiv k σ M n
      (symmetricHochschildFreeExteriorClass k σ M n
        (m ⊗ₜ[k] exteriorPower.ιMulti k n
          (fun j => Finsupp.single (f j) (1 : k)))) =
      m ⊗ₜ[A] exteriorPower.ιMulti A n
        (fun j => KaehlerDifferential.D k A (MvPolynomial.X (f j))) := by
  change KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv k σ M n
    (symmetricHochschildFreeExteriorEquiv k σ M n
      (symmetricHochschildFreeExteriorClass k σ M n _)) = _
  rw [symmetricHochschildFreeExteriorClass_coordinates,
    KaehlerDifferential.mvPolynomialCoefficientExteriorEquiv_tmul_basis]

end Symmetric

end ModuleCat.Algebra.Hochschild.PolynomialDiagonal
