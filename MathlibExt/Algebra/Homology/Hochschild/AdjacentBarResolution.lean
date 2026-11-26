/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/- The original adjacent bar and augmentation are retained. -/
module

public import MathlibExt.Algebra.Homology.Hochschild.AdjacentBarEnveloping
public import MathlibExt.Algebra.Homology.Hochschild.NonUnital.ConnesBoundary
public import MathlibExt.Algebra.Homology.HomologicalComplex.SplitExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Projective

/-!
# The enveloping bar resolution

The ground-linear b′ contraction makes the augmented enveloping bar
exact for every unital ground algebra. When A is projective over k,
its tensor-power terms are projective over the enveloping algebra,
giving a projective resolution of A. Polynomial algebras with arbitrary
variable types satisfy this projectivity condition.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

universe u v

namespace ModuleCat.Algebra.Hochschild.AdjacentBar

variable (k : Type u) [CommRing k] (A : Type v) [Ring A] [Algebra k A]

/-- The original unit insertion contracts the original ground b-prime complex. -/
def bPrimeGroundContraction :
    Homotopy (𝟙 (NonUnital.bPrimeComplex k A)) 0 :=
  NonUnital.bPrimeContraction k A

/-- Exactness in every original ground b-prime degree follows from that contraction. -/
theorem bPrimeGround_acyclic : (NonUnital.bPrimeComplex k A).Acyclic :=
  HomologicalComplex.acyclic_of_homotopy_id_zero (bPrimeGroundContraction k A)

/-- The original enriched multiplication augmentation is genuinely surjective. -/
theorem envelopingBarAugmentation_surjective : Function.Surjective (envelopingBarAugmentation k A).hom := by
  intro a
  refine ⟨a.down ⊗ₜ[k] PiTensorProduct.tprod k (fun _ : Fin 1 => (1 : A)), ?_⟩
  erw [envelopingBarAugmentation_apply, underlyingBarAugmentationLinear_tprod, mul_one]
  exact ULift.up_down a

/-- The original adjacent boundary and its original multiplication augmentation are exact over A^e. -/
theorem envelopingBarAugmentation_exact :
    (ShortComplex.mk ((envelopingBar k A).d 1 0) (envelopingBarAugmentation k A)
      (envelopingBar_d_augmentation k A)).Exact := by
  let B := NonUnital.bPrimeComplex k A
  have h := bPrimeGround_acyclic k A 1
  rw [HomologicalComplex.exactAt_iff' B 2 1 0 (by simp) (by simp)] at h
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx0 : underlyingBarAugmentationLinear k A x = 0 := by
    have hv := envelopingBarAugmentation_apply k A x
    rw [hx] at hv
    exact congrArg ULift.down hv.symm
  have hx1 : (B.d 1 0).hom x = 0 := by
    apply (underlyingBarZeroCoordinate k A).injective
    change underlyingBarAugmentationLinear k A x = underlyingBarZeroCoordinate k A 0
    rw [hx0, map_zero]
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp h x hx1
  refine ⟨y, ?_⟩
  change ((envelopingBar k A).d 1 0).hom y = x
  erw [envelopingBar_d_apply]
  change (B.d 2 1).hom y = x
  exact hy

/-- Positive exactness over A^e is from the same original ground boundary functions. -/
theorem envelopingBar_exactAt_succ (n : ℕ) : (envelopingBar k A).ExactAt (n + 1) := by
  let B := NonUnital.bPrimeComplex k A
  have h := bPrimeGround_acyclic k A (n + 2)
  rw [HomologicalComplex.exactAt_iff' B (n + 3) (n + 2) (n + 1) (by simp) (by simp)] at h
  rw [HomologicalComplex.exactAt_iff' (envelopingBar k A) (n + 2) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hxB : (B.d (n + 2) (n + 1)).hom x = 0 := by
    have hv := envelopingBar_d_apply k A n x
    change ((envelopingBar k A).d (n + 1) n).hom x = (B.d (n + 2) (n + 1)).hom x at hv
    exact hv.symm.trans hx
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp h x hxB
  refine ⟨y, ?_⟩
  have hv := envelopingBar_d_apply k A (n + 1) y
  change ((envelopingBar k A).d (n + 2) (n + 1)).hom y = (B.d (n + 3) (n + 2)).hom y at hv
  exact hv.trans hy

/-- The original bar augmentation as a native chain map to the original regular target. -/
def envelopingBarAugmentationMap :
    envelopingBar k A ⟶ (ChainComplex.single₀ (ModuleCat.{max u v} (EnvelopingAlgebra k A))).obj
      (regularEnvelopingTarget k A) :=
  (ChainComplex.toSingle₀Equiv (envelopingBar k A) (regularEnvelopingTarget k A)).symm
    ⟨envelopingBarAugmentation k A, envelopingBar_d_augmentation k A⟩

/-- The chain augmentation keeps the original multiplication in degree zero. -/
theorem envelopingBarAugmentationMap_f_zero :
    (envelopingBarAugmentationMap k A).f 0 = envelopingBarAugmentation k A :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

/-- The original bar augmentation is a quasi-isomorphism without ground projectivity. -/
instance envelopingBarAugmentationMap_quasiIso : QuasiIso (envelopingBarAugmentationMap k A) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · constructor
      · change (ShortComplex.mk ((envelopingBar k A).d 1 0) ((envelopingBarAugmentationMap k A).f 0) _).Exact
        simp only [envelopingBarAugmentationMap_f_zero] at ⊢
        exact envelopingBarAugmentation_exact k A
      · change Epi ((envelopingBarAugmentationMap k A).f 0)
        rw [envelopingBarAugmentationMap_f_zero]
        exact (ModuleCat.epi_iff_surjective _).mpr (envelopingBarAugmentation_surjective k A)
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact envelopingBar_exactAt_succ k A n
    · exact ChainComplex.exactAt_succ_single_obj (regularEnvelopingTarget k A) n

/-- The original outer coordinate is linear over the enveloping action. -/
def envelopingBarDegreeEquivBaseChange (n : ℕ) :
    envelopingBarDegree k A n ≃ₗ[EnvelopingAlgebra k A]
      (EnvelopingAlgebra k A) ⊗[k] TensorPower k n A where
  toFun := TensorPower.outerCoordinate k A n
  invFun := (TensorPower.outerCoordinate k A n).symm
  left_inv := (TensorPower.outerCoordinate k A n).symm_apply_apply
  right_inv := (TensorPower.outerCoordinate k A n).apply_symm_apply
  map_add' := (TensorPower.outerCoordinate k A n).map_add
  map_smul' z x := by
    change TensorPower.outerCoordinate k A n
      (TensorPower.outerRepresentation k A n z (x : A ⊗[k] TensorPower k (n + 1) A)) =
      z • TensorPower.outerCoordinate k A n (x : A ⊗[k] TensorPower k (n + 1) A)
    erw [TensorPower.outerRepresentation_apply, LinearEquiv.apply_symm_apply]

/-- Original first, middle and opposite last factors are retained by the base-change coordinate. -/
theorem envelopingBarDegreeEquivBaseChange_tprod (n : ℕ) (a₀ : A) (a : Fin (n + 1) → A) :
    envelopingBarDegreeEquivBaseChange k A n (a₀ ⊗ₜ[k] PiTensorProduct.tprod k a) =
      (a₀ ⊗ₜ[k] MulOpposite.op (a (Fin.last n))) ⊗ₜ[k] PiTensorProduct.tprod k (Fin.init a) :=
  TensorPower.outerCoordinate_tprod k A n a₀ a

/-- Finite native ground tensor powers preserve ground projectivity. -/
theorem tensorPower_projective [Module.Projective k A] (n : ℕ) :
    Module.Projective k (TensorPower k n A) := by
  induction n with
  | zero => exact Module.Projective.of_equiv' (TensorPower.zeroEquiv k A).symm
  | succ n hn =>
    letI : Module.Projective k (TensorPower k n A) := hn
    letI : Module.Projective k (A ⊗[k] TensorPower k n A) :=
      Module.Projective.tensorProduct (R := k) (R₀ := k) (M := A) (N := TensorPower k n A)
    exact Module.Projective.of_equiv' (TensorPower.consEquiv k A n)

/-- The original bar terms are projective over A^e by the original base-change coordinate. -/
theorem envelopingBarDegree_projective [Module.Projective k A] (n : ℕ) :
    Projective ((envelopingBar k A).X n) := by
  letI : Module.Projective k (TensorPower k n A) := tensorPower_projective k A n
  letI : Module.Projective (EnvelopingAlgebra k A)
      ((EnvelopingAlgebra k A) ⊗[k] TensorPower k n A) :=
    Module.Projective.tensorProduct (R := EnvelopingAlgebra k A) (R₀ := k)
      (M := EnvelopingAlgebra k A) (N := TensorPower k n A)
  letI : Module.Projective (EnvelopingAlgebra k A) ((envelopingBar k A).X n) :=
    Module.Projective.of_equiv' (envelopingBarDegreeEquivBaseChange k A n).symm
  infer_instance

/-- The adjacent bar is a projective resolution of the regular enveloping target. -/
def envelopingBarProjectiveResolution [Module.Projective k A] :
    ProjectiveResolution (regularEnvelopingTarget k A) where
  complex := envelopingBar k A
  projective := envelopingBarDegree_projective k A
  π := envelopingBarAugmentationMap k A
  quasiIso := envelopingBarAugmentationMap_quasiIso k A

/-- The constructed resolution keeps exactly the original adjacent bar complex. -/
theorem envelopingBarProjectiveResolution_complex [Module.Projective k A] :
    (envelopingBarProjectiveResolution k A).complex = envelopingBar k A := rfl

/-- The constructed resolution keeps the original multiplication augmentation. -/
theorem envelopingBarProjectiveResolution_π [Module.Projective k A] :
    (envelopingBarProjectiveResolution k A).π = envelopingBarAugmentationMap k A := rfl

/-- For an arbitrary polynomial variable type, polynomial
freeness supplies ground projectivity of the original polynomial bar. -/
def polynomialEnvelopingBarProjectiveResolution (σ : Type v) :
    ProjectiveResolution (regularEnvelopingTarget k (MvPolynomial σ k)) := by
  letI : Module.Projective k (MvPolynomial σ k) := inferInstance
  exact envelopingBarProjectiveResolution k (MvPolynomial σ k)

/-- The canonical polynomial bar resolution retains the original multiplication augmentation. -/
theorem polynomialEnvelopingBarProjectiveResolution_π (σ : Type v) :
    (polynomialEnvelopingBarProjectiveResolution k σ).π =
      envelopingBarAugmentationMap k (MvPolynomial σ k) := rfl

end ModuleCat.Algebra.Hochschild.AdjacentBar
