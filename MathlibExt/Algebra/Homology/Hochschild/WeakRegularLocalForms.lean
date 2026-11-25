/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.KoszulComplexConormalComparison
public import MathlibExt.RingTheory.Ideal.FlatCotangentBaseChange
public import MathlibExt.LinearAlgebra.ExteriorPower.SurjectiveScalarCoefficients
public import MathlibExt.RingTheory.Kaehler.EtaleFormsBaseChange.Basic
public import MathlibExt.RingTheory.Localization.AtPrimeSurjective
public import Mathlib.RingTheory.Localization.Algebra

/-!
# Local diagonal tensor homology and Kähler forms

Let `A` be a commutative `k`-algebra and let `p` be a prime of `A`. Localize
`A ⊗[k] A` at the inverse image of `p` under multiplication, and localize
`A` at `p`. A finite ordered weakly regular family generating the kernel
of the induced local multiplication map gives a Koszul resolution of the
support local ring.

For a coefficient module with compatible ground, algebra and local scalar
actions, tensor homology of this resolution is identified with coefficient
exterior powers of relative Kähler differentials of the support local ring.
Flat localization identifies the conormal modules, multiplication describes
the diagonal action on Kähler differentials, and formally étale base change
identifies the relative forms. The comparison includes degree zero and
preserves the coefficient carrier and its given actions.

The rings may be non-Noetherian. The coefficient module need not be finite
or flat, and no finite-presentation or factorial-invertibility assumption
is required.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace ModuleCat.Algebra.Hochschild.WeakRegularLocalDiagonal

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]
  (p : Ideal A) [p.IsPrime]

local notation "E" => A ⊗[k] A
local notation "μ" => (Algebra.TensorProduct.lmul' («S» := A) k : E →ₐ[k] A)
local notation "J" => KaehlerDifferential.ideal k A
local notation "Ω" => KaehlerDifferential k A
local notation "P" => p.comap (AlgHom.toRingHom μ)
local notation "S" => Localization.AtPrime P
local notation "B" => Localization.AtPrime p

/-- The enveloping action on the Kähler module through the two tensor factors. -/
local instance originalDifferentialEnvelopingModule :
    Module (A ⊗[k] A) (KaehlerDifferential k A) :=
  inferInstance

/-- Scalar multiplication from the original native enveloping module. -/
local instance originalDifferentialEnvelopingSMul :
    SMul (A ⊗[k] A) (KaehlerDifferential k A) :=
  (originalDifferentialEnvelopingModule k A).toSMul

/-- The original local diagonal map. -/
def localDiagonalHom : S →+* B :=
  Localization.localRingHom P p (AlgHom.toRingHom μ) rfl

/-- The ambient local ring acts on the support local ring through the actual localized diagonal homomorphism. -/
local instance localDiagonalAlgebra : Algebra S B := (localDiagonalHom k A p).toAlgebra
/-- The original base algebra structure on the support localization through `k → A → B`. -/
local instance baseSupportAlgebra : Algebra k B :=
  inferInstanceAs (Algebra k (Localization.AtPrime p))
local instance baseSupportTower : IsScalarTower k A B :=
  inferInstanceAs (IsScalarTower k A (Localization.AtPrime p))
/-- The original left `A`-algebra structure on the ambient localization. -/
local instance leftAmbientAlgebra : Algebra A S :=
  inferInstanceAs (Algebra A
    (Localization.AtPrime (p.comap (AlgHom.toRingHom μ))))
/-- The ambient localization as a module over the enveloping algebra. -/
local instance originalAmbientEnvelopingModule : Module E S := inferInstance

local instance ambientFlat : Module.Flat E S := IsLocalization.flat S (P).primeCompl
local instance supportFormallyEtale : Algebra.FormallyEtale A B :=
  Algebra.FormallyEtale.of_isLocalization p.primeCompl

local notation "L" => RingHom.ker (localDiagonalHom k A p)

/-- Multiplication is surjective through its actual first-factor unit section. -/
theorem diagonalMultiplication_surjective : Function.Surjective μ := by
  intro a
  exact ⟨a ⊗ₜ[k] (1 : A), by rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]⟩

/-- The actual canonical map of the two local rings is surjective. -/
theorem localDiagonalHom_surjective : Function.Surjective (localDiagonalHom k A p) :=
  Localization.localRingHom_surjective (AlgHom.toRingHom μ) (diagonalMultiplication_surjective k A) p

/-- The original diagonal denominators map onto precisely the original support denominators. -/
theorem diagonalPrimeCompl_map : Submonoid.map (AlgHom.toRingHom μ) (P).primeCompl = p.primeCompl := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    refine ⟨a ⊗ₜ[k] (1 : A), ?_, ?_⟩
    · change μ (a ⊗ₜ[k] (1 : A)) ∉ p
      rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]
      exact ha
    · change μ (a ⊗ₜ[k] (1 : A)) = a
      rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

/-- Native localization carries the actual global diagonal kernel to the actual local kernel. -/
theorem localDiagonalKernel_eq_map : L = (J).map (algebraMap E S) := by
  have h := IsLocalization.ker_map («S» := S) B (AlgHom.toRingHom μ) (diagonalPrimeCompl_map k A p)
  have hJ : RingHom.ker (AlgHom.toRingHom μ) = J := by
    ext x
    change μ x = 0 ↔ μ x = 0
    rfl
  have h' := h.trans (congrArg (Ideal.map (algebraMap E S)) hJ)
  simpa only [localDiagonalHom, Localization.localRingHom] using h'

/-- The actual conormal base-change equivalence has the literal local diagonal kernel as target. -/
def localDiagonalCotangentEquiv : S ⊗[E] Ω ≃ₗ[S] (Ideal.Cotangent L) :=
  (Ideal.flatCotangentBaseChangeEquiv E S J).trans
    (Ideal.Cotangent.equivOfEq ((J).map (algebraMap E S)) L
      (localDiagonalKernel_eq_map k A p).symm)

/-- The localized original diagonal difference, retained as an actual local kernel element. -/
def localDifferentialGenerator (a : A) : L :=
  ⟨algebraMap E S ((1 : A) ⊗ₜ[k] a - a ⊗ₜ[k] (1 : A)), by
    rw [localDiagonalKernel_eq_map]
    exact Ideal.mem_map_of_mem (algebraMap E S)
      (KaehlerDifferential.one_smul_sub_smul_one_mem_ideal k a)⟩

/-- The conormal map pins the sign and value of every original differential. -/
theorem localDiagonalCotangentEquiv_D (a : A) :
    localDiagonalCotangentEquiv k A p
      ((1 : S) ⊗ₜ[E] KaehlerDifferential.D k A a) =
      Ideal.toCotangent L (localDifferentialGenerator k A p a) := by
  rw [KaehlerDifferential.D_apply, localDiagonalCotangentEquiv]
  change (Ideal.Cotangent.equivOfEq ((J).map (algebraMap E S)) L
      (localDiagonalKernel_eq_map k A p).symm)
    (Ideal.flatCotangentBaseChangeEquiv E S J
      ((1 : S) ⊗ₜ[E] Ideal.toCotangent J
        ⟨(1 : A) ⊗ₜ[k] a - a ⊗ₜ[k] (1 : A),
          KaehlerDifferential.one_smul_sub_smul_one_mem_ideal k a⟩)) = _
  rw [Ideal.flatCotangentBaseChangeEquiv_tmul_toCotangent, one_smul,
    Ideal.Cotangent.equivOfEq_toCotangent]
  apply congrArg (Ideal.toCotangent L)
  apply Subtype.ext
  rfl

private theorem diagonal_smul_differentials (x : E) (ω : Ω) : x • ω = μ x • ω := by
  have hx : x - μ x ⊗ₜ[k] (1 : A) ∈ J := by
    change μ (x - μ x ⊗ₜ[k] (1 : A)) = 0
    rw [map_sub, Algebra.TensorProduct.lmul'_apply_tmul, mul_one, sub_self]
  have hz := Ideal.Cotangent.smul_eq_zero_of_mem hx ω
  change (x - μ x ⊗ₜ[k] (1 : A)) • ω = 0 at hz
  rw [sub_smul] at hz
  exact (sub_eq_zero.mp hz).trans (IsScalarTower.algebraMap_smul E (μ x) ω)

/-- Multiplication gives the diagonal enveloping algebra structure on `A`. -/
local instance diagonalAlgebra : Algebra E A := (AlgHom.toRingHom μ).toAlgebra

local instance differentialDiagonalTower : IsScalarTower E A Ω :=
  IsScalarTower.of_algebraMap_smul (fun x ω => (diagonal_smul_differentials k A x ω).symm)

/-- The original left algebra map followed by the actual local diagonal is the original support localization. -/
theorem localDiagonalHom_left_algebraMap (a : A) :
    localDiagonalHom k A p (algebraMap A S a) = algebraMap A B a := by
  change localDiagonalHom k A p (algebraMap E S (a ⊗ₜ[k] (1 : A))) = _
  rw [localDiagonalHom, Localization.localRingHom_to_map]
  change algebraMap A B (μ (a ⊗ₜ[k] (1 : A))) = algebraMap A B a
  rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

section Coefficients

variable (M : Type w) [AddCommGroup M] [Module A M]
  [Module (Localization.AtPrime p) M]
  [Module (Localization.AtPrime (p.comap
    (Algebra.TensorProduct.lmul' («S» := A) k : A ⊗[k] A →ₐ[k] A).toRingHom)) M]
  [IsScalarTower A (Localization.AtPrime p) M]
  [IsScalarTower (Localization.AtPrime (p.comap
    (Algebra.TensorProduct.lmul' («S» := A) k : A ⊗[k] A →ₐ[k] A).toRingHom))
    (Localization.AtPrime p) M]

/-- The enveloping action on a coefficient module obtained by restriction along multiplication. -/
local instance (priority := 10) diagonalCoefficientModule :
    Module E M := Module.compHom M (AlgHom.toRingHom μ)
local instance diagonalCoefficientTower : IsScalarTower E A M where
  smul_assoc x a m := by
    change (μ x * a) • m = μ x • (a • m)
    exact mul_smul _ _ _

local instance ambientCoefficientTower : IsScalarTower E S M :=
  IsScalarTower.of_algebraMap_smul (R := E) (A := S) (M := M) (fun (x : E) (m : M) => by
    calc
      algebraMap E S x • m = localDiagonalHom k A p (algebraMap E S x) • m :=
        (IsScalarTower.algebraMap_smul B (algebraMap E S x) m).symm
      _ = algebraMap A B (μ x) • m := by
        rw [localDiagonalHom, Localization.localRingHom_to_map]
        rfl
      _ = μ x • m := IsScalarTower.algebraMap_smul B (μ x) m
      _ = x • m := rfl)

local instance leftCoefficientTower : IsScalarTower A S M :=
  IsScalarTower.of_algebraMap_smul (R := A) (A := S) (M := M) (fun (a : A) (m : M) => by
    calc
      algebraMap A S a • m = localDiagonalHom k A p (algebraMap A S a) • m :=
        (IsScalarTower.algebraMap_smul B (algebraMap A S a) m).symm
      _ = algebraMap A B a • m := by rw [localDiagonalHom_left_algebraMap]
      _ = a • m := IsScalarTower.algebraMap_smul B a m)

local instance leftCoefficientComm : SMulCommClass A S M where
  smul_comm a s m := by
    rw [← IsScalarTower.algebraMap_smul S a (s • m),
      ← IsScalarTower.algebraMap_smul S a m, smul_smul, smul_smul, mul_comm]

local instance globalFormsSupportTower (q : ℕ) :
    IsScalarTower S B (M ⊗[A] KaehlerDifferential.DeRham.Forms k A q) where
  smul_assoc s b x := by
    induction x using TensorProduct.inductionOn with
    | tmul m ω =>
      change ((s • b) • m) ⊗ₜ[A] ω = (s • (b • m)) ⊗ₜ[A] ω
      rw [smul_assoc]
    | add x y hx hy => simp only [smul_add, hx, hy]

local instance localFormsCoefficientComm : SMulCommClass B S M where
  smul_comm b s m := by
    rw [← IsScalarTower.algebraMap_smul B s (b • m),
      ← IsScalarTower.algebraMap_smul B s m, smul_smul, smul_smul, mul_comm]

/-- The original ambient scalar acts on coefficient-valued local forms through the original coefficient module. -/
local instance localFormsAmbientModule (q : ℕ) :
    Module S (M ⊗[B] KaehlerDifferential.DeRham.Forms k B q) :=
  inferInstance

local instance localFormsAmbientTower (q : ℕ) :
    IsScalarTower S B (M ⊗[B] KaehlerDifferential.DeRham.Forms k B q) where
  smul_assoc s b x := by
    induction x using TensorProduct.inductionOn with
    | tmul m ω =>
      change ((s • b) • m) ⊗ₜ[B] ω = (s • (b • m)) ⊗ₜ[B] ω
      rw [smul_assoc]
    | add x y hx hy => simp only [smul_add, hx, hy]

omit [Module A M] [IsScalarTower A B M] in
/-- The native tensor scalar is the original coefficient scalar, and equals
restriction through the actual local diagonal by the given original tower. -/
theorem localFormsAmbient_smul_tmul (q : ℕ) (s : S) (m : M)
    (ω : KaehlerDifferential.DeRham.Forms k B q) :
    s • (m ⊗ₜ[B] ω) = (algebraMap S B s • m) ⊗ₜ[B] ω := by
  change (s • m) ⊗ₜ[B] ω = (algebraMap S B s • m) ⊗ₜ[B] ω
  rw [IsScalarTower.algebraMap_smul B s m]

/-- Existing formally étale forms base change preserves the original relative base k and original coefficient action. -/
def coefficientLocalizedFormsEquiv (q : ℕ) :
    M ⊗[A] KaehlerDifferential.DeRham.Forms k A q ≃ₗ[S]
      M ⊗[B] KaehlerDifferential.DeRham.Forms k B q :=
  (((TensorProduct.AlgebraTensorModule.cancelBaseChange A B B M
      (KaehlerDifferential.DeRham.Forms k A q)).symm).trans
    (TensorProduct.congr (LinearEquiv.refl B M)
      (KaehlerDifferential.DeRham.tensorFormsEquivOfFormallyEtale k A B q))).restrictScalars S

variable {r : ℕ}
  (c : Fin r → Localization.AtPrime (p.comap
    (AlgHom.toRingHom (Algebra.TensorProduct.lmul' («S» := A) k : A ⊗[k] A →ₐ[k] A))))
  (hker : RingHom.ker (localDiagonalHom k A p) = Ideal.span (Set.range c))

local notation "Ic" => KoszulComplex.ideal S (Fin r → S) (KoszulComplex.familyFunctional S c)
local notation "Q" => S ⧸ Ic

/-- The literal local coordinate quotient is the original support local ring,
through its actual canonical diagonal map. -/
def localQuotientAlgEquiv : Q ≃ₐ[S] B := by
  let g : S →ₐ[S] B := Algebra.ofId S B
  have hg : Function.Surjective g := localDiagonalHom_surjective k A p
  have hI : RingHom.ker g.toRingHom = Ic :=
    hker.trans (KoszulComplex.familyIdeal_eq_span S c).symm
  exact (Ideal.quotientEquivAlgOfEq S hI.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)

/-- The actual quotient action is earned from the displayed kernel equality. -/
abbrev quotientCoefficientModule : Module Q M :=
  Module.compHom M (localQuotientAlgEquiv k A p c hker).toRingHom

omit [Module A M] [IsScalarTower A B M] in
/-- The earned quotient action preserves the original ambient coefficient action. -/
theorem quotientCoefficientTower :
    letI := quotientCoefficientModule k A p M c hker
    IsScalarTower S Q M := by
  let := quotientCoefficientModule k A p M c hker
  exact IsScalarTower.of_algebraMap_smul (R := S) (A := Q) (M := M)
    (fun (s : S) (m : M) => by
      change localQuotientAlgEquiv k A p c hker (algebraMap S Q s) • m = s • m
      rw [(localQuotientAlgEquiv k A p c hker).commutes]
      exact IsScalarTower.algebraMap_smul B s m)

omit [Module A M] [IsScalarTower A B M] in
/-- The earned quotient action commutes with the original ambient scalar
because both act through the actual commutative quotient. -/
theorem quotientCoefficientComm :
    letI := quotientCoefficientModule k A p M c hker
    SMulCommClass Q S M := by
  let := quotientCoefficientModule k A p M c hker
  let := quotientCoefficientTower k A p M c hker
  exact ⟨fun q s m => by
    rw [← IsScalarTower.algebraMap_smul Q s (q • m),
      ← IsScalarTower.algebraMap_smul Q s m, smul_smul, smul_smul, mul_comm]⟩

/-- The original local conormal coefficient forms are identified
with the original support-local relative Kähler forms. The comparison
includes degree zero and retains every coefficient carrier. -/
def localConormalCoefficientFormsEquiv (q : ℕ) :
    letI := quotientCoefficientModule k A p M c hker
    letI := quotientCoefficientTower k A p M c hker
    letI := quotientCoefficientComm k A p M c hker
    M ⊗[Q] (⋀[Q]^q (Ideal.Cotangent Ic)) ≃ₗ[S]
      M ⊗[B] KaehlerDifferential.DeRham.Forms k B q := by
  letI := quotientCoefficientModule k A p M c hker
  letI := quotientCoefficientTower k A p M c hker
  letI := quotientCoefficientComm k A p M c hker
  letI : Module E S := originalAmbientEnvelopingModule k A p
  letI : Module E Ω := originalDifferentialEnvelopingModule k A
  letI : Module S (S ⊗[E] Ω) :=
    @TensorProduct.leftModule E S _ _ S Ω _ _
      (Semiring.toModule (R := S)) (originalAmbientEnvelopingModule k A p)
      (originalDifferentialEnvelopingModule k A)
      (Algebra.to_smulCommClass (R := E) (A := S))
  let hQ : Function.Surjective (algebraMap S Q) := Ideal.Quotient.mk_surjective
  let eStart :=
    (exteriorPower.surjectiveScalarCoefficientEquiv S Q M (Ideal.Cotangent Ic) hQ q).symm.restrictScalars S
  let eCot : S ⊗[E] Ω ≃ₗ[S] (Ideal.Cotangent Ic) :=
    (localDiagonalCotangentEquiv k A p).trans
      (Ideal.Cotangent.equivOfEq L Ic
        (hker.trans (KoszulComplex.familyIdeal_eq_span S c).symm))
  let eCotCoef : M ⊗[S] (⋀[S]^q (Ideal.Cotangent Ic)) ≃ₗ[S]
      M ⊗[S] (⋀[S]^q (S ⊗[E] Ω)) :=
    TensorProduct.congr (LinearEquiv.refl S M)
      (exteriorPower.mapEquiv S (Ideal.Cotangent Ic) q eCot.symm)
  let eExterior : M ⊗[S] (⋀[S]^q (S ⊗[E] Ω)) ≃ₗ[S]
      M ⊗[S] (S ⊗[E] (⋀[E]^q Ω)) :=
    TensorProduct.congr (LinearEquiv.refl S M)
      (exteriorPower.baseChangeEquiv E S Ω q).symm
  let eCancel := TensorProduct.AlgebraTensorModule.cancelBaseChange E S S M (⋀[E]^q Ω)
  let hμ : Function.Surjective (algebraMap E A) := diagonalMultiplication_surjective k A
  let eDiagonal := exteriorPower.surjectiveScalarCoefficientEquivWithActor E A M Ω hμ S q
  exact eStart.trans (eCotCoef.trans
    (eExterior.trans (eCancel.trans (eDiagonal.trans (coefficientLocalizedFormsEquiv k A p M q)))))

/-- The weak-regular local diagonal resolution computes the actual
original derived tensor functor in exterior Kähler form coordinates.
The ordinary coefficient modules need no finiteness or flatness assumption. -/
def localWeakRegularDerivedFormsIso
    (hc : RingTheory.Sequence.IsWeaklyRegular S (List.ofFn c)) (q : ℕ) :
    ((KoszulComplex.coefficientTensorFunctor S (ModuleCat.of S M)).leftDerived q).obj
        (ModuleCat.of S B) ≅
      ModuleCat.of S (M ⊗[B] KaehlerDifferential.DeRham.Forms k B q) := by
  letI := quotientCoefficientModule k A p M c hker
  letI := quotientCoefficientTower k A p M c hker
  letI := quotientCoefficientComm k A p M c hker
  exact (((KoszulComplex.coefficientTensorFunctor S (ModuleCat.of S M)).leftDerived q).mapIso
    (localQuotientAlgEquiv k A p c hker).toLinearEquiv.toModuleIso).symm ≪≫
      KoszulComplex.weakRegularConormalDerivedTensorIso S c (ModuleCat.of S M) hc q ≪≫
        (localConormalCoefficientFormsEquiv k A p M c hker q).toModuleIso

end Coefficients

end ModuleCat.Algebra.Hochschild.WeakRegularLocalDiagonal
