/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

public import MathlibExt.Algebra.Lie.BaseChange
public import MathlibExt.Algebra.Lie.BaseChange.UniversalProperty
public import MathlibExt.Algebra.Lie.UniversalEnveloping.PrimitiveLift
public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Scalar extension of enveloping bialgebras

Let S be a commutative R-algebra and L any R-Lie algebra. Put U = U_R(L), SL = S ⊗[R] L, B = S
⊗[R] U and V = U_S(SL). The coefficient tensor of the Lie inclusion sends s ⊗ x to s ⊗ ι_R(x),
which is primitive in the S-bialgebra B.

The forward algebra comparison Φ : B → V sends s ⊗ ι_R(x) to ι_S(s ⊗ x). Its inverse Ψ : V → B
is the bialgebra lift of the primitive-valued coefficient map. Their generator formulas give
inverse maps and an S-bialgebra equivalence B ≃ V. This equivalence is natural in R-Lie maps
and retains the original R-action on L. The scalar and Lie-carrier universes are independent.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace UniversalEnvelopingAlgebra

universe u v w w'

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  (L : Type w) [LieRing L] [LieAlgebra R L]

local notation "U" => UniversalEnvelopingAlgebra R L
local notation "SL" => S ⊗[R] L
local notation "B" => S ⊗[R] U
local notation "V" => UniversalEnvelopingAlgebra S SL
local notation "P" => Bialgebra.primitiveLieSubalgebra S B

private theorem one_tmul_ι_mem (x : L) : (1 : S) ⊗ₜ[R] ι R x ∈ P := by
  apply (Bialgebra.mem_primitiveLieSubalgebra S B).2
  apply (Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul (R := S) (A := B)).2
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, comul_ι]
  simp only [TensorProduct.tmul_add, map_add,
    TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul,
    Algebra.TensorProduct.one_def]

private theorem tensor_ι_mem (z : SL) :
    TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z ∈ P := by
  refine z.inductionOn ?_ ?_
  · intro s x
    have h := P.smul_mem s (one_tmul_ι_mem R S L x)
    simpa only [TensorProduct.AlgebraTensorModule.lTensor_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  · intro z z' hz hz'
    simpa only [map_add] using P.add_mem hz hz'

private theorem tensor_ι_lie (z z' : SL) :
    TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap ⁅z, z'⁆ =
      TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z *
          TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z' -
        TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z' *
          TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z := by
  letI : LieRing B := LieRing.ofAssociativeRing
  letI : LieAlgebra R B := LieAlgebra.ofAssociativeAlgebra
  letI : LieAlgebra S B := LieAlgebra.ofAssociativeAlgebra
  let f : L →ₗ⁅R⁆ B :=
    ((Algebra.TensorProduct.includeRight : U →ₐ[R] B) : U →ₗ⁅R⁆ B).comp (ι R)
  let ψ : SL →ₗ⁅S⁆ B := LieHom.liftBaseChange R S f
  have hψ : ψ.toLinearMap =
      TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s x
    change LieHom.liftBaseChange R S f (s ⊗ₜ[R] x) = s ⊗ₜ[R] ι R x
    rw [LieHom.liftBaseChange_tmul]
    change s • ((1 : S) ⊗ₜ[R] ι R x) = s ⊗ₜ[R] ι R x
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h := ψ.map_lie z z'
  simp only [LieRing.of_associative_ring_bracket] at h
  change ψ.toLinearMap ⁅z, z'⁆ =
    ψ.toLinearMap z * ψ.toLinearMap z' - ψ.toLinearMap z' * ψ.toLinearMap z at h
  simpa only [hψ] using h

/-- Primitive-valued coefficient extension of the Lie inclusion.

For U = U_R(L) and B = S ⊗[R] U, the S-linear extension of ι_R sends S ⊗[R] L into the
primitive Lie subalgebra of B. It gives an S-Lie map with value s ⊗ x ↦ s ⊗ ι_R(x). -/
def baseChangePrimitive : SL →ₗ⁅S⁆ P where
  toLinearMap :=
    (TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap).codRestrict
      P.toSubmodule (by intro z; exact tensor_ι_mem R S L z)
  map_lie' := by
    intro z z'
    apply Subtype.ext
    change TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap ⁅z, z'⁆ =
      TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z *
          TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z' -
        TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z' *
          TensorProduct.AlgebraTensorModule.lTensor S S (ι R : L →ₗ⁅R⁆ U).toLinearMap z
    exact tensor_ι_lie R S L z z'

/-- Value of the primitive coefficient map on a pure tensor.

For s ∈ S and x ∈ L, baseChangePrimitive R S L applied to s ⊗[R] x, viewed in S ⊗[R] U_R(L),
is s ⊗[R] ι_R(x). -/
@[simp]
theorem baseChangePrimitive_tmul (s : S) (x : L) :
    (baseChangePrimitive R S L (s ⊗ₜ[R] x) : B) = s ⊗ₜ[R] ι R x := rfl

/-- Forward algebra comparison for enveloping scalar extension.

For a commutative R-algebra S and R-Lie algebra L, the Lie scalar-extension and enveloping
universal properties define Φ : S ⊗[R] U_R(L) →ₐ[S] U_S(S ⊗[R] L). It takes coefficient
tensors of generators to the corresponding S-Lie generators. -/
def baseChangeTo : B →ₐ[S] V :=
  letI : Algebra R V := Algebra.restrictScalars R S V
  letI : IsScalarTower R S V := IsScalarTower.restrictScalars R S V
  AlgHom.liftEquiv R S U V
    (lift R ((LieHom.liftBaseChangeEquiv R S L V).symm (ι S : SL →ₗ⁅S⁆ V)))

/-- Generator formula for the forward enveloping comparison.

The forward algebra map Φ satisfies Φ(s ⊗[R] ι_R(x)) = ι_S(s ⊗[R] x) for s ∈ S and x ∈ L. -/
@[simp]
theorem baseChangeTo_tmul_ι (s : S) (x : L) :
    baseChangeTo R S L (s ⊗ₜ[R] ι R x) = ι S (s ⊗ₜ[R] x) := by
  letI : Algebra R V := Algebra.restrictScalars R S V
  letI : IsScalarTower R S V := IsScalarTower.restrictScalars R S V
  simp only [baseChangeTo, AlgHom.liftEquiv_tmul, lift_ι_apply,
    LieHom.liftBaseChangeEquiv_symm_apply]
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    using (map_smul (ι S : SL →ₗ⁅S⁆ V) s ((1 : S) ⊗ₜ[R] x)).symm

/-- Inverse bialgebra comparison for enveloping scalar extension.

Lift the primitive S-Lie map S ⊗[R] L → P_S(S ⊗[R] U_R(L)) to a bialgebra map Ψ : U_S(S ⊗[R]
L) →ₐc[S] S ⊗[R] U_R(L). Its generator values are the coefficient tensors s ⊗ ι_R(x). -/
def baseChangeFrom : V →ₐc[S] B := liftPrimitive S (baseChangePrimitive R S L)

/-- Generator formula for the inverse enveloping comparison.

The bialgebra map Ψ satisfies Ψ(ι_S(s ⊗[R] x)) = s ⊗[R] ι_R(x) for s ∈ S and x ∈ L. -/
@[simp]
theorem baseChangeFrom_ι_tmul (s : S) (x : L) :
    baseChangeFrom R S L (ι S (s ⊗ₜ[R] x)) = s ⊗ₜ[R] ι R x := by
  rw [baseChangeFrom, liftPrimitive_ι, baseChangePrimitive_tmul]

private theorem baseChangeFrom_comp_to :
    (baseChangeFrom R S L).toAlgHom.comp (baseChangeTo R S L) = AlgHom.id S B := by
  apply (AlgHom.liftEquiv R S U B).symm.injective
  apply hom_ext
  apply LieHom.ext
  intro x
  change baseChangeFrom R S L (baseChangeTo R S L ((1 : S) ⊗ₜ[R] ι R x)) =
    (1 : S) ⊗ₜ[R] ι R x
  rw [baseChangeTo_tmul_ι, baseChangeFrom_ι_tmul]

private theorem baseChangeTo_comp_from :
    (baseChangeTo R S L).comp (baseChangeFrom R S L).toAlgHom = AlgHom.id S V := by
  apply hom_ext
  apply LieHom.ext
  intro z
  change baseChangeTo R S L (baseChangeFrom R S L (ι S z)) = ι S z
  refine z.inductionOn ?_ ?_
  · intro s x
    rw [baseChangeFrom_ι_tmul, baseChangeTo_tmul_ι]
  · intro z z' hz hz'
    simpa only [map_add] using congrArg₂ (· + ·) hz hz'

/-- Bialgebra equivalence between two enveloping scalar extensions.

For arbitrary R-Lie algebra L and commutative R-algebra S, the inverse comparisons Φ and Ψ
define S ⊗[R] U_R(L) ≃ₐc[S] U_S(S ⊗[R] L). Their inverse laws follow from the two universal
properties and the generator formulas. -/
def baseChangeEquiv : B ≃ₐc[S] V :=
  (BialgEquiv.ofAlgEquiv
    (AlgEquiv.ofAlgHom (baseChangeFrom R S L).toAlgHom (baseChangeTo R S L)
      (by exact baseChangeFrom_comp_to R S L) (by exact baseChangeTo_comp_from R S L))
    (by exact (baseChangeFrom R S L).counitAlgHom_comp)
    (by exact (baseChangeFrom R S L).map_comp_comulAlgHom)).symm

/-- Forward generator value of the enveloping bialgebra equivalence.

The equivalence S ⊗[R] U_R(L) ≃ₐc[S] U_S(S ⊗[R] L) sends s ⊗[R] ι_R(x) to ι_S(s ⊗[R] x). -/
@[simp]
theorem baseChangeEquiv_tmul_ι (s : S) (x : L) :
    baseChangeEquiv R S L (s ⊗ₜ[R] ι R x) = ι S (s ⊗ₜ[R] x) :=
  baseChangeTo_tmul_ι R S L s x

/-- Inverse generator value of the enveloping bialgebra equivalence.

The inverse equivalence sends ι_S(s ⊗[R] x) to s ⊗[R] ι_R(x), preserving the left coefficient
factor. -/
@[simp]
theorem baseChangeEquiv_symm_ι_tmul (s : S) (x : L) :
    (baseChangeEquiv R S L).symm (ι S (s ⊗ₜ[R] x)) = s ⊗ₜ[R] ι R x :=
  baseChangeFrom_ι_tmul R S L s x

/-- Naturality of the enveloping bialgebra base-change equivalence.

For an R-Lie map f : L → L', the S-bialgebra maps satisfy U_S(baseChange f) ∘ Φ_L = Φ_{L'} ∘
(id_S ⊗ U_R(f)). The coefficient algebra is unchanged and the Lie map is extended by the
S-linear tensor map. -/
theorem baseChangeEquiv_naturality
    {L' : Type w'} [LieRing L'] [LieAlgebra R L'] (f : L →ₗ⁅R⁆ L') :
    (mapBialgHom S (LieHom.baseChange R S f)).comp (baseChangeEquiv R S L).toBialgHom =
      (baseChangeEquiv R S L').toBialgHom.comp
        (Bialgebra.TensorProduct.map (BialgHom.id S S) (mapBialgHom R f)) := by
  letI : Algebra R (UniversalEnvelopingAlgebra S (S ⊗[R] L')) :=
    Algebra.restrictScalars R S _
  letI : IsScalarTower R S (UniversalEnvelopingAlgebra S (S ⊗[R] L')) :=
    IsScalarTower.restrictScalars R S _
  apply BialgHom.coe_toAlgHom_injective
  apply (AlgHom.liftEquiv R S U (UniversalEnvelopingAlgebra S (S ⊗[R] L'))).symm.injective
  apply hom_ext
  apply LieHom.ext
  intro x
  change mapBialgHom S (LieHom.baseChange R S f)
      (baseChangeEquiv R S L ((1 : S) ⊗ₜ[R] ι R x)) =
    baseChangeEquiv R S L' ((1 : S) ⊗ₜ[R] mapBialgHom R f (ι R x))
  rw [baseChangeEquiv_tmul_ι, mapBialgHom_apply, map_ι, LieHom.baseChange_tmul,
    mapBialgHom_apply, map_ι, baseChangeEquiv_tmul_ι]

end UniversalEnvelopingAlgebra
