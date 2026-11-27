/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Algebra.Algebra.NonUnitalHom

/-!
# The canonical nonunital normed-ring completion

Pinned Mathlib installs multiplication on `UniformSpace.Completion A` only
when `A` is unital.  This module gives the same dense bilinear extension for a
`NonUnitalSeminormedRing` as an explicit, locally activated factory.  It is not
a global instance, so it does not form a dictionary diamond with Mathlib's
existing completion `NormedRing` when the source happens to be unital.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace UniformSpace.Completion

universe u𝕜 uA

variable {𝕜 : Type u𝕜}
variable (A : Type uA) [NonUnitalSeminormedRing A]

private theorem nonUnitalCompletion_coe_mul_aux
    (a b : A) :
    let _ : Mul (UniformSpace.Completion A) :=
      ⟨Function.curry <|
        (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
          ((↑) ∘ Function.uncurry (· * ·))⟩
    ((a * b : A) : UniformSpace.Completion A) =
      (a : UniformSpace.Completion A) *
        (b : UniformSpace.Completion A) := by
  let _ : Mul (UniformSpace.Completion A) :=
    ⟨Function.curry <|
      (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
        ((↑) ∘ Function.uncurry (· * ·))⟩
  exact
    ((isDenseInducing_coe.prodMap isDenseInducing_coe).extend_eq
      ((continuous_coe A).comp
        (@continuous_mul A _ _ _)) (a, b)).symm

/-- Continuity of the dense bilinear extension. -/
private theorem nonUnitalCompletion_continuous_mul_aux :
    let _ : Mul (UniformSpace.Completion A) :=
      ⟨Function.curry <|
        (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
          ((↑) ∘ Function.uncurry (· * ·))⟩
    ContinuousMul (UniformSpace.Completion A) := by
  let _ : Mul (UniformSpace.Completion A) :=
    ⟨Function.curry <|
      (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
        ((↑) ∘ Function.uncurry (· * ·))⟩
  refine { continuous_mul := ?_ }
  let m :=
    (AddMonoidHom.mul : A →+ A →+ A).compr₂ toCompl
  have hmul : Continuous (fun p : A × A => m p.1 p.2) :=
    (continuous_coe A).comp continuous_mul
  have hdense : IsDenseInducing
      (toCompl : A → UniformSpace.Completion A) :=
    isDenseInducing_coe
  exact (hdense.extend_Z_bilin hdense hmul :)

/-- **Normed ring structure on a nonunital completion.** For a nonunital seminormed ring `A`, its
uniform completion carries a nonunital normed ring structure extending its multiplication and
additive operations. The source may be incomplete or nonseparated. -/
@[instance_reducible]
noncomputable def nonUnitalCompletionNormedRing :
    NonUnitalNormedRing (UniformSpace.Completion A) := by
  letI : Mul (UniformSpace.Completion A) :=
    ⟨Function.curry <|
      (isDenseInducing_coe.prodMap isDenseInducing_coe).extend
        ((↑) ∘ Function.uncurry (· * ·))⟩
  letI : ContinuousMul (UniformSpace.Completion A) :=
    by exact nonUnitalCompletion_continuous_mul_aux A
  let completionNormedAddCommGroup :
      NormedAddCommGroup (UniformSpace.Completion A) := inferInstance
  letI : NormedAddCommGroup (UniformSpace.Completion A) :=
    completionNormedAddCommGroup
  let completionNonUnitalRing :
      NonUnitalRing (UniformSpace.Completion A) :=
    { toAddCommGroup := completionNormedAddCommGroup.toAddCommGroup
      mul := (· * ·)
      left_distrib := by
        intro x y z
        exact induction_on₃ x y z
          (isClosed_eq (by fun_prop) (by fun_prop))
          (fun a b c => by
            rw [← coe_add, ← nonUnitalCompletion_coe_mul_aux,
              ← nonUnitalCompletion_coe_mul_aux,
              ← nonUnitalCompletion_coe_mul_aux,
              ← coe_add, mul_add])
      right_distrib := by
        intro x y z
        exact induction_on₃ x y z
          (isClosed_eq (by fun_prop) (by fun_prop))
          (fun a b c => by
            rw [← coe_add, ← nonUnitalCompletion_coe_mul_aux,
              ← nonUnitalCompletion_coe_mul_aux,
              ← nonUnitalCompletion_coe_mul_aux,
              ← coe_add, add_mul])
      zero_mul := by
        intro x
        exact induction_on x
          (isClosed_eq (by fun_prop) continuous_const)
          (fun a => by
            rw [← coe_zero, ← nonUnitalCompletion_coe_mul_aux, zero_mul])
      mul_zero := by
        intro x
        exact induction_on x
          (isClosed_eq (by fun_prop) continuous_const)
          (fun a => by
            rw [← coe_zero, ← nonUnitalCompletion_coe_mul_aux, mul_zero])
      mul_assoc := by
        intro x y z
        exact induction_on₃ x y z
          (isClosed_eq (by fun_prop) (by fun_prop))
          (fun a b c => by
            rw [← nonUnitalCompletion_coe_mul_aux,
              ← nonUnitalCompletion_coe_mul_aux,
              ← nonUnitalCompletion_coe_mul_aux,
              ← nonUnitalCompletion_coe_mul_aux, mul_assoc]) }
  letI : NonUnitalRing (UniformSpace.Completion A) :=
    completionNonUnitalRing
  exact
    { completionNonUnitalRing, completionNormedAddCommGroup with
      norm_mul_le := by
        intro x y
        induction x, y using induction_on₂ with
        | hp => apply isClosed_le <;> fun_prop
        | ih a b =>
            simpa only [← nonUnitalCompletion_coe_mul_aux, norm_coe] using
              norm_mul_le a b }

/-- **Multiplication on dense completion images.** For a nonunital seminormed ring `A` and its canonical
map `ι` into the uniform completion, `ι(a b) = ι(a) ι(b)` for every `a,b ∈ A`, using the induced
completed multiplication. -/
theorem nonUnitalCompletion_coe_mul
    (a b : A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    ((a * b : A) : UniformSpace.Completion A) =
      (a : UniformSpace.Completion A) *
        (b : UniformSpace.Completion A) := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  exact nonUnitalCompletion_coe_mul_aux A a b

/-- **Scalar associativity in a nonunital completion.** Let a type `𝕜` act on a nonunital seminormed
ring `A`, with every fixed-scalar map uniformly continuous. If `(c • a) b = c • (a b)` in `A`, the
induced scalar action and multiplication on its uniform completion satisfy the same identity. -/
theorem nonUnitalCompletionIsScalarTower
    [SMul 𝕜 A] [UniformContinuousConstSMul 𝕜 A]
    [IsScalarTower 𝕜 A A] :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    IsScalarTower 𝕜 (UniformSpace.Completion A)
      (UniformSpace.Completion A) := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  refine { smul_assoc := ?_ }
  intro c x y
  change (c • x) * y = c • (x * y)
  refine induction_on₂ x y
    (isClosed_eq
      (((continuous_const_smul c).comp continuous_fst).mul
        continuous_snd)
      ((continuous_const_smul c).comp
        (continuous_fst.mul continuous_snd))) ?_
  intro a b
  simpa only [← coe_smul, ← nonUnitalCompletion_coe_mul] using
    congrArg ((↑) : A → UniformSpace.Completion A)
      (smul_mul_assoc c a b)

/-- **Scalar commutation in a nonunital completion.** Let a type `𝕜` act on a nonunital seminormed ring
`A`, with every fixed-scalar map uniformly continuous. If `a (c • b) = c • (a b)` in `A`, the
induced action and multiplication on its uniform completion satisfy the same identity. -/
theorem nonUnitalCompletionSMulCommClass
    [SMul 𝕜 A] [UniformContinuousConstSMul 𝕜 A]
    [SMulCommClass 𝕜 A A] :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    SMulCommClass 𝕜 (UniformSpace.Completion A)
      (UniformSpace.Completion A) := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  refine { smul_comm := ?_ }
  intro c x y
  change c • (x * y) = x * (c • y)
  refine induction_on₂ x y
    (isClosed_eq
      ((continuous_const_smul c).comp
        (continuous_fst.mul continuous_snd))
      (continuous_fst.mul
        ((continuous_const_smul c).comp continuous_snd))) ?_
  intro a b
  simpa only [← coe_smul, ← nonUnitalCompletion_coe_mul] using
    congrArg ((↑) : A → UniformSpace.Completion A)
      (mul_smul_comm c a b).symm

/-- **Equivariant homomorphism into a completion.** Let `A` be a nonunital seminormed ring and let a
monoid `𝕜` act distributively on its additive group, with each fixed-scalar map uniformly
continuous. The canonical map from `A` to its uniform completion preserves addition, multiplication,
and the `𝕜`-action. -/
noncomputable def coeNonUnitalAlgHom
    [Monoid 𝕜] [DistribMulAction 𝕜 A]
    [UniformContinuousConstSMul 𝕜 A] :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    A →ₙₐ[𝕜] UniformSpace.Completion A := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  exact
    { toFun := fun a => (a : UniformSpace.Completion A)
      map_zero' := coe_zero
      map_add' := coe_add
      map_smul' := coe_smul
      map_mul' := nonUnitalCompletion_coe_mul A }

/-- **Value of the completion homomorphism.** Let `A` be a nonunital seminormed ring and let a monoid
`𝕜` act distributively on its additive group, with each fixed-scalar map uniformly continuous. The
canonical equivariant nonunital homomorphism sends `a ∈ A` to its uniform-completion image. -/
theorem coeNonUnitalAlgHom_apply
    [Monoid 𝕜] [DistribMulAction 𝕜 A]
    [UniformContinuousConstSMul 𝕜 A] (a : A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    coeNonUnitalAlgHom (𝕜 := 𝕜) A a =
      (a : UniformSpace.Completion A) :=
  rfl

/-- **Completion homomorphism preserves products.** Let `A` be a nonunital seminormed ring and let a
monoid `𝕜` act distributively on its additive group, with each fixed-scalar map uniformly
continuous. For every `a,b ∈ A`, the completion homomorphism satisfies `ι(a b) = ι(a) ι(b)`. -/
theorem coeNonUnitalAlgHom_mul
    [Monoid 𝕜] [DistribMulAction 𝕜 A]
    [UniformContinuousConstSMul 𝕜 A] (a b : A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    coeNonUnitalAlgHom (𝕜 := 𝕜) A (a * b) =
      coeNonUnitalAlgHom (𝕜 := 𝕜) A a *
        coeNonUnitalAlgHom (𝕜 := 𝕜) A b := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  exact map_mul (coeNonUnitalAlgHom (𝕜 := 𝕜) A) a b

/-- **Completion homomorphism preserves scalars.** Let `A` be a nonunital seminormed ring and let a
monoid `𝕜` act distributively on its additive group, with each fixed-scalar map uniformly
continuous. For every `c ∈ 𝕜` and `a ∈ A`, the completion homomorphism satisfies `ι(c • a) = c •
ι(a)`. -/
theorem coeNonUnitalAlgHom_smul
    [Monoid 𝕜] [DistribMulAction 𝕜 A]
    [UniformContinuousConstSMul 𝕜 A] (c : 𝕜) (a : A) :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    coeNonUnitalAlgHom (𝕜 := 𝕜) A (c • a) =
      c • coeNonUnitalAlgHom (𝕜 := 𝕜) A a := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  exact map_smul (coeNonUnitalAlgHom (𝕜 := 𝕜) A) c a

/-- **Continuity of the completion homomorphism.** Let `A` be a nonunital seminormed ring and let a
monoid `𝕜` act distributively on its additive group, with each fixed-scalar map uniformly
continuous. The canonical equivariant nonunital homomorphism into the uniform completion is
continuous. -/
theorem continuous_coeNonUnitalAlgHom
    [Monoid 𝕜] [DistribMulAction 𝕜 A]
    [UniformContinuousConstSMul 𝕜 A] :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    Continuous (coeNonUnitalAlgHom (𝕜 := 𝕜) A) := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  exact (continuous_coe A).congr fun a =>
    (coeNonUnitalAlgHom_apply (𝕜 := 𝕜) A a).symm

/-- **Dense range of the completion homomorphism.** Let `A` be a nonunital seminormed ring and let a
monoid `𝕜` act distributively on its additive group, with each fixed-scalar map uniformly
continuous. The canonical equivariant nonunital homomorphism has dense range in the uniform
completion. -/
theorem denseRange_coeNonUnitalAlgHom
    [Monoid 𝕜] [DistribMulAction 𝕜 A]
    [UniformContinuousConstSMul 𝕜 A] :
    let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
      nonUnitalCompletionNormedRing A
    DenseRange (coeNonUnitalAlgHom (𝕜 := 𝕜) A) := by
  let _ : NonUnitalNormedRing (UniformSpace.Completion A) :=
    nonUnitalCompletionNormedRing A
  have hcoe : (coeNonUnitalAlgHom (𝕜 := 𝕜) A :
      A → UniformSpace.Completion A) = ((↑) : A → UniformSpace.Completion A) :=
    funext (coeNonUnitalAlgHom_apply (𝕜 := 𝕜) A)
  rw [hcoe]
  exact denseRange_coe

end UniformSpace.Completion
