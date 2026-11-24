/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The Hochschild degree-two presentation of Kähler differentials

The actual tensor differential sends a ⊗ b ⊗ c to
ab ⊗ c - a ⊗ bc + ca ⊗ b. Its cokernel is the native module of Kähler
differentials, with representative a ⊗ b mapped to a db.

The inverse is the native universal derivation into the actual boundary-range
quotient. No flatness, finite generation, smoothness or characteristic
assumption is made. These are A-linear Hochschild coordinates; subsequent
cyclic quotients by exact differentials are only k-linear.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace KaehlerDifferential.Hochschild

universe u v

variable (k : Type u) (A : Type v) [CommRing k] [CommRing A] [Algebra k A]

/-- The original degree-two relation, with both endpoint tensors present. -/
def relationMap : (A ⊗[k] A) →ₗ[k] A ⊗[k] A :=
  LinearMap.id -
    (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toLinearMap.comp
      (Algebra.TensorProduct.lmul' k : A ⊗[k] A →ₐ[k] A).toLinearMap +
    (TensorProduct.comm k A A).toLinearMap

/-- The relation map retains the actual ordered three-term expression. -/
lemma relationMap_tmul (a b : A) :
    relationMap k A (a ⊗ₜ[k] b) =
      a ⊗ₜ[k] b - 1 ⊗ₜ[k] (a * b) + b ⊗ₜ[k] a := by
  change a ⊗ₜ[k] b -
      (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A)
        (Algebra.TensorProduct.lmul' k (a ⊗ₜ[k] b)) +
      (TensorProduct.comm k A A) (a ⊗ₜ[k] b) = _
  rw [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.includeRight_apply,
    TensorProduct.comm_tmul]

/-- The A-linear Hochschild b₂ on the original triple tensor. -/
def boundaryTwo : (A ⊗[k] (A ⊗[k] A)) →ₗ[A] A ⊗[k] A :=
  TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.lsmul A ((A ⊗[k] A) →ₗ[k] A ⊗[k] A)).flip (relationMap k A))

/-- The pure-tensor formula has the printed positive final endpoint. -/
lemma boundaryTwo_tmul (a b c : A) :
    boundaryTwo k A (a ⊗ₜ[k] (b ⊗ₜ[k] c)) =
      (a * b) ⊗ₜ[k] c - a ⊗ₜ[k] (b * c) + (c * a) ⊗ₜ[k] b := by
  rw [boundaryTwo, TensorProduct.AlgebraTensorModule.lift_tmul]
  change a • relationMap k A (b ⊗ₜ[k] c) = _
  rw [relationMap_tmul, smul_add, smul_sub]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, mul_comm a c]

/-- The original tensor space modulo the actual range of b₂. -/
abbrev BoundaryQuotient : Type v :=
  (A ⊗[k] A) ⧸ LinearMap.range (boundaryTwo k A)

/-- The actual projection onto the Hochschild boundary quotient. -/
def quotientMap : (A ⊗[k] A) →ₗ[A] BoundaryQuotient k A :=
  (LinearMap.range (boundaryTwo k A)).mkQ

/-- Every actual degree-two boundary vanishes under the quotient. -/
lemma quotientMap_boundaryTwo (x : A ⊗[k] (A ⊗[k] A)) :
    quotientMap k A (boundaryTwo k A x) = 0 := by
  rw [quotientMap, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, rfl⟩

/-- The degenerate tensor a ⊗ 1 is itself an actual boundary. -/
lemma quotientMap_tmul_one (a : A) : quotientMap k A (a ⊗ₜ[k] (1 : A)) = 0 := by
  have h := quotientMap_boundaryTwo k A (a ⊗ₜ[k] ((1 : A) ⊗ₜ[k] (1 : A)))
  simpa only [boundaryTwo_tmul, mul_one, one_mul, sub_self, zero_add] using h

/-- Multiplying the first tensor coordinate is the native A-module action. -/
lemma quotientMap_tmul_eq_smul (a b : A) :
    quotientMap k A (a ⊗ₜ[k] b) = a • quotientMap k A (1 ⊗ₜ[k] b) := by
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
    (quotientMap k A).map_smul a (1 ⊗ₜ[k] b)

/-- The actual b₂ boundary gives the Leibniz relation in its quotient. -/
lemma quotientMap_leibniz (a b : A) :
    quotientMap k A (1 ⊗ₜ[k] (a * b)) =
      quotientMap k A (a ⊗ₜ[k] b) + quotientMap k A (b ⊗ₜ[k] a) := by
  have h := quotientMap_boundaryTwo k A ((1 : A) ⊗ₜ[k] (a ⊗ₜ[k] b))
  simp only [boundaryTwo_tmul, one_mul, mul_one, map_add, map_sub] at h
  have h' : (quotientMap k A (a ⊗ₜ[k] b) + quotientMap k A (b ⊗ₜ[k] a)) -
      quotientMap k A (1 ⊗ₜ[k] (a * b)) = 0 := by
    simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  exact (sub_eq_zero.mp h').symm

/-- The actual class of 1 ⊗ a defines a native k-derivation. -/
def quotientDerivation : Derivation k A (BoundaryQuotient k A) where
  toLinearMap := ((quotientMap k A).restrictScalars k).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[k] A ⊗[k] A).toLinearMap
  map_one_eq_zero' := by
    change quotientMap k A (1 ⊗ₜ[k] (1 : A)) = 0
    exact quotientMap_tmul_one k A 1
  leibniz' a b := by
    change quotientMap k A (1 ⊗ₜ[k] (a * b)) =
      a • quotientMap k A (1 ⊗ₜ[k] b) + b • quotientMap k A (1 ⊗ₜ[k] a)
    exact (quotientMap_leibniz k A a b).trans
      (congrArg₂ (fun x y => x + y)
        (quotientMap_tmul_eq_smul k A a b) (quotientMap_tmul_eq_smul k A b a))

/-- The derivation is the original tensor representative. -/
lemma quotientDerivation_apply (a : A) :
    quotientDerivation k A a = quotientMap k A (1 ⊗ₜ[k] a) := rfl

/-- The native tensor-to-differentials map kills the actual Hochschild b₂. -/
lemma boundaryTwo_comp_tensorProductTo :
    (KaehlerDifferential.D k A).tensorProductTo.comp (boundaryTwo k A) = 0 := by
  apply LinearMap.ext
  intro x
  change (KaehlerDifferential.D k A).tensorProductTo (boundaryTwo k A x) = 0
  refine TensorProduct.induction_on (motive := fun t : A ⊗[k] (A ⊗[k] A) =>
    (KaehlerDifferential.D k A).tensorProductTo (boundaryTwo k A t) = 0) x ?_ ?_ ?_
  · simp only [map_zero]
  · intro a y
    refine TensorProduct.induction_on (motive := fun t : A ⊗[k] A =>
      (KaehlerDifferential.D k A).tensorProductTo (boundaryTwo k A (a ⊗ₜ[k] t)) = 0)
      y ?_ ?_ ?_
    · simp only [TensorProduct.tmul_zero, map_zero]
    · intro b c
      rw [boundaryTwo_tmul]
      simp only [map_add, map_sub, Derivation.tensorProductTo_tmul,
        Derivation.leibniz, smul_add, smul_smul]
      rw [mul_comm c a]
      abel
    · intro y z hy hz
      simp only [TensorProduct.tmul_add, map_add, hy, hz, zero_add]
  · intro x y hx hy
    simp only [map_add, hx, hy, zero_add]

/-- Descend the actual a ⊗ b ↦ a db map through the actual boundary range. -/
def toKaehler : BoundaryQuotient k A →ₗ[A] KaehlerDifferential k A :=
  (LinearMap.range (boundaryTwo k A)).liftQ (KaehlerDifferential.D k A).tensorProductTo (by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    change (KaehlerDifferential.D k A).tensorProductTo (boundaryTwo k A y) = 0
    exact congrArg (fun f : (A ⊗[k] (A ⊗[k] A)) →ₗ[A] KaehlerDifferential k A => f y)
      (boundaryTwo_comp_tensorProductTo k A))

/-- The descended map retains the original native tensor-to-differentials map. -/
lemma toKaehler_quotientMap (x : A ⊗[k] A) :
    toKaehler k A (quotientMap k A x) = (KaehlerDifferential.D k A).tensorProductTo x := rfl

/-- The canonical pure representative is a db. -/
lemma toKaehler_tmul (a b : A) :
    toKaehler k A (quotientMap k A (a ⊗ₜ[k] b)) = a • KaehlerDifferential.D k A b :=
  (toKaehler_quotientMap k A (a ⊗ₜ[k] b)).trans
    (Derivation.tensorProductTo_tmul (KaehlerDifferential.D k A) a b)

/-- The inverse is supplied by the native universal derivation, not comparison data. -/
def fromKaehler : KaehlerDifferential k A →ₗ[A] BoundaryQuotient k A :=
  (quotientDerivation k A).liftKaehlerDifferential

/-- Native universal lifting sends da to the actual class of 1 ⊗ a. -/
lemma fromKaehler_D (a : A) :
    fromKaehler k A (KaehlerDifferential.D k A a) = quotientMap k A (1 ⊗ₜ[k] a) :=
  (Derivation.liftKaehlerDifferential_comp_D (quotientDerivation k A) a).trans
    (quotientDerivation_apply k A a)

lemma fromKaehler_toKaehler (x : BoundaryQuotient k A) :
    fromKaehler k A (toKaehler k A x) = x := by
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (boundaryTwo k A)) x
  change fromKaehler k A (toKaehler k A (quotientMap k A y)) = quotientMap k A y
  refine TensorProduct.induction_on (motive := fun t : A ⊗[k] A =>
    fromKaehler k A (toKaehler k A (quotientMap k A t)) = quotientMap k A t)
    y ?_ ?_ ?_
  · simp only [map_zero]
  · intro a b
    exact (congrArg (fromKaehler k A) (toKaehler_tmul k A a b)).trans
      (((fromKaehler k A).map_smul a (KaehlerDifferential.D k A b)).trans
        ((congrArg (fun x => a • x) (fromKaehler_D k A b)).trans
          (quotientMap_tmul_eq_smul k A a b).symm))
  · intro y z hy hz
    simp only [map_add, hy, hz]

lemma toKaehler_fromKaehler (x : KaehlerDifferential k A) :
    toKaehler k A (fromKaehler k A x) = x := by
  have h : (toKaehler k A).comp (fromKaehler k A) = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change toKaehler k A (fromKaehler k A (KaehlerDifferential.D k A a)) =
      KaehlerDifferential.D k A a
    rw [fromKaehler_D, toKaehler_tmul, one_smul]
  exact congrArg (fun f : KaehlerDifferential k A →ₗ[A] KaehlerDifferential k A => f x) h

/-- The actual Hochschild boundary-range quotient is the native Kähler module. -/
def quotientLinearEquiv : BoundaryQuotient k A ≃ₗ[A] KaehlerDifferential k A :=
  { toKaehler k A with
    invFun := fromKaehler k A
    left_inv := fromKaehler_toKaehler k A
    right_inv := toKaehler_fromKaehler k A }

/-- Exactness of the actual tensor differential and the actual universal differential map. -/
lemma boundaryTwo_exact : Function.Exact (boundaryTwo k A)
    (KaehlerDifferential.D k A).tensorProductTo := by
  intro x
  constructor
  · intro hx
    have hq : quotientMap k A x = 0 := (quotientLinearEquiv k A).injective
      ((toKaehler_quotientMap k A x).trans (hx.trans (map_zero (toKaehler k A)).symm))
    have hm : x ∈ LinearMap.range (boundaryTwo k A) := by
      simpa only [quotientMap, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hq
    exact hm
  · rintro ⟨y, rfl⟩
    exact congrArg (fun f : (A ⊗[k] (A ⊗[k] A)) →ₗ[A] KaehlerDifferential k A => f y)
      (boundaryTwo_comp_tensorProductTo k A)

/-- The original Hochschild b₂ followed by a ⊗ b ↦ a db is a short complex. -/
def presentation : ShortComplex (ModuleCat.{v} A) :=
  ShortComplex.mk (ModuleCat.ofHom (boundaryTwo k A))
    (ModuleCat.ofHom (KaehlerDifferential.D k A).tensorProductTo) (by
      apply ModuleCat.hom_ext
      change (KaehlerDifferential.D k A).tensorProductTo.comp (boundaryTwo k A) = 0
      exact boundaryTwo_comp_tensorProductTo k A)

/-- The native module cokernel property is earned from the constructed exact tensor sequence. -/
def presentationIsCokernel :
    IsColimit (CokernelCofork.ofπ (presentation k A).g (presentation k A).zero) :=
  ModuleCat.isColimitCokernelCofork
    (ModuleCat.ofHom (boundaryTwo k A))
    (ModuleCat.ofHom (KaehlerDifferential.D k A).tensorProductTo)
    (boundaryTwo_exact k A) (KaehlerDifferential.tensorProductTo_surjective k A)

/-- The tensor presentation is exact over A with no flatness premise. -/
lemma presentation_exact : (presentation k A).Exact :=
  ShortComplex.exact_of_g_is_cokernel (presentation k A) (presentationIsCokernel k A)

/-- The canonical cokernel isomorphism uses the actual boundary quotient. -/
def presentationCokernelIso : cokernel (presentation k A).f ≅
    ModuleCat.of A (KaehlerDifferential k A) :=
  ModuleCat.cokernelIsoRangeQuotient (presentation k A).f ≪≫
    (quotientLinearEquiv k A).toModuleIso

/-- The categorical cokernel map is the original a ⊗ b ↦ a db map. -/
@[reassoc]
lemma presentationCokernelIso_π :
    cokernel.π (presentation k A).f ≫ (presentationCokernelIso k A).hom =
      (presentation k A).g := by
  let e : cokernel (ModuleCat.ofHom (boundaryTwo k A)) ≅
      ModuleCat.of A (BoundaryQuotient k A) :=
    ModuleCat.cokernelIsoRangeQuotient (ModuleCat.ofHom (boundaryTwo k A))
  let φ : ModuleCat.of A (BoundaryQuotient k A) ⟶
      ModuleCat.of A (KaehlerDifferential k A) := ModuleCat.ofHom (toKaehler k A)
  change cokernel.π (ModuleCat.ofHom (boundaryTwo k A)) ≫ (e.hom ≫ φ) =
    ModuleCat.ofHom (KaehlerDifferential.D k A).tensorProductTo
  have hπ : cokernel.π (ModuleCat.ofHom (boundaryTwo k A)) ≫ e.hom =
      ModuleCat.ofHom (quotientMap k A) :=
    ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom _
  have hφ : ModuleCat.ofHom (quotientMap k A) ≫ φ =
      ModuleCat.ofHom (KaehlerDifferential.D k A).tensorProductTo := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact toKaehler_quotientMap k A x
  exact (Category.assoc (cokernel.π (ModuleCat.ofHom (boundaryTwo k A))) e.hom φ).symm.trans
    ((congrArg (fun f => f ≫ φ) hπ).trans hφ)

end KaehlerDifferential.Hochschild
