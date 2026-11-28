/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Ring
public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Module
public import Mathlib.Algebra.Module.GradedModule
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The total associated graded module and its action

Let `R` be a commutative ring, `I` an ideal, and `M` an `R`-module. The total associated
graded module is `gr_I M = ⨁ n : ℕ, I^n M/I^(n+1) M`. The homogeneous action `[r]_m • [x]_n =
[r • x]_(m+n)` makes it a module over `gr_I R`.

The coefficient action of `R/I` is componentwise and agrees with the degree-zero inclusion
`R/I → gr_I R`, giving the scalar tower `R/I → gr_I R → gr_I M`.

Every `R`-linear map `f : M → N` induces a `gr_I R`-linear map `gr_I M → gr_I N`, acting on
representatives by `[x]_n ↦ [f x]_n`. These maps preserve identity and composition, and a
surjective `f` induces a surjective graded map.

Reference: Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapter 10.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped DirectSum Pointwise

universe u v w z

namespace Ideal

variable {R : Type u} [CommRing R]

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, the total associated graded
module is `I.AssociatedGradedModule M = ⨁ n : ℕ, I^n M/I^(n+1) M`. Its homogeneous degree `n`
is `I.AssociatedGradedModulePiece M n`. -/
abbrev AssociatedGradedModule (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : Type v :=
  ⨁ n, I.AssociatedGradedModulePiece M n

private def associatedGradedModuleSMulRep (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (m n : ℕ) (x : (I ^ m : Ideal R))
    (y : ↥(I ^ n • (⊤ : Submodule R M))) :
    ↥(I ^ (m + n) • (⊤ : Submodule R M)) :=
  ⟨x.1 • y.1, by
    rw [pow_add, Submodule.mul_smul]
    exact Submodule.smul_mem_smul x.2 y.2⟩

private def associatedGradedModuleSMulRaw (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (m n : ℕ) :
    (I ^ m : Ideal R) →ₗ[R]
      ↥(I ^ n • (⊤ : Submodule R M)) →ₗ[R]
        I.AssociatedGradedModulePiece M (m + n) :=
  LinearMap.mk₂ R
    (fun x y ↦ I.initialFormModule M (m + n)
      (associatedGradedModuleSMulRep I M m n x y))
    (fun x₁ x₂ y ↦ by
      rw [← map_add]
      apply congrArg (I.initialFormModule M (m + n))
      apply Subtype.ext
      exact add_smul (x₁ : R) x₂ (y : M))
    (fun r x y ↦ by
      rw [← map_smul]
      apply congrArg (I.initialFormModule M (m + n))
      apply Subtype.ext
      exact (smul_smul r (x : R) (y : M)).symm)
    (fun x y₁ y₂ ↦ by
      rw [← map_add]
      apply congrArg (I.initialFormModule M (m + n))
      apply Subtype.ext
      exact smul_add (x : R) (y₁ : M) (y₂ : M))
    (fun r x y ↦ by
      rw [← map_smul]
      apply congrArg (I.initialFormModule M (m + n))
      apply Subtype.ext
      simp only [associatedGradedModuleSMulRep,
        Submodule.coe_smul_of_tower]
      rw [smul_smul, smul_smul, mul_comm r (x : R)])

private theorem associatedGradedModuleSMulRaw_left_ker
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (m n : ℕ) :
    (I • ⊤ : Submodule R (I ^ m : Ideal R)) ≤
      (associatedGradedModuleSMulRaw I M m n).ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro y
  rw [LinearMap.zero_apply]
  change I.initialFormModule M (m + n)
      (associatedGradedModuleSMulRep I M m n x y) = 0
  rw [I.initialFormModule_eq_zero_iff]
  change (x : R) • (y : M) ∈ I ^ (m + n + 1) • (⊤ : Submodule R M)
  have hx' : (x : R) ∈ I ^ (m + 1) := by
    simpa [Submodule.mem_smul_top_iff, pow_succ'] using hx
  have hxy : (x : R) • (y : M) ∈
      I ^ ((m + 1) + n) • (⊤ : Submodule R M) := by
    rw [pow_add, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hx' y.2
  simpa only [add_assoc, add_comm, add_left_comm] using hxy

private theorem associatedGradedModuleSMulRaw_right_ker
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (m n : ℕ) :
    (I • ⊤ : Submodule R ↥(I ^ n • (⊤ : Submodule R M))) ≤
      (associatedGradedModuleSMulRaw I M m n).flip.ker := by
  intro y hy
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro x
  rw [LinearMap.zero_apply, LinearMap.flip_apply]
  change I.initialFormModule M (m + n)
      (associatedGradedModuleSMulRep I M m n x y) = 0
  rw [I.initialFormModule_eq_zero_iff]
  change (x : R) • (y : M) ∈ I ^ (m + n + 1) • (⊤ : Submodule R M)
  have hy' : (y : M) ∈ I ^ (n + 1) • (⊤ : Submodule R M) := by
    simpa [Submodule.mem_smul_top_iff, pow_succ', ← Submodule.mul_smul]
      using hy
  have hxy : (x : R) • (y : M) ∈
      I ^ (m + (n + 1)) • (⊤ : Submodule R M) := by
    rw [pow_add, Submodule.mul_smul]
    exact Submodule.smul_mem_smul x.2 hy'
  simpa only [add_assoc] using hxy

private def associatedGradedModuleSMulBilinear (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (m n : ℕ) :
    I.AssociatedGradedPiece m →ₗ[R]
      I.AssociatedGradedModulePiece M n →ₗ[R]
        I.AssociatedGradedModulePiece M (m + n) :=
  (associatedGradedModuleSMulRaw I M m n).liftQ₂ _ _
    (associatedGradedModuleSMulRaw_left_ker I M m n)
    (associatedGradedModuleSMulRaw_right_ker I M m n)

/-- Let `R` be a commutative ring, `I` an ideal, `M` an `R`-module, and `m n : ℕ`. The homogeneous
action is the `R/I`-bilinear map `(I^m/I^(m+1)) × (I^n M/I^(n+1) M) → I^(m+n) M/I^(m+n+1) M`,
sending `[r]_m,[x]_n` to `[r • x]_(m+n)`. -/
@[no_expose]
def associatedGradedModuleSMul (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (m n : ℕ) :
    I.AssociatedGradedPiece m →ₗ[R ⧸ I]
      I.AssociatedGradedModulePiece M n →ₗ[R ⧸ I]
        I.AssociatedGradedModulePiece M (m + n) := by
  let b := associatedGradedModuleSMulBilinear I M m n
  let b₁ : I.AssociatedGradedPiece m →ₗ[R]
      I.AssociatedGradedModulePiece M n →ₗ[R ⧸ I]
        I.AssociatedGradedModulePiece M (m + n) :=
    { toFun := fun x ↦
        (b x).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      map_add' := fun x y ↦ by
        apply LinearMap.ext
        intro z
        change b (x + y) z = b x z + b y z
        rw [map_add, LinearMap.add_apply]
      map_smul' := fun r x ↦ by
        apply LinearMap.ext
        intro z
        change b (r • x) z = r • b x z
        rw [map_smul, LinearMap.smul_apply] }
  exact b₁.extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- Let `R` be a commutative ring, `I` an ideal, `M` an `R`-module, `m n : ℕ`, `x : I^m`, and `y :
I^n M`. Then the homogeneous action satisfies `[x]_m • [y]_n = [(x : R) • (y : M)]_(m+n)`,
where the ring and module brackets are respectively `initialForm` and `initialFormModule`. -/
theorem associatedGradedModuleSMul_initialForm
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (m n : ℕ) (x : (I ^ m : Ideal R))
    (y : ↥(I ^ n • (⊤ : Submodule R M))) :
    I.associatedGradedModuleSMul M m n (I.initialForm m x)
        (I.initialFormModule M n y) =
      I.initialFormModule M (m + n)
        ⟨(x : R) • (y : M), by
          rw [pow_add, Submodule.mul_smul]
          exact Submodule.smul_mem_smul x.2 y.2⟩ := by
  rw [associatedGradedModuleSMul]
  rfl

private theorem modulePow_cast_coe (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {m n : ℕ} (h : m = n)
    (x : ↥(I ^ m • (⊤ : Submodule R M))) :
    ((cast
        (congrArg
          (fun k ↦ (↥(I ^ k • (⊤ : Submodule R M)) : Type v)) h) x :
      ↥(I ^ n • (⊤ : Submodule R M))) : M) = x := by
  subst h
  rfl

private theorem initialFormModule_cast (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {m n : ℕ} (h : m = n)
    (x : ↥(I ^ m • (⊤ : Submodule R M))) :
    cast (congrArg (I.AssociatedGradedModulePiece M) h)
        (I.initialFormModule M m x) =
      I.initialFormModule M n
        (cast
          (congrArg
            (fun k ↦ (↥(I ^ k • (⊤ : Submodule R M)) : Type v)) h) x) := by
  subst h
  rfl

private noncomputable local instance associatedGradedModuleGSMul
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    GradedMonoid.GSMul I.AssociatedGradedPiece
      (I.AssociatedGradedModulePiece M) where
  smul := fun x y ↦ I.associatedGradedModuleSMul M _ _ x y

private theorem associatedGradedModule_one_smul
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (a : GradedMonoid (I.AssociatedGradedModulePiece M)) :
    GradedMonoid.mk (0 + a.fst)
      (I.associatedGradedModuleSMul M 0 a.fst
        GradedMonoid.GOne.one a.snd) = a := by
  obtain ⟨n, a⟩ := a
  obtain ⟨y, rfl⟩ := I.initialFormModule_surjective M n a
  apply Sigma.ext (zero_add n)
  change HEq
    (I.associatedGradedModuleSMul M 0 n
      (I.initialForm 0 ⟨1, by simp⟩) (I.initialFormModule M n y))
    (I.initialFormModule M n y)
  rw [I.associatedGradedModuleSMul_initialForm]
  refine heq_of_cast_eq
    (congrArg (I.AssociatedGradedModulePiece M) (zero_add n)) ?_
  rw [initialFormModule_cast I M (zero_add n)]
  apply congrArg (I.initialFormModule M n)
  apply Subtype.ext
  rw [modulePow_cast_coe I M (zero_add n)]
  exact one_smul R (y : M)

private theorem associatedGradedModuleSMul_mul_initialForm
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (i j k : ℕ) (x : (I ^ i : Ideal R)) (y : (I ^ j : Ideal R))
    (z : ↥(I ^ k • (⊤ : Submodule R M))) :
    I.associatedGradedModuleSMul M (i + j) k
        (I.adicGradedMul i j (I.initialForm i x) (I.initialForm j y))
        (I.initialFormModule M k z) =
      I.initialFormModule M ((i + j) + k)
        (associatedGradedModuleSMulRep I M (i + j) k
          ⟨(x : R) * (y : R), by
            rw [pow_add]
            exact Ideal.mul_mem_mul x.2 y.2⟩ z) := by
  rw [show I.initialForm = I.adicSymbol from rfl, I.adicGradedMul_symbol,
    show I.adicSymbol = I.initialForm from rfl,
    I.associatedGradedModuleSMul_initialForm]
  rfl

private theorem associatedGradedModuleSMul_nested_initialForm
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (i j k : ℕ) (x : (I ^ i : Ideal R)) (y : (I ^ j : Ideal R))
    (z : ↥(I ^ k • (⊤ : Submodule R M))) :
    I.associatedGradedModuleSMul M i (j + k) (I.initialForm i x)
        (I.associatedGradedModuleSMul M j k (I.initialForm j y)
          (I.initialFormModule M k z)) =
      I.initialFormModule M (i + (j + k))
        (associatedGradedModuleSMulRep I M i (j + k) x
          (associatedGradedModuleSMulRep I M j k y z)) := by
  rw [I.associatedGradedModuleSMul_initialForm,
    I.associatedGradedModuleSMul_initialForm]
  rfl

private theorem associatedGradedModule_mul_smul
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (a b : GradedMonoid I.AssociatedGradedPiece)
    (c : GradedMonoid (I.AssociatedGradedModulePiece M)) :
    (a * b) • c = a • b • c := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  obtain ⟨k, c⟩ := c
  obtain ⟨x, rfl⟩ := I.initialForm_surjective i a
  obtain ⟨y, rfl⟩ := I.initialForm_surjective j b
  obtain ⟨z, rfl⟩ := I.initialFormModule_surjective M k c
  apply Sigma.ext (add_assoc i j k)
  change HEq
    (I.associatedGradedModuleSMul M (i + j) k
      (I.adicGradedMul i j
        (I.initialForm i x) (I.initialForm j y))
      (I.initialFormModule M k z))
    (I.associatedGradedModuleSMul M i (j + k) (I.initialForm i x)
      (I.associatedGradedModuleSMul M j k (I.initialForm j y)
        (I.initialFormModule M k z)))
  rw [associatedGradedModuleSMul_mul_initialForm,
    associatedGradedModuleSMul_nested_initialForm]
  refine heq_of_cast_eq
    (congrArg (I.AssociatedGradedModulePiece M) (add_assoc i j k)) ?_
  rw [initialFormModule_cast I M (add_assoc i j k)]
  apply congrArg (I.initialFormModule M (i + (j + k)))
  apply Subtype.ext
  rw [modulePow_cast_coe I M (add_assoc i j k)]
  exact mul_smul (x : R) (y : R) (z : M)

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, the family `n ↦
I.AssociatedGradedModulePiece M n` is a graded module over `m ↦ I.AssociatedGradedPiece m`.
The action is `[r]_m • [x]_n = [r • x]_(m+n)`; the degree-zero unit acts as the identity and
the action satisfies the module addition and associativity laws. -/
noncomputable instance associatedGradedModuleGmodule
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    DirectSum.Gmodule I.AssociatedGradedPiece
      (I.AssociatedGradedModulePiece M) where
  smul := fun x y ↦ I.associatedGradedModuleSMul M _ _ x y
  one_smul := by
    exact associatedGradedModule_one_smul I M
  mul_smul := by
    exact associatedGradedModule_mul_smul I M
  smul_add := fun a b c ↦
    map_add (I.associatedGradedModuleSMul M _ _ a) b c
  smul_zero := fun a ↦
    map_zero (I.associatedGradedModuleSMul M _ _ a)
  add_smul := fun a b c ↦
    LinearMap.congr_fun
      (map_add (I.associatedGradedModuleSMul M _ _) a b) c
  zero_smul := fun b ↦
    LinearMap.congr_fun
      (map_zero (I.associatedGradedModuleSMul M _ _)) b

private theorem associatedGradedModule_gsmul
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (m n : ℕ) (x : I.AssociatedGradedPiece m)
    (y : I.AssociatedGradedModulePiece M n) :
    GradedMonoid.GSMul.smul x y =
      I.associatedGradedModuleSMul M m n x y := by
  rfl

/-- Let `R` be a commutative ring, `I` an ideal, `M` an `R`-module, and `m n : ℕ`. For `x ∈ gr_I^m
R` and `y ∈ gr_I^n M`, the homogeneous inclusions satisfy `j_m(x) • j_n(y) =
j_(m+n)(I.associatedGradedModuleSMul M m n x y)`. Here `j_k` is `DirectSum.of` into the
appropriate total associated graded ring or module. -/
theorem associatedGradedModule_of_smul_of
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (m n : ℕ) (x : I.AssociatedGradedPiece m)
    (y : I.AssociatedGradedModulePiece M n) :
    DirectSum.of I.AssociatedGradedPiece m x •
        DirectSum.of (I.AssociatedGradedModulePiece M) n y =
      DirectSum.of (I.AssociatedGradedModulePiece M) (m + n)
        (I.associatedGradedModuleSMul M m n x y) :=
  by
    rw [DirectSum.Gmodule.of_smul_of]
    rw [associatedGradedModule_gsmul]
    apply DirectSum.of_eq_of_gradedMonoid_eq
    rfl

private theorem associatedGradedModuleSMul_zero
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (r : R ⧸ I) (n : ℕ) (y : I.AssociatedGradedModulePiece M n) :
    GradedMonoid.mk (0 + n)
      (I.associatedGradedModuleSMul M 0 n
        (I.associatedGradedGAlgebra.toFun r) y) =
      GradedMonoid.mk n (r • y) := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
  obtain ⟨z, rfl⟩ := I.initialFormModule_surjective M n y
  apply Sigma.ext (zero_add n)
  change HEq
    (I.associatedGradedModuleSMul M 0 n
      (I.associatedGradedGAlgebra.toFun (Ideal.Quotient.mk I r))
      (I.initialFormModule M n z))
    (Ideal.Quotient.mk I r • I.initialFormModule M n z)
  rw [I.associatedGradedGAlgebra_toFun_mk,
    I.associatedGradedModuleSMul_initialForm]
  let rz : ↥(I ^ n • (⊤ : Submodule R M)) :=
    ⟨r • z, (I ^ n • (⊤ : Submodule R M)).smul_mem r z.2⟩
  have hsmul : Ideal.Quotient.mk I r • I.initialFormModule M n z =
      I.initialFormModule M n rz := by
    rw [I.initialFormModule_apply, I.initialFormModule_apply,
      Module.Quotient.mk_smul_mk]
    rfl
  rw [hsmul]
  refine heq_of_cast_eq
    (congrArg (I.AssociatedGradedModulePiece M) (zero_add n)) ?_
  rw [initialFormModule_cast I M (zero_add n)]
  apply congrArg (I.initialFormModule M n)
  apply Subtype.ext
  rw [modulePow_cast_coe I M (zero_add n)]

/-- Let `R` be a commutative ring, `I` an ideal, `M` an `R`-module, `r : R/I`, `n : ℕ`, and `y ∈
gr_I^n M`. If `j_n` is the homogeneous inclusion, then `(algebraMap (R/I) (gr_I R) r) • j_n(y)
= j_n(r • y)`. Thus the scalar inclusion into degree zero agrees with the quotient-ring action
on each degree. -/
theorem associatedGradedModule_algebraMap_smul_of
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]
    (r : R ⧸ I) (n : ℕ) (y : I.AssociatedGradedModulePiece M n) :
    (algebraMap (R ⧸ I) I.AssociatedGraded :
      (R ⧸ I) →+* I.AssociatedGraded) r •
        DirectSum.of (I.AssociatedGradedModulePiece M) n y =
      DirectSum.of (I.AssociatedGradedModulePiece M) n (r • y) := by
  rw [DirectSum.algebraMap_apply, I.associatedGradedModule_of_smul_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq
    (associatedGradedModuleSMul_zero I M r n y)

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, the componentwise
`R/I`-action and the `gr_I R`-module action on `gr_I M` form the scalar tower `IsScalarTower
(R/I) (gr_I R) (gr_I M)`. Explicitly, `(a • b) • x = a • (b • x)` for `a : R/I`, `b : gr_I R`,
and `x : gr_I M`. -/
noncomputable instance associatedGradedModuleIsScalarTower
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsScalarTower (R ⧸ I) I.AssociatedGraded
      (I.AssociatedGradedModule M) := by
  change @IsScalarTower (R ⧸ I) I.AssociatedGraded
    (I.AssociatedGradedModule M)
    (inferInstance : Algebra (R ⧸ I) I.AssociatedGraded).toSMul
    inferInstance inferInstance
  apply IsScalarTower.of_algebraMap_smul
  intro r x
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n y =>
      exact (I.associatedGradedModule_algebraMap_smul_of M r n y).trans
        (DirectSum.of_smul (R ⧸ I) n r y)
  | add x y hx hy =>
      rw [DirectSum.Gmodule.smul_def, map_add]
      rw [show r • (x + y) = r • x + r • y by exact smul_add r x y]
      change (((algebraMap (R ⧸ I) I.AssociatedGraded :
          (R ⧸ I) →+* I.AssociatedGraded) r) • x) +
        (((algebraMap (R ⧸ I) I.AssociatedGraded :
          (R ⧸ I) →+* I.AssociatedGraded) r) • y) = r • x + r • y
      rw [hx, hy]

private def associatedGradedModuleMapTotal0 (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    I.AssociatedGradedModule M →ₗ[R ⧸ I]
      I.AssociatedGradedModule N :=
  DirectSum.lmap fun n ↦ I.associatedGradedModuleMap f n

@[simp]
private theorem associatedGradedModuleMapTotal0_of (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ)
    (x : I.AssociatedGradedModulePiece M n) :
    associatedGradedModuleMapTotal0 I f
        (DirectSum.of (I.AssociatedGradedModulePiece M) n x) =
      DirectSum.of (I.AssociatedGradedModulePiece N) n
        (I.associatedGradedModuleMap f n x) := by
  simp [associatedGradedModuleMapTotal0]

private theorem associatedGradedModuleMap_smul
    (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (m n : ℕ)
    (a : I.AssociatedGradedPiece m)
    (x : I.AssociatedGradedModulePiece M n) :
    I.associatedGradedModuleMap f (m + n)
        (I.associatedGradedModuleSMul M m n a x) =
      I.associatedGradedModuleSMul N m n a
        (I.associatedGradedModuleMap f n x) := by
  obtain ⟨r, rfl⟩ := I.initialForm_surjective m a
  obtain ⟨y, rfl⟩ := I.initialFormModule_surjective M n x
  rw [I.associatedGradedModuleSMul_initialForm]
  simp only [I.initialFormModule_apply, I.associatedGradedModuleMap_initialFormModule]
  rw [← I.initialFormModule_apply, ← I.initialFormModule_apply,
    I.associatedGradedModuleSMul_initialForm]
  apply congrArg (I.initialFormModule N (m + n))
  apply Subtype.ext
  exact f.map_smul (r : R) (y : M)

private theorem associatedGradedModuleMapTotal0_smul
    (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (a : I.AssociatedGraded)
    (x : I.AssociatedGradedModule M) :
    associatedGradedModuleMapTotal0 I f (a • x) =
      a • associatedGradedModuleMapTotal0 I f x := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | add a b ha hb =>
      change associatedGradedModuleMapTotal0 I f
          ((DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
            (I.AssociatedGradedModulePiece M)) a x) =
        (DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
          (I.AssociatedGradedModulePiece N)) a
            (associatedGradedModuleMapTotal0 I f x) at ha
      change associatedGradedModuleMapTotal0 I f
          ((DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
            (I.AssociatedGradedModulePiece M)) b x) =
        (DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
          (I.AssociatedGradedModulePiece N)) b
            (associatedGradedModuleMapTotal0 I f x) at hb
      change associatedGradedModuleMapTotal0 I f
          ((DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
            (I.AssociatedGradedModulePiece M)) (a + b) x) =
        (DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
          (I.AssociatedGradedModulePiece N)) (a + b)
            (associatedGradedModuleMapTotal0 I f x)
      simp only [map_add, AddMonoidHom.add_apply, ha, hb]
  | of m a =>
      induction x using DirectSum.induction_on with
      | zero => simp
      | add x y hx hy =>
          change associatedGradedModuleMapTotal0 I f
              ((DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
                (I.AssociatedGradedModulePiece M))
                  (DirectSum.of I.AssociatedGradedPiece m a) x) =
            (DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
              (I.AssociatedGradedModulePiece N))
                (DirectSum.of I.AssociatedGradedPiece m a)
                  (associatedGradedModuleMapTotal0 I f x) at hx
          change associatedGradedModuleMapTotal0 I f
              ((DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
                (I.AssociatedGradedModulePiece M))
                  (DirectSum.of I.AssociatedGradedPiece m a) y) =
            (DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
              (I.AssociatedGradedModulePiece N))
                (DirectSum.of I.AssociatedGradedPiece m a)
                  (associatedGradedModuleMapTotal0 I f y) at hy
          change associatedGradedModuleMapTotal0 I f
              ((DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
                (I.AssociatedGradedModulePiece M))
                  (DirectSum.of I.AssociatedGradedPiece m a) (x + y)) =
            (DirectSum.Gmodule.smulAddMonoidHom I.AssociatedGradedPiece
              (I.AssociatedGradedModulePiece N))
                (DirectSum.of I.AssociatedGradedPiece m a)
                  (associatedGradedModuleMapTotal0 I f (x + y))
          simp only [map_add, hx, hy]
      | of n x =>
          rw [I.associatedGradedModule_of_smul_of,
            associatedGradedModuleMapTotal0_of,
            associatedGradedModuleMapTotal0_of,
            I.associatedGradedModule_of_smul_of,
            associatedGradedModuleMap_smul]

private theorem associatedGradedModuleMapTotal0_id
    (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    associatedGradedModuleMapTotal0 I (LinearMap.id : M →ₗ[R] M) =
      LinearMap.id := by
  rw [associatedGradedModuleMapTotal0, ← DirectSum.lmap_id]
  congr 1
  funext n
  exact I.associatedGradedModuleMap_id M n

private theorem associatedGradedModuleMapTotal0_comp
    (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {P : Type z} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    associatedGradedModuleMapTotal0 I (g.comp f) =
      (associatedGradedModuleMapTotal0 I g).comp
        (associatedGradedModuleMapTotal0 I f) := by
  rw [associatedGradedModuleMapTotal0, associatedGradedModuleMapTotal0,
    associatedGradedModuleMapTotal0, ← DirectSum.lmap_comp]
  congr 1
  funext n
  exact I.associatedGradedModuleMap_comp f g n

/-- Let `R` be a commutative ring, `I` an ideal, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. This
is the induced `gr_I R`-linear map `I.AssociatedGradedModule M → I.AssociatedGradedModule N`.
In degree `n`, it sends an initial form `[x]_n` to `[f x]_n`. -/
@[no_expose]
def associatedGradedModuleMapTotal (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    I.AssociatedGradedModule M →ₗ[I.AssociatedGraded]
      I.AssociatedGradedModule N where
  toFun := associatedGradedModuleMapTotal0 I f
  map_add' := map_add _
  map_smul' := associatedGradedModuleMapTotal0_smul I f

/-- Let `R` be a commutative ring, `I` an ideal, `M,N` be `R`-modules, `f : M →ₗ[R] N`, and `n :
ℕ`. For `x ∈ I.AssociatedGradedModulePiece M n`, the total map satisfies `gr_I(f)(j_n(x)) =
j_n(I.associatedGradedModuleMap f n x)`, where `j_n` denotes the degree-`n` direct-sum
inclusion. -/
@[simp]
theorem associatedGradedModuleMapTotal_of (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ)
    (x : I.AssociatedGradedModulePiece M n) :
    I.associatedGradedModuleMapTotal f
        (DirectSum.of (I.AssociatedGradedModulePiece M) n x) =
      DirectSum.of (I.AssociatedGradedModulePiece N) n
        (I.associatedGradedModuleMap f n x) := by
  exact associatedGradedModuleMapTotal0_of I f n x

/-- Let `R` be a commutative ring, `I` an ideal, `M,N` be `R`-modules, `f : M →ₗ[R] N`, `n : ℕ`,
and `x ∈ I^n M`. For the homogeneous inclusions `j_n`, `gr_I(f)(j_n([x]_n)) = j_n([f x]_n)`.
The brackets are the module initial forms in degrees `n` of `M` and `N`. -/
theorem associatedGradedModuleMapTotal_initialFormModule
    (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ)
    (x : ↥(I ^ n • (⊤ : Submodule R M))) :
    I.associatedGradedModuleMapTotal f
        (DirectSum.of (I.AssociatedGradedModulePiece M) n
          (I.initialFormModule M n x)) =
      DirectSum.of (I.AssociatedGradedModulePiece N) n
        (I.initialFormModule N n
          ⟨f x, (Submodule.smul_top_le_comap_smul_top (I ^ n) f) x.2⟩) := by
  rw [I.associatedGradedModuleMapTotal_of,
    I.initialFormModule_apply, I.associatedGradedModuleMap_initialFormModule]

/-- For an ideal `I` in a commutative ring `R` and an `R`-module `M`, the map induced by `id_M` on
the total associated graded module is the identity: `I.associatedGradedModuleMapTotal
(LinearMap.id : M →ₗ[R] M) = LinearMap.id`. -/
@[simp]
theorem associatedGradedModuleMapTotal_id (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] :
    I.associatedGradedModuleMapTotal (LinearMap.id : M →ₗ[R] M) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  change associatedGradedModuleMapTotal0 I (LinearMap.id : M →ₗ[R] M) x = x
  rw [associatedGradedModuleMapTotal0_id]
  rfl

/-- Let `R` be a commutative ring, `I` an ideal, `M,N,P` be `R`-modules, and `f : M →ₗ[R] N`, `g :
N →ₗ[R] P`. The induced total maps satisfy `gr_I(g ∘ f) = gr_I(g) ∘ gr_I(f)` as `gr_I
R`-linear maps `gr_I M → gr_I P`. -/
theorem associatedGradedModuleMapTotal_comp (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    {P : Type z} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    I.associatedGradedModuleMapTotal (g.comp f) =
      (I.associatedGradedModuleMapTotal g).comp
        (I.associatedGradedModuleMapTotal f) := by
  apply LinearMap.ext
  intro x
  change associatedGradedModuleMapTotal0 I (g.comp f) x =
    associatedGradedModuleMapTotal0 I g
      (associatedGradedModuleMapTotal0 I f x)
  exact LinearMap.congr_fun (associatedGradedModuleMapTotal0_comp I f g) x

/-- Let `R` be a commutative ring, `I` an ideal, `M,N` be `R`-modules, and `f : M →ₗ[R] N` a
surjective map. Then `I.associatedGradedModuleMapTotal f : gr_I M → gr_I N` is surjective. -/
theorem associatedGradedModuleMapTotal_surjective (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Function.Surjective (I.associatedGradedModuleMapTotal f) := by
  change Function.Surjective (associatedGradedModuleMapTotal0 I f)
  exact (DirectSum.lmap_surjective _).mpr fun n ↦
    I.associatedGradedModuleMap_surjective f hf n

end Ideal
