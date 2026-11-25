/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.PicardGroup

/-! # Duals of submodules of the fraction field -/

@[expose] public noncomputable section

open scoped nonZeroDivisors
open Module

variable {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] [IsFractionRing A K] in
/-- **The multiplication dual is a colon quotient.** Let $A$ be a commutative ring and $K$ a field
that is an $A$-algebra, and write $1$ for the $A$-submodule $A \cdot 1$ of $K$. For every
$A$-submodule $M$ of $K$, the dual submodule of $M$ with respect to the multiplication form
$(x, y) \mapsto xy$ on $K$ equals the quotient $1 / M$, the set of $x \in K$ with $xy \in A \cdot 1$
for all $y \in M$. -/
theorem dualSubmodule_mul_eq_div (M : Submodule A K) :
    LinearMap.BilinForm.dualSubmodule (LinearMap.mul K K : LinearMap.BilinForm K K) M =
      (1 : Submodule A K) / M := by
  ext x
  simp only [LinearMap.BilinForm.mem_dualSubmodule, Submodule.mem_div_iff_forall_mul_mem,
    LinearMap.mul_apply']

/-- **Functionals on a submodule of the fraction field are multiplications.** Let $A$ be an
integral domain with fraction field $K$ and let $M$ be a nonzero $A$-submodule of $K$. For every
$A$-linear map $f \colon M \to A$ there is $x \in K$ such that the image of $f(m)$ in $K$ equals
$xm$ for every $m \in M$. -/
theorem Submodule.exists_mul_rep (M : Submodule A K) (hM : M ≠ ⊥)
    (f : Module.Dual A M) :
    ∃ x : K, ∀ m : M, algebraMap A K (f m) = x * m := by
  obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff M).mp hM
  let mm : M := ⟨m, hmM⟩
  refine ⟨algebraMap A K (f mm) / m, fun y ↦ ?_⟩
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A ((y : K) / m)
  have hb0 : algebraMap A K b ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors (algebraMap A K) (IsFractionRing.injective A K) hb
  have hcross : algebraMap A K a * m = algebraMap A K b * (y : K) := by
    rw [div_eq_div_iff hb0 hm0] at hab
    simpa [mul_comm] using hab
  have hsub : b • y = a • mm := by
    apply Subtype.ext
    simpa [Algebra.smul_def, mm] using hcross.symm
  have hfrel : b * f y = a * f mm := by
    have := congrArg f hsub
    simpa only [map_smul, smul_eq_mul] using this
  have hmap : algebraMap A K b * algebraMap A K (f y) =
      algebraMap A K a * algebraMap A K (f mm) := by
    simpa only [map_mul] using congrArg (algebraMap A K) hfrel
  apply mul_left_cancel₀ hb0
  rw [hmap]
  calc algebraMap A K a * algebraMap A K (f mm) =
      algebraMap A K (f mm) / m * (algebraMap A K a * m) := by field_simp
    _ = algebraMap A K b * (algebraMap A K (f mm) / m * (y : K)) := by rw [hcross]; ring

omit [CommRing A] [IsDomain A] [Algebra A K] [IsFractionRing A K] in
/-- **Multiplication is a nondegenerate bilinear form.** For every field $K$, the $K$-bilinear
form $(x, y) \mapsto xy$ on $K$ is nondegenerate: if $xy = 0$ for all $y \in K$ then $x = 0$, and
if $xy = 0$ for all $x \in K$ then $y = 0$. -/
theorem LinearMap.BilinForm.mul_nondegenerate :
    (LinearMap.mul K K : LinearMap.BilinForm K K).Nondegenerate := by
  constructor
  · intro x hx; simpa using hx 1
  · intro y hy; simpa using hy 1

omit [IsDomain A] [IsFractionRing A K] in
/-- **A nonzero submodule spans the field.** Let $A$ be a commutative ring and $K$ a field that is
an $A$-algebra. Then every nonzero $A$-submodule $M$ of $K$ spans $K$ as a $K$-vector space. -/
theorem Submodule.span_coe_eq_top (M : Submodule A K) (hM : M ≠ ⊥) :
    Submodule.span K (M : Set K) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨m, hmM, hm0⟩ := (Submodule.ne_bot_iff M).mp hM
  rw [← div_mul_cancel₀ x hm0, ← smul_eq_mul]
  exact Submodule.smul_mem _ (x / m) (Submodule.subset_span hmM)

/-- **Every functional comes from the multiplication dual.** Let $A$ be an integral domain with
fraction field $K$, identify $A$ with its image in $K$, and let $M$ be a nonzero $A$-submodule of
$K$. Let $M^\vee = \{x \in K : xy \in A \text{ for all } y \in M\}$ be the dual submodule of $M$
for the multiplication form $(x, y) \mapsto xy$ on $K$. Then the $A$-linear map
$M^\vee \to \operatorname{Hom}_A(M, A)$ sending $x$ to the functional $y \mapsto xy$ on $M$ is
surjective. -/
theorem Submodule.mul_dualSubmoduleToDual_surjective (M : Submodule A K) (hM : M ≠ ⊥) :
    Function.Surjective (LinearMap.BilinForm.dualSubmoduleToDual
      (LinearMap.mul K K : LinearMap.BilinForm K K) M) := by
  intro f
  obtain ⟨x, hx⟩ := Submodule.exists_mul_rep M hM f
  let xdual : LinearMap.BilinForm.dualSubmodule (LinearMap.mul K K : LinearMap.BilinForm K K) M :=
    ⟨x, fun y hy ↦ by
      change x * y ∈ (1 : Submodule A K)
      rw [← hx ⟨y, hy⟩]
      exact Submodule.mem_one.mpr ⟨f ⟨y, hy⟩, rfl⟩⟩
  refine ⟨xdual, LinearMap.ext fun y ↦ ?_⟩
  apply IsFractionRing.injective A K
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply,
    LinearMap.BilinForm.dualSubmoduleParing_spec, hx]
  rfl

/-- **Dual of a nonzero submodule of the fraction field.** Let $A$ be an integral domain with
fraction field $K$, identify $A$ with its image in $K$, and let $M$ be a nonzero $A$-submodule of
$K$. Let $M^\vee = \{x \in K : xy \in A \text{ for all } y \in M\}$ be the dual submodule of $M$
for the multiplication form $(x, y) \mapsto xy$ on $K$. This is the $A$-linear isomorphism
$\operatorname{Hom}_A(M, A) \to M^\vee$ inverse to the map sending $x \in M^\vee$ to the
functional $y \mapsto xy$ on $M$; it sends $f$ to the unique $x \in M^\vee$ with $f(y) = xy$ for
all $y \in M$. -/
noncomputable def Submodule.dualEquivMulDualSubmodule (M : Submodule A K) (hM : M ≠ ⊥) :
    Module.Dual A M ≃ₗ[A] LinearMap.BilinForm.dualSubmodule
      (LinearMap.mul K K : LinearMap.BilinForm K K) M :=
  (LinearEquiv.ofBijective (LinearMap.BilinForm.dualSubmoduleToDual
      (LinearMap.mul K K : LinearMap.BilinForm K K) M)
    ⟨LinearMap.BilinForm.dualSubmoduleToDual_injective _
      LinearMap.BilinForm.mul_nondegenerate M
      (Submodule.span_coe_eq_top M hM),
      Submodule.mul_dualSubmoduleToDual_surjective M hM⟩).symm

/-- **Formula for the isomorphism onto the multiplication dual.** Let $A$ be an integral domain
with fraction field $K$, let $M$ be a nonzero $A$-submodule of $K$, and let
$\varphi \colon \operatorname{Hom}_A(M, A) \to M^\vee$ be the isomorphism onto the dual submodule
$M^\vee$ of $M$ for the multiplication form $(x, y) \mapsto xy$ on $K$. Then for every
$f \in \operatorname{Hom}_A(M, A)$ and every $m \in M$, the image of $f(m)$ in $K$ equals
$\varphi(f) \, m$. -/
theorem Submodule.dualEquivMulDualSubmodule_spec (M : Submodule A K) (hM : M ≠ ⊥)
    (f : Module.Dual A M) (m : M) :
    algebraMap A K (f m) = (Submodule.dualEquivMulDualSubmodule M hM f : K) * (m : K) := by
  have hfun : LinearMap.BilinForm.dualSubmoduleToDual
      (LinearMap.mul K K : LinearMap.BilinForm K K) M
      (Submodule.dualEquivMulDualSubmodule M hM f) = f :=
    LinearEquiv.symm_apply_apply (Submodule.dualEquivMulDualSubmodule M hM) f
  have hcon := congrArg (fun g : Module.Dual A M => g m) hfun
  have hmap := congrArg (algebraMap A K) hcon
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply,
    LinearMap.BilinForm.dualSubmoduleParing_spec] at hmap
  exact hmap.symm

/-- **The inverse of a nonzero fractional ideal is its multiplication dual.** Let $A$ be an
integral domain with fraction field $K$, and let $I$ be a nonzero fractional ideal of $A$ in $K$.
Then $I^{-1}$, viewed as an $A$-submodule of $K$, equals the dual submodule of $I$ with respect
to the multiplication form $(x, y) \mapsto xy$ on $K$, namely the set
$\{x \in K : xy \in A \text{ for all } y \in I\}$, where $A$ is identified with its image in $K$. -/
theorem FractionalIdeal.coe_inv_eq_mul_dualSubmodule
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    ((I⁻¹ : FractionalIdeal A⁰ K) : Submodule A K) =
      LinearMap.BilinForm.dualSubmodule
        (LinearMap.mul K K : LinearMap.BilinForm K K)
        (I : Submodule A K) := by
  ext x
  change x ∈ (I⁻¹ : FractionalIdeal A⁰ K) ↔ _
  rw [FractionalIdeal.mem_inv_iff hI]
  simp [LinearMap.BilinForm.mem_dualSubmodule, FractionalIdeal.mem_coe]

/-- **Dual of a nonzero fractional ideal is its inverse.** Let $A$ be an integral domain with
fraction field $K$ and let $I$ be a nonzero fractional ideal of $A$ in $K$. This is the $A$-linear
isomorphism $\operatorname{Hom}_A(I, A) \to I^{-1}$, with $I^{-1}$ viewed as an $A$-submodule of
$K$, sending $f$ to the unique $x \in I^{-1}$ such that $f(y) = xy$ in $K$ for all $y \in I$
(where $A$ is identified with its image in $K$). -/
noncomputable def FractionalIdeal.dualEquivInv
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0) :
    Module.Dual A (I : Submodule A K) ≃ₗ[A]
      ((I⁻¹ : FractionalIdeal A⁰ K) : Submodule A K) := by
  have hM : (I : Submodule A K) ≠ ⊥ :=
    FractionalIdeal.coeToSubmodule_ne_bot.mpr hI
  exact (Submodule.dualEquivMulDualSubmodule (I : Submodule A K) hM).trans
    (LinearEquiv.ofEq _ _
      (FractionalIdeal.coe_inv_eq_mul_dualSubmodule I hI).symm)

/-- **Double dual of an invertible fractional ideal.** Let $A$ be an integral domain with fraction
field $K$ and let $I$ be an invertible fractional ideal of $A$ in $K$. This is the $A$-linear
isomorphism $\operatorname{Hom}_A(\operatorname{Hom}_A(I, A), A) \to I$ inverse to the canonical
evaluation map $I \to \operatorname{Hom}_A(\operatorname{Hom}_A(I, A), A)$,
$x \mapsto (f \mapsto f(x))$. -/
noncomputable def FractionalIdeal.doubleDualEquivOfIsUnit
    (I : FractionalIdeal A⁰ K) (hI : IsUnit I) :
    Module.Dual A (Module.Dual A (I : Submodule A K)) ≃ₗ[A]
      (I : Submodule A K) := by
  haveI : Module.Finite A (I : Submodule A K) :=
    Module.Finite.of_fg (FractionalIdeal.fg_of_isUnit I hI)
  have hcoe : IsUnit (I : Submodule A K) :=
    hI.map (FractionalIdeal.coeSubmoduleHom A⁰ K)
  haveI : Module.Projective A (I : Submodule A K) := by
    apply Submodule.projective_of_isUnit
    exact hcoe
  exact (Module.evalEquiv A (I : Submodule A K)).symm
