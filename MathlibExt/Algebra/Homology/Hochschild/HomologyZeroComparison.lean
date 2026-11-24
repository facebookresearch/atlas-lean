/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.HomologyZero
public import MathlibExt.AlgebraicTopology.AlternatingFaceMapComplex.HomologyZero
public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Degree-zero comparison for characterized Hochschild bars

Degree-zero and degree-one tensor coordinates and the first two
face formulas identify the boundary image with the commutator
submodule. The homology class map then identifies degree-zero
Hochschild homology with the corresponding module quotient.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped TensorProduct Simplicial

universe u

namespace ModuleCat.Algebra.Hochschild.FaceValues

variable (k A M : Type u) [CommRing k] [Ring A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [Module Aᵐᵒᵖ M]

/-- The span of the right-minus-left boundary values. -/
def boundarySubmodule : Submodule k M :=
  Submodule.span k
    (Set.range (fun p : A × M => MulOpposite.op p.1 • p.2 - p.1 • p.2))

omit [Algebra k A] in
/-- Reversing all generator signs gives the commutator submodule of the
Hochschild coefficient quotient. -/
theorem boundarySubmodule_eq_commutatorSubmodule :
    boundarySubmodule k A M = Hochschild.commutatorSubmodule k A M := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨⟨a, m⟩, rfl⟩
    change MulOpposite.op a • m - a • m ∈ Hochschild.commutatorSubmodule k A M
    simpa only [neg_sub] using
      (Hochschild.commutatorSubmodule k A M).neg_mem
        (Hochschild.commutator_mem k A M a m)
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨⟨a, m⟩, rfl⟩
    change a • m - MulOpposite.op a • m ∈ boundarySubmodule k A M
    have h : MulOpposite.op a • m - a • m ∈ boundarySubmodule k A M :=
      Submodule.subset_span ⟨(a, m), rfl⟩
    simpa only [neg_sub] using (boundarySubmodule k A M).neg_mem h

variable {k A M}

variable (X : SimplicialObject (ModuleCat.{u} ℤ))
  (e₀ : X _⦋0⦌ ≅
    (ModuleCat.restrictScalars (Int.castRingHom k)).obj (ModuleCat.of k M))
  (e₁ : X _⦋1⦌ ≅
    (ModuleCat.restrictScalars (Int.castRingHom k)).obj
      (ModuleCat.of k (M ⊗[k] A)))

/-- A face map in the specified coefficient coordinates. The
restriction-of-scalars object types fix the integer module structures. -/
def coordinateFace (i : Fin 2) :
    ((ModuleCat.restrictScalars (Int.castRingHom k)).obj
      (ModuleCat.of k (M ⊗[k] A))).carrier →ₗ[ℤ]
    ((ModuleCat.restrictScalars (Int.castRingHom k)).obj
      (ModuleCat.of k M)).carrier :=
  (e₁.inv ≫ X.δ i ≫ e₀.hom).hom

variable
  (hRight : ∀ (m : M) (a : A),
    coordinateFace X e₀ e₁ 0 (m ⊗ₜ[k] a) = MulOpposite.op a • m)
  (hLeft : ∀ (m : M) (a : A),
    coordinateFace X e₀ e₁ 1 (m ⊗ₜ[k] a) = a • m)

omit [Module A M] in
include hRight in
/-- Tensor balancing with the unit forces the right action of the
algebra map to equal the given ground-ring action. -/
theorem rightGroundSmul (s : k) (m : M) :
    MulOpposite.op (algebraMap k A s) • m = s • m := by
  have h := congrArg (coordinateFace X e₀ e₁ 0)
    (TensorProduct.smul_tmul s m (1 : A))
  rw [hRight, hRight, MulOpposite.op_one, one_smul,
    Algebra.smul_def, mul_one] at h
  exact h.symm

omit [Module Aᵐᵒᵖ M] in
include hLeft in
/-- The left action has the same forced ground-ring compatibility. -/
theorem leftGroundSmul (s : k) (m : M) :
    algebraMap k A s • m = s • m := by
  have h := congrArg (coordinateFace X e₀ e₁ 1)
    (TensorProduct.smul_tmul s m (1 : A))
  rw [hLeft, hLeft, one_smul, Algebra.smul_def, mul_one] at h
  exact h.symm

private theorem algebraAction_smul_comm (B : Type u) [Ring B] [Algebra k B]
    [Module B M] (h : ∀ (s : k) (m : M), algebraMap k B s • m = s • m)
    (s : k) (b : B) (m : M) : b • (s • m) = s • (b • m) := by
  calc
    b • (s • m) = b • (algebraMap k B s • m) := by rw [h]
    _ = (b * algebraMap k B s) • m := (mul_smul _ _ _).symm
    _ = (algebraMap k B s * b) • m :=
      congrArg (fun a : B => a • m) (Algebra.commutes s b).symm
    _ = algebraMap k B s • (b • m) := mul_smul _ _ _
    _ = s • (b • m) := h s (b • m)

include hRight hLeft in
/-- The transported boundary is ground-ring linear. Its underlying
function is the difference of the two transported native faces. -/
def boundaryLinearMap : M ⊗[k] A →ₗ[k] M where
  toFun x := (coordinateFace X e₀ e₁ 0 - coordinateFace X e₀ e₁ 1) x
  map_add' := (coordinateFace X e₀ e₁ 0 - coordinateFace X e₀ e₁ 1).map_add
  map_smul' s x := by
    have hr : ∀ (s : k) (m : M), algebraMap k Aᵐᵒᵖ s • m = s • m := by
      intro s m
      simpa only [MulOpposite.algebraMap_apply] using rightGroundSmul X e₀ e₁ hRight s m
    have hl : ∀ (s : k) (m : M), algebraMap k A s • m = s • m :=
      leftGroundSmul X e₀ e₁ hLeft
    let b : M ⊗[k] A → M :=
      fun y => (coordinateFace X e₀ e₁ 0 - coordinateFace X e₀ e₁ 1) y
    change b (s • x) = s • b x
    have hbadd (y z : M ⊗[k] A) : b (y + z) = b y + b z :=
      (coordinateFace X e₀ e₁ 0 - coordinateFace X e₀ e₁ 1).map_add y z
    have hbtmul (m : M) (a : A) :
        b (m ⊗ₜ[k] a) = MulOpposite.op a • m - a • m :=
      congrArg₂ (fun x y : M => x - y) (hRight m a) (hLeft m a)
    induction x using TensorProduct.inductionOn with
    | tmul m a =>
      calc
        b (s • (m ⊗ₜ[k] a)) = b ((s • m) ⊗ₜ[k] a) :=
          congrArg b (TensorProduct.smul_tmul' s m a)
        _ = MulOpposite.op a • (s • m) - a • (s • m) := hbtmul (s • m) a
        _ = s • (MulOpposite.op a • m) - s • (a • m) :=
          congrArg₂ (fun x y : M => x - y)
            (algebraAction_smul_comm Aᵐᵒᵖ hr s (MulOpposite.op a) m)
            (algebraAction_smul_comm A hl s a m)
        _ = s • (MulOpposite.op a • m - a • m) := (smul_sub s _ _).symm
        _ = s • b (m ⊗ₜ[k] a) :=
          congrArg (fun y : M => s • y) (hbtmul m a).symm
    | add x y hx hy =>
      calc
        b (s • (x + y)) = b (s • x + s • y) := congrArg b (smul_add s x y)
        _ = b (s • x) + b (s • y) := hbadd (s • x) (s • y)
        _ = s • b x + s • b y := congrArg₂ (fun x y : M => x + y) hx hy
        _ = s • (b x + b y) := (smul_add s (b x) (b y)).symm
        _ = s • b (x + y) := congrArg (fun z : M => s • z) (hbadd x y).symm

@[simp]
theorem boundaryLinearMap_tmul (m : M) (a : A) :
    boundaryLinearMap X e₀ e₁ hRight hLeft (m ⊗ₜ[k] a) =
      MulOpposite.op a • m - a • m := by
  exact congrArg₂ (fun x y : M => x - y) (hRight m a) (hLeft m a)

/-- Pure tensors generate, so this is the full image computation. -/
theorem range_boundaryLinearMap :
    LinearMap.range (boundaryLinearMap X e₀ e₁ hRight hLeft) =
      boundarySubmodule k A M := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul m a =>
      rw [boundaryLinearMap_tmul]
      exact Submodule.subset_span ⟨(a, m), rfl⟩
    | add x y hx hy =>
      rw [map_add]
      exact (boundarySubmodule k A M).add_mem hx hy
  · refine Submodule.span_le.mpr ?_
    rintro y ⟨⟨a, m⟩, rfl⟩
    exact ⟨m ⊗ₜ[k] a, boundaryLinearMap_tmul X e₀ e₁ hRight hLeft m a⟩

/-- The degree-one differential square, before taking any homology. -/
theorem bottomDifferential_square :
    (AlternatingFaceMapComplex.obj X).d 1 0 ≫ e₀.hom =
      e₁.hom ≫ (ModuleCat.restrictScalars (Int.castRingHom k)).map
        (ModuleCat.ofHom (boundaryLinearMap X e₀ e₁ hRight hLeft)) := by
  apply (cancel_epi e₁.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [AlternatingFaceMapComplex.degreeOneDifferential_eq_sub X]
  ext x
  change e₀.hom.hom
    ((X.δ (0 : Fin 2) - X.δ (1 : Fin 2)).hom (e₁.inv.hom x)) =
      boundaryLinearMap X e₀ e₁ hRight hLeft x
  rw [ModuleCat.hom_sub, LinearMap.sub_apply, map_sub]
  rfl

/-- The quotient projection, in the original additive chain coordinates. -/
def quotientProjection : X _⦋0⦌ ⟶
    (ModuleCat.restrictScalars (Int.castRingHom k)).obj
      (ModuleCat.of k (M ⧸ boundarySubmodule k A M)) :=
  e₀.hom ≫ (ModuleCat.restrictScalars (Int.castRingHom k)).map
    (ModuleCat.ofHom (boundarySubmodule k A M).mkQ)

include hRight hLeft in
/-- Restriction of scalars retains the computed quotient exactness; the
bottom square transports it back to the original integer complex. -/
theorem differential_exact_quotientProjection :
    Function.Exact ((AlternatingFaceMapComplex.obj X).d 1 0).hom
      (quotientProjection (A := A) X e₀).hom := by
  let U : ModuleCat.{u} k ⥤ ModuleCat.{u} ℤ :=
    ModuleCat.restrictScalars (Int.castRingHom k)
  let b := U.map (ModuleCat.ofHom (boundaryLinearMap X e₀ e₁ hRight hLeft))
  let q := U.map (ModuleCat.ofHom (boundarySubmodule k A M).mkQ)
  have hExact : Function.Exact b.hom q.hom := by
    change Function.Exact (boundaryLinearMap X e₀ e₁ hRight hLeft)
      (boundarySubmodule k A M).mkQ
    apply LinearMap.exact_iff.mpr
    rw [Submodule.ker_mkQ, range_boundaryLinearMap]
  exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective
    ((AlternatingFaceMapComplex.obj X).d 1 0).hom (quotientProjection (A := A) X e₀).hom
    b.hom q.hom e₁.hom.hom e₀.hom.hom LinearMap.id
    (by
      simpa only [ModuleCat.hom_comp] using congrArg
        (fun f : X _⦋1⦌ ⟶ U.obj (ModuleCat.of k M) => f.hom)
        (bottomDifferential_square X e₀ e₁ hRight hLeft).symm)
    (by rfl) e₁.toLinearEquiv.surjective e₀.toLinearEquiv.bijective
    (fun _ _ h => h)).mpr hExact

omit [Algebra k A] in
theorem quotientProjection_surjective :
    Function.Surjective (quotientProjection (A := A) X e₀).hom := by
  change Function.Surjective
    (fun x => (boundarySubmodule k A M).mkQ (e₀.hom.hom x))
  exact (boundarySubmodule k A M).mkQ_surjective.comp e₀.toLinearEquiv.surjective

include hRight hLeft in
/-- The quotient kills the native differential. -/
theorem differential_quotientProjection :
    (AlternatingFaceMapComplex.obj X).d 1 0 ≫ quotientProjection (A := A) X e₀ = 0 := by
  ext x
  exact (differential_exact_quotientProjection X e₀ e₁ hRight hLeft).apply_apply_eq_zero x

include hRight hLeft in
/-- The coefficient quotient as a cofork of the two faces. -/
def quotientCofork : Cofork (X.δ (0 : Fin 2)) (X.δ (1 : Fin 2)) :=
  Cofork.ofπ (quotientProjection (A := A) X e₀) (by
    apply sub_eq_zero.mp
    rw [← Preadditive.sub_comp,
      ← AlternatingFaceMapComplex.degreeOneDifferential_eq_sub X]
    exact differential_quotientProjection X e₀ e₁ hRight hLeft)

/-- The native integer-module cokernel API earns the quotient universal
property from the computed exactness and surjectivity. -/
def quotientCoforkIsColimit : IsColimit (quotientCofork X e₀ e₁ hRight hLeft) := by
  have hExact : Function.Exact (X.δ (0 : Fin 2) - X.δ (1 : Fin 2)).hom
      (quotientProjection (A := A) X e₀).hom := by
    rw [← AlternatingFaceMapComplex.degreeOneDifferential_eq_sub X]
    exact differential_exact_quotientProjection X e₀ e₁ hRight hLeft
  exact Preadditive.isColimitCoforkOfCokernelCofork
    (ModuleCat.isColimitCokernelCofork
      (X.δ (0 : Fin 2) - X.δ (1 : Fin 2)) (quotientProjection (A := A) X e₀)
      hExact (quotientProjection_surjective (A := A) X e₀))

/-- The characterized bar homology is the coefficient quotient,
using uniqueness of the two coequalizer coforks. -/
def homologyZeroIso : (AlternatingFaceMapComplex.obj X).homology 0 ≅
    (ModuleCat.restrictScalars (Int.castRingHom k)).obj
      (ModuleCat.of k (M ⧸ boundarySubmodule k A M)) :=
  IsColimit.coconePointUniqueUpToIso
    (AlternatingFaceMapComplex.homologyZeroCoforkIsColimit X)
    (quotientCoforkIsColimit X e₀ e₁ hRight hLeft)

@[reassoc]
theorem homologyZeroIso_class :
    AlternatingFaceMapComplex.homologyZeroClass X ≫
      (homologyZeroIso X e₀ e₁ hRight hLeft).hom = quotientProjection (A := A) X e₀ :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (AlternatingFaceMapComplex.homologyZeroCoforkIsColimit X)
    (quotientCoforkIsColimit X e₀ e₁ hRight hLeft) WalkingParallelPair.one

end ModuleCat.Algebra.Hochschild.FaceValues
