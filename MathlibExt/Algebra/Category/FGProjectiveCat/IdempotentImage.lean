/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.FiniteFreeComplement
public import MathlibExt.Algebra.Category.FGProjectiveCat.BaseChange
public import Mathlib.LinearAlgebra.Projection

/-!
# Actual scalar idempotent images of finite projectives

The scalar ranges of e and 1-e are actual finite projective submodules
and give the original module's direct-sum decomposition.
-/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v w

namespace FGProjectiveCat

variable {R : Type u} [CommRing R] {e : R}

private theorem scalar_isIdempotent (he : IsIdempotentElem e) (M : FGProjectiveCat.{v} R) :
    IsIdempotentElem (e • (LinearMap.id : M →ₗ[R] M)) := by
  ext m
  change e • (e • m) = e • m
  rw [smul_smul, he.eq]

/-- The actual range of scalar multiplication by an idempotent on a finite projective module. -/
def idempotentImage (he : IsIdempotentElem e) (M : FGProjectiveCat.{v} R) :
    FGProjectiveCat.{v} R := by
  let p := e • (LinearMap.id : M →ₗ[R] M)
  refine ⟨ModuleCat.of R p.range, inferInstance, ?_⟩
  apply Module.Projective.of_split p.range.subtype p.rangeRestrict
  ext m
  obtain ⟨x, hx⟩ := m.property
  change e • m.val = m.val
  rw [← hx]
  change e • (e • x) = e • x
  rw [smul_smul, he.eq]

/-- The scalar acts as the identity on its actual image submodule. -/
theorem idempotentImage_fixed (he : IsIdempotentElem e) (M : FGProjectiveCat.{v} R)
    (m : idempotentImage he M) : e • m.val = m.val :=
  (LinearMap.IsIdempotentElem.mem_range_iff (scalar_isIdempotent he M)).mp m.property

/-- A finite projective module splits into the actual ranges of `e` and `1-e`. -/
def idempotentDecompositionIso (he : IsIdempotentElem e) (M : FGProjectiveCat.{v} R) :
    M ≅ idempotentImage he M ⊞ idempotentImage he.one_sub M := by
  let p := e • (LinearMap.id : M →ₗ[R] M)
  let q := (1 - e) • (LinearMap.id : M →ₗ[R] M)
  have hp : IsIdempotentElem p := by
    ext m
    change e • (e • m) = e • m
    rw [smul_smul, he.eq]
  have hq : 1 - p = q := by
    ext m
    simp [p, q, sub_smul]
  have hk : p.ker = q.range := by
    rw [← hq]
    exact LinearMap.IsIdempotentElem.ker_eq_range_one_sub hp
  have hc : IsCompl p.range q.range := by
    rw [← hk]
    exact LinearMap.IsIdempotentElem.isCompl hp
  let split : M ≃ₗ[R] p.range × q.range :=
    (Submodule.prodEquivOfIsCompl p.range q.range hc).symm
  let F := FGProjectiveCat.toModuleCat (R := R)
  let P := idempotentImage he M
  let Q := idempotentImage he.one_sub M
  let _ : PreservesBiproduct (pairFunction P Q) F := inferInstance
  let _ : PreservesBinaryBiproduct P Q F :=
    preservesBinaryBiproduct_of_preservesBiproduct F P Q
  let carrier : ((P ⊞ Q : FGProjectiveCat.{v} R) : Type v) ≃ₗ[R] (P × Q) :=
    ((F.mapBiprod P Q).trans (ModuleCat.biprodIsoProd P.obj Q.obj)).toLinearEquiv
  exact LinearEquiv.toFGProjectiveCatIso (split.trans carrier.symm)

private theorem baseChange_isZero_of_fixed {S : Type w} [CommRing S] (f : R →+* S)
    (a : R) (ha : f a = 0) (M : FGProjectiveCat.{v} R) (hM : ∀ m : M.obj, a • m = m) :
    IsZero ((baseChange f).obj M) := by
  have hzero : ∀ z : TensorProduct R
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) M.obj, z = 0 := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
        calc
          s ⊗ₜ[R] m = s ⊗ₜ[R] (a • m) := congrArg (fun n => s ⊗ₜ[R] n) (hM m).symm
          _ = (a • s) ⊗ₜ[R] m :=
            (TensorProduct.tmul_smul a s m).trans (TensorProduct.smul_tmul' a s m)
          _ = 0 := by
            have hs : (a • s : (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) = 0 := by
              change f a * (show S from s) = (0 : S)
              rw [ha, zero_mul]
            rw [hs]
            exact TensorProduct.zero_tmul _ _
    | add x y hx hy => rw [hx, hy, zero_add]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply FGProjectiveCat.hom_ext
  ext z
  change z = 0
  exact hzero z

/-- Quotient scalar extension annihilates the actual image object, in every module universe. -/
theorem idempotentImage_quotient_isZero (he : IsIdempotentElem e)
    (M : FGProjectiveCat.{v} R) :
    IsZero ((baseChange (Ideal.Quotient.mk (Ideal.span {e}))).obj (idempotentImage he M)) := by
  apply baseChange_isZero_of_fixed _ e
  · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton e))
  · intro m
    apply Subtype.ext
    exact idempotentImage_fixed he M m

/-- The original quotient scalar-extension object has its earned isomorphism to zero. -/
def idempotentImageQuotientIsoZero (he : IsIdempotentElem e) (M : FGProjectiveCat.{v} R) :
    (baseChange (Ideal.Quotient.mk (Ideal.span {e}))).obj (idempotentImage he M) ≅
      (0 : FGProjectiveCat.{max u v} (R ⧸ Ideal.span {e})) :=
  (idempotentImage_quotient_isZero he M).isoZero

end FGProjectiveCat

end
