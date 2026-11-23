/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported from `TauCeti/Topology/Algebra/Module/ContinuousLinearMap/IdempotentRange.lean` in
TauCetiProject/TauCeti (https://github.com/TauCetiProject/TauCeti) at revision
62bbc0596dc3539d488232e4e924a338548ea0a9; the copyright and license notice above are the
source's. Modification: imports of the coupled ports point to `MathlibExt`; declarations and
proofs are unchanged.
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import Mathlib.Tactic.Abel

/-!
# Ranges of intertwined projections

For idempotent continuous linear maps `p` and `q` on a topological module, the operator
`U = q * p + (1 - q) * (1 - p)` satisfies `q * U = U * p`. When `U` is invertible, it therefore
carries the range of `p` isomorphically onto the range of `q`
(`ContinuousLinearMap.IsIdempotentElem.rangeEquiv`). This is the intertwining operator of a pair
of projections; it is the local chart of the image bundle of a continuous family of projections,
and it shows that nearby projections have isomorphic ranges.

For a retract `r ∘ i = id` of `M` through `N`, the extension `i ∘ e ∘ r` of an endomorphism `e`
of `M` is idempotent when `e` is, and `i` identifies the range of `e` with the range of
`i ∘ e ∘ r` (`ContinuousLinearMap.rangeEquivOfRetract`).

A pseudo-inverse `g` of `f`, with `f ∘ g ∘ f = f`, gives the projection `g ∘ f`
(`ContinuousLinearMap.isIdempotentElem_comp_of_comp_comp_eq_self`).

## Main definitions

* `ContinuousLinearMap.IsIdempotentElem.rangeEquiv`: the isomorphism of the ranges of `p` and
  `q` induced by `q * p + (1 - q) * (1 - p)`, when that operator is invertible.
* `ContinuousLinearMap.rangeEquivOfRetract`: the identification of the range of `e` with the
  range of its extension `i ∘ e ∘ r` along a retract.

## Main results

* `ContinuousLinearMap.IsIdempotentElem.apply_coe_range`: an idempotent continuous linear map
  fixes every vector of its range.
* `ContinuousLinearMap.IsIdempotentElem.mul_self_add_one_sub_mul_one_sub`: the operator
  `p * p + (1 - p) * (1 - p)` intertwining an idempotent `p` with itself is the identity.
* `ContinuousLinearMap.isIdempotentElem_comp_comp_of_retract`: the extension of an idempotent
  along a retract is idempotent.
* `ContinuousLinearMap.isIdempotentElem_comp_of_comp_comp_eq_self`: if `g` is a pseudo-inverse
  of `f`, then `g ∘ f` is a continuous projection.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer, Chapter I, §4.6, for the
  intertwining operator of a pair of projections.
-/

public section

open scoped Ring

namespace ContinuousLinearMap.IsIdempotentElem

variable {R M : Type*} [Ring R] [TopologicalSpace M] [AddCommGroup M] [Module R M]
  {p q : M →L[R] M}

/-- An idempotent continuous linear map fixes every vector of its range. -/
@[simp]
theorem apply_coe_range (hp : IsIdempotentElem p) (w : p.range) : p w = w :=
  (LinearMap.IsIdempotentElem.mem_range_iff
    (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp)).mp w.2

variable [IsTopologicalAddGroup M]

/-- The operator `p * p + (1 - p) * (1 - p)`, which intertwines an idempotent `p` with itself, is
the identity. -/
theorem mul_self_add_one_sub_mul_one_sub (hp : IsIdempotentElem p) :
    p * p + (1 - p) * (1 - p) = 1 := by
  rw [hp.eq, hp.one_sub.eq, add_sub_cancel]

/-- The operator `p * p + (1 - p) * (1 - p)` is invertible for an idempotent `p`. -/
theorem isUnit_mul_self_add_one_sub_mul_one_sub (hp : IsIdempotentElem p) :
    IsUnit (p * p + (1 - p) * (1 - p)) := by
  rw [mul_self_add_one_sub_mul_one_sub hp]
  exact isUnit_one

/-- The operator `q * p + (1 - q) * (1 - p)`, which intertwines `p` with `q`. -/
private def intertwiner (p q : M →L[R] M) : M →L[R] M :=
  q * p + (1 - q) * (1 - p)

private theorem mul_intertwiner (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    q * intertwiner p q = intertwiner p q * p := by
  have h := hq.eq
  have h₀ := hp.eq
  simp only [intertwiner, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul, ← mul_assoc, h]
  simp only [mul_assoc, h₀]
  abel

/-- Where the intertwiner is invertible, its inverse intertwines `q` with `p`. -/
private theorem inverse_intertwiner_mul (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (intertwiner p q)) :
    (intertwiner p q)⁻¹ʳ * q = p * (intertwiner p q)⁻¹ʳ := by
  have h := congr((intertwiner p q)⁻¹ʳ * $(mul_intertwiner hp hq) * (intertwiner p q)⁻¹ʳ)
  simpa only [mul_assoc, Ring.mul_inverse_cancel _ hU, Ring.inverse_mul_cancel_left _ _ hU,
    mul_one] using h

private theorem apply_intertwiner (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) (v : M) :
    q (intertwiner p q v) = intertwiner p q (p v) :=
  congr($(mul_intertwiner hp hq) v)

private theorem inverse_intertwiner_apply (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (intertwiner p q)) (v : M) :
    (intertwiner p q)⁻¹ʳ (q v) = p ((intertwiner p q)⁻¹ʳ v) :=
  congr($(inverse_intertwiner_mul hp hq hU) v)

private theorem intertwiner_mem_range (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (w : p.range) : intertwiner p q w ∈ q.range :=
  ⟨intertwiner p q w,
    (apply_intertwiner hp hq w).trans congr(intertwiner p q $(apply_coe_range hp w))⟩

private theorem inverse_intertwiner_mem_range (hp : IsIdempotentElem p)
    (hq : IsIdempotentElem q) (hU : IsUnit (intertwiner p q)) (w : q.range) :
    (intertwiner p q)⁻¹ʳ w ∈ p.range :=
  ⟨(intertwiner p q)⁻¹ʳ w,
    (inverse_intertwiner_apply hp hq hU w).symm.trans
      congr((intertwiner p q)⁻¹ʳ $(apply_coe_range hq w))⟩

/-- **Intertwined projections have isomorphic ranges.** For idempotents `p` and `q` such that
`U = q * p + (1 - q) * (1 - p)` is invertible, `U` restricts to an isomorphism from the range
of `p` onto the range of `q`, with inverse the restriction of `U⁻¹`. -/
noncomputable def rangeEquiv (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hU : IsUnit (q * p + (1 - q) * (1 - p))) : p.range ≃L[R] q.range :=
  .equivOfInverse ((intertwiner p q ∘L p.range.subtypeL).codRestrict q.range
      (intertwiner_mem_range hp hq))
    (((intertwiner p q)⁻¹ʳ ∘L q.range.subtypeL).codRestrict p.range
      (inverse_intertwiner_mem_range hp hq hU))
    (fun w ↦ Subtype.ext (congr($(Ring.inverse_mul_cancel _ hU) (w : M))))
    (fun w ↦ Subtype.ext (congr($(Ring.mul_inverse_cancel _ hU) (w : M))))

variable (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
  (hU : IsUnit (q * p + (1 - q) * (1 - p)))

/-- The isomorphism of ranges applies `q * p + (1 - q) * (1 - p)`. -/
@[simp]
theorem coe_rangeEquiv_apply (w : p.range) :
    (rangeEquiv hp hq hU w : M) = (q * p + (1 - q) * (1 - p)) w :=
  (rfl)

/-- The inverse isomorphism of ranges applies the inverse of `q * p + (1 - q) * (1 - p)`. -/
@[simp]
theorem coe_rangeEquiv_symm_apply (w : q.range) :
    ((rangeEquiv hp hq hU).symm w : M) = (q * p + (1 - q) * (1 - p))⁻¹ʳ w :=
  (rfl)

end ContinuousLinearMap.IsIdempotentElem

namespace ContinuousLinearMap

/-- If `g` is a pseudo-inverse of `f`, that is `f ∘ g ∘ f = f`, then `g ∘ f` is a projection. -/
theorem isIdempotentElem_comp_of_comp_comp_eq_self {R M N : Type*} [Semiring R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] [TopologicalSpace N] [AddCommMonoid N]
    [Module R N] {f : M →L[R] N} {g : N →L[R] M} (hfg : f ∘L g ∘L f = f) :
    IsIdempotentElem (g ∘L f) := by
  ext v
  simpa using congrArg g congr($hfg v)

section Retract

variable {R M N : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [TopologicalSpace N] [AddCommMonoid N] [Module R N] {i : M →L[R] N} {r : N →L[R] M}

/-- For a retract `r ∘ i = id` of `M` through `N`, the extension `i ∘ e ∘ r` of an idempotent `e`
of `M` is an idempotent of `N`. -/
theorem isIdempotentElem_comp_comp_of_retract {e : M →L[R] M} (he : IsIdempotentElem e)
    (hri : r.comp i = .id R M) : IsIdempotentElem (i.comp (e.comp r)) := by
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  have hee (x : M) : e (e x) = e x := congr($he.eq x)
  ext x : 1
  simp [hri', hee]

/-- For a retract `r ∘ i = id` of `M` through `N`, the inclusion `i` identifies the range of an
endomorphism `e` of `M` with the range of its extension `i ∘ e ∘ r`. -/
noncomputable def rangeEquivOfRetract (e : M →L[R] M) (hri : r.comp i = .id R M) :
    LinearMap.range (e : M →ₗ[R] M) ≃ₗ[R]
      LinearMap.range ((i : M →ₗ[R] N) ∘ₗ (e : M →ₗ[R] M) ∘ₗ (r : N →ₗ[R] M)) :=
  have hri' (x : M) : r (i x) = x := by simpa using DFunLike.congr_fun hri x
  (Submodule.equivMapOfInjective (i : M →ₗ[R] N) (Function.LeftInverse.injective hri') _).trans
    (LinearEquiv.ofEq _ _ (by
      rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top]
      exact LinearMap.range_eq_top.2 (Function.LeftInverse.surjective hri')))

/-- The identification of ranges along a retract applies the inclusion `i`. -/
@[simp]
theorem coe_rangeEquivOfRetract_apply (e : M →L[R] M) (hri : r.comp i = .id R M)
    (x : LinearMap.range (e : M →ₗ[R] M)) : (rangeEquivOfRetract e hri x : N) = i x :=
  (rfl)

/-- The inverse identification of ranges along a retract applies the retraction `r`. -/
@[simp]
theorem coe_rangeEquivOfRetract_symm_apply (e : M →L[R] M) (hri : r.comp i = .id R M)
    (y : LinearMap.range ((i : M →ₗ[R] N) ∘ₗ (e : M →ₗ[R] M) ∘ₗ (r : N →ₗ[R] M))) :
    ((rangeEquivOfRetract e hri).symm y : M) = r y := by
  obtain ⟨x, rfl⟩ := (rangeEquivOfRetract e hri).surjective y
  rw [LinearEquiv.symm_apply_apply, coe_rangeEquivOfRetract_apply]
  exact (DFunLike.congr_fun hri (x : M)).symm

end Retract

end ContinuousLinearMap
