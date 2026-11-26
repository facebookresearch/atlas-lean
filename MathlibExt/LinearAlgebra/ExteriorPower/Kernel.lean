/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Kernel-slot relations for a surjective exterior map

For an `R`-linear map `f : M → N` over a commutative ring, let `S_f^n` be the span in `Λ^n_R
M` of words containing a vector in `ker f` in at least one slot.

If `f` is surjective, `ker(Λ^n f)=S_f^n`. The quotient word depends only on the images of its
slots, so it descends to an alternating map on `N`. The statement includes degree zero.

Reference: Bourbaki, *Algebra*, Chapter III.
-/

public section
noncomputable section

namespace exteriorPower

open Function

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. For `n : ℕ`,
`kernelSlotWords f n` is the span in `Λ^n_R M` of words `ιMulti_R(v)` with `f(v i)=0` for some
slot `i : Fin n`. -/
def kernelSlotWords (f : M →ₗ[R] N) (n : ℕ) : Submodule R (⋀[R]^n M) :=
  Submodule.span R {x | ∃ (v : Fin n → M) (i : Fin n), f (v i) = 0 ∧ x = exteriorPower.ιMulti R n v}

/-- Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. For `n : ℕ`,
`kernelSlotWords f n = span_R {ιMulti_R(v) | ∃ i : Fin n, f(v i)=0}`. -/
theorem kernelSlotWords_eq_span (f : M →ₗ[R] N) (n : ℕ) :
    kernelSlotWords f n = Submodule.span R
      {x | ∃ (v : Fin n → M) (i : Fin n), f (v i) = 0 ∧ x = exteriorPower.ιMulti R n v} := by
  unfold kernelSlotWords
  rfl

/-- Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. For `n : ℕ`, this is
the alternating `R`-multilinear map on `Fin n → M` with value `v ↦ [ιMulti_R(v)]` in `Λ^n_R M
/ kernelSlotWords f n`. -/
def quotientKernelWord (f : M →ₗ[R] N) (n : ℕ) :
    M [⋀^Fin n]→ₗ[R] ((⋀[R]^n M) ⧸ kernelSlotWords f n) :=
  (kernelSlotWords f n).mkQ.compAlternatingMap (exteriorPower.ιMulti R n)

theorem quotientKernelWord_apply (f : M →ₗ[R] N) (n : ℕ) (v : Fin n → M) :
    quotientKernelWord f n v = (kernelSlotWords f n).mkQ (exteriorPower.ιMulti R n v) := by
  unfold quotientKernelWord
  rfl

private theorem quotientKernelWord_update_add (f : M →ₗ[R] N) (n : ℕ)
    [DecidableEq (Fin n)]
    (v : Fin n → M) (i : Fin n) (x y : M) :
    quotientKernelWord f n (update v i (x + y)) =
      quotientKernelWord f n (update v i x) + quotientKernelWord f n (update v i y) := by
  rw [quotientKernelWord_apply, (exteriorPower.ιMulti R n).map_update_add, map_add,
    quotientKernelWord_apply, quotientKernelWord_apply]

private theorem quotientKernelWord_update_smul (f : M →ₗ[R] N) (n : ℕ)
    [DecidableEq (Fin n)]
    (v : Fin n → M) (i : Fin n) (r : R) (x : M) :
    quotientKernelWord f n (update v i (r • x)) =
      r • quotientKernelWord f n (update v i x) := by
  rw [quotientKernelWord_apply, (exteriorPower.ιMulti R n).map_update_smul, map_smul,
    quotientKernelWord_apply]

private theorem quotientKernelWord_slot_zero (f : M →ₗ[R] N) (n : ℕ)
    (v : Fin n → M) (i : Fin n) (hi : f (v i) = 0) : quotientKernelWord f n v = 0 := by
  rw [quotientKernelWord_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨v, i, hi, rfl⟩)

private theorem quotientKernelWord_update_eq (f : M →ₗ[R] N) (n : ℕ)
    [DecidableEq (Fin n)]
    (v : Fin n → M) (i : Fin n) (x y : M) (h : f x = f y) :
    quotientKernelWord f n (update v i x) = quotientKernelWord f n (update v i y) := by
  have hz : quotientKernelWord f n (update v i (x - y)) = 0 :=
    quotientKernelWord_slot_zero f n _ i (by simp only [update_self, map_sub, h, sub_self])
  rw [AlternatingMap.map_update_sub] at hz
  exact sub_eq_zero.mp hz

/-- Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. Let `n : ℕ` and `v,w
: Fin n → M` satisfy `f(v i)=f(w i)` for every `i`. Then `quotientKernelWord f n v =
quotientKernelWord f n w` in `Λ^n_R M / kernelSlotWords f n`. -/
theorem quotientKernelWord_invariant (f : M →ₗ[R] N) (n : ℕ)
    (v w : Fin n → M) (h : ∀ i, f (v i) = f (w i)) :
    quotientKernelWord f n v = quotientKernelWord f n w := by
  have all : ∀ (s : Finset (Fin n)) (v w : Fin n → M),
      (∀ i, i ∉ s → v i = w i) → (∀ i, f (v i) = f (w i)) →
      quotientKernelWord f n v = quotientKernelWord f n w := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro v w hv hw
      exact congrArg (quotientKernelWord f n) (funext (fun i => hv i (Finset.notMem_empty i)))
    | @insert i s hi ih =>
      intro v w hv hw
      calc
        quotientKernelWord f n v = quotientKernelWord f n (update v i (w i)) := by
          have he := quotientKernelWord_update_eq f n v i (v i) (w i) (hw i)
          simpa only [update_eq_self] using he
        _ = quotientKernelWord f n w := by
          apply ih
          · intro j hj
            by_cases hji : j = i
            · subst j
              exact update_self _ _ _
            · rw [update_of_ne hji]
              exact hv j (by simp only [Finset.mem_insert, not_or]; exact ⟨hji, hj⟩)
          · intro j
            by_cases hji : j = i
            · subst j
              rw [update_self]
            · rw [update_of_ne hji]
              exact hw j
  exact all Finset.univ v w (by simp) h

/-- Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. If `f` is
surjective, the alternating `R`-multilinear map `descendedKernelWord f hf n` on `Fin n → N`
sends a tuple to the exterior quotient class of any slotwise lift in `M`. Equality of image
tuples makes this class independent of the lift. -/
def descendedKernelWord (f : M →ₗ[R] N) (hf : Surjective f) (n : ℕ) :
    N [⋀^Fin n]→ₗ[R] ((⋀[R]^n M) ⧸ kernelSlotWords f n) where
  toFun v := quotientKernelWord f n (surjInv hf ∘ v)
  map_update_add' v i x y := by
    change quotientKernelWord f n (surjInv hf ∘ update v i (x + y)) =
      quotientKernelWord f n (surjInv hf ∘ update v i x) +
        quotientKernelWord f n (surjInv hf ∘ update v i y)
    rw [comp_update, comp_update, comp_update]
    calc
      quotientKernelWord f n (update (surjInv hf ∘ v) i (surjInv hf (x + y))) =
          quotientKernelWord f n (update (surjInv hf ∘ v) i (surjInv hf x + surjInv hf y)) :=
        quotientKernelWord_update_eq f n _ i _ _ (by
          rw [surjInv_eq hf, map_add, surjInv_eq hf, surjInv_eq hf])
      _ = _ := quotientKernelWord_update_add f n (surjInv hf ∘ v) i (surjInv hf x) (surjInv hf y)
  map_update_smul' v i r x := by
    change quotientKernelWord f n (surjInv hf ∘ update v i (r • x)) =
      r • quotientKernelWord f n (surjInv hf ∘ update v i x)
    rw [comp_update, comp_update]
    calc
      quotientKernelWord f n (update (surjInv hf ∘ v) i (surjInv hf (r • x))) =
          quotientKernelWord f n (update (surjInv hf ∘ v) i (r • surjInv hf x)) :=
        quotientKernelWord_update_eq f n _ i _ _ (by rw [surjInv_eq hf, map_smul, surjInv_eq hf])
      _ = _ := quotientKernelWord_update_smul f n (surjInv hf ∘ v) i r (surjInv hf x)
  map_eq_zero_of_eq' v i j h hij := by
    exact (quotientKernelWord f n).map_eq_zero_of_eq _ (congrArg (surjInv hf) h) hij

/-- Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. Assume `f` is
surjective. For `n : ℕ` and `v : Fin n → M`, `descendedKernelWord f hf n (f ∘ v) =
[ιMulti_R(v)]` in `Λ^n_R M / kernelSlotWords f n`. -/
theorem descendedKernelWord_comp (f : M →ₗ[R] N) (hf : Surjective f) (n : ℕ)
    (v : Fin n → M) :
    descendedKernelWord f hf n (f ∘ v) =
      (kernelSlotWords f n).mkQ (exteriorPower.ιMulti R n v) := by
  unfold descendedKernelWord
  change quotientKernelWord f n (surjInv hf ∘ f ∘ v) = _
  rw [← quotientKernelWord_apply]
  apply quotientKernelWord_invariant
  intro i
  exact surjInv_eq hf _

/-- Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. If `f` is
surjective, then for every `n : ℕ`, `ker(exteriorPower.map n f) = kernelSlotWords f n`, the
span of exterior words having a slot in `ker f`. -/
theorem ker_exteriorPower_map (f : M →ₗ[R] N) (hf : Surjective f) (n : ℕ) :
    LinearMap.ker (exteriorPower.map n f) = kernelSlotWords f n := by
  let g := exteriorPower.alternatingMapLinearEquiv (descendedKernelWord f hf n)
  have hg : g.comp (exteriorPower.map n f) = (kernelSlotWords f n).mkQ := by
    dsimp only [g]
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      exteriorPower.map_apply_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    exact descendedKernelWord_comp f hf n v
  apply le_antisymm
  · intro x hx
    change exteriorPower.map n f x = 0 at hx
    have hz : (kernelSlotWords f n).mkQ x = 0 := by
      rw [← hg, LinearMap.comp_apply, hx, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  · apply Submodule.span_le.mpr
    rintro x ⟨v, i, hi, rfl⟩
    change exteriorPower.map n f (exteriorPower.ιMulti R n v) = 0
    rw [exteriorPower.map_apply_ιMulti]
    exact (exteriorPower.ιMulti R n).map_coord_zero i hi

end exteriorPower
