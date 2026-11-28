/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.ExteriorPower.Kernel
public import MathlibExt.LinearAlgebra.ExteriorPower.ContractionWedge

/-!
# Exterior relations with one fixed slot

For a module `M` over a commutative ring `R`, let `S_m^n` be the span of exterior words of
length `n` having the vector `m` in some slot. Alternation moves that slot to the first
position with the permutation sign.

In degree `n+1`, this span is the range of `m ∧ - : Λ^n_R M → Λ^(n+1)_R M`. In degree zero it
is zero. If `ker f = Rm`, the kernel-slot relation span for `f` equals `S_m^n`.

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

/-- Let `R` be a commutative ring and `M` an `R`-module. For `m : M` and `n : ℕ`, `fixedSlotWords
m n` is the submodule of `Λ^n_R M` spanned by `ιMulti_R(v)` for tuples `v : Fin n → M` with `v
i=m` for some `i : Fin n`. -/
def fixedSlotWords (m : M) (n : ℕ) : Submodule R (⋀[R]^n M) :=
  Submodule.span R {x | ∃ (v : Fin n → M) (i : Fin n), v i = m ∧ x = exteriorPower.ιMulti R n v}

/-- Let `R` be a commutative ring and `M` an `R`-module. For `m : M` and `n : ℕ`, `fixedSlotWords
m n = span_R {ιMulti_R(v) | ∃ i : Fin n, v i=m}`. -/
theorem fixedSlotWords_eq_span (m : M) (n : ℕ) :
    fixedSlotWords (R := R) m n = Submodule.span R
      {x | ∃ (v : Fin n → M) (i : Fin n), v i = m ∧ x = exteriorPower.ιMulti R n v} := by
  unfold fixedSlotWords
  rfl

/-- Let `R` be a commutative ring, `M,N` be `R`-modules, and `f : M →ₗ[R] N`. If `ker f = span_R
{m}` for `m : M`, then for every `n : ℕ`, `kernelSlotWords f n = fixedSlotWords m n`. Both
sides are submodules of `Λ^n_R M`. -/
theorem kernelSlotWords_eq_fixedSlotWords (f : M →ₗ[R] N) (m : M)
    (hker : LinearMap.ker f = Submodule.span R {m}) (n : ℕ) :
    kernelSlotWords f n = fixedSlotWords m n := by
  apply le_antisymm
  · rw [kernelSlotWords_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨v, i, hi, rfl⟩
    have hm : v i ∈ Submodule.span R {m} := by
      rw [← hker]
      exact hi
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hm
    have hv : v = update v i (r • m) := by
      funext j
      by_cases hji : j = i
      · subst j
        rw [update_self]
        exact hr.symm
      · rw [update_of_ne hji]
    rw [hv, AlternatingMap.map_update_smul]
    exact (fixedSlotWords m n).smul_mem r
      (by unfold fixedSlotWords;
          exact Submodule.subset_span ⟨update v i m, i, update_self _ _ _, rfl⟩)
  · have hm : f m = 0 := by
      have h := Submodule.mem_span_singleton_self (R := R) m
      rw [← hker] at h
      exact h
    unfold fixedSlotWords
    apply Submodule.span_le.mpr
    rintro x ⟨v, i, hi, rfl⟩
    rw [kernelSlotWords_eq_span]
    exact Submodule.subset_span ⟨v, i, by rw [hi, hm], rfl⟩

private theorem word_first_mem_range_wedgeLeft (m : M) (n : ℕ)
    (v : Fin (n + 1) → M) (h : v 0 = m) :
    exteriorPower.ιMulti R (n + 1) v ∈ LinearMap.range (exteriorPower.wedgeLeft R M m n) := by
  refine ⟨exteriorPower.ιMulti R n (fun i => v i.succ), ?_⟩
  rw [exteriorPower.wedgeLeft_apply_ιMulti]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => exact h.symm
  | succ i => rfl

/-- Let `R` be a commutative ring and `M` an `R`-module. For `m : M` and `n : ℕ`, `fixedSlotWords
m (n+1) = range(wedgeLeft R M m n)`, where `wedgeLeft` sends `x ∈ Λ^n_R M` to `m ∧ x`. -/
theorem fixedSlotWords_succ_eq_range_wedgeLeft (m : M) (n : ℕ) :
    fixedSlotWords m (n + 1) = LinearMap.range (exteriorPower.wedgeLeft R M m n) := by
  apply le_antisymm
  · unfold fixedSlotWords
    apply Submodule.span_le.mpr
    rintro x ⟨v, i, hi, rfl⟩
    by_cases hi0 : i = 0
    · subst i
      exact word_first_mem_range_wedgeLeft (R := R) m n v hi
    · have hv : (v ∘ Equiv.swap 0 i) 0 = m := by
        rw [Function.comp_apply, Equiv.swap_apply_left, hi]
      have hm := word_first_mem_range_wedgeLeft (R := R) m n (v ∘ Equiv.swap 0 i) hv
      rw [(exteriorPower.ιMulti R (n + 1)).map_swap v (Ne.symm hi0)] at hm
      exact (LinearMap.range (exteriorPower.wedgeLeft R M m n)).neg_mem_iff.mp hm
  · rw [LinearMap.range_eq_map, ← exteriorPower.ιMulti_span R n M,
      Submodule.map_span, ← Set.range_comp]
    apply Submodule.span_le.mpr
    rintro x ⟨v, rfl⟩
    rw [Function.comp_apply, exteriorPower.wedgeLeft_apply_ιMulti]
    unfold fixedSlotWords
    exact Submodule.subset_span ⟨Matrix.vecCons m v, 0, rfl, rfl⟩

/-- Let `R` be a commutative ring and `M` an `R`-module. For every `m : M`, `fixedSlotWords m 0 =
⊥` in `Λ^0_R M`, because `Fin 0` has no slot. -/
theorem fixedSlotWords_zero (m : M) : fixedSlotWords (R := R) m 0 = ⊥ := by
  unfold fixedSlotWords
  apply Submodule.span_eq_bot.mpr
  rintro x ⟨v, i, hi, hx⟩
  exact i.elim0

end exteriorPower
