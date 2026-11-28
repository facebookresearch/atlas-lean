/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SchwartzSpace.RapidSequence
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Order.Filter.Cofinite

/-!
# Finitely supported sequences in the rapid-sequence space

A finitely supported sequence has rapidly decreasing norms because it vanishes
eventually. Its inclusion into the rapid-sequence space is linear and injective.
Each weighted seminorm of the included sequence is the finite supremum of its
weighted coefficient norms. The finite supremum is taken in the nonnegative reals,
so the empty support has supremum zero.
-/

@[expose] public noncomputable section

open scoped NNReal Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace RapidSequence

/-- The linear inclusion of finitely supported sequences into rapidly decreasing sequences. -/
def ofFinsupp : (ℕ →₀ E) →ₗ[𝕜] RapidSequence 𝕜 E where
  toFun f := ofFunction (fun n ↦ f n) (by
    have hf : ∀ᶠ n in Filter.atTop, f n = 0 := by
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite]
      exact f.hasFiniteSupport
    refine (Asymptotics.superpolynomialDecay_zero Filter.atTop
      (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ))).congr' ?_
    filter_upwards [hf] with n hn
    simp [hn])
  map_add' f g := by
    ext n
    simp only [ofFunction_apply, Finsupp.add_apply, add_apply]
  map_smul' c f := by
    ext n
    simp only [ofFunction_apply, Finsupp.smul_apply, smul_apply, RingHom.id_apply]

/-- The finite-support inclusion preserves every coordinate. -/
@[simp]
theorem ofFinsupp_apply (f : ℕ →₀ E) (n : ℕ) : ofFinsupp (𝕜 := 𝕜) f n = f n := rfl

/-- The finite-support inclusion is injective. -/
theorem ofFinsupp_injective : Function.Injective (ofFinsupp (𝕜 := 𝕜) (E := E)) := by
  intro f g h
  apply Finsupp.ext
  intro n
  have hn := congrArg (fun s : RapidSequence 𝕜 E ↦ s n) h
  simpa only [ofFinsupp_apply] using hn

/-- A finitely supported singleton includes as the corresponding rapid singleton. -/
@[simp]
theorem ofFinsupp_single (n : ℕ) (x : E) :
    ofFinsupp (𝕜 := 𝕜) (Finsupp.single n x) = single n x := by
  ext m
  by_cases hm : m = n
  · subst m
    simp only [ofFinsupp_apply, Finsupp.single_eq_same, single_apply_self]
  · simp only [ofFinsupp_apply, Finsupp.single_eq_of_ne' (Ne.symm hm),
      single_apply_ne n x hm]

/-- A weighted seminorm on finite support is the finite supremum of weighted coefficient norms. -/
theorem seminorm_ofFinsupp (k : ℕ) (f : ℕ →₀ E) :
    seminorm k (ofFinsupp (𝕜 := 𝕜) f) =
      ((f.support.sup (fun n ↦ ((n + 1 : ℕ) : ℝ≥0) ^ k * ‖f n‖₊) : ℝ≥0) : ℝ) := by
  let w : ℕ → ℝ≥0 := fun n ↦ ((n + 1 : ℕ) : ℝ≥0) ^ k * ‖f n‖₊
  let C : ℝ≥0 := f.support.sup w
  change seminorm k (ofFinsupp (𝕜 := 𝕜) f) = (C : ℝ)
  apply le_antisymm
  · apply seminorm_le_of_forall_le k (ofFinsupp f)
    intro n
    by_cases hn : n ∈ f.support
    · have h : w n ≤ C := Finset.le_sup hn
      have h' : (w n : ℝ) ≤ (C : ℝ) := NNReal.coe_le_coe.mpr h
      simpa only [w, ofFinsupp_apply, NNReal.coe_mul, NNReal.coe_pow,
        NNReal.coe_natCast, coe_nnNorm] using h'
    · rw [ofFinsupp_apply, Finsupp.notMem_support_iff.mp hn, norm_zero, mul_zero]
      exact NNReal.coe_nonneg C
  · have h : C ≤ ⟨seminorm k (ofFinsupp (𝕜 := 𝕜) f),
        apply_nonneg (seminorm k) (ofFinsupp f)⟩ := by
      apply Finset.sup_le
      intro n _
      have hw : (w n : ℝ) ≤ seminorm k (ofFinsupp (𝕜 := 𝕜) f) := by
        simpa only [w, ofFinsupp_apply, NNReal.coe_mul, NNReal.coe_pow,
          NNReal.coe_natCast, coe_nnNorm] using
          weight_mul_norm_le_seminorm k n (ofFinsupp (𝕜 := 𝕜) f)
      exact NNReal.coe_le_coe.mp hw
    exact NNReal.coe_le_coe.mpr h

end RapidSequence
