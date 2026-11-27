/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from `ZInQKernel/OneProof/H/LPrefix.lean` and
`ZInQKernel/Contrib/G9/I4Layer.lean` (https://github.com/Deicyde/diophantine-z-q),
compared with the source files at commit `e9956cda4174c060ff85f5a6ddc7e4003e63fdd3`.
Copyright 2026 the contributors to Deicyde/diophantine-z-q.
Licensed under the Apache License, Version 2.0.
-/

module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# The ring of integers of `ℂ_[p]` is `p`-adically complete

We record elementary facts about the ring of integers `𝓞_ℂ_[p]` of the `p`-adic complex numbers:
an element of `ℂ_[p]` is integral exactly when its norm is at most `1`, the norm of `p` is
`p⁻¹`, an integer lies in `p ^ n 𝓞_ℂ_[p]` exactly when its norm is at most `‖p‖ ^ n`, and `p` is
not a unit. From these we deduce that `𝓞_ℂ_[p]` is `p`-adically complete and separated, which
provides the instances `Fact ¬IsUnit (p : 𝓞_ℂ_[p])` and
`IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p]` that Mathlib's tilt, Fontaine's map `θ`
and the period ring `BDeRhamPlus 𝓞_ℂ_[p] p` require.

## Main results

* `PadicComplexInt.mem_iff_norm_le_one`: `x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1`.
* `PadicComplex.norm_p`: `‖(p : ℂ_[p])‖ = p⁻¹`.
* `PadicComplexInt.mem_span_pow_iff`: membership in `(p) ^ n` in terms of the norm.
* `PadicComplexInt.not_isUnit_p`: `p` is not a unit of `𝓞_ℂ_[p]`.
* `PadicComplexInt.isAdicComplete`: `𝓞_ℂ_[p]` is `p`-adically complete.

## References

* [J.-M. Fontaine, *Le corps des périodes p-adiques*][fontaine1994corps], Astérisque 223 (1994),
  Exposé II, §2.3.3 p. 78 and §4.1.2 p. 83, which use these facts for `𝓞_ℂ_[p]`.
-/

@[expose] public noncomputable section

open Ideal

variable (p : ℕ) [hp : Fact p.Prime]

namespace PadicComplex

/-- The norm of `p` in `ℂ_[p]` is `p⁻¹`. -/
theorem norm_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]),
    IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p], ← PadicComplex.coe_eq,
    PadicComplex.norm_extends, PadicAlgCl.norm_extends, Padic.norm_p]

/-- The norm of `p` in `ℂ_[p]` is positive. -/
theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := by
  rw [norm_p]
  exact inv_pos.mpr (by exact_mod_cast hp.1.pos)

/-- The norm of `p` in `ℂ_[p]` is less than `1`. -/
theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.1.one_lt)

end PadicComplex

namespace PadicComplexInt

open PadicComplex

/-- An element of `ℂ_[p]` lies in `𝓞_ℂ_[p]` if and only if its norm is at most `1`. -/
theorem mem_iff_norm_le_one (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def]
  change (PadicComplex.valued p).v x ≤ 1 ↔ _
  rw [← map_one (PadicComplex.valued p).v, ← Valuation.restrict_le_iff]
  simpa only [map_one, NNReal.coe_le_one] using
    ((Valuation.RankOne.strictMono (PadicComplex.valued p).v).le_iff_le (b := 1)).symm

/-- Every element of `𝓞_ℂ_[p]` has norm at most `1` in `ℂ_[p]`. -/
theorem norm_le_one (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 :=
  (mem_iff_norm_le_one p _).mp x.2

/-- An element `x` of `𝓞_ℂ_[p]` lies in `(p) ^ n` if and only if `‖x‖ ≤ ‖p‖ ^ n`. -/
theorem mem_span_pow_iff (x : 𝓞_ℂ_[p]) (n : ℕ) :
    x ∈ span {(p : 𝓞_ℂ_[p])} ^ n ↔ ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, rfl⟩
    have hz : ‖(z : ℂ_[p])‖ ≤ 1 := norm_le_one p z
    have e : ((z * (p : 𝓞_ℂ_[p]) ^ n : 𝓞_ℂ_[p]) : ℂ_[p]) = (z : ℂ_[p]) * (p : ℂ_[p]) ^ n := by
      push_cast
      rfl
    rw [e, norm_mul, norm_pow]
    calc ‖(z : ℂ_[p])‖ * ‖(p : ℂ_[p])‖ ^ n ≤ 1 * ‖(p : ℂ_[p])‖ ^ n := by gcongr
      _ = _ := one_mul _
  · intro h
    have hpn : (p : ℂ_[p]) ^ n ≠ 0 := pow_ne_zero _ (norm_pos_iff.mp (norm_p_pos p))
    refine ⟨⟨(x : ℂ_[p]) / (p : ℂ_[p]) ^ n, (mem_iff_norm_le_one p _).mpr ?_⟩, ?_⟩
    · rw [norm_div, norm_pow, div_le_one (pow_pos (norm_p_pos p) n)]
      exact h
    · apply Subtype.ext
      push_cast
      field_simp

private theorem smodEq_iff (x y : 𝓞_ℂ_[p]) (n : ℕ) :
    x ≡ y [SMOD (span {(p : 𝓞_ℂ_[p])} ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow_iff]
  push_cast
  rfl

/-- The prime `p` is not a unit of `𝓞_ℂ_[p]`. -/
theorem not_isUnit_p : ¬IsUnit (p : 𝓞_ℂ_[p]) := fun h => by
  obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp h
  have hv' : (p : ℂ_[p]) * (v : ℂ_[p]) = 1 := by
    have := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) hv
    push_cast at this
    exact this
  have h1 : ‖(v : ℂ_[p])‖ ≤ 1 := norm_le_one p v
  have h2 : ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ = 1 := by rw [← norm_mul, hv', norm_one]
  have h3 : ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ < 1 :=
    calc ‖(p : ℂ_[p])‖ * ‖(v : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact norm_p_lt_one p
  linarith

/-- The prime `p` is not a unit of `𝓞_ℂ_[p]`, as an instance. -/
instance fact_not_isUnit_p : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) :=
  ⟨not_isUnit_p p⟩

private theorem tendsto_norm_p_pow :
    Filter.Tendsto (fun n : ℕ => ‖(p : ℂ_[p])‖ ^ n) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_p_lt_one p)

/-- `𝓞_ℂ_[p]` is `p`-adically separated. -/
instance isHausdorff : IsHausdorff (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where
  haus' x hx := by
    have h : ∀ n : ℕ, ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := fun n => by
      have := (smodEq_iff p x 0 n).mp (hx n)
      simpa using this
    have h0 : ‖(x : ℂ_[p])‖ ≤ 0 := ge_of_tendsto' (tendsto_norm_p_pow p) h
    exact Subtype.ext (by simpa using norm_le_zero_iff.mp h0)

/-- Every `p`-adic Cauchy sequence in `𝓞_ℂ_[p]` has a limit. -/
instance isPrecomplete : IsPrecomplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where
  prec' f hf := by
    set g : ℕ → ℂ_[p] := fun n => (f n : ℂ_[p])
    have hmn : ∀ m n, m ≤ n → ‖g m - g n‖ ≤ ‖(p : ℂ_[p])‖ ^ m := fun m n h =>
      (smodEq_iff p _ _ m).mp (hf h)
    have hcs : CauchySeq g := by
      refine cauchySeq_of_le_tendsto_0 (fun N => 2 * ‖(p : ℂ_[p])‖ ^ N)
        (fun n m N hn hm => ?_) ?_
      · rw [dist_eq_norm]
        calc ‖g n - g m‖ = ‖(g N - g m) - (g N - g n)‖ := by congr 1; ring
          _ ≤ ‖g N - g m‖ + ‖g N - g n‖ := norm_sub_le _ _
          _ ≤ ‖(p : ℂ_[p])‖ ^ N + ‖(p : ℂ_[p])‖ ^ N := add_le_add (hmn N m hm) (hmn N n hn)
          _ = 2 * ‖(p : ℂ_[p])‖ ^ N := by ring
      · simpa using (tendsto_norm_p_pow p).const_mul 2
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    have hL1 : ‖L‖ ≤ 1 :=
      le_of_tendsto' (hL.norm) fun n => norm_le_one p (f n)
    refine ⟨⟨L, (mem_iff_norm_le_one p L).mpr hL1⟩, fun n => (smodEq_iff p _ _ n).mpr ?_⟩
    have ht : Filter.Tendsto (fun k => ‖g n - g k‖) Filter.atTop (nhds ‖g n - L‖) :=
      (tendsto_const_nhds.sub hL).norm
    exact le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨n, fun k hk => hmn n k hk⟩)

/-- `𝓞_ℂ_[p]` is `p`-adically complete and separated. -/
instance isAdicComplete : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] where

end PadicComplexInt
