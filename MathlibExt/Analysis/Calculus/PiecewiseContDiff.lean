/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Data.Set.Piecewise
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.TangentCone.Real

/-! # Gluing smooth functions on adjacent closed intervals

At the common endpoint, matching one-sided derivatives give the derivative on the union.
Induction on the differentiability order applies the same gluing argument to the derivatives.
-/

public section

open Set Filter
open scoped Topology

namespace MathlibExt.Analysis.Calculus.PiecewiseContDiffWanted

section

variable {E : Type*}

private theorem piecewise_eqOn_right {a b c : ℝ} {f g : ℝ → E} (hab : a ≤ b)
    (h : f b = g b) : EqOn ((Icc a b).piecewise f g) g (Icc b c) := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hbx
  · exact ((piecewise_eqOn (Icc a b) f g) ⟨hab, le_rfl⟩).trans h
  · exact piecewise_eqOn_compl (Icc a b) f g (show x ∉ Icc a b from fun hm ↦ hbx.not_ge hm.2)

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem piecewise_deriv {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {f g : ℝ → E} (hf : DifferentiableOn ℝ f (Icc a b))
    (hg : DifferentiableOn ℝ g (Icc b c)) (hval : f b = g b)
    (hderiv : derivWithin f (Icc a b) b = derivWithin g (Icc b c) b) :
    DifferentiableOn ℝ ((Icc a b).piecewise f g) (Icc a c) ∧
      EqOn (derivWithin ((Icc a b).piecewise f g) (Icc a c))
        ((Icc a b).piecewise (derivWithin f (Icc a b)) (derivWithin g (Icc b c))) (Icc a c) := by
  let p := (Icc a b).piecewise f g
  let q := (Icc a b).piecewise (derivWithin f (Icc a b)) (derivWithin g (Icc b c))
  have pl : EqOn p f (Icc a b) := piecewise_eqOn _ _ _
  have pr : EqOn p g (Icc b c) := piecewise_eqOn_right hab.le hval
  have ql : EqOn q (derivWithin f (Icc a b)) (Icc a b) := piecewise_eqOn _ _ _
  have qr : EqOn q (derivWithin g (Icc b c)) (Icc b c) := piecewise_eqOn_right hab.le hderiv
  -- Away from the join, only one side matters locally. At the join, glue both derivatives.
  have hp (x : ℝ) (hx : x ∈ Icc a c) : HasDerivWithinAt p (q x) (Icc a c) x := by
    rcases lt_trichotomy x b with hxb | hxb | hbx
    · have hxl : x ∈ Icc a b := ⟨hx.1, hxb.le⟩
      rw [ql hxl]
      apply ((hf x hxl).hasDerivWithinAt.congr_of_mem pl hxl).mono_of_mem_nhdsWithin
      change ∀ᶠ t in 𝓝[Icc a c] x, t ∈ Icc a b
      filter_upwards [eventually_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds
          (show ∀ᶠ t in 𝓝 x, t ∈ Iio b from Iio_mem_nhds hxb)]
        with t ht htlt
      exact ⟨ht.1, htlt.le⟩
    · subst x
      have hbl : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
      have hbr : b ∈ Icc b c := ⟨le_rfl, hbc.le⟩
      rw [← Icc_union_Icc_eq_Icc hab.le hbc.le, ql hbl]
      exact ((hf b hbl).hasDerivWithinAt.congr_of_mem pl hbl).union
        (((hg b hbr).hasDerivWithinAt.congr_of_mem pr hbr).congr_deriv hderiv.symm)
    · have hxr : x ∈ Icc b c := ⟨hbx.le, hx.2⟩
      rw [qr hxr]
      apply ((hg x hxr).hasDerivWithinAt.congr_of_mem pr hxr).mono_of_mem_nhdsWithin
      change ∀ᶠ t in 𝓝[Icc a c] x, t ∈ Icc b c
      filter_upwards [eventually_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds
          (show ∀ᶠ t in 𝓝 x, t ∈ Ioi b from Ioi_mem_nhds hbx)]
        with t ht htgt
      exact ⟨htgt.le, ht.2⟩
  exact ⟨fun x hx ↦ (hp x hx).differentiableWithinAt,
    fun x hx ↦ (hp x hx).derivWithin (uniqueDiffOn_Icc (hab.trans hbc) x hx)⟩

private theorem piecewise_nat {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (n : ℕ) {f g : ℝ → E}
    (hf : ContDiffOn ℝ n f (Icc a b)) (hg : ContDiffOn ℝ n g (Icc b c))
    (hjets : ∀ k : ℕ, k ≤ n →
      iteratedDerivWithin k f (Icc a b) b = iteratedDerivWithin k g (Icc b c) b) :
    ContDiffOn ℝ n ((Icc a b).piecewise f g) (Icc a c) := by
  induction n generalizing f g with
  | zero =>
    have hval : f b = g b := by simpa only [iteratedDerivWithin_zero] using hjets 0 (le_refl 0)
    rw [Nat.cast_zero, contDiffOn_zero, ← Icc_union_Icc_eq_Icc hab.le hbc.le]
    exact (continuousOn_union_iff_of_isClosed isClosed_Icc isClosed_Icc).2
      ⟨hf.continuousOn.congr (piecewise_eqOn _ _ _),
        hg.continuousOn.congr (piecewise_eqOn_right hab.le hval)⟩
  | succ k ih =>
    have hval : f b = g b := by
      simpa only [iteratedDerivWithin_zero] using hjets 0 (Nat.zero_le (k + 1))
    have hcast : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by simp
    have hs : UniqueDiffOn ℝ (Icc a c) := uniqueDiffOn_Icc (hab.trans hbc)
    rw [hcast, contDiffOn_succ_iff_derivWithin hs]
    rw [hcast, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)] at hf
    rw [hcast, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hbc)] at hg
    have hderiv : derivWithin f (Icc a b) b = derivWithin g (Icc b c) b := by
      simpa only [iteratedDerivWithin_succ, iteratedDerivWithin_zero] using
        hjets (0 + 1) (Nat.succ_le_succ (Nat.zero_le k))
    obtain ⟨hpd, hpq⟩ := piecewise_deriv hab hbc hf.1 hg.1 hval hderiv
    refine ⟨hpd, by simp, ?_⟩
    apply (ih hf.2.2 hg.2.2 ?_).congr hpq
    intro j hj
    simpa only [iteratedDerivWithin_succ'] using hjets (j + 1) (Nat.succ_le_succ hj)

end

/-- **Gluing $C^n$ functions on adjacent closed intervals.** Let $E$ be a real normed space, let
$n \in \mathbb{N} \cup \{\infty\}$ and let $a \le b \le c$ be real numbers. Let
$f, g : \mathbb{R} \to E$ be such that $f$ is $C^n$ on $[a, b]$ and $g$ is $C^n$ on $[b, c]$, and
suppose that for every natural number $k \le n$ the $k$-th derivative of $f$ within $[a, b]$ and
the $k$-th derivative of $g$ within $[b, c]$ agree at $b$. Then the function equal to $f$ on
$[a, b]$ and to $g$ elsewhere is $C^n$ on $[a, c]$.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Single Variable Real Analysis /
  Differentiability", entry "piecewise $C^k$ functions" (linked there to the exposition below).
- https://en.wikipedia.org/wiki/Piecewise#Continuity_and_differentiability_of_piecewise_functions
-/
theorem contDiffOn_piecewise_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ∞} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    {f g : ℝ → E}
    (hf : ContDiffOn ℝ n f (Icc a b)) (hg : ContDiffOn ℝ n g (Icc b c))
    (hjets : ∀ k : ℕ, (k : ℕ∞) ≤ n →
      iteratedDerivWithin k f (Icc a b) b =
        iteratedDerivWithin k g (Icc b c) b) :
    ContDiffOn ℝ n (Set.piecewise (Icc a b) f g) (Icc a c) := by
  -- A singleton side contributes only the value at the common endpoint.
  rcases eq_or_lt_of_le hab with rfl | hab'
  · have hval : f a = g a := by simpa only [iteratedDerivWithin_zero] using hjets 0 (by simp)
    exact hg.congr (piecewise_eqOn_right le_rfl hval)
  · rcases eq_or_lt_of_le hbc with rfl | hbc'
    · exact hf.congr (piecewise_eqOn _ _ _)
    · refine contDiffOn_iff_forall_nat_le.2 fun k hk ↦
        piecewise_nat hab' hbc' k (contDiffOn_iff_forall_nat_le.1 hf k hk)
          (contDiffOn_iff_forall_nat_le.1 hg k hk) fun j hj ↦ hjets j (le_trans ?_ hk)
      exact_mod_cast hj

end MathlibExt.Analysis.Calculus.PiecewiseContDiffWanted
