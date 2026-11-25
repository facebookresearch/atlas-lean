/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_WLight_exists_mdifferentiable_div_of_monicRel.lean`
and
`P2M/Sol/S_WLight_exists_mdifferentiable_div_of_monicRel.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
import MathlibExt.NumberTheory.ModularForms.FrickeFunctions.AnalyticDivMonicRel

/-!
# Holomorphic quotients on the upper half-plane from monic relations

This file transfers the analytic quotient criterion to holomorphic functions on the upper
half-plane.

## Main statement

* `UpperHalfPlane.exists_mdifferentiable_div_of_monicRel`
-/
namespace FrickeFunctions.MDifferentiableDivMonicRel

noncomputable section

open Complex
open Real
open UpperHalfPlane
open Polynomial
open Real.Polynomial
open scoped Topology Manifold MatrixGroups

namespace Aux
open Aux

section ValuationEngine

private theorem le_meromorphicOrderAt_sum {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {ι : Type*} (s : Finset ι) {f : ι → 𝕜 → 𝕜} {x : 𝕜}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x) (m : WithTop ℤ)
    (hm : ∀ i ∈ s, m ≤ meromorphicOrderAt (f i) x) :
    m ≤ meromorphicOrderAt (∑ i ∈ s, f i) x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    calc m ≤ min (meromorphicOrderAt (f a) x) (meromorphicOrderAt (∑ i ∈ s, f i) x) := by
            refine le_min (hm a (Finset.mem_insert_self a s)) ?_
            exact ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
              (fun i hi ↦ hm i (Finset.mem_insert_of_mem hi))
      _ ≤ meromorphicOrderAt (f a + ∑ i ∈ s, f i) x := by
            apply meromorphicOrderAt_add (hf a (Finset.mem_insert_self a s))
            exact MeromorphicAt.sum (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

private theorem meromorphicOrderAt_le_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    meromorphicOrderAt G τ ≤ meromorphicOrderAt F τ := by
  by_contra hlt
  rw [not_le] at hlt
  lift meromorphicOrderAt G τ to ℤ using hGord with m hm
  have hFord : meromorphicOrderAt F τ ≠ ⊤ := hlt.ne_top
  lift meromorphicOrderAt F τ to ℤ using hFord with r hr
  have hrm : r < m := WithTop.coe_lt_coe.mp hlt
  set S := ∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k with hS
  have hMerS : ∀ k ∈ Finset.range n, MeromorphicAt (c k * G ^ (n - k) * F ^ k) τ := by
    intro k hk
    exact (((hc k (Finset.mem_range.mp hk)).mul ((hG.pow _))).mul (hF.pow _)).meromorphicAt
  have hsum_ord : (↑(n * r) + 1 : WithTop ℤ) ≤ meromorphicOrderAt S τ := by
    refine le_meromorphicOrderAt_sum _ hMerS _ ?_
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hterm : meromorphicOrderAt (c k * G ^ (n - k) * F ^ k) τ
        = meromorphicOrderAt (c k) τ + ((n - k : ℕ) * meromorphicOrderAt G τ
            + k * meromorphicOrderAt F τ) := by
      rw [meromorphicOrderAt_mul (((hc k hk').mul (hG.pow (n - k))).meromorphicAt)
            ((hF.pow k).meromorphicAt),
          meromorphicOrderAt_mul (hc k hk').meromorphicAt ((hG.pow (n - k)).meromorphicAt),
          meromorphicOrderAt_pow hG.meromorphicAt (n := n - k),
          meromorphicOrderAt_pow hF.meromorphicAt (n := k), add_assoc]
    rw [hterm, ← hm, ← hr]
    have hc_ord : (0 : WithTop ℤ) ≤ meromorphicOrderAt (c k) τ :=
      (hc k hk').meromorphicOrderAt_nonneg
    have hnk : ((n - k : ℕ) : ℤ) = (n : ℤ) - k := by omega
    have key : (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := by
      rw [show ((n - k : ℕ) : WithTop ℤ) = (((n - k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          show ((k : ℕ) : WithTop ℤ) = (((k : ℕ) : ℤ) : WithTop ℤ) by push_cast; rfl,
          ← WithTop.coe_mul, ← WithTop.coe_mul, ← WithTop.coe_add,
          ← WithTop.coe_one, ← WithTop.coe_add, WithTop.coe_le_coe, hnk]
      have h1 : (1 : ℤ) ≤ (n : ℤ) - k := by omega
      nlinarith [h1, hrm]
    calc (↑(n * r) + 1 : WithTop ℤ)
        ≤ (↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r := key
      _ = 0 + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := (zero_add _).symm
      _ ≤ meromorphicOrderAt (c k) τ + ((↑(n - k : ℕ) : WithTop ℤ) * ↑m + ↑k * ↑r) := by
          gcongr
  have hFn_ord : meromorphicOrderAt (F ^ n) τ = (↑(n * r) : WithTop ℤ) := by
    rw [meromorphicOrderAt_pow hF.meromorphicAt, ← hr]; push_cast; ring_nf
  have hlt2 : meromorphicOrderAt (F ^ n) τ < meromorphicOrderAt S τ := by
    rw [hFn_ord]
    refine lt_of_lt_of_le ?_ hsum_ord
    exact_mod_cast lt_add_one (n * r)
  have heq : meromorphicOrderAt (F ^ n + S) τ = meromorphicOrderAt (F ^ n) τ :=
    meromorphicOrderAt_add_eq_left_of_lt
      (MeromorphicAt.sum (fun i hi ↦ hMerS i hi)) hlt2
  have hzero : (F ^ n + S) =ᶠ[𝓝[≠] τ] 0 :=
    hrel.filter_mono nhdsWithin_le_nhds
  have htop : meromorphicOrderAt (F ^ n + S) τ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]; exact hzero
  rw [heq, hFn_ord] at htop
  exact WithTop.coe_ne_top htop

open WithTop.LinearOrderedAddCommGroup in
private theorem meromorphicOrderAt_div_nonneg_of_monicRel {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F G : 𝕜 → 𝕜} {c : ℕ → 𝕜 → 𝕜} {n : ℕ} {τ : 𝕜}
    (hF : AnalyticAt 𝕜 F τ) (hG : AnalyticAt 𝕜 G τ)
    (hGord : meromorphicOrderAt G τ ≠ ⊤) (hc : ∀ k < n, AnalyticAt 𝕜 (c k) τ)
    (hrel : F ^ n + (∑ k ∈ Finset.range n, c k * G ^ (n - k) * F ^ k) =ᶠ[𝓝 τ] 0) :
    0 ≤ meromorphicOrderAt (F / G) τ := by
  have hle := meromorphicOrderAt_le_of_monicRel hF hG hGord hc hrel
  rw [meromorphicOrderAt_div hF.meromorphicAt hG.meromorphicAt,
      ← LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hGord]
  exact (LinearOrderedAddCommGroupWithTop.sub_le_sub_iff_left_of_ne_top hGord).mpr hle

end ValuationEngine

section HBridge

private lemma analyticOnNhd_comp_ofComplex {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet :=
  (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet

private lemma mdifferentiable_of_analyticOnNhd {f : ℍ → ℂ}
    (hf : AnalyticOnNhd ℂ (f ∘ ofComplex) upperHalfPlaneSet) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f :=
  UpperHalfPlane.mdifferentiable_iff.mpr hf.differentiableOn

private theorem mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero {f g : ℍ → ℂ}
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hfg : f * g = 0) : f = 0 ∨ g = 0 := by
  rw [UpperHalfPlane.mdifferentiable_iff] at hf hg
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
  have key := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero (hf.analyticOnNhd hU)
    (hg.analyticOnNhd hU) (fun z hz ↦ by
      have := congrFun hfg (ofComplex z)
      simpa using this) (convex_halfSpace_im_gt 0).isPreconnected
  rcases key with k | k
  · left; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos
  · right; funext τ; simpa [ofComplex_apply] using k (τ : ℂ) τ.im_pos

end HBridge

end Aux

open _root_.FrickeFunctions.MDifferentiableDivMonicRel.Aux in
/-- Let `a`, `b` and `c k` (`k < d`) be holomorphic on the upper half-plane with `b ≠ 0`. If `a ^ d
+ ∑_{k < d} c k b ^ (d - k) a ^ k = 0`, then `a = F b` for a holomorphic `F`. -/
public theorem _root_.UpperHalfPlane.exists_mdifferentiable_div_of_monicRel {a b : ℍ → ℂ} {c : ℕ →
    ℍ → ℂ} {d : ℕ}
    (hahol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a) (hbhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b)
    (hb0 : b ≠ 0) (hc : ∀ k < d, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (c k))
    (hrel : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) :
    ∃ F : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F ∧ F * b = a := by
  obtain ⟨τ₀, hτ₀⟩ := Function.ne_iff.mp hb0
  have hrelH : ∀ τ : ℍ, a τ ^ d
      + ∑ k ∈ Finset.range d, c k τ * b τ ^ (d - k) * a τ ^ k = 0 := by
    intro τ
    simpa only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply,
      Pi.zero_apply] using congrFun hrel τ
  let a' := a ∘ ofComplex
  let b' := b ∘ ofComplex
  let c' := fun k ↦ (c k) ∘ ofComplex
  have hrel' : Set.EqOn (a' ^ d + ∑ k ∈ Finset.range d, c' k * b' ^ (d - k) * a' ^ k) 0
      upperHalfPlaneSet := by
    intro z hz
    simp only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply,
      a', b', c', comp_ofComplex_of_im_pos _ z hz]
    exact hrelH ⟨z, hz⟩
  obtain ⟨H', hH'an, hH'eq⟩ := AnalyticOnNhd.exists_div_of_monicRel isOpen_upperHalfPlaneSet
    (convex_halfSpace_im_gt 0).isPreconnected (analyticOnNhd_comp_ofComplex hahol)
    (analyticOnNhd_comp_ofComplex hbhol)
    ⟨(τ₀ : ℂ), τ₀.im_pos, by
      simpa [b', comp_ofComplex_of_im_pos b _ τ₀.im_pos] using hτ₀⟩
    (fun k hk ↦ analyticOnNhd_comp_ofComplex (hc k hk)) hrel'
  have hHmem : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ ↦ H' ↑τ) := by
    apply mdifferentiable_of_analyticOnNhd
    refine AnalyticOnNhd.congr isOpen_upperHalfPlaneSet hH'an (fun z hz ↦ ?_)
    exact (comp_ofComplex_of_im_pos (fun τ : ℍ ↦ H' ↑τ) z hz).symm
  refine ⟨fun τ ↦ H' ↑τ, hHmem, ?_⟩
  funext τ
  have heq := hH'eq τ.im_pos
  simp only [Pi.mul_apply, Function.comp_apply, ofComplex_apply] at heq
  change H' ↑τ * b τ = a τ
  rw [mul_comm]
  exact heq.symm

end

end MDifferentiableDivMonicRel

end FrickeFunctions
