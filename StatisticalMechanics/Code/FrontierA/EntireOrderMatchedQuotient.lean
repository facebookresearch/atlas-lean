/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.NormalForm





open Set

namespace StatMech.FrontierA

noncomputable section



def entireOrderMatchedQuotient (f g : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (f / g) Set.univ

theorem entireOrderMatchedQuotient_meromorphicNFOn
    (f g : ℂ → ℂ) :
    MeromorphicNFOn (entireOrderMatchedQuotient f g) Set.univ := by
  unfold entireOrderMatchedQuotient
  exact meromorphicNFOn_toMeromorphicNFOn (f / g) Set.univ

theorem entireOrderMatchedQuotient_order_eq_zero
    {f g : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hg : ∀ z, AnalyticAt ℂ g z)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤)
    (z : ℂ) :
    meromorphicOrderAt (entireOrderMatchedQuotient f g) z = 0 := by
  let hdiv : MeromorphicOn (f / g) Set.univ := fun w _ =>
    (hf w).meromorphicAt.div (hg w).meromorphicAt
  unfold entireOrderMatchedQuotient
  rw [meromorphicOrderAt_toMeromorphicNFOn hdiv (Set.mem_univ z)]
  rw [meromorphicOrderAt_div (hf z).meromorphicAt (hg z).meromorphicAt]
  rw [(hf z).meromorphicOrderAt_eq, (hg z).meromorphicOrderAt_eq,
    horder z]
  simp [hfinite z]

theorem analyticAt_entireOrderMatchedQuotient
    {f g : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hg : ∀ z, AnalyticAt ℂ g z)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤)
    (z : ℂ) :
    AnalyticAt ℂ (entireOrderMatchedQuotient f g) z := by
  have hnf := entireOrderMatchedQuotient_meromorphicNFOn f g
    (show z ∈ Set.univ by trivial)
  apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [entireOrderMatchedQuotient_order_eq_zero hf hg horder hfinite z]

theorem entireOrderMatchedQuotient_ne_zero
    {f g : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hg : ∀ z, AnalyticAt ℂ g z)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤)
    (z : ℂ) :
    entireOrderMatchedQuotient f g z ≠ 0 := by
  have hnf := entireOrderMatchedQuotient_meromorphicNFOn f g
    (show z ∈ Set.univ by trivial)
  apply hnf.meromorphicOrderAt_eq_zero_iff.mp
  exact entireOrderMatchedQuotient_order_eq_zero hf hg horder hfinite z

theorem entireOrderMatchedQuotient_mul_eq
    {f g : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hg : ∀ z, AnalyticAt ℂ g z)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (z : ℂ) :
    entireOrderMatchedQuotient f g z * g z = f z := by
  by_cases hgz : g z = 0
  · have hgOrder : analyticOrderAt g z ≠ 0 :=
      (hg z).analyticOrderAt_ne_zero.mpr hgz
    have hfOrder : analyticOrderAt f z ≠ 0 := by
      rw [horder z]
      exact hgOrder
    have hfz : f z = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hfOrder
    simp [hgz, hfz]
  · let hdiv : MeromorphicOn (f / g) Set.univ := fun w _ =>
      (hf w).meromorphicAt.div (hg w).meromorphicAt
    have hlocal : toMeromorphicNFAt (f / g) z = f / g :=
      toMeromorphicNFAt_eq_self.mpr ((hf z).div (hg z) hgz).meromorphicNFAt
    have hvalue : entireOrderMatchedQuotient f g z = (f / g) z := by
      unfold entireOrderMatchedQuotient
      rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hdiv (Set.mem_univ z)]
      exact congrFun hlocal z
    rw [hvalue]
    exact div_mul_cancel₀ (f z) hgz



theorem exists_entire_zeroFree_quotient_of_analyticOrderAt_eq
    {f g : ℂ → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) (hg : ∀ z, AnalyticAt ℂ g z)
    (horder : ∀ z, analyticOrderAt f z = analyticOrderAt g z)
    (hfinite : ∀ z, analyticOrderAt g z ≠ ⊤) :
    ∃ Q : ℂ → ℂ,
      (∀ z, AnalyticAt ℂ Q z) ∧
      (∀ z, Q z ≠ 0) ∧
      f = fun z => Q z * g z := by
  refine ⟨entireOrderMatchedQuotient f g,
    analyticAt_entireOrderMatchedQuotient hf hg horder hfinite,
    entireOrderMatchedQuotient_ne_zero hf hg horder hfinite, ?_⟩
  funext z
  exact (entireOrderMatchedQuotient_mul_eq hf hg horder z).symm

end

end StatMech.FrontierA
