/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Smooth function with some vanishing derivative at each point is polynomial

The following OpenBMB notice applies to the adapted statement and its documentation.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_81.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. The original ATLAS import converted
`theorem ma_proofbench_l2_81 … := by sorry` into the Batteries `theorem_wanted`
`exists_polynomial_eq_of_forall_exists_iteratedDerivWithin_eq_zero`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.PolynomialOfPointwiseVanishingDerivWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; corrected the statement: replaced
`ContDiffOn ℝ ⊤` (analytic in current Mathlib) by `ContDiffOn ℝ ∞` and `iteratedDeriv` by
`iteratedDerivWithin … (Icc 0 1)`.
This change proves the published smooth version and moves it to the proved library.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.DimOne
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Tactic.Ring

/-! # Smooth functions with a vanishing derivative at every point

The relative complement of the open set of polynomial germs has no isolated points:
polynomials on either side of an isolated point would have the same jet there. If the
complement is nonempty, Baire category gives a relatively open patch where one fixed
derivative vanishes. Accumulation makes every higher derivative vanish on that patch.
The boundary jets force the same derivative to vanish on the neighboring polynomial
components, yielding a polynomial throughout a neighborhood of a point in the complement.
-/

open Set Polynomial
open scoped ContDiff Interval Nat Topology

namespace MathlibExt.Analysis.Calculus.PolynomialOfPointwiseVanishingDerivWanted

-- On an interval with a fixed vanishing derivative, the Taylor remainder is zero.
private theorem polynomial_of_deriv_zero_on_open_interval {f : ℝ → ℝ} {S : Set ℝ}
    (hopen : IsOpen S) (hconn : S.OrdConnected) (hf : ContDiffOn ℝ ∞ f S)
    (n : ℕ) (hz : EqOn (iteratedDeriv n f) 0 S) :
    ∃ p : ℝ[X], EqOn f (fun x => p.eval x) S := by
  cases n with
  | zero =>
    refine ⟨0, fun x hx => ?_⟩
    simpa only [iteratedDeriv_zero, Pi.zero_apply, eval_zero] using hz hx
  | succ n =>
    by_cases hS : S.Nonempty
    · obtain ⟨a, ha⟩ := hS
      let p : ℝ[X] := ∑ k ∈ Finset.range (n + 1),
        C ((k ! : ℝ)⁻¹ * iteratedDeriv k f a) * (X - C a) ^ k
      have heval (x : ℝ) (hne : a ≠ x) :
          taylorWithinEval f n (uIcc a x) a x = p.eval x := by
        rw [taylor_within_apply]
        unfold p
        rw [eval_finsetSum]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hda : ContDiffAt ℝ k f a := (hf.contDiffAt (hopen.mem_nhds ha)).of_le (by simp)
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne) hda left_mem_uIcc]
        simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, smul_eq_mul]
        ring
      have hpa : p.eval a = f a := by
        dsimp only [p]
        simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro k _ hk
          rw [zero_pow hk, mul_zero]
        · simp
      refine ⟨p, fun x hx => ?_⟩
      by_cases hxa : a = x
      · subst x
        exact hpa.symm
      · have hsub : uIcc a x ⊆ S := hconn.uIcc_subset ha hx
        obtain ⟨c, hc, hcEq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n) hxa
          ((hf.of_le (by simp)).mono hsub)
        rw [hz (hsub (uIoo_subset_uIcc_self hc)), Pi.zero_apply, zero_mul, zero_div,
          sub_eq_zero] at hcEq
        exact hcEq.trans (heval x hxa)
    · exact ⟨0, fun x hx => (hS ⟨x, hx⟩).elim⟩

private theorem iteratedDeriv_eval (n : ℕ) (p : ℝ[X]) :
    iteratedDeriv n (fun x => p.eval x) = fun x => (derivative^[n] p).eval x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    exact funext fun x => ((derivative^[n] p).hasDerivAt x).deriv

private theorem polynomial_eq_zero_of_jets (a : ℝ) (p : ℝ[X])
    (h : ∀ n, (derivative^[n] p).eval a = 0) : p = 0 := by
  apply eq_zero_of_hasseDeriv_eq_zero p a
  intro n
  have he := h n
  rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, eval_smul] at he
  exact (smul_eq_zero.mp he).resolve_left (Nat.factorial_ne_zero n)

private def polynomialGerms (f : ℝ → ℝ) (S : Set ℝ) : Set ℝ :=
  {x | ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧ U ⊆ S ∧ ∃ p : ℝ[X], EqOn f (fun y => p.eval y) U}

private theorem polynomialGerms_subset (f : ℝ → ℝ) (S : Set ℝ) : polynomialGerms f S ⊆ S := by
  rintro x ⟨U, _, hx, hUS, _, _⟩
  exact hUS hx

private theorem isOpen_polynomialGerms (f : ℝ → ℝ) (S : Set ℝ) : IsOpen (polynomialGerms f S) := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨U, hU, hx, hUS, p, hp⟩
  exact Filter.mem_of_superset (hU.mem_nhds hx) fun y hy => ⟨U, hU, hy, hUS, p, hp⟩

-- Local polynomiality makes the function analytic on a component, not on the whole domain.
private theorem polynomial_on_of_germs {f : ℝ → ℝ} {S U : Set ℝ}
    (hU : IsPreconnected U) (hUS : U ⊆ polynomialGerms f S) :
    ∃ p : ℝ[X], EqOn f (fun y => p.eval y) U := by
  classical
  by_cases hne : U.Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨V, hV, hxV, _, p, hp⟩ := hUS hx
    refine ⟨p, ?_⟩
    have hA : AnalyticOnNhd ℝ f U := by
      intro z hz
      obtain ⟨W, hW, hzW, _, q, hq⟩ := hUS hz
      have he : f =ᶠ[𝓝 z] (fun y => q.eval y) :=
        Filter.eventually_of_mem (hW.mem_nhds hzW) fun _ hy => hq hy
      exact (analyticAt_congr he).mpr (AnalyticOnNhd.eval_polynomial q z (mem_univ _))
    have hpA := (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) p).mono (subset_univ U)
    exact hA.eqOn_of_preconnected_of_eventuallyEq hpA hU hx
      (Filter.eventually_of_mem (hV.mem_nhds hxV) fun _ hy => hp hy)
  · exact ⟨0, fun y hy => (hne ⟨y, hy⟩).elim⟩

private theorem continuousOn_derivative_tower {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (n : ℕ) : ContinuousOn (iteratedDeriv n f) S :=
  (hf.continuousOn_iteratedDerivWithin (m := n) (by simp) hS.uniqueDiffOn).congr
    (iteratedDerivWithin_of_isOpen hS).symm

-- Continuity transports every jet from an open polynomial region to its boundary.
private theorem jets_match_at_closure {f : ℝ → ℝ} {S U : Set ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (hU : IsOpen U) (hUS : U ⊆ S)
    {p : ℝ[X]} (hp : EqOn f (fun y => p.eval y) U) {z : ℝ}
    (hzU : z ∈ closure U) (hzS : z ∈ S) (n : ℕ) :
    iteratedDeriv n f z = (derivative^[n] p).eval z := by
  have he := hp.iteratedDeriv_of_isOpen hU n
  rw [iteratedDeriv_eval] at he
  have hc : ContinuousOn (iteratedDeriv n f) (closure U ∩ S) :=
    (continuousOn_derivative_tower hS hf n).mono inter_subset_right
  have hcp : ContinuousOn (fun x => (derivative^[n] p).eval x) (closure U ∩ S) :=
    (derivative^[n] p).continuous.continuousOn
  exact he.of_subset_closure hc hcp (fun _ hy => ⟨subset_closure hy, hUS hy⟩)
    inter_subset_left ⟨hzU, hzS⟩

private theorem component_closure_hits_bad {G V : Set ℝ} (hG : IsOpen G) (hV : IsOpen V)
    (hVc : IsPreconnected V) {x z : ℝ} (hx : x ∈ V ∩ G) (hz : z ∈ V) (hzG : z ∉ G) :
    ∃ y ∈ closure (connectedComponentIn (V ∩ G) x), y ∈ V ∧ y ∉ G := by
  let C := connectedComponentIn (V ∩ G) x
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hC : C ⊆ V ∩ G := connectedComponentIn_subset _ _
  have hpc : IsPreconnected (closure C ∩ (V ∩ G)) :=
    isPreconnected_connectedComponentIn.subset_closure
      (fun y hy => ⟨subset_closure hy, hC hy⟩) inter_subset_left
  have hcls : closure C ∩ (V ∩ G) ⊆ C :=
    hpc.subset_connectedComponentIn ⟨subset_closure hxC, hx⟩ inter_subset_right
  by_contra! hn
  have hclV : closure C ∩ V ⊆ C := fun y hy =>
    hcls ⟨hy.1, hy.2, hn y hy.1 hy.2⟩
  have hVC : V ⊆ C := hVc.subset_of_closure_inter_subset ((hV.inter hG).connectedComponentIn)
    ⟨x, hx.1, hxC⟩ hclV
  exact hzG (hC (hVC hz)).2

-- At an isolated bad point, the two adjacent polynomials would have the same jet.
private theorem bad_accumulates {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) {a : ℝ} (ha : a ∈ S \ polynomialGerms f S) :
    AccPt a (Filter.principal (S \ polynomialGerms f S)) := by
  classical
  by_contra hacc
  rw [accPt_iff_nhds] at hacc
  obtain ⟨N, hN⟩ := not_forall.mp hacc
  obtain ⟨hN₁, hN₂⟩ := not_imp.mp hN
  obtain ⟨l, r, haV, hV⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (Filter.inter_mem hN₁ (hS.mem_nhds ha.1))
  have hgood (z : ℝ) (hz : z ∈ Ioo l r) (hne : z ≠ a) : z ∈ polynomialGerms f S := by
    by_contra hn
    exact hN₂ ⟨z, ⟨(hV hz).1, ⟨(hV hz).2, hn⟩⟩, hne⟩
  have hlS : Ioo l a ⊆ S := fun _ hx => (hV ⟨hx.1, hx.2.trans haV.2⟩).2
  have hrS : Ioo a r ⊆ S := fun _ hx => (hV ⟨haV.1.trans hx.1, hx.2⟩).2
  obtain ⟨p, hp⟩ := polynomial_on_of_germs isPreconnected_Ioo
    (fun x hx => hgood x ⟨hx.1, hx.2.trans haV.2⟩ hx.2.ne : Ioo l a ⊆ polynomialGerms f S)
  obtain ⟨q, hq⟩ := polynomial_on_of_germs isPreconnected_Ioo
    (fun x hx => hgood x ⟨haV.1.trans hx.1, hx.2⟩ hx.1.ne' : Ioo a r ⊆ polynomialGerms f S)
  have hla : a ∈ closure (Ioo l a) := by
    rw [closure_Ioo haV.1.ne]
    exact ⟨haV.1.le, le_rfl⟩
  have hra : a ∈ closure (Ioo a r) := by
    rw [closure_Ioo haV.2.ne]
    exact ⟨le_rfl, haV.2.le⟩
  have hjp := jets_match_at_closure hS hf isOpen_Ioo hlS hp hla ha.1
  have hjq := jets_match_at_closure hS hf isOpen_Ioo hrS hq hra ha.1
  have hpq : p = q := sub_eq_zero.mp <| polynomial_eq_zero_of_jets a (p - q) fun n => by
    rw [iterate_derivative_sub, eval_sub, ← hjp n, ← hjq n, sub_self]
  apply ha.2
  refine ⟨Ioo l r, isOpen_Ioo, haV, fun _ hz => (hV hz).2, p, ?_⟩
  intro z hz
  rcases lt_trichotomy z a with hlt | rfl | hgt
  · exact hp ⟨hz.1, hlt⟩
  · exact hjp 0
  · simpa only [hpq] using hq ⟨hgt, hz.2⟩

-- At each accumulation point the derivative within the bad set is unique.
private theorem higher_zeros_on_bad_patch {f : ℝ → ℝ} {S V : Set ℝ}
    (hS : IsOpen S) (hf : ContDiffOn ℝ ∞ f S) (hV : IsOpen V)
    {n : ℕ} (hz : EqOn (iteratedDeriv n f) 0 (V ∩ (S \ polynomialGerms f S))) :
    ∀ k : ℕ, EqOn (iteratedDeriv (n + k) f) 0 (V ∩ (S \ polynomialGerms f S)) := by
  intro k
  induction k with
  | zero => exact hz
  | succ k ih =>
    intro x hx
    have hD : UniqueDiffWithinAt ℝ (V ∩ (S \ polynomialGerms f S)) x := by
      rw [inter_comm]
      exact (AccPt.uniqueDiffWithinAt (𝕜 := ℝ) (bad_accumulates hS hf hx.2)).inter
        (hV.mem_nhds hx.1)
    have hm : ((n + k : ℕ) : ℕ∞ω) < ∞ :=
      WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (n + k))
    have hdiff : DifferentiableOn ℝ (iteratedDeriv (n + k) f) S :=
      (hf.differentiableOn_iteratedDerivWithin hm hS.uniqueDiffOn).congr
        (iteratedDerivWithin_of_isOpen hS).symm
    have hd : HasDerivAt (iteratedDeriv (n + k) f) (deriv (iteratedDeriv (n + k) f) x) x :=
      ((hdiff x hx.2.1).differentiableAt (hS.mem_nhds hx.2.1)).hasDerivAt
    have hn : HasDerivWithinAt (iteratedDeriv (n + k) f) 0 (V ∩ (S \ polynomialGerms f S)) x :=
      (hasDerivWithinAt_const x _ (0 : ℝ)).congr_of_mem (fun _ hy => ih hy) hx
    rw [Nat.add_succ, iteratedDeriv_succ, ← hd.hasDerivWithinAt.derivWithin hD,
      hn.derivWithin hD]
    rfl

-- Apply Baire on the relative bad set, not on the entire interval.
private theorem exists_bad_patch {f : ℝ → ℝ} {S : Set ℝ} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (hvanish : ∀ x ∈ S, ∃ n : ℕ, iteratedDeriv n f x = 0)
    (hK : (S \ polynomialGerms f S).Nonempty) :
    ∃ (a l r : ℝ) (n : ℕ), a ∈ Ioo l r ∩ (S \ polynomialGerms f S) ∧
      Ioo l r ⊆ S ∧ EqOn (iteratedDeriv n f) 0 (Ioo l r ∩ (S \ polynomialGerms f S)) := by
  let K := S \ polynomialGerms f S
  have hKS : K ⊆ S := sdiff_subset
  have hKG : IsGδ K := hS.isGδ.inter (isOpen_polynomialGerms f S).isClosed_compl.isGδ
  let : BaireSpace K := hKG.baireSpace_of_t2Space_locallyCompactSpace
  let : Nonempty K := hK.to_subtype
  let Z (n : ℕ) : Set K := {y | iteratedDeriv n f y = 0}
  have hZc (n : ℕ) : IsClosed (Z n) :=
    isClosed_eq (continuousOn_iff_continuous_domRestrict.mp
      ((continuousOn_derivative_tower hS hf n).mono hKS)) continuous_const
  have hU : (⋃ n, Z n) = univ := by
    apply eq_univ_of_forall
    intro x
    exact mem_iUnion.mpr (hvanish x (hKS x.property))
  obtain ⟨n, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hZc hU
  obtain ⟨W, hW, heq⟩ := isOpen_induced_iff.mp (isOpen_interior : IsOpen (interior (Z n)))
  have hxW : (x : ℝ) ∈ W := by
    rw [← heq] at hx
    exact hx
  obtain ⟨l, r, hxV, hV⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hW.inter hS).mem_nhds ⟨hxW, hKS x.property⟩)
  refine ⟨x, l, r, n, ⟨hxV, x.property⟩, fun _ hy => (hV hy).2, ?_⟩
  intro y hy
  have hyInt : (⟨y, hy.2⟩ : K) ∈ interior (Z n) := by
    rw [← heq]
    exact (hV hy.1).1
  exact interior_subset hyInt

private theorem polynomial_of_pointwise_on_open {f : ℝ → ℝ} {S : Set ℝ}
    (hS : IsOpen S) (hSc : IsPreconnected S) (hf : ContDiffOn ℝ ∞ f S)
    (hvanish : ∀ x ∈ S, ∃ n : ℕ, iteratedDeriv n f x = 0) :
    ∃ p : ℝ[X], EqOn f (fun y => p.eval y) S := by
  classical
  let G := polynomialGerms f S
  refine polynomial_on_of_germs (S := S) hSc ?_
  by_contra hbad
  have hK : (S \ G).Nonempty := Set.not_subset.mp hbad
  obtain ⟨a, l, r, n, ha, hVS, hn⟩ := exists_bad_patch hS hf hvanish hK
  have hz : EqOn (iteratedDeriv n f) 0 (Ioo l r) := by
    intro x hx
    by_cases hxG : x ∈ G
    · let C := connectedComponentIn (Ioo l r ∩ G) x
      have hGS : G ⊆ S := polynomialGerms_subset f S
      have hxC : x ∈ C := mem_connectedComponentIn ⟨hx, hxG⟩
      have hCG : C ⊆ G := (connectedComponentIn_subset _ _).trans inter_subset_right
      have hCo : IsOpen C := (isOpen_Ioo.inter (isOpen_polynomialGerms f S)).connectedComponentIn
      obtain ⟨p, hp⟩ := polynomial_on_of_germs isPreconnected_connectedComponentIn hCG
      obtain ⟨b, hbC, hbV, hbG⟩ := component_closure_hits_bad (isOpen_polynomialGerms f S)
        isOpen_Ioo isPreconnected_Ioo ⟨hx, hxG⟩ ha.1 ha.2.2
      have hb : b ∈ Ioo l r ∩ (S \ G) := ⟨hbV, hVS hbV, hbG⟩
      have ht := higher_zeros_on_bad_patch hS hf isOpen_Ioo hn
      have hjets (k : ℕ) : (derivative^[k] (derivative^[n] p)).eval b = 0 := by
        rw [← Function.iterate_add_apply, Nat.add_comm k n,
          ← jets_match_at_closure hS hf hCo (hCG.trans hGS) hp hbC hb.2.1]
        exact ht k hb
      have hpoly : derivative^[n] p = 0 := polynomial_eq_zero_of_jets b _ hjets
      have hEq := hp.iteratedDeriv_of_isOpen hCo n hxC
      rw [iteratedDeriv_eval, hpoly] at hEq
      simpa only [eval_zero, Pi.zero_apply] using hEq
    · exact hn ⟨hx, hVS hx, hxG⟩
  have hp := polynomial_of_deriv_zero_on_open_interval isOpen_Ioo ordConnected_Ioo
    (hf.mono hVS) n hz
  exact ha.2.2 ⟨Ioo l r, isOpen_Ioo, ha.1, hVS, hp⟩

private theorem polynomial_on_unit_of_pointwise {f : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f (Icc (0 : ℝ) 1))
    (hvanish : ∀ x ∈ Icc (0 : ℝ) 1, ∃ n : ℕ, iteratedDerivWithin n f (Icc (0 : ℝ) 1) x = 0) :
    ∃ p : ℝ[X], ∀ x ∈ Icc (0 : ℝ) 1, f x = p.eval x := by
  have hv (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : ∃ n : ℕ, iteratedDeriv n f x = 0 := by
    obtain ⟨n, hn⟩ := hvanish x (Ioo_subset_Icc_self hx)
    have hdiff : ContDiffAt ℝ n f x := (hf.contDiffAt (Icc_mem_nhds hx.1 hx.2)).of_le (by simp)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) hdiff
      (Ioo_subset_Icc_self hx)] at hn
    exact ⟨n, hn⟩
  obtain ⟨p, hp⟩ := polynomial_of_pointwise_on_open isOpen_Ioo isPreconnected_Ioo
    (hf.mono Ioo_subset_Icc_self) hv
  refine ⟨p, hp.of_subset_closure hf.continuousOn p.continuous.continuousOn Ioo_subset_Icc_self ?_⟩
  rw [closure_Ioo zero_ne_one]

/-- **A smooth function on the unit interval with some vanishing derivative at each point is a
polynomial there.** Let $f : \mathbb{R} \to \mathbb{R}$ be infinitely differentiable on $[0, 1]$,
and suppose that for every $x \in [0, 1]$ there is an integer $n \ge 0$ such that the $n$-th
derivative of $f$ within $[0, 1]$ vanishes at $x$ (at the endpoints these derivatives are
one-sided). Then there is a polynomial $p$ with real coefficients such that $f(x) = p(x)$ for
every $x \in [0, 1]$.

Smoothness means infinite differentiability here, not real analyticity: the source's formal
statement assumed real analyticity, which reduces the problem to the identity theorem.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Real functions; Functions of
one variable), `benchmark/level2/ma_proofbench_l2_81.lean` at openbmb/ma-proofbench@31bab4c,
with the change above.
-/
public theorem exists_polynomial_eq_of_forall_exists_iteratedDerivWithin_eq_zero (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ ∞ f (Icc (0 : ℝ) 1))
    (hvanish : ∀ x ∈ Icc (0 : ℝ) 1, ∃ n : ℕ, iteratedDerivWithin n f (Icc (0 : ℝ) 1) x = 0) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Icc (0 : ℝ) 1, f x = p.eval x := by
  exact polynomial_on_unit_of_pointwise hf hvanish

end MathlibExt.Analysis.Calculus.PolynomialOfPointwiseVanishingDerivWanted
