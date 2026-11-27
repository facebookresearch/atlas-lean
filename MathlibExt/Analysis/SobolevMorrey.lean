/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/SobolevMorrey.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `sobolev_embedding_morrey` (manifest
`manifests/problems/sobolev_embedding_morrey.toml`, revision 1, submitted by Kim Morrison).
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License").
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). The adapted portions are the definitions
`E`, `partialDeriv`, `mixedDeriv`, `IsWeakDeriv`, `MemSobolevWk` and `MemHolder` and the
statement of `sobolev_embedding`, with the docstrings they had in the former wanted module.
That module used a Batteries `theorem_wanted`, inlined the LeanEval helpers, and placed the
declarations in the ATLAS namespace. They are moved here with their names and statements
preserved. The proof is new.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.WLOG

/-!
# Sobolev embedding theorem in the Morrey regime

`sobolev_embedding` gives a bounded Hölder representative, with bounded derivatives through order
`r`, of a whole-space Sobolev function when `n < p` and `r + α < k - n / p`.

The proof mollifies each weak derivative. At scale `t`, both the spatial derivative and the scale
derivative of a mollification are bounded by a constant times `t ^ (-n / p)`. The scale bound
gives uniform limits with error of order `t ^ (1 - n / p)`. Choosing the scale to be the distance
between two points then gives the first-order Morrey estimate. Uniform convergence also lets us
pass the spatial differentiations to the limit.
-/

@[expose] public section

namespace MathlibExt.Analysis.SobolevMorreyWanted
namespace Analysis
namespace SobolevMorreyProblem

open MeasureTheory
open scoped ENNReal NNReal

set_option linter.dupNamespace false in
/-- **Euclidean space $\mathbb{R}^n$.** For a natural number $n$, $\mathbb{R}^n$ denotes the real
Euclidean space of dimension $n$: real vectors with coordinates indexed by $0, \dots, n-1$, with
the Euclidean inner product and norm. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

set_option linter.dupNamespace false in
/-- **Partial derivative.** For a coordinate index $i \in \{0, \dots, n-1\}$ and a function
$\varphi : \mathbb{R}^n \to \mathbb{R}$, the partial derivative $\partial_i \varphi$ is the
function $\mathbb{R}^n \to \mathbb{R}$ sending $x$ to $D\varphi(x)(e_i)$, the Fréchet derivative
of $\varphi$ at $x$ applied to the $i$-th standard basis vector $e_i$. At points where $\varphi$
is not differentiable its value is $0$. -/
noncomputable def partialDeriv {n : ℕ} (i : Fin n) (φ : E n → ℝ) : E n → ℝ :=
  fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))

set_option linter.dupNamespace false in
/-- **Mixed partial derivative.** For a multi-index $m = (m_0, \dots, m_{n-1})$ of natural numbers
and a function $\varphi : \mathbb{R}^n \to \mathbb{R}$, the mixed partial derivative is
$D^m \varphi = \partial_0^{m_0} \partial_1^{m_1} \cdots \partial_{n-1}^{m_{n-1}} \varphi$, where
$\partial_i^{j}$ is the $j$-fold iterate of the partial derivative $\partial_i$; thus
$\partial_{n-1}$ is applied first and $\partial_0$ last. -/
noncomputable def mixedDeriv {n : ℕ} (m : Fin n → ℕ) (φ : E n → ℝ) : E n → ℝ :=
  (List.finRange n).foldr (fun i ψ => (partialDeriv i)^[m i] ψ) φ

set_option linter.dupNamespace false in
/-- **Weak derivative.** Let $f, g : \mathbb{R}^n \to \mathbb{R}$ and let
$m = (m_0, \dots, m_{n-1})$ be a multi-index of order $|m| = m_0 + \cdots + m_{n-1}$. Then $g$ is
a weak derivative $D^m f$ of $f$ when every smooth ($C^\infty$) compactly supported function
$\varphi : \mathbb{R}^n \to \mathbb{R}$ satisfies
$$\int_{\mathbb{R}^n} f \, D^m \varphi \, dx = (-1)^{|m|} \int_{\mathbb{R}^n} g \, \varphi \, dx,$$
where $D^m \varphi$ is the classical mixed partial derivative and each integral is the Lebesgue
integral, taken to be $0$ when the integrand is not integrable. -/
def IsWeakDeriv {n : ℕ} (f g : E n → ℝ) (m : Fin n → ℕ) : Prop :=
  ∀ φ : E n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, f x * mixedDeriv m φ x = (-1) ^ (∑ i, m i) * ∫ x, g x * φ x

set_option linter.dupNamespace false in
/-- **Sobolev space $W^{k,p}(\mathbb{R}^n)$.** For a natural number $k$ and $p \in [0, \infty]$, a
function $f : \mathbb{R}^n \to \mathbb{R}$ belongs to $W^{k,p}(\mathbb{R}^n)$ when $f$ is locally
integrable and, for every multi-index $m = (m_0, \dots, m_{n-1})$ of natural numbers with
$m_0 + \cdots + m_{n-1} \le k$, $f$ has a weak derivative $D^m f$ that lies in
$L^p(\mathbb{R}^n)$. Local integrability and $L^p$ are with respect to Lebesgue measure. -/
def MemSobolevWk {n : ℕ} (k : ℕ) (p : ℝ≥0∞) (f : E n → ℝ) : Prop :=
  LocallyIntegrable f volume ∧
  ∀ m : Fin n → ℕ, (∑ i, m i) ≤ k →
    ∃ g : E n → ℝ, IsWeakDeriv f g m ∧ MemLp g p volume

set_option linter.dupNamespace false in
/-- **Hölder space $C^{r,\alpha}(\mathbb{R}^n)$.** For a natural number $r$ and a real number
$\alpha$, a function $g : \mathbb{R}^n \to \mathbb{R}$ belongs to $C^{r,\alpha}(\mathbb{R}^n)$ when
$g$ is $r$ times continuously differentiable, its iterated derivatives $D^j g$ for $j \le r$ are
bounded on $\mathbb{R}^n$, and its $r$-th derivative is $\alpha$-Hölder: there is $C \ge 0$ with
$\|D^r g(x) - D^r g(y)\| \le C \|x - y\|^{\alpha}$ for all $x, y \in \mathbb{R}^n$. Here
$D^j g(x)$ is the $j$-th Fréchet derivative of $g$ at $x$, a $j$-linear map measured in the
operator norm, and a negative $\alpha$ is replaced by $0$. -/
def MemHolder {n : ℕ} (r : ℕ) (α : ℝ) (g : E n → ℝ) : Prop :=
  ContDiff ℝ (r : ℕ∞) g ∧
  (∃ C : NNReal, HolderWith C α.toNNReal (iteratedFDeriv ℝ r g)) ∧
  (∀ j ≤ r, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ M)

open Set Function Filter Metric ContinuousLinearMap
open scoped ContDiff Topology Convolution

noncomputable section

private lemma ae_eq_of_weak_zero {n : ℕ} {f u : E n → ℝ}
    (hf : LocallyIntegrable f volume) (hu : LocallyIntegrable u volume)
    (h : IsWeakDeriv f u 0) : f =ᵐ[volume] u := by
  refine ae_eq_of_integral_contDiff_smul_eq hf hu ?_
  intro φ hφ hφc
  simpa [mixedDeriv, smul_eq_mul, mul_comm] using h φ hφ hφc

private abbrev basisVec {n : ℕ} (i : Fin n) : E n := EuclideanSpace.single i 1

private lemma smooth_partial {n : ℕ} {φ : E n → ℝ} (h : ContDiff ℝ ∞ φ) (i : Fin n) :
    ContDiff ℝ ∞ (partialDeriv i φ) := by
  unfold partialDeriv
  exact (h.fderiv_right (by simp)).clm_apply contDiff_const

private lemma partial_comm {n : ℕ} {φ : E n → ℝ} (h : ContDiff ℝ ∞ φ)
    (i j : Fin n) : partialDeriv i (partialDeriv j φ) = partialDeriv j (partialDeriv i φ) := by
  ext x
  unfold partialDeriv
  have hd := (h.fderiv_right (m := 1) (by norm_num)).differentiable_one x
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using (h.contDiffAt.isSymmSndFDerivAt (by simp : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω)))
    (basisVec i) (basisVec j)

-- Partial derivatives commute on the space of smooth functions.
private def testPartial {n : ℕ} (i : Fin n) :
    {φ : E n → ℝ // ContDiff ℝ ∞ φ} → {φ : E n → ℝ // ContDiff ℝ ∞ φ} :=
  fun φ => ⟨partialDeriv i φ, smooth_partial φ.2 i⟩

private lemma commute_testPartial {n : ℕ} (i j : Fin n) :
    Function.Commute (testPartial i) (testPartial j) :=
  fun φ => Subtype.ext (partial_comm φ.2 i j)

private lemma testPartial_foldr {n : ℕ} (m : Fin n → ℕ) (i : Fin n)
    (l : List (Fin n)) (φ : {φ : E n → ℝ // ContDiff ℝ ∞ φ}) :
    testPartial i (l.foldr (fun j => (testPartial j)^[m j]) φ) =
      l.foldr (fun j => (testPartial j)^[m j]) (testPartial i φ) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [(commute_testPartial i j).iterate_right (m j) _, ih]

private lemma testPartial_foldr_add {n : ℕ} (m : Fin n → ℕ) (i : Fin n)
    (l : List (Fin n)) (hl : l.Nodup) (hi : i ∈ l) (φ : {φ : E n → ℝ // ContDiff ℝ ∞ φ}) :
    l.foldr (fun j => (testPartial j)^[(m + (Pi.single i 1 : Fin n → ℕ)) j]) φ =
      l.foldr (fun j => (testPartial j)^[m j]) (testPartial i φ) := by
  classical
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rw [List.nodup_cons] at hl
    by_cases hji : j = i
    · subst j
      have htail : ∀ j ∈ l, (testPartial j)^[(m + (Pi.single i 1 : Fin n → ℕ)) j] =
          (testPartial j)^[m j] := by
        intro j hj
        have hj' : j ≠ i := by rintro rfl; exact hl.1 hj
        simp [Pi.single_eq_of_ne hj']
      have hfold : ∀ l' : List (Fin n),
          (∀ j ∈ l', (testPartial j)^[(m + (Pi.single i 1 : Fin n → ℕ)) j] =
            (testPartial j)^[m j]) →
          l'.foldr (fun j => (testPartial j)^[(m + (Pi.single i 1 : Fin n → ℕ)) j]) φ =
            l'.foldr (fun j => (testPartial j)^[m j]) φ := by
        intro l' hh
        induction l' with
        | nil => rfl
        | cons b l' ih =>
          simp only [List.foldr_cons, hh b (by simp), ih fun j hj => hh j (by simp [hj])]
      rw [List.foldr_cons, List.foldr_cons, hfold l htail]
      simp only [Pi.add_apply, Pi.single_eq_same, Function.iterate_succ_apply']
      rw [(commute_testPartial i i).iterate_right (m i) _, testPartial_foldr]
    · have hil : i ∈ l := (List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simp only [List.foldr_cons, Pi.add_apply, Pi.single_eq_of_ne hji, add_zero]
      exact congrArg ((testPartial j)^[m j]) (ih hl.2 hil)

private lemma val_foldr_testPartial {n : ℕ} (m : Fin n → ℕ) (l : List (Fin n))
    (φ : {φ : E n → ℝ // ContDiff ℝ ∞ φ}) :
    (l.foldr (fun i => (testPartial i)^[m i]) φ).val =
      l.foldr (fun i => (partialDeriv i)^[m i]) φ.val := by
  have hc (i : Fin n) : Semiconj Subtype.val (testPartial i) (partialDeriv i) := fun _ => rfl
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, (hc i).iterate_right (m i) _, ih]

private lemma mixedDeriv_add_single {n : ℕ} (m : Fin n → ℕ) (i : Fin n)
    {φ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    mixedDeriv (m + (Pi.single i 1 : Fin n → ℕ)) φ = mixedDeriv m (partialDeriv i φ) := by
  simpa only [val_foldr_testPartial, mixedDeriv, testPartial] using congrArg Subtype.val
    (testPartial_foldr_add m i _ (List.nodup_finRange n) (List.mem_finRange i) ⟨φ, hφ⟩)

private def WeakFirst {n : ℕ} (u : E n → ℝ) (v : Fin n → E n → ℝ) : Prop :=
  ∀ i φ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∫ y, u y * partialDeriv i φ y) = -∫ y, v i y * φ y

private lemma weakFirst_of_mixed {n : ℕ} {f u : E n → ℝ} {v : Fin n → E n → ℝ}
    {m : Fin n → ℕ} (hu : IsWeakDeriv f u m)
    (hv : ∀ i, IsWeakDeriv f (v i) (m + (Pi.single i 1 : Fin n → ℕ))) : WeakFirst u v := by
  classical
  intro i φ hφ hφc
  have h1 := hu (partialDeriv i φ) (smooth_partial hφ i) (hφc.fderiv_apply ℝ (basisVec i))
  have h2 := hv i φ hφ hφc
  rw [mixedDeriv_add_single m i hφ] at h2
  have hsum : ∑ j, (m + (Pi.single i 1 : Fin n → ℕ)) j = (∑ j, m j) + 1 := by
    simp [Pi.add_apply, Finset.sum_add_distrib]
  rw [hsum, pow_succ, h1] at h2
  have hn : (-1 : ℝ) ^ (∑ j, m j) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hn (by linear_combination h2)

-- All mollifiers below are dilations of one normalized bump.
private def bump {n : ℕ} (t : ℝ) (ht : 0 < t) : ContDiffBump (0 : E n) :=
  ⟨t / 2, t, half_pos ht, half_lt_self ht⟩

private def dilate {n : ℕ} (K : E n → ℝ) (t : ℝ) (z : E n) : ℝ :=
  (t ^ n)⁻¹ * K (t⁻¹ • z)

private lemma dilate_normed_bump {n : ℕ} (t : ℝ) (ht : 0 < t) :
    dilate ((bump (n := n) 1 one_pos).normed volume) t = (bump t ht).normed volume := by
  have hscale (z : E n) : (bump (n := n) t ht : E n → ℝ) z =
      (bump (n := n) 1 one_pos : E n → ℝ) (t⁻¹ • z) := by
    simp only [ContDiffBump.apply, bump, sub_zero]
    congr 1
    · field_simp
    · rw [smul_smul]
      congr 1
      field_simp
  have hint : (∫ z, (bump (n := n) t ht : E n → ℝ) z) =
      t ^ n * ∫ z, (bump (n := n) 1 one_pos : E n → ℝ) z := by
    simp_rw [hscale]
    rw [Measure.integral_comp_inv_smul_of_nonneg volume _ (hR := ht.le)]
    simp [smul_eq_mul]
  ext z
  rw [dilate, ContDiffBump.normed_def, ContDiffBump.normed_def, hint, hscale]
  ring

private lemma dilate_smooth {n : ℕ} {K : E n → ℝ} (hK : ContDiff ℝ ∞ K) :
    ContDiffOn ℝ ∞ (uncurry (dilate K)) (Ioi 0 ×ˢ univ) := by
  have hfst : ContDiffOn ℝ ∞ (Prod.fst : ℝ × E n → ℝ) (Ioi 0 ×ˢ univ) :=
    contDiffOn_fst
  have hne (x : ℝ × E n) (hx : x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (E n))) :
      x.1 ≠ 0 := (show 0 < x.1 from hx.1).ne'
  exact ((hfst.pow n).inv (fun x hx => pow_ne_zero _ (hne x hx))).mul
    (hK.comp_contDiffOn ((hfst.inv hne).smul contDiffOn_snd))

private lemma dilate_smooth_at {n : ℕ} {K : E n → ℝ} (hK : ContDiff ℝ ∞ K)
    (t : ℝ) : ContDiff ℝ ∞ (dilate K t) :=
  contDiff_const.mul (hK.comp (contDiff_id.const_smul _))

private lemma dilate_compact {n : ℕ} {K : E n → ℝ} (hK : HasCompactSupport K)
    {t : ℝ} (ht : 0 < t) : HasCompactSupport (dilate K t) :=
  (hK.comp_smul (inv_ne_zero ht.ne')).mul_left

private def avg {n : ℕ} (K u : E n → ℝ) (t : ℝ) (x : E n) : ℝ :=
  (u ⋆[lsmul ℝ ℝ] dilate K t) x

private lemma avg_ae_tendsto {n : ℕ} {u : E n → ℝ} (hu : LocallyIntegrable u volume) :
    ∀ᵐ x ∂(volume : Measure (E n)),
      Tendsto (fun t => avg ((bump 1 one_pos).normed volume) u t x) (𝓝[>] 0) (𝓝 (u x)) := by
  let B (t : ℝ) : ContDiffBump (0 : E n) :=
    if ht : 0 < t then bump t ht else bump 1 one_pos
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hsupp : Tendsto (fun t => (B t).rOut) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id |>.congr' (hpos.mono fun t ht => by
      simp [B, ht, bump])
  have hratio : ∀ᶠ t in 𝓝[>] (0 : ℝ), (B t).rOut ≤ 2 * (B t).rIn := by
    filter_upwards [hpos] with t ht
    simp [B, ht, bump]
    linarith
  filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hsupp hratio hu]
    with x hx
  refine hx.congr' (hpos.mono fun t ht => ?_)
  change ((B t).normed volume ⋆[lsmul ℝ ℝ] u) x = (u ⋆[lsmul ℝ ℝ] dilate _ t) x
  rw [show B t = bump t ht by simp [B, ht], dilate_normed_bump t ht]
  rw [convolution_lsmul_swap, convolution_lsmul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => mul_comm _ _

private lemma fderiv_convolution_coord {n : ℕ} {u K : E n → ℝ}
    {v : Fin n → E n → ℝ} (hu : LocallyIntegrable u volume) (hw : WeakFirst u v)
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) (x : E n) (i : Fin n) :
    fderiv ℝ (u ⋆[lsmul ℝ ℝ] K) x (basisVec i) = (v i ⋆[lsmul ℝ ℝ] K) x := by
  rw [(hKc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hK.of_le (by simp)) x).fderiv,
    convolution_precompR_apply _ hu (hKc.fderiv ℝ)
      (hK.continuous_fderiv (by simp)) x, convolution_lsmul, convolution_lsmul]
  let φ (y : E n) := K (x - y)
  have hφ : ContDiff ℝ ∞ φ := hK.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ :=
    hKc.comp_homeomorph (Homeomorph.subLeft x)
  have hpartial (y : E n) : partialDeriv i φ y = -fderiv ℝ K (x - y) (basisVec i) := by
    have hsub : HasFDerivAt (fun y : E n => x - y) (-(ContinuousLinearMap.id ℝ (E n))) y := by
      exact (hasFDerivAt_const x y).fun_sub (hasFDerivAt_id y) |>.congr_fderiv (zero_sub _)
    have hD := ((hK.differentiable (by simp) (x - y)).hasFDerivAt.comp y hsub).fderiv
    change fderiv ℝ (K ∘ (x - ·)) y (basisVec i) = _
    rw [hD]
    simp
  have h := hw i φ hφ hφc
  simp only [hpartial, mul_neg, integral_neg, neg_inj] at h
  simpa [φ, smul_eq_mul] using h

private def moment {n : ℕ} (K : E n → ℝ) (i : Fin n) (z : E n) : ℝ :=
  z i * K z

private lemma smooth_moment {n : ℕ} {K : E n → ℝ} (hK : ContDiff ℝ ∞ K) (i : Fin n) :
    ContDiff ℝ ∞ (moment K i) :=
  (EuclideanSpace.proj i).contDiff.mul hK

private lemma compact_moment {n : ℕ} {K : E n → ℝ} (hK : HasCompactSupport K) (i : Fin n) :
    HasCompactSupport (moment K i) := hK.mul_left

private lemma sum_coord_basisVec {n : ℕ} (x : E n) :
    ∑ i, x i • basisVec i = x := by
  simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
    (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x

private lemma fderiv_dilate_apply {n : ℕ} {K : E n → ℝ} (hK : ContDiff ℝ ∞ K)
    (t : ℝ) (z w : E n) :
    fderiv ℝ (dilate K t) z w = (t ^ n)⁻¹ * fderiv ℝ K (t⁻¹ • z) (t⁻¹ • w) := by
  have hs := (hasFDerivAt_id z (𝕜 := ℝ)).const_smul t⁻¹
  have h := ((hK.differentiable (by simp) (t⁻¹ • z)).hasFDerivAt.comp z hs).const_mul (t ^ n)⁻¹
  rw [show fderiv ℝ (dilate K t) z = _ from h.fderiv]
  simp [smul_eq_mul]

-- The scale derivative of the dilated bump is minus the divergence of its moments.
private lemma sum_partial_dilate_moment {n : ℕ} {K : E n → ℝ} (hK : ContDiff ℝ ∞ K)
    (t : ℝ) (z : E n) :
    ∑ i, partialDeriv i (dilate (moment K i) t) z =
      (t ^ n)⁻¹ * t⁻¹ * ((n : ℝ) * K (t⁻¹ • z) + fderiv ℝ K (t⁻¹ • z) (t⁻¹ • z)) := by
  have hterm (i : Fin n) :
      partialDeriv i (dilate (moment K i) t) z =
        (t ^ n)⁻¹ * t⁻¹ * (K (t⁻¹ • z) +
          (t⁻¹ • z) i * fderiv ℝ K (t⁻¹ • z) (basisVec i)) := by
    rw [partialDeriv, fderiv_dilate_apply (smooth_moment hK i)]
    have hm := ((EuclideanSpace.proj i).hasFDerivAt (x := t⁻¹ • z)).mul
      (hK.differentiable (by simp) (t⁻¹ • z)).hasFDerivAt
    rw [show fderiv ℝ (moment K i) (t⁻¹ • z) = _ from hm.fderiv]
    simp [EuclideanSpace.proj, smul_eq_mul]
    ring
  simp_rw [hterm, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← smul_eq_mul, ← map_smul, ← map_sum, sum_coord_basisVec]

private lemma hasDerivAt_dilate_scale {n : ℕ} {K : E n → ℝ} (hK : ContDiff ℝ ∞ K)
    {t : ℝ} (ht : 0 < t) (z : E n) :
    HasDerivAt (fun t => dilate K t z) (-∑ i, partialDeriv i (dilate (moment K i) t) z) t := by
  have hpow := ((hasDerivAt_id t).pow n).inv (pow_ne_zero _ ht.ne')
  have harg := (hasDerivAt_inv ht.ne').smul_const z
  have hcomp := (hK.differentiable (by simp) (t⁻¹ • z)).hasFDerivAt.comp_hasDerivAt t harg
  refine (hpow.mul hcomp).congr_deriv ?_
  rw [sum_partial_dilate_moment hK]
  have harg' : -(t ^ 2)⁻¹ • z = -t⁻¹ • (t⁻¹ • z) := by
    rw [smul_smul]
    congr 1
    field_simp
  change (-(↑n * t ^ (n - 1) * 1) / (t ^ n) ^ 2) * K (t⁻¹ • z) +
    (t ^ n)⁻¹ * fderiv ℝ K (t⁻¹ • z) (-(t ^ 2)⁻¹ • z) = _
  rw [harg']
  simp only [map_smul, smul_eq_mul]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_one_sub_one, Nat.cast_succ, pow_succ]
    field_simp
    ring

private lemma dilate_zero_of_one_support {n : ℕ} {K : E n → ℝ}
    (hKs : support K ⊆ ball 0 1) {t : ℝ} (ht : 0 < t) {z : E n} (hz : z ∉ ball 0 t) :
    dilate K t z = 0 := by
  have h0 : K (t⁻¹ • z) = 0 := by
    by_contra! hne
    have hb := hKs (mem_support.2 hne)
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
      ← div_eq_inv_mul, div_lt_one ht] at hb
    exact hz (mem_ball_zero_iff.mpr hb)
  simp [dilate, h0]

private lemma hasDerivAt_avg_scale {n : ℕ} {u K : E n → ℝ} {v : Fin n → E n → ℝ}
    (hu : LocallyIntegrable u volume) (hw : WeakFirst u v)
    (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) (hKs : support K ⊆ ball 0 1)
    {t : ℝ} (ht : 0 < t) (x : E n) :
    HasDerivAt (fun t => avg K u t x) (-∑ i, avg (moment K i) (v i) t x) t := by
  let s := Ioo (0 : ℝ) (2 * t)
  let c := closedBall (0 : E n) (2 * t)
  have hs : IsOpen s := isOpen_Ioo
  have hc : IsCompact c := isCompact_closedBall _ _
  have hsc : ∀ r z, r ∈ s → z ∉ c → dilate K r z = 0 := by
    intro r z hr hz
    exact dilate_zero_of_one_support hKs hr.1
      (fun h => hz (ball_subset_closedBall (ball_subset_ball hr.2.le h)))
  have hD : ContDiffOn ℝ 1 (uncurry (dilate K)) (s ×ˢ univ) :=
    ((dilate_smooth hK).of_le (by simp)).mono (prod_mono (fun _ hr => hr.1) (Subset.rfl))
  have hts : t ∈ s := ⟨ht, by linarith⟩
  have hparam := hasFDerivAt_convolution_right_with_param (lsmul ℝ ℝ) hs hc hsc hu hD (t, x) hts
  have hpair : HasDerivAt (fun r => (r, x)) (1, (0 : E n)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  refine (hparam.comp_hasDerivAt t hpair).congr_deriv ?_
  change ((u ⋆[(lsmul ℝ ℝ).precompR (ℝ × E n)]
    fun z => fderiv ℝ (uncurry (dilate K)) (t, z)) x) (1, 0) = _
  have hDc : HasCompactSupport (fun z => fderiv ℝ (uncurry (dilate K)) (t, z)) := by
    apply hc.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ hc.isClosed
    intro z hz
    by_contra hzc
    have he : (fun _ : ℝ × E n => (0 : ℝ)) =ᶠ[𝓝 (t, z)] uncurry (dilate K) := by
      rw [nhds_prod_eq]
      filter_upwards [prod_mem_prod (hs.mem_nhds hts) (hc.isClosed.isOpen_compl.mem_nhds hzc)]
      rintro ⟨r, y⟩ ⟨hr, hy⟩
      exact (hsc r y hr hy).symm
    exact hz ((hasFDerivAt_const (0 : ℝ) (t, z)).congr_of_eventuallyEq he.symm).fderiv
  have hDcont : Continuous (fun z => fderiv ℝ (uncurry (dilate K)) (t, z)) :=
    (hD.continuousOn_fderiv_of_isOpen (hs.prod isOpen_univ) le_rfl).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hts, mem_univ _⟩)
  rw [convolution_precompR_apply _ hu hDc hDcont]
  have heval (z : E n) : fderiv ℝ (uncurry (dilate K)) (t, z) (1, 0) =
      -∑ i, partialDeriv i (dilate (moment K i) t) z := by
    have hd := (hD.differentiableOn one_ne_zero).differentiableAt
      ((hs.prod isOpen_univ).mem_nhds (show (t, z) ∈ s ×ˢ univ from ⟨hts, mem_univ _⟩))
    have hpair' : HasDerivAt (fun r => (r, z)) (1, (0 : E n)) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
    rw [← (hd.hasFDerivAt.comp_hasDerivAt t hpair').deriv]
    exact (hasDerivAt_dilate_scale hK ht z).deriv
  simp_rw [heval, convolution_lsmul, smul_eq_mul, mul_neg, integral_neg, Finset.mul_sum]
  congr 1
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    have hKi := dilate_smooth_at (smooth_moment hK i) t
    have hcKi := dilate_compact (compact_moment hKc i) ht
    rw [avg, ← fderiv_convolution_coord hu hw hKi hcKi,
      (hcKi.hasFDerivAt_convolution_right (lsmul ℝ ℝ) hu (hKi.of_le (by simp)) x).fderiv,
      convolution_precompR_apply _ hu (hcKi.fderiv ℝ) (hKi.continuous_fderiv (by simp)),
      convolution_lsmul]
    rfl
  · intro i _
    have hKi := dilate_smooth_at (smooth_moment hK i) t
    have hcKi := dilate_compact (compact_moment hKc i) ht
    exact (hcKi.fderiv_apply ℝ (basisVec i)).convolutionExists_right
      (lsmul ℝ ℝ) hu (smooth_partial hKi i).continuous x

private lemma norm_avg_le {n : ℕ} {u K : E n → ℝ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (hu : MemLp u (ENNReal.ofReal p) volume)
    (hK : Continuous K) (hKc : HasCompactSupport K) {t : ℝ} (ht : 0 < t) (x : E n) :
    ‖avg K u t x‖ ≤
      lpNorm u (ENNReal.ofReal p) volume * lpNorm K (ENNReal.ofReal q) volume *
        t ^ (-(n : ℝ) / p) := by
  have hscont : Continuous (t⁻¹ • · : E n → E n) :=
    continuous_id.const_smul t⁻¹
  have hc : Continuous (dilate K t) :=
    continuous_const.mul (hK.comp hscont)
  have hKm : MemLp (dilate K t) (ENNReal.ofReal q) volume :=
    hc.memLp_of_hasCompactSupport (dilate_compact hKc ht)
  let := hpq.ennrealOfReal
  have hnorm := eNorm_convolution_le (lsmul ℝ ℝ) (p := ENNReal.ofReal p) (q := ENNReal.ofReal q)
    hu.aestronglyMeasurable hKm.aestronglyMeasurable x
  have hL : ‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ ≤ 1 := opENorm_lsmul_le
  have hs : ‖avg K u t x‖ₑ ≤
      eLpNorm u (ENNReal.ofReal p) volume * eLpNorm (dilate K t) (ENNReal.ofReal q) volume := by
    calc
      _ ≤ ‖(lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)‖ₑ * _ * _ := hnorm
      _ ≤ 1 * eLpNorm u (ENNReal.ofReal p) volume *
          eLpNorm (dilate K t) (ENNReal.ofReal q) volume := by gcongr
      _ = _ := by rw [one_mul]
  have hB := ENNReal.toReal_mono
    (by simpa using ENNReal.mul_ne_top hu.eLpNorm_ne_top hKm.eLpNorm_ne_top) hs
  have hlp : ‖avg K u t x‖ ≤ lpNorm u (ENNReal.ofReal p) volume *
      lpNorm (dilate K t) (ENNReal.ofReal q) volume := by
    simpa [avg, ENNReal.toReal_mul, toReal_eLpNorm] using hB
  refine hlp.trans_eq ?_
  rw [mul_assoc (lpNorm u _ _)]
  congr 1
  have hmap : (volume : Measure (E n)).map (t⁻¹ • ·) =
      (t ^ n).toNNReal • volume := by
    rw [Measure.map_addHaar_smul _ (inv_ne_zero ht.ne'), finrank_euclideanSpace_fin,
      inv_pow, inv_inv, abs_of_pos (pow_pos ht n)]
    rfl
  have hscale : lpNorm (fun z => K (t⁻¹ • z)) (ENNReal.ofReal q) volume =
      ((t ^ n) ^ q⁻¹) * lpNorm K (ENNReal.ofReal q) volume := by
    simp only [← toReal_eLpNorm]
    rw [show (fun z => K (t⁻¹ • z)) = K ∘ (t⁻¹ • ·) from rfl,
      ← eLpNorm_map_measure hK.aestronglyMeasurable hscont.aemeasurable,
      hmap, toReal_eLpNorm, lpNorm_smul_measure_of_ne_zero (by simpa using pow_pos ht n)]
    simp [toReal_eLpNorm, ENNReal.toReal_ofReal hpq.symm.nonneg, NNReal.smul_def, NNReal.coe_rpow,
      Real.coe_toNNReal _ (pow_nonneg ht.le _)]
  change lpNorm ((t ^ n)⁻¹ • (fun z => K (t⁻¹ • z))) (ENNReal.ofReal q) volume = _
  rw [lpNorm_const_smul, hscale, coe_nnNorm,
    Real.norm_of_nonneg (inv_nonneg.2 (pow_nonneg ht.le _))]
  have hpow : (t ^ n)⁻¹ * (t ^ n) ^ q⁻¹ = t ^ (-(n : ℝ) / p) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_mul ht.le,
      ← Real.rpow_add ht]
    congr 1
    have hinv := hpq.inv_add_inv_eq_one
    rw [div_eq_mul_inv]
    linear_combination (n : ℝ) * hinv
  rw [← mul_assoc, hpow, mul_comm]

private lemma scale_comparison {f : ℝ → ℝ} {β C : ℝ} (hβ : 0 < β)
    (hf : ∀ t > 0, DifferentiableAt ℝ f t)
    (hderiv : ∀ t > 0, |deriv f t| ≤ C * t ^ (β - 1))
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |f s - f t| ≤ (C / β) * |s ^ β - t ^ β| := by
  wlog hst : s ≤ t generalizing s t
  · rw [abs_sub_comm (f s), abs_sub_comm (s ^ β)]
    exact this ht hs (le_of_not_ge hst)
  have hm (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun t => (C / β) * t ^ β) (C * x ^ (β - 1)) x := by
    convert (Real.hasDerivAt_rpow_const (p := β) (Or.inl hx.ne')).const_mul (C / β) using 1
    field_simp
  have hmonoPlus : MonotoneOn (fun t => (C / β) * t ^ β + f t) (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => C * t ^ (β - 1) + deriv f t)
      (convex_Ioi _)
    · exact fun x hx => ((hm x hx).add (hf x hx).hasDerivAt).continuousAt.continuousWithinAt
    · rw [isOpen_Ioi.interior_eq]
      exact fun x hx => ((hm x hx).add (hf x hx).hasDerivAt).hasDerivWithinAt
    · rw [isOpen_Ioi.interior_eq]
      exact fun x hx => by linarith only [(abs_le.mp (hderiv x hx)).1]
  have hmonoSub : MonotoneOn (fun t => (C / β) * t ^ β - f t) (Ioi 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => C * t ^ (β - 1) - deriv f t)
      (convex_Ioi _)
    · exact fun x hx => ((hm x hx).sub (hf x hx).hasDerivAt).continuousAt.continuousWithinAt
    · rw [isOpen_Ioi.interior_eq]
      exact fun x hx => ((hm x hx).sub (hf x hx).hasDerivAt).hasDerivWithinAt
    · rw [isOpen_Ioi.interior_eq]
      exact fun x hx => by linarith only [(abs_le.mp (hderiv x hx)).2]
  have hp := hmonoPlus (show s ∈ Ioi 0 from hs) (show t ∈ Ioi 0 from ht) hst
  have hm' := hmonoSub (show s ∈ Ioi 0 from hs) (show t ∈ Ioi 0 from ht) hst
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.rpow_le_rpow hs.le hst hβ.le))]
  apply abs_le.mpr
  dsimp only at hp hm'
  constructor <;> linarith only [hp, hm']

private lemma tendstoUniformly_of_scale_comparison {X : Type*} {F : ℝ → X → ℝ}
    {β B : ℝ} (hβ : 0 < β) (hB : 0 ≤ B)
    (h : ∀ s t, 0 < s → 0 < t → ∀ x, |F s x - F t x| ≤ B * |s ^ β - t ^ β|) :
    ∃ g, TendstoUniformly F g (𝓝[>] 0) ∧
      ∀ t > 0, ∀ x, |F t x - g x| ≤ B * t ^ β := by
  have hpow : Tendsto (fun t : ℝ => t ^ β) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousWithinAt (fun t : ℝ => t ^ β) (Ioi 0) 0 :=
      (Real.continuousAt_rpow_const 0 β (Or.inr hβ.le)).continuousWithinAt
    change Tendsto _ _ (𝓝 ((0 : ℝ) ^ β)) at hc
    simpa [Real.zero_rpow hβ.ne'] using hc
  have hsmall : ∀ ε > 0, ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ B * t ^ β < ε := by
    intro ε hε
    have hBp : Tendsto (fun t : ℝ => B * t ^ β) (𝓝[>] 0) (𝓝 0) := by
      simpa using hpow.const_mul B
    exact (show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin).and
      (hBp.eventually (gt_mem_nhds hε))
  have hlim (x : X) : ∃ a, Tendsto (fun t => F t x) (𝓝[>] 0) (𝓝 a) := by
    apply cauchy_iff_exists_le_nhds.mp
    refine Metric.cauchy_iff.mpr ⟨inferInstance, fun ε hε => ?_⟩
    let s := {t : ℝ | 0 < t ∧ B * t ^ β < ε / 2}
    refine ⟨(fun t => F t x) '' s, mem_map.mpr ((hsmall (ε/2) (half_pos hε)).mono
      (fun t ht => mem_image_of_mem _ ht)), ?_⟩
    rintro _ ⟨t, ht, rfl⟩ _ ⟨u, hu, rfl⟩
    have hdist := h t u ht.1 hu.1 x
    rw [Real.dist_eq]
    refine hdist.trans_lt ?_
    rw [← abs_of_nonneg hB, ← abs_mul, mul_sub]
    exact (abs_sub _ _).trans_lt (by
      have ht₀ := mul_nonneg hB (Real.rpow_nonneg ht.1.le β)
      have hu₀ := mul_nonneg hB (Real.rpow_nonneg hu.1.le β)
      rw [abs_of_nonneg ht₀, abs_of_nonneg hu₀]
      linarith only [ht.2, hu.2])
  choose g hg using hlim
  have herror (t : ℝ) (ht : 0 < t) (x : X) : |F t x - g x| ≤ B * t ^ β := by
    have hL := (tendsto_const_nhds (x := F t x)).sub (hg x) |>.abs
    have hR := ((tendsto_const_nhds (x := t ^ β)).sub hpow).abs.const_mul B
    have he := le_of_tendsto_of_tendsto hL hR
      ((show ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s from self_mem_nhdsWithin).mono
        (fun s hs => h t s ht hs x))
    simpa [abs_of_nonneg (Real.rpow_nonneg ht.le _)] using he
  refine ⟨g, Metric.tendstoUniformly_iff.mpr (fun ε hε => (hsmall ε hε).mono ?_), herror⟩
  exact fun t ht x => by simpa [dist_comm, Real.dist_eq] using (herror t ht.1 x).trans_lt ht.2

private lemma fderiv_eq_coord_sum {n : ℕ} (L : E n →L[ℝ] ℝ) :
    L = ∑ i, L (basisVec i) • (EuclideanSpace.proj i : E n →L[ℝ] ℝ) := by
  ext y
  simp only [sum_apply, smul_apply, smul_eq_mul]
  conv_lhs => rw [← sum_coord_basisVec y, map_sum]
  simp only [map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private lemma norm_fderiv_le_coord_sum {n : ℕ} (L : E n →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ i, ‖L (basisVec i)‖ * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖ := by
  conv_lhs => rw [fderiv_eq_coord_sum L]
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_smul _ _)

private def morreyKernel (n : ℕ) : E n → ℝ := (bump 1 one_pos).normed volume

private structure MorreyApprox {n : ℕ} (β : ℝ) (u : E n → ℝ) where
  val : E n → ℝ
  ae_eq : u =ᵐ[volume] val
  uniform : TendstoUniformly (avg (morreyKernel n) u) val (𝓝[>] 0)
  holder : ∃ C : ℝ≥0, HolderWith C β.toNNReal val
  bounded : ∃ M : ℝ, ∀ x, ‖val x‖ ≤ M

private lemma holder_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {β C : ℝ} {f : X → Y} (hβ : 0 ≤ β) (hC : 0 ≤ C)
    (h : ∀ x y, dist (f x) (f y) ≤ C * dist x y ^ β) :
    HolderWith C.toNNReal β.toNNReal f := by
  intro x y
  rw [edist_dist, edist_dist, Real.coe_toNNReal _ hβ]
  change ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal C * ENNReal.ofReal (dist x y) ^ β
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg hβ, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (h x y)

-- A first-order Morrey estimate, including a uniform error bound for the mollifications.
private lemma morreyApprox_nonempty {n : ℕ} {p : ℝ} (hnp : (n : ℝ) < p)
    (hp : 1 < p) {u : E n → ℝ} {v : Fin n → E n → ℝ}
    (hu : MemLp u (ENNReal.ofReal p) volume) (hv : ∀ i, MemLp (v i) (ENNReal.ofReal p) volume)
    (hw : WeakFirst u v) : Nonempty (MorreyApprox (1 - n / p) u) := by
  let q := p.conjExponent
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  let β := 1 - (n : ℝ) / p
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hβ : 0 < β := sub_pos.mpr ((div_lt_one hp₀).mpr hnp)
  have hβ' : β - 1 = -(n : ℝ) / p := by dsimp [β]; ring
  let K := morreyKernel n
  have hK : ContDiff ℝ ∞ K := (bump 1 one_pos).contDiff_normed
  have hKc : HasCompactSupport K := (bump 1 one_pos).hasCompactSupport_normed
  have hKs : support K ⊆ ball 0 1 := (bump 1 one_pos).support_normed_eq.subset
  let C := ∑ i, lpNorm (v i) (ENNReal.ofReal p) volume *
    lpNorm (moment K i) (ENNReal.ofReal q) volume
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => mul_nonneg lpNorm_nonneg lpNorm_nonneg)
  let D := ∑ i, lpNorm (v i) (ENNReal.ofReal p) volume *
    lpNorm K (ENNReal.ofReal q) volume * ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖
  have hD : 0 ≤ D := Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (mul_nonneg lpNorm_nonneg lpNorm_nonneg) (norm_nonneg _))
  have hscale (x : E n) (t : ℝ) (ht : 0 < t) :=
    hasDerivAt_avg_scale (hu.locallyIntegrable hp₁) hw hK hKc hKs ht x
  have hdiff (x : E n) (t : ℝ) (ht : 0 < t) :
      |deriv (fun t => avg K u t x) t| ≤ C * t ^ (β - 1) := by
    rw [(hscale x t ht).deriv, abs_neg, hβ', Finset.sum_mul, ← Real.norm_eq_abs]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
    exact norm_avg_le hpq (hv i) (smooth_moment hK i).continuous (compact_moment hKc i) ht x
  have hcompare (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (x : E n) :=
    scale_comparison hβ (fun t ht => (hscale x t ht).differentiableAt) (hdiff x) hs ht
  obtain ⟨g, hg, herror⟩ :=
    tendstoUniformly_of_scale_comparison hβ (div_nonneg hC hβ.le) hcompare
  refine ⟨⟨g, ?_, hg, ?_, ?_⟩⟩
  · filter_upwards [avg_ae_tendsto (hu.locallyIntegrable hp₁)] with x hx
    exact tendsto_nhds_unique hx (hg.tendsto_at x)
  · refine ⟨(C / β + D + C / β).toNNReal, holder_of_dist_le hβ.le (by positivity) ?_⟩
    intro x y
    by_cases hxy : x = y
    · subst y
      simp only [dist_self]
      exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
    let t := dist x y
    have ht : 0 < t := dist_pos.mpr hxy
    have hKt := dilate_smooth_at hK t
    have hKtc := dilate_compact hKc ht
    have hcont := hKtc.contDiff_convolution_right (lsmul ℝ ℝ)
      (hu.locallyIntegrable hp₁) hKt
    have hgrad (z : E n) : ‖fderiv ℝ (avg K u t) z‖ ≤ D * t ^ (-(n : ℝ) / p) := by
      refine (norm_fderiv_le_coord_sum _).trans ?_
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i _
      change ‖fderiv ℝ (u ⋆[lsmul ℝ ℝ] dilate K t) z (basisVec i)‖ *
        ‖(EuclideanSpace.proj i : E n →L[ℝ] ℝ)‖ ≤ _
      rw [fderiv_convolution_coord (hu.locallyIntegrable hp₁) hw hKt hKtc]
      have h := mul_le_mul_of_nonneg_right (norm_avg_le hpq (hv i) hK.continuous hKc ht z)
        (norm_nonneg (EuclideanSpace.proj i : E n →L[ℝ] ℝ))
      simpa only [avg, mul_right_comm] using h
    have hspatial : dist (avg K u t x) (avg K u t y) ≤ D * t ^ β := by
      have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hcont.differentiable (by simp) z) (fun z _ => hgrad z)
        (mem_univ y) (mem_univ x)
      rw [dist_eq_norm]
      refine h.trans_eq ?_
      rw [← dist_eq_norm, show dist x y = t from rfl, mul_assoc, ← Real.rpow_add_one ht.ne']
      rw [show -(n : ℝ) / p + 1 = β by linarith only [hβ']]
    have hx : dist (g x) (avg K u t x) ≤ C / β * t ^ β := by
      rw [dist_comm, Real.dist_eq]
      exact herror t ht x
    have hy : dist (avg K u t y) (g y) ≤ C / β * t ^ β :=
      herror t ht y
    calc
      dist (g x) (g y) ≤ dist (g x) (avg K u t x) +
          (dist (avg K u t x) (avg K u t y) + dist (avg K u t y) (g y)) :=
        (dist_triangle _ _ _).trans (add_le_add_right (dist_triangle _ _ _) _)
      _ ≤ C / β * t ^ β + (D * t ^ β + C / β * t ^ β) :=
        add_le_add hx (add_le_add hspatial hy)
      _ = (C / β + D + C / β) * t ^ β := by ring
  · refine ⟨C / β + lpNorm u (ENNReal.ofReal p) volume * lpNorm K (ENNReal.ofReal q) volume, ?_⟩
    intro x
    have hx := herror 1 one_pos x
    have hy := norm_avg_le hpq hu hK.continuous hKc one_pos x
    rw [Real.one_rpow, mul_one] at hx hy
    calc
      ‖g x‖ = ‖(g x - avg K u 1 x) + avg K u 1 x‖ := by rw [sub_add_cancel]
      _ ≤ _ := by
        refine (norm_add_le _ _).trans ?_
        rw [Real.norm_eq_abs, abs_sub_comm (g x)]
        exact add_le_add hx hy

private lemma uniform_finset_sum {ι T X Y : Type*} [SeminormedAddCommGroup Y] {l : Filter T}
    (s : Finset ι) {F : ι → T → X → Y} {g : ι → X → Y}
    (h : ∀ i ∈ s, TendstoUniformly (F i) (g i) l) :
    TendstoUniformly (fun t x => ∑ i ∈ s, F i t x) (fun x => ∑ i ∈ s, g i x) l := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (tendsto_const_nhds (x := (0 : Y)) (f := l)).tendstoUniformly_const (α := X)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

-- If the weak partials also have continuous representatives, they are the classical partials.
private lemma fderiv_morreyApprox {n : ℕ} {u : E n → ℝ} {v : Fin n → E n → ℝ} {β : ℝ}
    (hu : LocallyIntegrable u volume) (hw : WeakFirst u v)
    (g : MorreyApprox β u) (G : ∀ i, MorreyApprox β (v i)) (x : E n) :
    HasFDerivAt g.val (∑ i, (G i).val x • (EuclideanSpace.proj i : E n →L[ℝ] ℝ)) x := by
  let K := morreyKernel n
  let F (t : ℝ) : E n → ℝ := if 0 < t then avg K u t else 0
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hK : ContDiff ℝ ∞ K := (bump 1 one_pos).contDiff_normed
  have hKc : HasCompactSupport K := (bump 1 one_pos).hasCompactSupport_normed
  have hFt : TendstoUniformly F g.val (𝓝[>] 0) :=
    (tendstoUniformly_congr (hpos.mono (fun t ht => by simp [F, ht, K]))).mp g.uniform
  have hD (t : ℝ) : Differentiable ℝ (F t) := by
    by_cases ht : 0 < t
    · simp only [F, ite_eq_left ht]
      exact ((dilate_compact hKc ht).contDiff_convolution_right (lsmul ℝ ℝ) hu
        (dilate_smooth_at hK t)).differentiable (by simp)
    · simp only [F, ite_eq_right ht]
      exact differentiable_const _
  refine hasFDerivAt_of_tendstoUniformly (f' := fun t => fderiv ℝ (F t)) (l := 𝓝[>] 0)
    (g' := fun y => ∑ i, (G i).val y • (EuclideanSpace.proj i : E n →L[ℝ] ℝ))
    ?_ (fun t y => (hD t y).hasFDerivAt) hFt.tendsto_at x
  · have hev : (fun t => fun x => ∑ i, avg K (v i) t x •
        (EuclideanSpace.proj i : E n →L[ℝ] ℝ)) =ᶠ[𝓝[>] 0] (fun t => fderiv ℝ (F t)) := by
      filter_upwards [hpos] with t ht
      funext y
      rw [show F t = avg K u t by simp [F, ht], fderiv_eq_coord_sum (fderiv ℝ (avg K u t) y)]
      apply Finset.sum_congr rfl
      intro i _
      rw [show fderiv ℝ (avg K u t) y (basisVec i) = avg K (v i) t y from
        fderiv_convolution_coord hu hw (dilate_smooth_at hK t) (dilate_compact hKc ht) y i]
    apply (tendstoUniformly_congr hev).mp
    apply uniform_finset_sum Finset.univ
    intro i _
    exact (toSpanSingleton ℝ (EuclideanSpace.proj i : E n →L[ℝ] ℝ)).uniformContinuous
      |>.comp_tendstoUniformly (G i).uniform

private def BoundedHolder {X Y : Type*} [PseudoMetricSpace X] [SeminormedAddCommGroup Y]
    (β : ℝ) (f : X → Y) : Prop :=
  (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) ∧ ∃ C : ℝ≥0, HolderWith C β.toNNReal f

private lemma boundedHolder_comp {X Y Z : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {β : ℝ} {f : X → Y} (hf : BoundedHolder β f) (L : Y →L[ℝ] Z) :
    BoundedHolder β (L ∘ f) := by
  obtain ⟨⟨M, hM⟩, C, hC⟩ := hf
  refine ⟨⟨‖L‖ * M, fun x => (L.le_opNorm (f x)).trans
    (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _))⟩, ‖L‖₊ * C, ?_⟩
  simpa using (L.lipschitzWith.holderWith.comp hC)

private lemma boundedHolder_sum {ι X Y : Type*} [PseudoMetricSpace X] [NormedAddCommGroup Y]
    {β : ℝ} (s : Finset ι) {f : ι → X → Y} (h : ∀ i ∈ s, BoundedHolder β (f i)) :
    BoundedHolder β (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⟨0, by simp⟩, 0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨⟨Ma, hMa⟩, Ca, hCa⟩ := h a (Finset.mem_insert_self _ _)
    obtain ⟨⟨Ms, hMs⟩, Cs, hCs⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨⟨Ma + Ms, ?_⟩, Ca + Cs, ?_⟩
    · intro x
      simp only [Finset.sum_insert ha]
      exact (norm_add_le _ _).trans (add_le_add (hMa x) (hMs x))
    · simp only [Finset.sum_insert ha]
      exact hCa.add hCs

private lemma boundedHolder_toNNReal_le {X Y : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup Y] {β α : ℝ} {f : X → Y} (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hf : BoundedHolder β f) : ∃ C : ℝ≥0, HolderWith C α.toNNReal f := by
  obtain ⟨⟨M, hM⟩, C, hC⟩ := hf
  have hM₀ : 0 ≤ max M 0 := le_max_right _ _
  let D := (C : ℝ) + 2 * max M 0
  have hD : 0 ≤ D := by positivity
  refine ⟨D.toNNReal, holder_of_dist_le hα hD (fun x y => ?_)⟩
  have hβ : 0 ≤ β := hα.trans hαβ
  have hd := hC.dist_le x y
  rw [Real.coe_toNNReal _ hβ] at hd
  by_cases hy : dist x y ≤ 1
  · exact hd.trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge'
      dist_nonneg hy hα hαβ) C.coe_nonneg).trans
      (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (Real.rpow_nonneg dist_nonneg _)))
  · have hd₁ : 1 ≤ dist x y ^ α := Real.one_le_rpow (le_of_not_ge hy) hα
    rw [dist_eq_norm]
    calc
      ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ D := by dsimp [D]; linarith [hM x, hM y, le_max_left M 0, C.coe_nonneg]
      _ ≤ D * dist x y ^ α := le_mul_of_one_le_right hD hd₁

private lemma index_sum_add_single {n : ℕ} (m : Fin n → ℕ) (i : Fin n) :
    ∑ j, (m + (Pi.single i 1 : Fin n → ℕ)) j = (∑ j, m j) + 1 := by
  classical
  simp [Pi.add_apply, Finset.sum_add_distrib]

-- Assemble the iterated Fréchet derivatives from the system of coordinate derivatives.
private lemma contDiff_boundedHolder_of_coord_system {n k : ℕ} {β : ℝ}
    {g : (Fin n → ℕ) → E n → ℝ}
    (hcont : ∀ m, (∑ i, m i) < k → Continuous (g m))
    (hbh : ∀ m, (∑ i, m i) < k → BoundedHolder β (g m))
    (hderiv : ∀ m, (∑ i, m i) + 1 < k → ∀ x,
      HasFDerivAt (g m) (∑ i, g (m + (Pi.single i 1 : Fin n → ℕ)) x •
        (EuclideanSpace.proj i : E n →L[ℝ] ℝ)) x) (j : ℕ)
    (m : Fin n → ℕ) (hm : (∑ i, m i) + j < k) :
    ContDiff ℝ (j : ℕ∞) (g m) ∧ BoundedHolder β (iteratedFDeriv ℝ j (g m)) := by
  induction j generalizing m with
  | zero =>
    simp only [add_zero] at hm
    refine ⟨contDiff_zero.mpr (hcont m hm), ?_⟩
    rw [iteratedFDeriv_zero_eq_comp]
    exact boundedHolder_comp (hbh m hm)
      (continuousMultilinearCurryFin0 ℝ (E n) ℝ).symm.toLinearIsometry.toContinuousLinearMap
  | succ j ih =>
    let m' (i : Fin n) := m + (Pi.single i 1 : Fin n → ℕ)
    let L (i : Fin n) := toSpanSingleton ℝ (EuclideanSpace.proj i : E n →L[ℝ] ℝ)
    have hstep (i : Fin n) : (∑ h, m' i h) + j < k := by
      simp only [m', index_sum_add_single]
      omega
    have hf : ∀ x, HasFDerivAt (g m) (∑ i, L i (g (m' i) x)) x :=
      hderiv m (by omega)
    have hf' : fderiv ℝ (g m) = fun x => ∑ i, L i (g (m' i) x) :=
      funext (fun x => (hf x).fderiv)
    let H (i : Fin n) := L i ∘ g (m' i)
    have hcd (i : Fin n) : ContDiff ℝ (j : ℕ∞) (H i) :=
      (L i).contDiff.comp (ih _ (hstep i)).1
    constructor
    · rw [Nat.cast_succ, WithTop.coe_add, WithTop.coe_one, contDiff_succ_iff_fderiv, hf']
      exact ⟨fun x => (hf x).differentiableAt, by simp,
        ContDiff.sum (f := H) (fun i _ => hcd i)⟩
    · have hcast (i : Fin n) :
          iteratedFDeriv ℝ j (L i ∘ g (m' i)) =
            (compContinuousMultilinearMapL ℝ (fun _ : Fin j => E n) ℝ (E n →L[ℝ] ℝ) (L i)) ∘
              iteratedFDeriv ℝ j (g (m' i)) := by
        funext x
        exact (L i).iteratedFDeriv_comp_left ((ih _ (hstep i)).1.contDiffAt) (by simp)
      have hsum : BoundedHolder β (iteratedFDeriv ℝ j (fderiv ℝ (g m))) := by
        have hsumEq : iteratedFDeriv ℝ j (fderiv ℝ (g m)) =
            fun x => ∑ i, iteratedFDeriv ℝ j (H i) x := by
          rw [hf']
          exact funext (fun x => iteratedFDeriv_fun_sum_apply
            (f := H) (x := x) (fun i _ => (hcd i).contDiffAt))
        rw [hsumEq]
        apply boundedHolder_sum Finset.univ
        intro i _
        rw [hcast i]
        exact boundedHolder_comp (ih _ (hstep i)).2 _
      have heq : iteratedFDeriv ℝ (j + 1) (g m) =
          (continuousMultilinearCurryRightEquiv' ℝ j (E n) ℝ).symm ∘
            iteratedFDeriv ℝ j (fderiv ℝ (g m)) :=
        funext (fun _ => iteratedFDeriv_succ_eq_comp_right)
      rw [heq]
      let uncurryD := (continuousMultilinearCurryRightEquiv' ℝ j (E n) ℝ).symm
      exact boundedHolder_comp hsum uncurryD.toLinearIsometry.toContinuousLinearMap

private lemma weak_zero_dim {r : ℕ} {α : ℝ} (f : E 0 → ℝ) :
    ∃ g : E 0 → ℝ, f =ᵐ[volume] g ∧ MemHolder r α g := by
  have hconst : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
  refine ⟨f, Filter.EventuallyEq.refl _ _, ?_⟩
  rw [hconst]
  refine ⟨contDiff_const, ⟨0, ?_⟩, ?_⟩
  · have heq : iteratedFDeriv ℝ r (fun _ : E 0 => f 0) =
        fun _ => iteratedFDeriv ℝ r (fun _ : E 0 => f 0) 0 := by
      ext x
      rw [Subsingleton.elim x 0]
    rw [heq]
    exact HolderWith.const
  · intro j _
    exact ⟨‖iteratedFDeriv ℝ j (fun _ : E 0 => f 0) 0‖, fun x => by
      rw [Subsingleton.elim x 0]⟩

set_option linter.dupNamespace false in
/-- **Sobolev embedding theorem (Morrey regime).** Let $n, k, r$ be natural numbers and
$\alpha, p$ real numbers with $n < p$, $0 < \alpha \le 1$ and $r + \alpha < k - n/p$. Then every
function $f : \mathbb{R}^n \to \mathbb{R}$ in the Sobolev space $W^{k,p}(\mathbb{R}^n)$ is equal
almost everywhere, for Lebesgue measure, to some function $g$ in the Hölder space
$C^{r,\alpha}(\mathbb{R}^n)$.

Source: C.B. Morrey, 'Functions of several variables and absolute continuity, II', Duke Math. J. 6
(1940) 187–215; full Sobolev-embedding development in *Multiple Integrals in the Calculus of
Variations*, Springer 1966. Listed as §111 in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `sobolev_embedding_morrey`. -/
public theorem sobolev_embedding {n k r : ℕ} {α p : ℝ}
    (_hp : (n : ℝ) < p) (_hα : 0 < α) (_hα1 : α ≤ 1)
    (_hgap : (r : ℝ) + α < (k : ℝ) - n / p)
    (f : E n → ℝ) (_hf : MemSobolevWk k (ENNReal.ofReal p) f) :
    ∃ g : E n → ℝ, f =ᵐ[volume] g ∧ MemHolder r α g := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact weak_zero_dim f
  have hp : 1 < p := (show (1 : ℝ) ≤ n by exact_mod_cast hn).trans_lt _hp
  have hp₁ : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hp.le
  let β := 1 - (n : ℝ) / p
  have hβ : 0 < β := sub_pos.mpr ((div_lt_one (zero_lt_one.trans hp)).mpr _hp)
  have hrk : r < k := by
    have hnonneg : 0 ≤ (n : ℝ) / p := div_nonneg (Nat.cast_nonneg n) (zero_lt_one.trans hp).le
    have h : (r : ℝ) < k := by linarith only [_hgap, _hα, hnonneg]
    exact_mod_cast h
  -- Choose the weak derivatives, then take the uniform mollification limits below order k.
  choose u hwu hpu using _hf.2
  let U (m : Fin n → ℕ) : E n → ℝ := if hm : (∑ i, m i) ≤ k then u m hm else 0
  have hUlp (m : Fin n → ℕ) : MemLp (U m) (ENNReal.ofReal p) volume := by
    by_cases hm : (∑ i, m i) ≤ k
    · simpa [U, hm] using hpu m hm
    · simp [U, hm]
  have hUw (m : Fin n → ℕ) (hm : (∑ i, m i) ≤ k) : IsWeakDeriv f (U m) m := by
    simpa [U, hm] using hwu m hm
  have hstep (m : Fin n → ℕ) (hm : (∑ i, m i) < k) :
      WeakFirst (U m) (fun i => U (m + (Pi.single i 1 : Fin n → ℕ))) := by
    refine weakFirst_of_mixed (hUw m hm.le) (fun i => hUw _ ?_)
    rw [index_sum_add_single]
    omega
  let A (m : Fin n → ℕ) (hm : (∑ i, m i) < k) : MorreyApprox β (U m) :=
    Classical.choice (morreyApprox_nonempty _hp hp (hUlp m) (fun i => hUlp _) (hstep m hm))
  let g (m : Fin n → ℕ) : E n → ℝ := if hm : (∑ i, m i) < k then (A m hm).val else 0
  have hgeq (m : Fin n → ℕ) (hm : (∑ i, m i) < k) : g m = (A m hm).val := by simp [g, hm]
  have hcont (m : Fin n → ℕ) (hm : (∑ i, m i) < k) : Continuous (g m) := by
    rw [hgeq m hm]
    obtain ⟨C, hC⟩ := (A m hm).holder
    exact hC.continuous (Real.toNNReal_pos.mpr hβ)
  have hbh (m : Fin n → ℕ) (hm : (∑ i, m i) < k) : BoundedHolder β (g m) := by
    rw [hgeq m hm]
    exact ⟨(A m hm).bounded, (A m hm).holder⟩
  have hd (m : Fin n → ℕ) (hm : (∑ i, m i) + 1 < k) (x : E n) :
      HasFDerivAt (g m) (∑ i, g (m + (Pi.single i 1 : Fin n → ℕ)) x •
        (EuclideanSpace.proj i : E n →L[ℝ] ℝ)) x := by
    have hm' (i : Fin n) : (∑ j, (m + (Pi.single i 1 : Fin n → ℕ)) j) < k := by
      rwa [index_sum_add_single]
    have hm₀ : (∑ i, m i) < k := by omega
    simp_rw [hgeq m hm₀, fun i => hgeq (m + (Pi.single i 1 : Fin n → ℕ)) (hm' i)]
    exact fderiv_morreyApprox ((hUlp m).locallyIntegrable hp₁) (hstep m hm₀) _ _ x
  have hreg (j : ℕ) (hj : j < k) :
      ContDiff ℝ (j : ℕ∞) (g 0) ∧ BoundedHolder β (iteratedFDeriv ℝ j (g 0)) :=
    contDiff_boundedHolder_of_coord_system hcont hbh hd j 0 (by simpa using hj)
  have hk₀ : (∑ i : Fin n, (0 : Fin n → ℕ) i) < k := by simpa using (Nat.zero_le r).trans_lt hrk
  have hae : f =ᵐ[volume] g 0 := by
    rw [hgeq 0 hk₀]
    exact (ae_eq_of_weak_zero _hf.1 ((hUlp 0).locallyIntegrable hp₁) (hUw 0 hk₀.le)).trans
      (A 0 hk₀).ae_eq
  refine ⟨g 0, hae, (hreg r hrk).1, ?_, fun j hj => (hreg j (hj.trans_lt hrk)).2.1⟩
  -- At order k - 1 use Morrey regularity. A bounded extra derivative gives Lipschitz continuity.
  by_cases hkr : k = r + 1
  · have hαβ : α ≤ β := by
      rw [hkr, Nat.cast_add, Nat.cast_one] at _hgap
      dsimp [β]
      linarith only [_hgap]
    exact boundedHolder_toNNReal_le _hα.le hαβ (hreg r hrk).2
  · have hrk' : r + 1 < k := by omega
    let F := iteratedFDeriv ℝ r (g 0)
    have hF : Differentiable ℝ F :=
      (hreg (r + 1) hrk').1.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self r)
    obtain ⟨M, hM⟩ := (hreg (r + 1) hrk').2.1
    have hL : LipschitzWith M.toNNReal F := by
      refine lipschitzWith_of_nnNorm_fderiv_le hF (fun x => ?_)
      rw [← NNReal.coe_le_coe, coe_nnNorm, Real.coe_toNNReal']
      exact (norm_fderiv_iteratedFDeriv (n := r) (f := g 0)).trans_le
        ((hM x).trans (le_max_left _ _))
    apply boundedHolder_toNNReal_le _hα.le _hα1
    exact ⟨(hreg r hrk).2.1, M.toNNReal, by simpa using hL.holderWith⟩

end

end SobolevMorreyProblem
end Analysis

end MathlibExt.Analysis.SobolevMorreyWanted
