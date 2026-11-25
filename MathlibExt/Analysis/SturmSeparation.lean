/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/ODE/SturmSeparation.lean` (leanprover/lean-eval),
commit 38361be884302c7edce1908c4aef8296eb2cb27e, for the statement of `sturm_separation`
(manifest `manifests/problems/sturm_separation.toml`, rev 1, status archived).
Copyright 2026 Lean FRO, LLC.
Author (problem submitter): Kim Morrison.
Licensed under the Apache License, Version 2.0 (the "License"). You may obtain a copy at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. The upstream project ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS converted the benchmark theorem to a
Batteries wanted declaration and placed it in its current namespace. ATLAS subsequently added
the proof and moved the theorem from `WantedExt/Analysis/SturmSeparationWanted.lean` to this
module, preserving the statement and its docstring.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MathlibExt.Analysis.ODE.GreenKernel

/-!
# Sturm separation theorem

`sturm_separation` gives a unique zero of one solution between consecutive zeros of an
independent solution of the same second-order homogeneous linear ODE. An integrating factor
keeps the Wronskian nonzero, and Rolle's theorem applied to a quotient separates the zeros.
-/

open Set GreenKernel

namespace MathlibExt.Analysis.SturmSeparationWanted.Analysis.ODE

/-- The integrating factor for `w' = -p w` propagates nonvanishing from a single point. -/
private theorem ne_zero_of_linear_ode {J : Set ℝ} {p w : ℝ → ℝ}
    (ho : IsOpen J) (hc : IsPreconnected J) (hp : ContinuousOn p J)
    (hw : ∀ x ∈ J, HasDerivAt w (-p x * w x) x) {x₀ : ℝ} (hx₀ : x₀ ∈ J)
    (hw₀ : w x₀ ≠ 0) : ∀ x ∈ J, w x ≠ 0 := by
  let P := fun x => ∫ t in x₀..x, p t
  have hP (x : ℝ) (hx : x ∈ J) : HasDerivAt P (p x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hp.mono (hc.ordConnected.uIcc_subset hx₀ hx)).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter ho hp x hx) (hp.continuousAt (ho.mem_nhds hx))
  have hd (x : ℝ) (hx : x ∈ J) :
      HasDerivAt (fun t => Real.exp (P t) * w t) 0 x :=
    ((hP x hx).exp.fun_mul (hw x hx)).congr_deriv (by ring)
  intro x hx hzero
  have heq := ho.is_const_of_deriv_eq_zero hc
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hx₀ hx
  simp [hzero, hw₀] at heq

/-- If the second function had no zero, the quotient would violate Rolle's theorem. -/
private theorem exists_zero_between {J : Set ℝ} {u v : ℝ → ℝ}
    (hu : ∀ x ∈ J, HasDerivAt u (deriv u x) x) (hv : ∀ x ∈ J, HasDerivAt v (deriv v x) x)
    (hW : ∀ x ∈ J, wronskian u v x ≠ 0) {a b : ℝ} (hab : a < b) (hs : Icc a b ⊆ J)
    (ha : u a = 0) (hb : u b = 0) : ∃ x ∈ Ioo a b, v x = 0 := by
  by_contra h
  have hn (x : ℝ) (hx : x ∈ Icc a b) : v x ≠ 0 := by
    intro hvx
    have hux : u x ≠ 0 := fun hux => hW x (hs hx) (by simp [wronskian, hux, hvx])
    exact h ⟨x, ⟨hx.1.lt_of_ne (by rintro rfl; exact hux ha),
      hx.2.lt_of_ne (by rintro rfl; exact hux hb)⟩, hvx⟩
  have hd (x : ℝ) (hx : x ∈ Icc a b) := (hu x (hs hx)).fun_div (hv x (hs hx)) (hn x hx)
  obtain ⟨c, hc, hzero⟩ := exists_hasDerivAt_eq_zero hab
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (by simp [ha, hb])
    (fun x hx => hd x (Ioo_subset_Icc_self hx))
  have hc' := Ioo_subset_Icc_self hc
  have heq := (div_eq_zero_iff.mp hzero).resolve_right (pow_ne_zero _ (hn c hc'))
  apply hW c (hs hc')
  exact neg_eq_zero.mp (by simpa only [wronskian, neg_sub] using heq)

-- Preserve the source namespace and its continuity hypothesis on q, which cancels in W'.
set_option linter.dupNamespace false in
set_option linter.unusedVariables false in
/-- **Sturm separation theorem.** Let $p, q, y_1, y_2 : \mathbb{R} \to \mathbb{R}$ and $a < b$,
and let $J \subseteq \mathbb{R}$ be an open connected set (an open interval, possibly unbounded)
containing $[a, b]$. Suppose that $p$ and $q$ are continuous on $J$, and that $y_1$ and $y_2$
are twice differentiable at every point of $J$ and solve $y'' + p(x)\, y' + q(x)\, y = 0$ at
every $x \in J$. Suppose further that the Wronskian $y_1 y_2' - y_2 y_1'$ is nonzero at some
point of $J$. If $y_1(a) = y_1(b) = 0$ and $y_1(x) \ne 0$ for every $x \in (a, b)$, then $y_2$
has exactly one zero in the open interval $(a, b)$.

Source: C. Sturm, Mémoire sur les équations différentielles linéaires du second ordre, 1836.
Via leanprover/lean-eval@38361be, problem `sturm_separation`. -/
public theorem sturm_separation
    (p q y₁ y₂ : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (J : Set ℝ) (hJ_open : IsOpen J) (hJ_conn : IsPreconnected J)
    (hJ_sub : Set.Icc a b ⊆ J)
    (hp : ContinuousOn p J) (hq : ContinuousOn q J)
    (hy₁ : ∀ x ∈ J, HasDerivAt y₁ (deriv y₁ x) x)
    (hy₁' : ∀ x ∈ J, HasDerivAt (deriv y₁) (-(p x * deriv y₁ x + q x * y₁ x)) x)
    (hy₂ : ∀ x ∈ J, HasDerivAt y₂ (deriv y₂ x) x)
    (hy₂' : ∀ x ∈ J, HasDerivAt (deriv y₂) (-(p x * deriv y₂ x + q x * y₂ x)) x)
    (hW : ∃ x₀ ∈ J, y₁ x₀ * deriv y₂ x₀ - y₂ x₀ * deriv y₁ x₀ ≠ 0)
    (hza : y₁ a = 0) (hzb : y₁ b = 0)
    (hne : ∀ x ∈ Set.Ioo a b, y₁ x ≠ 0) :
    ∃! c, c ∈ Set.Ioo a b ∧ y₂ c = 0 := by
  obtain ⟨x₀, hx₀, h₀⟩ := hW
  have hd (x : ℝ) (hx : x ∈ J) :
      HasDerivAt (wronskian y₁ y₂) (-p x * wronskian y₁ y₂ x) x := by
    apply (((hy₁ x hx).fun_mul (hy₂' x hx)).sub ((hy₁' x hx).fun_mul (hy₂ x hx))).congr_deriv
    unfold wronskian
    ring
  have hw := ne_zero_of_linear_ode hJ_open hJ_conn hp hd hx₀
    (by simpa only [wronskian, mul_comm (deriv y₁ x₀)] using h₀)
  obtain ⟨c, hc, hzc⟩ := exists_zero_between hy₁ hy₂ hw hab hJ_sub hza hzb
  refine ⟨c, ⟨hc, hzc⟩, ?_⟩
  rintro d ⟨hd, hzd⟩
  have hw' (x : ℝ) (hx : x ∈ J) : wronskian y₂ y₁ x ≠ 0 := by
    intro heq
    apply hw x hx
    unfold wronskian at heq ⊢
    linear_combination -heq
  have impossible {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
      (hzs : y₂ s = 0) (hzt : y₂ t = 0) (hst : s < t) : False := by
    have hsub : Icc s t ⊆ Ioo a b := fun x hx => ⟨hs.1.trans_le hx.1, hx.2.trans_lt ht.2⟩
    obtain ⟨x, hx, hz⟩ := exists_zero_between hy₂ hy₁ hw' hst
      (hsub.trans (Ioo_subset_Icc_self.trans hJ_sub)) hzs hzt
    exact hne x (hsub (Ioo_subset_Icc_self hx)) hz
  exact le_antisymm (le_of_not_gt (impossible hc hd hzc hzd))
    (le_of_not_gt (impossible hd hc hzd hzc))

end MathlibExt.Analysis.SturmSeparationWanted.Analysis.ODE
