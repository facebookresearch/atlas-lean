/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_22.lean` (OpenBMB/MA-ProofBench, commit 31bab4c):
the definitions of the unit disc and admissible family and the extremal theorem statement.
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li,
Jie Zhou and Yudong Wang. Licensed under the MIT License.

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
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Topology.Order.IsLUB
import MathlibExt.Analysis.Complex.Hurwitz
import MathlibExt.Analysis.Complex.NormalFamilies

/-!
# An extremal injective map into the unit disc

On a connected open subset of the unit disc containing zero, an admissible map attains the
supremum of the derivative norms at zero.
-/

@[expose] public section

namespace MathlibExt.Analysis.Complex.InjectiveDiskMapExtremalDerivWanted

/-- **Open unit disc.** The open unit disc is the set of complex numbers $z$ with $|z| < 1$, the
open ball of radius $1$ about $0$ in $\mathbb{C}$. -/
noncomputable abbrev unitDisk : Set ℂ := Metric.ball (0 : ℂ) 1

/-- **Admissible maps into the unit disc.** For a set $\Omega \subseteq \mathbb{C}$, the
admissible family of $\Omega$ is the set of functions $f : \mathbb{C} \to \mathbb{C}$ that are
complex differentiable on $\Omega$, injective on $\Omega$, satisfy $f(0) = 0$, and map $\Omega$
into the open unit disc $\{z \in \mathbb{C} : |z| < 1\}$. -/
def AdmissibleFamily (Ω : Set ℂ) : Set (ℂ → ℂ) :=
  {f | DifferentiableOn ℂ f Ω ∧ Set.InjOn f Ω ∧ f 0 = 0 ∧ Set.MapsTo f Ω unitDisk}

open Filter Metric Set
open scoped Topology

/-- Hurwitz applied to `F n z - F n a` on a ball missing `a` precludes a second
preimage of `g a`, unless the limit is constant on the whole domain. -/
private lemma injOn_limit {Ω : Set ℂ} (hΩ : IsOpen Ω) (hc : IsPreconnected Ω)
    (h0 : (0 : ℂ) ∈ Ω) {F : ℕ → ℂ → ℂ} (hF : ∀ n, F n ∈ AdmissibleFamily Ω)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g Ω) (hder : deriv g 0 ≠ 0)
    (hlim : TendstoLocallyUniformlyOn F g atTop Ω) : InjOn g Ω := by
  intro a ha b hb hab
  by_contra hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hΩ.sdiff isClosed_singleton) b
    (show b ∈ Ω \ {a} from ⟨hb, Ne.symm hne⟩)
  have hsub := hball.trans sdiff_subset
  have hb' := mem_ball_self hr (x := b)
  have hconv : TendstoLocallyUniformlyOn (fun n z => F n z - F n a)
      (fun z => g z - g a) atTop (ball b r) :=
    (hlim.mono hsub).sub
      ((hlim.tendsto_at ha).tendstoUniformlyOn_const _).tendstoLocallyUniformlyOn
  rcases hconv.eqOn_zero_or_ne_zero
      (.of_forall fun n => ((hF n).1.sub_const _).mono hsub)
      isOpen_ball (convex_ball b r).isPreconnected
      (.of_forall fun n z hz => sub_ne_zero.mpr fun he =>
        (hball hz).2 ((hF n).2.1 (hsub hz) ha he)) with hzero | hfree
  · have hlocal : g =ᶠ[𝓝 b] fun _ => g a := by
      filter_upwards [isOpen_ball.mem_nhds hb'] with z hz
      exact sub_eq_zero.mp (hzero hz)
    have hconst := (hg.analyticOnNhd hΩ).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hc hb hlocal
    have hatZero := hconst.eventuallyEq_of_mem (hΩ.mem_nhds h0)
    exact hder (hatZero.deriv_eq.trans (deriv_const _ _))
  · exact hfree b hb' (sub_eq_zero.mpr hab.symm)

/-- **Existence of an extremal injective map into the unit disc.** Let $D$ be the open unit disc
$\{z \in \mathbb{C} : |z| < 1\}$, let $\Omega \subseteq D$ be open and connected with
$0 \in \Omega$, and let $F$ be the family of functions $f$ that are holomorphic and injective on
$\Omega$, map $\Omega$ into $D$, and satisfy $f(0) = 0$. Then some $g \in F$ attains the supremum
of $|f'(0)|$ over $F$:

$$|g'(0)| = \sup_{f \in F} |f'(0)|.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functions of a complex
variable; Geometric function theory), `benchmark/level2/ma_proofbench_l2_22.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_mem_admissibleFamily_norm_deriv_eq_sSup
  (Ω : Set ℂ)
  (hΩ_open : IsOpen Ω)
  (hΩ_connected : IsConnected Ω)
  (h0 : (0 : ℂ) ∈ Ω)
  (hΩ_subset : Ω ⊆ unitDisk) :
  ∃ g ∈ AdmissibleFamily Ω,
    ‖deriv g 0‖ = sSup ((fun f : ℂ → ℂ => ‖deriv f 0‖) '' AdmissibleFamily Ω) := by
  let S := (fun f : ℂ → ℂ => ‖deriv f 0‖) '' AdmissibleFamily Ω
  have hid : id ∈ AdmissibleFamily Ω :=
    ⟨differentiableOn_id, injOn_id Ω, rfl, hΩ_subset⟩
  have hone : (1 : ℝ) ∈ S := ⟨id, hid, by simp⟩
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩ_open 0 h0
  have hbdd : BddAbove S := by
    refine ⟨1 / r, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    apply Complex.norm_deriv_le_div_of_mapsTo_ball (hf.1.mono hrΩ) _ hr
    rw [hf.2.2.1]
    exact fun z hz => ball_subset_closedBall (hf.2.2.2 (hrΩ hz))
  -- Montel gives a holomorphic limit of a sequence approaching the supremum.
  obtain ⟨u, -, hu, huS⟩ := exists_seq_tendsto_sSup ⟨1, hone⟩ hbdd
  choose F hF hFu using huS
  have hnorm (n : ℕ) (z : ℂ) (hz : z ∈ Ω) : ‖F n z‖ < 1 := by
    exact mem_ball_zero_iff.mp ((hF n).2.2.2 hz)
  obtain ⟨φ, hφ, g, hg, hlim⟩ := NormalFamilies.montel hΩ_open F (fun n => (hF n).1)
    (NormalFamilies.isLocallyUniformlyBoundedOn_of_forall_norm_le hΩ_open zero_le_one
      fun n z hz => (hnorm n z hz).le)
  have hg0 : g 0 = 0 := by
    symm
    simpa only [fun n => (hF (φ n)).2.2.1, tendsto_const_nhds_iff] using
      (hlim.tendsto_at h0)
  have hlimDeriv := (hlim.deriv (.of_forall fun n => (hF (φ n)).1) hΩ_open).tendsto_at h0
  have hmax : ‖deriv g 0‖ = sSup S := by
    apply tendsto_nhds_unique hlimDeriv.norm
    simpa only [Function.comp_def, hFu] using hu.comp hφ.tendsto_atTop
  have hder : deriv g 0 ≠ 0 := norm_pos_iff.mp <|
    (zero_lt_one.trans_le (le_csSup hbdd hone)).trans_eq hmax.symm
  refine ⟨g, ⟨hg, injOn_limit hΩ_open hΩ_connected.isPreconnected h0
    (fun n => hF (φ n)) hg hder hlim, hg0, ?_⟩, hmax⟩
  have hle (z : ℂ) (hz : z ∈ Ω) : ‖g z‖ ≤ 1 :=
    le_of_tendsto (hlim.tendsto_at hz).norm (.of_forall fun n => (hnorm (φ n) z hz).le)
  intro z hz
  rw [unitDisk, mem_ball, dist_zero_right]
  by_contra! hge
  have hmaxOn : IsMaxOn (norm ∘ g) Ω z := fun w hw => (hle w hw).trans hge
  have heq : g 0 = g z := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    hΩ_connected.isPreconnected hΩ_open hg hz hmaxOn h0
  rw [← heq, hg0, norm_zero] at hge
  exact one_pos.not_ge hge

end MathlibExt.Analysis.Complex.InjectiveDiskMapExtremalDerivWanted
