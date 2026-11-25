/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Batteries.Util.ProofWanted

open MeasureTheory

@[expose] public section

namespace MetaMathlibExt

/-- **Green's theorem.** Let $U \subseteq \mathbb{R}^2$ be open, let $D \subseteq U$ be bounded and
measurable, and let $L, M : \mathbb{R}^2 \to \mathbb{R}$ be continuously differentiable on $U$.
Let $a<b$ and let $\gamma=(\gamma_1,\gamma_2) : \mathbb{R} \to \mathbb{R}^2$ be continuous on
$[a,b]$, with $\gamma(a)=\gamma(b)$, injective on $[a,b)$, with $\gamma(t)\ne\gamma(a)$ for
$a<t<b$, with image $\gamma([a,b])$ equal to the boundary of $D$, and with $\gamma(t)\in U$ for
all $t\in[a,b]$. Suppose there is a finite set $S\subseteq[a,b]$ containing $a$ and $b$ such that
$\gamma$ is continuously differentiable on $[a,b]\setminus S$ and on $[u,v]$ for any two
consecutive points $u<v$ of $S$, and such that for every $t\in(a,b)\setminus S$ we have
$\gamma'(t)\ne0$ and, for some $\delta>0$, $\gamma(t)+\varepsilon(-\gamma_2'(t),\gamma_1'(t))\in D$
for all $0<\varepsilon<\delta$ (so $D$ lies to the left of the curve). Then
$$
\int_a^b \bigl(L(\gamma(t))\,\gamma_1'(t)+M(\gamma(t))\,\gamma_2'(t)\bigr)\,dt
=\int_D \Bigl(\frac{\partial M}{\partial x}-\frac{\partial L}{\partial y}\Bigr)\,d(x,y).
$$

Source: https://en.wikipedia.org/wiki/Green%27s_theorem (greens-theorem-s1). -/
theorem_wanted greens_theorem
    (U D : Set (ℝ × ℝ))
    (a b : ℝ)
    (γ : ℝ → ℝ × ℝ)
    (L M : ℝ × ℝ → ℝ)
    (hU : IsOpen U)
    (hDU : D ⊆ U)
    (hD_bdd : Bornology.IsBounded D)
    (hD_meas : MeasurableSet D)
    (hL : ContDiffOn ℝ 1 L U)
    (hM : ContDiffOn ℝ 1 M U)
    (hab : a < b)
    (hγcont : ContinuousOn γ (Set.Icc a b))
    (hγclosed : γ a = γ b)
    (hγinj : Set.InjOn γ (Set.Ico a b))
    (hγsimple : ∀ t ∈ Set.Ioo a b, γ t ≠ γ a)
    (hγtrace : γ '' Set.Icc a b = frontier D)
    (hγU : ∀ t ∈ Set.Icc a b, γ t ∈ U)
    (hγpw : ∃ S : Finset ℝ, a ∈ S ∧ b ∈ S ∧ ↑S ⊆ Set.Icc a b ∧
      ContDiffOn ℝ 1 γ (Set.Icc a b \ ↑S) ∧
      (∀ u v : ℝ, u ∈ S → v ∈ S → u < v → Set.Ioo u v ∩ ↑S = ∅ →
        ContDiffOn ℝ 1 γ (Set.Icc u v)) ∧
      ∀ t ∈ Set.Ioo a b \ ↑S, deriv γ t ≠ 0 ∧
        ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
          γ t + ε • (-(deriv γ t).2, (deriv γ t).1) ∈ D) :
    (∫ t in a..b,
      (L (γ t) * deriv (fun t => (γ t).1) t +
        M (γ t) * deriv (fun t => (γ t).2) t)) =
    ∫ p in D,
      (deriv (fun x => M (x, p.2)) p.1 -
        deriv (fun y => L (p.1, y)) p.2) ∂volume

end MetaMathlibExt