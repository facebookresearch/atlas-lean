/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic.Linarith

/-!
# Asymptotically equivalent cocompact metrics without a properness assumption

The theorem `conjecture_refuted` refutes `conjecture`, the unrestricted bounded-difference
conjecture, with complete, cocompact length metrics whose ratio tends to one and whose difference
is unbounded. On the product of the line and its space of bounded continuous
functions, pull the supremum metric back by the involution `(t, f) ↦ (t, bₜ - f)`, where
`bₜ(r) = √|r + t| - √|r|`. The two distances differ by at most the square root of the horizontal
distance. Equality holds between the origin and `(t, const (-t))` for every nonnegative `t`.
The function-space factor has a noncompact closed unit ball, so this example is non-proper.
The Engel-group example cited in the theorem docstring is a separate, proper example.

The unrestricted bounded-difference question has the following hypotheses and conclusion.
(a) `Γ` is a group (domain of the acting group).
(b) `(M, d₁)` is a complete length space (metric axioms via `MetricSpace`,
    completeness via `CompleteSpace`, length via approximate midpoints).
(c) `(M, d₂)` is a complete length space inducing the same topology on `M`
    (explicit metric axioms, explicit Cauchy completeness, approximate midpoints).
(d) `Γ` acts on `M` (a `MulAction`).
(e) the action is by isometries for `d₁` and for `d₂`.
(f) the action is cocompact (some compact set meets every `Γ`-orbit).
(g) asymptotic equivalence: `d₁ x y / d₂ x y → 1` as `d₁ x y → ∞`.
(h) question: whether `|d₁ - d₂|` is uniformly bounded over all pairs.
-/

@[expose] public section

namespace MathlibExt.Geometry.CocompactAsymptoticallyEquivalentMetricsWanted

/--
**Cocompact asymptotically equivalent length-space pair.** Let $\Gamma$ be a group acting on a
complete metric space $(M, d_1)$. A cocompact asymptotically equivalent length-space pair on $M$
is a function $d_2 \colon M \times M \to \mathbb{R}$ with the following properties. It is a
metric: $d_2(x, y) \ge 0$, $d_2(x, y) = 0$ if and only if $x = y$, $d_2(x, y) = d_2(y, x)$ and
$d_2(x, z) \le d_2(x, y) + d_2(y, z)$. It is complete: every sequence that is Cauchy for $d_2$
converges for $d_2$ to some point of $M$. Both $d_1$ and $d_2$ have approximate midpoints: for
$i = 1, 2$, all $x, y \in M$ and every $\varepsilon > 0$ there is $z \in M$ with
$\max(d_i(x, z), d_i(z, y)) \le d_i(x, y)/2 + \varepsilon$. The action is by isometries of both:
$d_i(g x, g y) = d_i(x, y)$ for all $g \in \Gamma$, $x, y \in M$ and $i = 1, 2$. The action is
cocompact: some compact set $K \subseteq M$ (compact for $d_1$) contains a point $g x$ of the orbit
of every $x \in M$. The two metrics induce the same topology: for every $x \in M$ and every
$\varepsilon > 0$ there is $\delta > 0$ with $d_2(x, y) < \varepsilon$ whenever
$d_1(x, y) < \delta$, and there is $\delta > 0$ with $d_1(x, y) < \varepsilon$ whenever
$d_2(x, y) < \delta$. Finally, $d_1$ and $d_2$ are asymptotically equivalent: for every
$\varepsilon > 0$ there is a real number $R$ such that
$|d_1(x, y) / d_2(x, y) - 1| < \varepsilon$ for all $x, y \in M$ with $d_1(x, y) \ge R$.

For complete metric spaces the approximate-midpoint property is equivalent to being a length
space.
-/
structure OWR1319022Data (Γ : Type*) (M : Type*) [Group Γ] [MetricSpace M]
    [CompleteSpace M] [MulAction Γ M] where
  d2 : M → M → ℝ
  d2_nonneg : ∀ x y : M, 0 ≤ d2 x y
  d2_eq_zero : ∀ x y : M, d2 x y = 0 ↔ x = y
  d2_symm : ∀ x y : M, d2 x y = d2 y x
  d2_triangle : ∀ x y z : M, d2 x z ≤ d2 x y + d2 y z
  d2_complete : ∀ u : ℕ → M,
    (∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m → d2 (u n) (u m) < ε) →
    ∃ x : M, ∀ (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → d2 (u n) x < ε
  length1 : ∀ (x y : M) (ε : ℝ), 0 < ε →
    ∃ z : M, max (dist x z) (dist z y) ≤ dist x y / 2 + ε
  length2 : ∀ (x y : M) (ε : ℝ), 0 < ε →
    ∃ z : M, max (d2 x z) (d2 z y) ≤ d2 x y / 2 + ε
  act_isom1 : ∀ g : Γ, ∀ x y : M, dist (g • x) (g • y) = dist x y
  act_isom2 : ∀ g : Γ, ∀ x y : M, d2 (g • x) (g • y) = d2 x y
  cocompact : ∃ K : Set M, IsCompact K ∧ ∀ x : M, ∃ g : Γ, g • x ∈ K
  /-- The second metric induces the ambient topology: `d2`-balls and
  `dist`-balls are locally cofinal at every point. Without this, a metric
  transported along a bijection to an unbounded space would make the
  asymptotic premise vacuous on a compact space while the conclusion
  fails. -/
  sameTopology : ∀ x : M, ∀ ε > 0,
    (∃ δ > 0, ∀ y : M, dist x y < δ → d2 x y < ε) ∧
      (∃ δ > 0, ∀ y : M, d2 x y < δ → dist x y < ε)
  asymptotic : ∀ (ε : ℝ), 0 < ε →
    ∃ R : ℝ, ∀ x y : M, R ≤ dist x y → |dist x y / d2 x y - 1| < ε

/--
**Unrestricted bounded-difference conjecture for cocompact metrics.** The conjecture asserts that
for every group $\Gamma$, every complete metric space $(M, d_1)$ on which $\Gamma$ acts, and every
cocompact asymptotically equivalent length-space pair on $M$ with second metric $d_2$, there is a
real number $C$ such that $|d_1(x, y) - d_2(x, y)| \le C$ for all $x, y \in M$.
This variant allows non-proper metric spaces and imposes no topology on the acting group.

Source: For Margulis's question about proper left-invariant pseudometrics on groups, see
Geometric Group Theory, Hyperbolic Dynamics and Symplectic Geometry, Oberwolfach Reports 3
(2006), pp. 1991--2058, DOI 10.4171/owr/2006/33 [OWR-1319-022].
-/
def conjecture : Prop :=
  ∀ (Γ : Type*) (M : Type*) [Group Γ] [MetricSpace M] [CompleteSpace M]
    [MulAction Γ M] (D : OWR1319022Data Γ M),
    ∃ C : ℝ, ∀ x y : M, |dist x y - D.d2 x y| ≤ C

noncomputable section

open scoped BoundedContinuousFunction

private abbrev Fiber := ℝ →ᵇ ℝ
private abbrev Space := ℝ × Fiber

private lemma sqrt_abs_sub (x y : ℝ) :
    |Real.sqrt (abs x) - Real.sqrt (abs y)| ≤ Real.sqrt |x - y| := by
  have h (a b : ℝ) : Real.sqrt |a| ≤ Real.sqrt |b| + Real.sqrt |a - b| := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hle := (abs_sub_abs_le_abs_sub a b)
    nlinarith [Real.sq_sqrt (abs_nonneg b), Real.sq_sqrt (abs_nonneg (a - b)),
      mul_nonneg (Real.sqrt_nonneg |b|) (Real.sqrt_nonneg |a - b|)]
  exact abs_le.mpr ⟨by linarith [abs_sub_comm y x ▸ h y x], by linarith [h x y]⟩

/-- Increment of the square-root profile under translation by `t`. -/
private def increment (t : ℝ) : Fiber :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun r : ℝ ↦ Real.sqrt |r + t| - Real.sqrt |r|) (by fun_prop) (Real.sqrt |t|) fun r ↦ by
      simpa [Real.norm_eq_abs] using sqrt_abs_sub (r + t) r

private lemma dist_increment_le (s t : ℝ) :
    dist (increment s) (increment t) ≤ Real.sqrt (dist s t) := by
  apply (BoundedContinuousFunction.dist_le (Real.sqrt_nonneg _)).2
  intro r
  change dist (Real.sqrt |r + s| - Real.sqrt |r|) (Real.sqrt |r + t| - Real.sqrt |r|) ≤ _
  simpa [Real.dist_eq, sub_sub_sub_cancel_right] using sqrt_abs_sub (r + s) (r + t)

/-- Reflecting each fiber about half its increment gives an involution. Its pullback of the
product metric is the second length metric. -/
private def reflect (x : Space) : Space := (x.1, increment x.1 - x.2)

private lemma reflect_twice (x : Space) : reflect (reflect x) = x := by
  simp [reflect]

private lemma reflect_dist_le (x y : Space) :
    dist (reflect x) (reflect y) ≤ dist x y + Real.sqrt (dist x.1 y.1) := by
  rw [Prod.dist_eq, max_le_iff]
  constructor
  · exact (le_max_left _ _).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · calc
      _ ≤ dist (increment x.1) (increment y.1) + dist x.2 y.2 := dist_sub_sub_le _ _ _ _
      _ ≤ _ := by
        linarith [dist_increment_le x.1 y.1, show dist x.2 y.2 ≤ dist x y from le_max_right _ _]

private lemma distortion (x y : Space) :
    |dist x y - dist (reflect x) (reflect y)| ≤ Real.sqrt (dist x.1 y.1) := by
  have h := reflect_dist_le (reflect x) (reflect y)
  rw [reflect_twice, reflect_twice] at h
  exact abs_le.mpr ⟨by linarith [reflect_dist_le x y], by
    change dist x y ≤ dist (reflect x) (reflect y) + Real.sqrt (dist x.1 y.1) at h
    linarith⟩

private lemma continuous_reflect : Continuous reflect := by
  have hi : Continuous increment := by
    refine Metric.continuous_iff.mpr fun x ε hε ↦ ⟨ε ^ 2, sq_pos_of_pos hε, fun y hy ↦ ?_⟩
    exact (dist_increment_le _ _).trans_lt ((Real.sqrt_lt' hε).2 hy)
  exact continuous_fst.prodMk ((hi.comp continuous_fst).sub continuous_snd)

private def shift (s : ℝ) (f : Fiber) : Fiber :=
  f.compContinuous ⟨(· + s), continuous_id.add continuous_const⟩

private lemma shift_dist (s : ℝ) (f g : Fiber) : dist (shift s f) (shift s g) = dist f g := by
  apply le_antisymm
  · exact (BoundedContinuousFunction.dist_le dist_nonneg).2 fun r ↦
      BoundedContinuousFunction.dist_coe_le_dist (r + s)
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).2 fun r ↦ ?_
    have h := BoundedContinuousFunction.dist_coe_le_dist (f := shift s f) (g := shift s g) (r - s)
    simpa [shift] using h

private lemma increment_add (s t : ℝ) :
    increment (s + t) = increment s + shift s (increment t) := by
  ext r
  change Real.sqrt |r + (s + t)| - Real.sqrt |r| =
    (Real.sqrt |r + s| - Real.sqrt |r|) + (Real.sqrt |r + s + t| - Real.sqrt |r + s|)
  rw [add_assoc]
  abel

/-- A shift of the real line together with a translation in the function space. -/
@[ext] private structure Motion where
  offset : ℝ
  vertical : Fiber

private instance motionGroup : Group Motion where
  one := ⟨0, 0⟩
  mul g h := ⟨g.offset + h.offset, g.vertical + shift g.offset h.vertical⟩
  inv g := ⟨-g.offset, -shift (-g.offset) g.vertical⟩
  mul_assoc g h k := by
    apply Motion.ext
    · exact add_assoc _ _ _
    · ext r
      change (g.vertical r + h.vertical (r + g.offset)) + k.vertical (r + (g.offset + h.offset)) =
        g.vertical r + (h.vertical (r + g.offset) + k.vertical ((r + g.offset) + h.offset))
      rw [add_assoc, add_assoc r]
  one_mul g := by
    refine Motion.ext (zero_add _) ?_
    ext r
    change 0 + g.vertical (r + 0) = g.vertical r
    simp
  mul_one g := Motion.ext (add_zero _) (by ext; exact add_zero _)
  inv_mul_cancel g := by
    apply Motion.ext
    · exact neg_add_cancel _
    · ext r
      exact neg_add_cancel _

private def point (g : Motion) : Space := (g.offset, g.vertical)

private instance motionAction : MulAction Motion Space where
  smul g x := point (g * ⟨x.1, x.2⟩)
  one_smul x := congrArg point (one_mul (⟨x.1, x.2⟩ : Motion))
  mul_smul g h x := congrArg point (mul_assoc g h ⟨x.1, x.2⟩)

private lemma move_dist (g : Motion) (x y : Space) :
    dist (g • x) (g • y) = dist x y := by
  change max (dist (g.offset + x.1) (g.offset + y.1))
    (dist (g.vertical + shift g.offset x.2) (g.vertical + shift g.offset y.2)) = _
  rw [dist_add_left, dist_add_left, shift_dist, Prod.dist_eq]

private lemma reflect_move (g : Motion) (x : Space) :
    reflect (g • x) = (⟨g.offset, increment g.offset - g.vertical⟩ : Motion) • reflect x := by
  refine Prod.ext rfl ?_
  change increment (g.offset + x.1) - (g.vertical + shift g.offset x.2) = _
  rw [increment_add]
  ext r
  change (increment g.offset r + increment x.1 (r + g.offset)) -
    (g.vertical r + x.2 (r + g.offset)) =
    increment g.offset r - g.vertical r + (increment x.1 (r + g.offset) - x.2 (r + g.offset))
  abel

private lemma ratio_close (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ x y : Space, R ≤ dist x y →
      |dist x y / dist (reflect x) (reflect y) - 1| < ε := by
  refine ⟨(2 + 2 / ε) ^ 2, fun x y hxy ↦ ?_⟩
  let a := dist x y
  let b := dist (reflect x) (reflect y)
  have herr : |a - b| ≤ Real.sqrt a :=
    (distortion x y).trans (Real.sqrt_le_sqrt (le_max_left _ _))
  have hs : 2 + 2 / ε ≤ Real.sqrt a := (Real.le_sqrt' (by positivity)).2 hxy
  have hs₂ : 2 ≤ Real.sqrt a := by linarith [show 0 < 2 / ε by positivity]
  have hsq : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt dist_nonneg
  have hab : a / 2 ≤ b := by
    nlinarith [(abs_le.mp herr).2, mul_nonneg (sub_nonneg.mpr hs₂) (Real.sqrt_nonneg a)]
  have hb : 0 < b := by nlinarith [sq_nonneg (Real.sqrt a - 2)]
  have hh : 2 < Real.sqrt a * ε := (div_lt_iff₀ hε).1 (by linarith)
  change |a / b - 1| < ε
  rw [div_sub_one hb.ne', abs_div, abs_of_pos hb, div_lt_iff₀ hb]
  apply herr.trans_lt
  calc
    Real.sqrt a < ε * (a / 2) := by
      nlinarith [mul_pos (sub_pos.mpr hh) (show 0 < Real.sqrt a by linarith)]
    _ ≤ ε * b := by gcongr

private lemma half_dist (x y : Space) :
    max (dist x (midpoint ℝ x y)) (dist (midpoint ℝ x y) y) = dist x y / 2 := by
  rw [dist_left_midpoint (𝕜 := ℝ) x y, dist_midpoint_right (𝕜 := ℝ) x y, max_self]
  norm_num [div_eq_inv_mul]

universe u v

/-- The group and space can be lifted independently to the universes in the question. -/
private def exampleData : OWR1319022Data (ULift.{u} Motion) (ULift.{v} Space) where
  d2 x y := dist (reflect x.down) (reflect y.down)
  d2_nonneg _ _ := dist_nonneg
  d2_eq_zero _ _ := dist_eq_zero.trans <|
    ((Function.Involutive.injective reflect_twice).comp ULift.down_injective).eq_iff
  d2_symm _ _ := dist_comm _ _
  d2_triangle _ _ _ := dist_triangle _ _ _
  d2_complete u hu := by
    have hc : CauchySeq (fun n ↦ reflect (u n).down) :=
      Metric.cauchySeq_iff.2 fun ε hε ↦
        (hu ε hε).imp fun _ h n hn m hm ↦ h n m hn hm
    obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hc
    exact ⟨⟨reflect p⟩, by simpa only [reflect_twice] using Metric.tendsto_atTop.1 hp⟩
  length1 x y _ hε :=
    ⟨⟨midpoint ℝ x.down y.down⟩, (half_dist _ _).le.trans (le_add_of_nonneg_right hε.le)⟩
  length2 x y _ hε := by
    refine ⟨⟨reflect (midpoint ℝ (reflect x.down) (reflect y.down))⟩, ?_⟩
    rw [reflect_twice, half_dist]
    exact le_add_of_nonneg_right hε.le
  act_isom1 g x y := move_dist g.down x.down y.down
  act_isom2 g x y := by
    change dist (reflect (g.down • x.down)) (reflect (g.down • y.down)) = _
    rw [reflect_move, reflect_move, move_dist]
  cocompact := by
    refine ⟨{ULift.up (point 1)}, isCompact_singleton, fun x ↦ ?_⟩
    let g : Motion := ⟨x.down.1, x.down.2⟩
    exact ⟨⟨g⁻¹⟩, congrArg (fun h ↦ ULift.up (point h)) (inv_mul_cancel g)⟩
  sameTopology x ε hε := by
    have hc (p : Space) := Metric.continuous_iff.mp continuous_reflect p ε hε
    constructor
    · obtain ⟨δ, hδ, h⟩ := hc x.down
      exact ⟨δ, hδ, fun y hy ↦ dist_comm (reflect y.down) _ ▸
        h y.down (dist_comm x.down y.down ▸ hy)⟩
    · obtain ⟨δ, hδ, h⟩ := hc (reflect x.down)
      refine ⟨δ, hδ, fun y hy ↦ ?_⟩
      simpa only [reflect_twice, dist_comm y.down, ULift.dist_eq] using
        h (reflect y.down) (dist_comm (reflect x.down) (reflect y.down) ▸ hy)
  asymptotic ε hε := (ratio_close ε hε).imp fun _ h x y ↦ h x.down y.down

/-- At horizontal distance `t`, use the constant function `-t` in the fiber. Evaluation at zero
detects the whole square-root increment on top of the ambient distance `t`. -/
private lemma gap_at (t : ℝ) (ht : 0 ≤ t) :
    ∃ x y : Space, Real.sqrt t ≤ |dist x y - dist (reflect x) (reflect y)| := by
  let y : Space := (t, BoundedContinuousFunction.const ℝ (-t))
  refine ⟨0, y, ?_⟩
  have h₁ : dist (0 : Space) y = t := by
    simp [y, Prod.dist_eq, Real.norm_eq_abs, abs_of_nonneg ht]
  have h₀ : increment 0 = 0 := by
    ext r
    change Real.sqrt |r + 0| - Real.sqrt |r| = 0
    simp
  have h₂ : t + Real.sqrt t ≤ dist (reflect 0) (reflect y) := by
    refine le_trans ?_ (le_max_right _ _)
    have he := BoundedContinuousFunction.dist_coe_le_dist
      (f := (reflect 0).2) (g := (reflect y).2) 0
    refine le_trans ?_ he
    change t + Real.sqrt t ≤ dist ((increment 0) 0 - 0)
      ((Real.sqrt |0 + t| - Real.sqrt |0|) - (-t))
    rw [h₀]
    simp [Real.dist_eq, abs_of_nonneg ht]
    linarith [neg_le_abs (-t + -Real.sqrt t)]
  rw [h₁, abs_sub_comm]
  exact le_trans (by linarith : Real.sqrt t ≤ dist (reflect 0) (reflect y) - t) (le_abs_self _)

/--
**Refutation of the unrestricted bounded-difference conjecture for cocompact metrics.**
There exist a group $\Gamma$, a complete metric space $(M, d_1)$ on which $\Gamma$ acts, and a
cocompact asymptotically equivalent length-space pair on $M$ with second metric $d_2$, such that
for every real number $C$ there are points $x, y \in M$ with $|d_1(x, y) - d_2(x, y)| > C$.

To refute `conjecture`, take the supremum product metric on
$\mathbb{R}\times C_b(\mathbb{R},\mathbb{R})$, where $C_b$
is the space of bounded continuous functions with the supremum norm. This space is non-proper
because the closed unit ball in the infinite-dimensional function space is noncompact. Pull back
the product metric along $(t,f)\mapsto(t,b_t-f)$, where $b_t(r)=\sqrt{|r+t|}-\sqrt{|r|}$.
The common isometric action is transitive. From the origin to $(t,f)$ with $t\ge 0$ and $f$
constant with value $-t$, the two distances are $t$ and $t+\sqrt{t}$.

For a separate example on a proper space, Le Donne, Nalon, Nicolussi Golo and Ryoo give a
left-invariant Riemannian metric on the Engel group whose difference from its canonical
asymptotic sub-Riemannian metric is unbounded (Example 4.2).

Source: E. Le Donne, L. Nalon, S. Nicolussi Golo, S.-Y.
Ryoo, Asymptotics of Riemannian Lie groups with nilpotency step 2, arXiv preprint (2025),
arXiv:2503.00560, https://arxiv.org/abs/2503.00560. Moved from
`OpenConjectures/Geometry/CocompactAsymptoticallyEquivalentMetrics`.
-/
public theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨C, hC⟩ := h _ _ exampleData
  obtain ⟨x, y, hxy⟩ := gap_at ((|C| + 1) ^ 2) (sq_nonneg _)
  rw [Real.sqrt_sq (by positivity)] at hxy
  have hbound := hC (ULift.up x) (ULift.up y)
  change |dist x y - dist (reflect x) (reflect y)| ≤ C at hbound
  linarith [le_abs_self C]

end

end MathlibExt.Geometry.CocompactAsymptoticallyEquivalentMetricsWanted
