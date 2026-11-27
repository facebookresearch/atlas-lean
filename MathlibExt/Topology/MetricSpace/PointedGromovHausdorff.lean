/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Pointed Gromov–Hausdorff convergence

For pointed pseudometric spaces `(X n, p n)` and `(Y, q)`, `PointedGHConverges`
says: for every `R > 0` and `ε > 0`, eventually there is
`f : ball (p n) R → Y` with `f (p n) = q`,
`|dist (f x) (f y) - dist x y| ≤ ε` for all `x y`, and
`ball q (R - ε) ⊆ thickening ε (range f)`, with no regularity on `f`.

Source: N. Gigli, A. Mondino, G. Savaré, "Convergence of pointed non-compact
metric measure spaces and stability of Ricci curvature bounds and heat flows",
Proc. London Math. Soc. (3) 111 (2015), 1071–1129, arXiv:1311.4907, Definition
"Pointed measured Gromov Hausdorff convergence" (def:pmGH), itself GMS's
adaptation of Burago–Burago–Ivanov, A course in metric geometry, AMS GSM 33,
2001, Def. 8.1.1; the book's wording was not checked here. GMS work with
complete separable spaces and Borel maps (needed for their measure clause),
while here the spaces are arbitrary pseudometric spaces and the maps are
arbitrary. Hence in general this relation is an extension of the metric part
of GMS def:pmGH; it matches the "(not necessarily continuous)" maps of the
Burago–Burago–Ivanov transcription in arXiv:2602.04826, Def. 2.12. The two
agree when every space of the sequence is separable; see
`GromovHausdorff.pointedGHConverges_iff_exists_measurable` in
`MathlibExt.Topology.MetricSpace.PointedGromovHausdorffBorel` (not imported
here).

Remark: GMS write `B_R` without specifying open or closed. The open balls
above are an implementation choice: since the condition quantifies over all
radii and all `ε`, the open- and closed-ball readings give the same relation.

The strict-distortion transcription (`dis f < ε`) in arXiv:2602.04826,
Def. 2.12 is equivalent; see `pointedGHConverges_iff_dis_lt`.

No completeness or properness is built in, so a sequence can converge to
non-isometric limits (e.g. to a space and to a dense subspace of it). The
radius slack `R - ε` in clause (3) matters: with an equal-radius condition on
closed balls the notion changes for spaces that are not length spaces.
-/

@[expose] public section

namespace GromovHausdorff

universe u v

variable {X : ℕ → Type u} [∀ n, PseudoMetricSpace (X n)] {Y : Type v} [PseudoMetricSpace Y]

/-- **Pointed Gromov–Hausdorff convergence.** Let $X_0, X_1, \dots$ and $Y$ be pseudometric
spaces with base points $p_n \in X_n$ and $q \in Y$. The sequence $(X_n, p_n)$ converges to
$(Y, q)$ in the pointed Gromov–Hausdorff sense if for all $R > 0$ and $\varepsilon > 0$ there is
$N$ such that for every $n \ge N$ there is a map $f$ from the open ball $B(p_n, R)$ to $Y$ with
$f(p_n) = q$, with $|d(f(x), f(y)) - d(x, y)| \le \varepsilon$ for all $x, y \in B(p_n, R)$, and
such that every point of the open ball $B(q, R - \varepsilon)$ is at distance less than
$\varepsilon$ from some point of the image of $f$.

No measurability or continuity is required of $f$, and the spaces need not be complete or
separable, so this extends the metric part of the pointed measured Gromov–Hausdorff convergence
of Gigli–Mondino–Savaré, who use Borel maps on complete separable spaces. Open balls are an
implementation choice for their unspecified balls $B_R$. -/
def PointedGHConverges (p : ∀ n, X n) (q : Y) : Prop :=
  ∀ (R : ℝ) (hR : 0 < R) (ε : ℝ) (_ : 0 < ε),
    ∀ᶠ n in Filter.atTop, ∃ f : ↥(Metric.ball (p n) R) → Y,
      f ⟨p n, Metric.mem_ball_self hR⟩ = q ∧
        (∀ x y, |dist (f x) (f y) - dist (x : X n) (y : X n)| ≤ ε) ∧
        Metric.ball q (R - ε) ⊆ Metric.thickening ε (Set.range f)

/-- **Pointed Gromov–Hausdorff convergence with strict distortion.** Let $X_0, X_1, \dots$ and
$Y$ be pseudometric spaces with base points $p_n \in X_n$ and $q \in Y$. Then $(X_n, p_n)$
converges to $(Y, q)$ in the pointed Gromov–Hausdorff sense if and only if for all $R > 0$ and
$\varepsilon > 0$ there is $N$ such that for every $n \ge N$ there are a map $f$ from the open
ball $B(p_n, R)$ to $Y$ and a real number $\delta < \varepsilon$ with $f(p_n) = q$, with
$|d(f(x), f(y)) - d(x, y)| \le \delta$ for all $x, y \in B(p_n, R)$, and such that every point
of the open ball $B(q, R - \varepsilon)$ is at distance less than $\varepsilon$ from some point
of the image of $f$.

That is, the distortion of $f$ may be required to be strictly less than $\varepsilon$, as in
arXiv:2602.04826, Def. 2.12. -/
theorem pointedGHConverges_iff_dis_lt (p : ∀ n, X n) (q : Y) :
    PointedGHConverges p q ↔
      ∀ (R : ℝ) (hR : 0 < R) (ε : ℝ) (_ : 0 < ε),
        ∀ᶠ n in Filter.atTop, ∃ f : ↥(Metric.ball (p n) R) → Y,
          f ⟨p n, Metric.mem_ball_self hR⟩ = q ∧
            (∃ δ, δ < ε ∧ ∀ x y,
              |dist (f x) (f y) - dist (x : X n) (y : X n)| ≤ δ) ∧
            Metric.ball q (R - ε) ⊆ Metric.thickening ε (Set.range f) := by
  constructor
  · intro h R hR ε hε
    have h' := h R hR (ε / 2) (by linarith)
    refine h'.mono fun n ⟨f, hbase, hdist, hcover⟩ =>
      ⟨f, hbase, ⟨ε / 2, by linarith, hdist⟩, ?_⟩
    intro x hx
    have hx1 : x ∈ Metric.ball q (R - ε / 2) :=
      Metric.ball_subset_ball (by linarith) hx
    have hx2 : x ∈ Metric.thickening (ε / 2) (Set.range f) := hcover hx1
    exact Metric.thickening_mono (by linarith) (Set.range f) hx2
  · intro h R hR ε hε
    have h' := h R hR ε hε
    refine h'.mono fun n ⟨f, hbase, ⟨δ, hδε, hdist⟩, hcover⟩ =>
      ⟨f, hbase, ?_, hcover⟩
    intro x y
    have hx := hdist x y
    linarith

/-- **Constant sequences converge in the pointed Gromov–Hausdorff sense.** For every
pseudometric space $Y$ and every point $q \in Y$, the constant sequence $(X_n, p_n) = (Y, q)$
converges to $(Y, q)$ in the pointed Gromov–Hausdorff sense. -/
theorem pointedGHConverges_const (q : Y) :
    PointedGHConverges (X := fun _ => Y) (fun _ => q) q := by
  intro R hR ε hε
  refine Filter.Eventually.of_forall fun n => ⟨Subtype.val, rfl, ?_, ?_⟩
  · intro x y
    simpa using hε.le
  · intro x hx
    have hxR : x ∈ Metric.ball q R := Metric.ball_subset_ball (by linarith) hx
    exact Metric.self_subset_thickening hε _ ⟨⟨x, hxR⟩, rfl⟩

end GromovHausdorff
