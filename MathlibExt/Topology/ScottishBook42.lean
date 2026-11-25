/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Closeds
import MathlibExt.Analysis.Convex.BrouwerFixedPoint

/-!
# Fixed points on the hyperspace of compact convex sets

This file proves the fixed-point property for the Hausdorff hyperspace of nonempty compact convex
subsets of a Euclidean unit ball. Weighted Minkowski sums give approximations through finite
simplices, where Brouwer's theorem applies.
-/

@[expose] public section

namespace MathlibExt.Topology.ScottishBook42Wanted

/-- **Hausdorff continuity on compact convex sets.** Let $E$ be a real normed space, let
$K \subseteq E$, let $f$ be a map from subsets of $E$ to subsets of $E$, and write $d_H$ for the
Hausdorff distance between subsets of $E$. Then $f$ is Hausdorff continuous on the compact convex
subsets of $K$ if for every nonempty compact convex set $X \subseteq K$ and every
$\varepsilon > 0$ there is $\delta > 0$ such that every nonempty compact convex set
$Y \subseteq K$ with $d_H(X, Y) < \delta$ satisfies $d_H(f(X), f(Y)) < \varepsilon$.

Here $d_H$ is taken to be $0$ where the Hausdorff distance is infinite, in particular when exactly
one of the two sets is empty. The values $f(X)$ are not required to be compact, convex or
nonempty. -/
def HausdorffContinuousOnConvexCompacts {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : Set E → Set E) (K : Set E) : Prop :=
  ∀ X : Set E, X ⊆ K → IsCompact X → Convex ℝ X → X.Nonempty → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : Set E, Y ⊆ K → IsCompact Y → Convex ℝ Y → Y.Nonempty →
      Metric.hausdorffDist X Y < δ → Metric.hausdorffDist (f X) (f Y) < ε

section

open Set Metric TopologicalSpace
open Convexity (StdSimplex)

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The hyperspace of nonempty compact convex subsets of a given set. -/
private abbrev ConvexCompacts (K : Set E) :=
  {X : NonemptyCompacts E // (X : Set E) ⊆ K ∧ Convex ℝ (X : Set E)}

private theorem isClosed_convex :
    IsClosed {X : NonemptyCompacts E | Convex ℝ (X : Set E)} := by
  -- Express convexity by the closed inclusion of each weighted sum of two copies of the set.
  have h (a b : ℝ) :
      IsClosed {X : NonemptyCompacts E |
        ∀ x ∈ (X : Set E), ∀ y ∈ (X : Set E), a • x + b • y ∈ (X : Set E)} := by
    let g : E × E → E := fun p => a • p.1 + b • p.2
    have hg : Continuous g := by dsimp [g]; fun_prop
    have hmap : Continuous (fun X : NonemptyCompacts E => (X ×ˢ X).map g hg) :=
      hg.nonemptyCompacts_map.comp (NonemptyCompacts.continuous_prod.comp
        (continuous_id.prodMk continuous_id))
    convert isClosed_le hmap continuous_id using 1
    ext X
    change (∀ x ∈ (X : Set E), ∀ y ∈ (X : Set E), a • x + b • y ∈ (X : Set E)) ↔
      g '' ((X : Set E) ×ˢ (X : Set E)) ⊆ (X : Set E)
    rw [Set.image_subset_iff]
    constructor
    · intro hv p hp
      exact hv p.1 hp.1 p.2 hp.2
    · intro hv x hx y hy
      exact hv (show (x, y) ∈ (X : Set E) ×ˢ (X : Set E) from ⟨hx, hy⟩)
  suffices IsClosed {X : NonemptyCompacts E | ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∀ x ∈ (X : Set E), ∀ y ∈ (X : Set E), a • x + b • y ∈ (X : Set E)} by
    convert this using 1
    ext X
    exact ⟨fun hv _ _ ha hb hab _ hx _ hy => hv hx hy ha hb hab,
      fun hv => convex_iff_add_mem.mpr fun _ hx _ hy _ _ ha hb hab => hv _ _ ha hb hab _ hx _ hy⟩
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => by
      simpa only [Set.ofPred_forall] using h a b

private theorem isCompact_convexCompacts {K : Set E} (hK : IsCompact K) :
    IsCompact {X : NonemptyCompacts E | (X : Set E) ⊆ K ∧ Convex ℝ (X : Set E)} :=
  (NonemptyCompacts.isCompact_subsets_of_isCompact hK).inter_right isClosed_convex

private def compactsProduct {K : Set E} {ι : Type} (X : ι → ConvexCompacts K) :
    NonemptyCompacts (ι → E) :=
  ⟨⟨univ.pi fun i => ((X i).val : Set E),
    isCompact_univ_pi fun i => (X i).val.isCompact⟩,
    Set.univ_pi_nonempty_iff.mpr fun i => (X i).val.nonempty⟩

/-- The Minkowski combination is the image of the product under the weighted sum. -/
private noncomputable def combine {K : Set E} (hK : Convex ℝ K) {ι : Type} [Fintype ι]
    (X : ι → ConvexCompacts K) (w : StdSimplex ℝ ι) : ConvexCompacts K := by
  let L : (ι → E) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, w.weights i • x i
      map_add' := fun x y => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun a x => by simp [smul_comm (w.weights _) a, Finset.smul_sum] }
  have hLcont : Continuous L := by
    change Continuous (fun x : ι → E => ∑ i, w.weights i • x i)
    fun_prop
  refine ⟨(compactsProduct X).map L hLcont, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hK.sum_mem (fun i _ => w.weights_nonneg i) w.total_of_fintype
      (fun i _ => (X i).property.1 (hx i (Set.mem_univ i)))
  · exact (convex_pi fun {i} _ => (X i).property.2).linear_image L

private theorem continuous_combine {K : Set E} (hK : Convex ℝ K) {ι : Type} [Fintype ι]
    (X : ι → ConvexCompacts K) : Continuous (combine hK X) := by
  apply Continuous.subtype_mk
  have hg : Continuous (Function.uncurry (fun (w : StdSimplex ℝ ι) (x : ι → E) =>
      ∑ i, w.weights i • x i)) := by
    change Continuous (fun p : StdSimplex ℝ ι × (ι → E) => ∑ i, p.1.weights i • p.2 i)
    fun_prop
  exact (continuous_const (y := compactsProduct X)).nonemptyCompacts_map' hg

omit [NormedSpace ℝ E] in
private theorem exists_dist_le {X Y : NonemptyCompacts E} {x : E} (hx : x ∈ (X : Set E)) :
    ∃ y ∈ (Y : Set E), dist x y ≤ dist X Y := by
  obtain ⟨y, hy, hdist⟩ := Y.isCompact.exists_infDist_eq_dist Y.nonempty x
  refine ⟨y, hy, hdist ▸ ?_⟩
  exact infDist_le_hausdorffDist_of_mem hx
    (hausdorffEDist_ne_top_of_nonempty_of_bounded X.nonempty Y.nonempty
      X.isCompact.isBounded Y.isCompact.isBounded)

private theorem dist_sum_smul_le {ι : Type} [Fintype ι] (w : StdSimplex ℝ ι)
    (x y : ι → E) (r : ℝ) (h : ∀ i, 0 < w.weights i → dist (x i) (y i) ≤ r) :
    dist (∑ i, w.weights i • x i) (∑ i, w.weights i • y i) ≤ r := by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib]
  calc
    ‖∑ i, (w.weights i • x i - w.weights i • y i)‖
      ≤ ∑ i, ‖w.weights i • x i - w.weights i • y i‖ := norm_sum_le _ _
    _ ≤ ∑ i, w.weights i * r := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (w.weights_nonneg i), ← dist_eq_norm]
      rcases (w.weights_nonneg i).eq_or_lt with hi | hi
      · simp [← hi]
      · exact mul_le_mul_of_nonneg_left (h i hi) hi.le
    _ = r := by rw [← Finset.sum_mul, w.total_of_fintype, one_mul]

/-- A Minkowski combination stays close to a convex set close to each positive-weight input. -/
private theorem dist_combine_le {K : Set E} (hK : Convex ℝ K) {ι : Type} [Fintype ι]
    (X : ι → ConvexCompacts K) (w : StdSimplex ℝ ι) (Y : ConvexCompacts K) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ i, 0 < w.weights i → dist (X i) Y ≤ r) :
    dist (combine hK X w) Y ≤ r := by
  classical
  change hausdorffDist ((combine hK X w).val : Set E) (Y.val : Set E) ≤ r
  apply hausdorffDist_le_of_mem_dist hr
  · rintro _ ⟨x, hx, rfl⟩
    choose y hy hxy using fun i => exists_dist_le (Y := Y.val)
      (hx i (Set.mem_univ i))
    exact ⟨∑ i, w.weights i • y i,
      Y.property.2.sum_mem (fun i _ => w.weights_nonneg i) w.total_of_fintype (fun i _ => hy i),
      dist_sum_smul_le w x y r (fun i hi => (hxy i).trans (h i hi))⟩
  · intro y hy
    choose x hx hyx using fun i => exists_dist_le (X := Y.val) (Y := (X i).val) hy
    refine ⟨∑ i, w.weights i • x i, ⟨x, fun i _ => hx i, rfl⟩, ?_⟩
    have hy' : (∑ i, w.weights i • y) = y := by
      rw [← Finset.sum_smul, w.total_of_fintype, one_smul]
    rw [← hy']
    exact dist_sum_smul_le w (fun _ => y) x r (fun i hi =>
      (hyx i).trans ((dist_comm Y (X i)).trans_le (h i hi)))

private theorem sum_bumps_pos {A : Type} [MetricSpace A] {ι : Type} [Fintype ι]
    (c : ι → A) {r : ℝ} {x : A} (hx : ∃ i, dist x (c i) < r) :
    0 < ∑ i, max 0 (r - dist x (c i)) := by
  obtain ⟨i, hi⟩ := hx
  exact Finset.sum_pos' (fun j _ => le_max_left _ _)
    ⟨i, Finset.mem_univ i, (sub_pos.mpr hi).trans_le (le_max_right _ _)⟩

/-- Normalized distance bumps at the members of a finite metric cover. -/
private noncomputable def coverWeights {A : Type} [MetricSpace A] {ι : Type} [Fintype ι]
    (c : ι → A) (r : ℝ) (hc : ∀ x, ∃ i, dist x (c i) < r) (x : A) : StdSimplex ℝ ι := by
  let u : ι → ℝ := fun i => max 0 (r - dist x (c i))
  have hu : 0 < ∑ i, u i := sum_bumps_pos c (hc x)
  refine ⟨Finsupp.equivFunOnFinite.symm (fun i => u i / ∑ j, u j), ?_, ?_⟩
  · intro i
    exact div_nonneg (le_max_left _ _) hu.le
  · rw [Finsupp.sum_fintype _ _ (by simp)]
    change (∑ i, u i / ∑ j, u j) = 1
    rw [← Finset.sum_div, div_self hu.ne']

private theorem continuous_coverWeights {A : Type} [MetricSpace A] {ι : Type} [Fintype ι]
    (c : ι → A) (r : ℝ) (hc : ∀ x, ∃ i, dist x (c i) < r) :
    Continuous (coverWeights c r hc) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ ι).continuous_iff, continuous_pi_iff]
  intro i
  change Continuous (fun x => max 0 (r - dist x (c i)) / ∑ j, max 0 (r - dist x (c j)))
  exact Continuous.div (by fun_prop) (by fun_prop) (fun x => (sum_bumps_pos c (hc x)).ne')

private theorem dist_lt_of_coverWeights_pos {A : Type} [MetricSpace A] {ι : Type} [Fintype ι]
    {c : ι → A} {r : ℝ} {hc : ∀ x, ∃ i, dist x (c i) < r} {x : A} {i : ι}
    (hi : 0 < (coverWeights c r hc x).weights i) : dist x (c i) < r := by
  by_contra! h
  change 0 < max 0 (r - dist x (c i)) / (∑ j, max 0 (r - dist x (c j))) at hi
  simp [max_eq_left (sub_nonpos.mpr h)] at hi

/-- Brouwer gives an approximate fixed point by factoring through the finite cover simplex. -/
private theorem exists_approx_fixedPoint {K : Set E} (hK : Convex ℝ K)
    [CompactSpace (ConvexCompacts K)] [Nonempty (ConvexCompacts K)]
    (f : ConvexCompacts K → ConvexCompacts K) (hf : Continuous f) {r : ℝ} (hr : 0 < r) :
    ∃ X, dist X (f X) ≤ r := by
  classical
  obtain ⟨s, -, hs, hcover⟩ := isCompact_univ.finite_cover_balls (X := ConvexCompacts K) hr
  have hc₀ (X : ConvexCompacts K) : ∃ Y : s, dist X Y.val < r := by
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop, Subtype.exists] using
      hcover (Set.mem_univ X)
  have : Finite s := hs
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  cases k with
  | zero => exact Fin.elim0 (e (hc₀ (Classical.choice inferInstance)).choose)
  | succ k =>
    let c (i : Fin (k + 1)) : ConvexCompacts K := (e.symm i).val
    have hc (X : ConvexCompacts K) : ∃ i, dist X (c i) < r := by
      obtain ⟨Y, hY⟩ := hc₀ X
      exact ⟨e Y, by simpa [c] using hY⟩
    let g := combine hK c
    let w := coverWeights c r hc
    obtain ⟨a, ha⟩ := MathlibExt.Analysis.Convex.BrouwerFixedPoint.exists_fixedPoint_stdSimplex
      (w ∘ f ∘ g) ((continuous_coverWeights c r hc).comp (hf.comp (continuous_combine hK c)))
    refine ⟨g a, dist_combine_le hK c a (f (g a)) hr.le (fun i hi => ?_)⟩
    have hw : w (f (g a)) = a := ha
    have hpos : 0 < (w (f (g a))).weights i := hw.symm ▸ hi
    exact (dist_comm (c i) (f (g a))).trans_le (dist_lt_of_coverWeights_pos hpos).le

end

/--
**Fixed point theorem for maps of compact convex sets.** Let $n \ge 0$ and let $B$ be the
closed unit ball about the origin in the Euclidean space $\mathbb{R}^n$. Let $f$ be a map from
subsets of $\mathbb{R}^n$ to subsets of $\mathbb{R}^n$ that sends every nonempty compact convex
subset of $B$ to a nonempty compact convex subset of $B$, and that is continuous in the Hausdorff
metric on the nonempty compact convex subsets of $B$. Then there is a nonempty compact convex set
$X_0 \subseteq B$ with $f(X_0) = X_0$.

This answers Ulam's Problem 42 of the Scottish Book, which asks this for closed convex sets inside
a ball $K$; inside a ball the closed convex sets are the compact ones, and the typescript's
"sphere $K$" is read as the solid ball. All sets are required to be nonempty, because the
Hausdorff distance used is degenerate at the empty set. The answer is yes: for $n \ge 2$ the space
of nonempty compact convex subsets of $B$ is homeomorphic to the Hilbert cube (Nadler, Quinn and
Stavrokas), which has the fixed-point property; for $n \le 1$ that space is a point or a $2$-cell,
and Brouwer's theorem applies.

Source: S. Ulam, Problem 42 of the Scottish Book; S. B. Nadler, J. Quinn and
N. Stavrokas, Pacific J. Math. 83 (1979), 441-462; the fixed-point theorem
for the Hilbert cube; see the commentary in R. D. Mauldin (ed.),
The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem fixed_point_for_convex_hyperspace_map :
    ∀ (n : ℕ) (f : Set (EuclideanSpace ℝ (Fin n)) → Set (EuclideanSpace ℝ (Fin n))),
      (∀ X : Set (EuclideanSpace ℝ (Fin n)),
        X ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 → IsCompact X →
        Convex ℝ X → X.Nonempty →
        f X ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ∧
        IsCompact (f X) ∧ Convex ℝ (f X) ∧ (f X).Nonempty) →
      HausdorffContinuousOnConvexCompacts f
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) →
      ∃ X₀ : Set (EuclideanSpace ℝ (Fin n)),
        X₀ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ∧ IsCompact X₀ ∧
        Convex ℝ X₀ ∧ X₀.Nonempty ∧ f X₀ = X₀ := by
  intro n f hmaps hcont
  let E := EuclideanSpace ℝ (Fin n)
  let B : Set E := Metric.closedBall 0 1
  have hB : IsCompact B := isCompact_closedBall _ _
  have hBconv : Convex ℝ B := convex_closedBall _ _
  have : CompactSpace (ConvexCompacts B) :=
    isCompact_iff_compactSpace.mp (isCompact_convexCompacts hB)
  have : Nonempty (ConvexCompacts B) :=
    ⟨⟨{0}, Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self (by norm_num)),
      convex_singleton _⟩⟩
  let F (X : ConvexCompacts B) : ConvexCompacts B :=
    let h := hmaps X.val X.property.1 X.val.isCompact X.property.2 X.val.nonempty
    ⟨⟨⟨f X.val, h.2.1⟩, h.2.2.2⟩, h.1, h.2.2.1⟩
  have hF : Continuous F := by
    rw [Metric.continuous_iff]
    intro X ε hε
    obtain ⟨δ, hδ, h⟩ := hcont X.val X.property.1 X.val.isCompact X.property.2 X.val.nonempty ε hε
    refine ⟨δ, hδ, fun {Y} hY => ?_⟩
    rw [dist_comm]
    exact h Y.val Y.property.1 Y.val.isCompact Y.property.2 Y.val.nonempty
      ((dist_comm X Y).trans_lt hY)
  obtain ⟨X, -, hX⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty
    (continuous_id.dist hF).continuousOn
  have hfix : X = F X := by
    apply dist_eq_zero.mp
    apply le_antisymm _ dist_nonneg
    apply le_of_forall_pos_le_add
    intro r hr
    obtain ⟨Y, hY⟩ := exists_approx_fixedPoint hBconv F hF hr
    simpa only [zero_add, id_eq] using (hX (Set.mem_univ Y)).trans hY
  exact ⟨X.val, X.property.1, X.val.isCompact, X.property.2, X.val.nonempty,
    congrArg (fun Y : ConvexCompacts B => (Y.val : Set E)) hfix.symm⟩

end MathlibExt.Topology.ScottishBook42Wanted
