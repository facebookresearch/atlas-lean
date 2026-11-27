/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Dynamics/HyperbolicShadowing.lean` (leanprover/lean-eval), revision 1 of
`manifests/problems/anosov_bowen_shadowing.toml` at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison (problem submitter).
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

The adapted portions are the definitions, the hyperbolic structure and the theorem statement.
ATLAS placed them in the namespace below and converted the benchmark statement to a wanted
declaration. This module preserves those declarations and supplies the proof.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Projection
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Tactic.GRewrite
import Mathlib.Tactic.LinearCombination

/-!
# Anosov–Bowen shadowing lemma

Every compact hyperbolic invariant set of a `C¹` diffeomorphism admits
an open neighbourhood on which every approximate orbit is `δ`-close to
a true `T`-orbit. Anosov 1967; Bowen 1975. §67 in Knill's *Some
Fundamental Theorems in Mathematics*.

The statement here is the Euclidean special case on
`E d := EuclideanSpace ℝ (Fin d)` — a faithful finite-dimensional local
model that captures the hyperbolic-dynamics content while avoiding the
smooth-manifold and tangent-bundle infrastructure mathlib does not yet
package. The hyperbolic-set predicate is bundled as a `HyperbolicStructure`:
a pointwise stable/unstable splitting with the uniform exponential
contraction/expansion estimates of Anosov's original definition. The
textbook definition additionally asks for the splitting to be continuous
in `x`; we encode only the pointwise content with uniform constants,
which is the minimal data the shadowing proof depends on.

The proof of `hyperbolic_has_shadowing` passes to a long iterate. Splitting each jump error
between its two endpoints halves the largest error at each refinement. Summing the corrections
gives a true orbit, and continuity controls the intermediate iterates.
-/

@[expose] public section

namespace MathlibExt.Dynamics.HyperbolicShadowingWanted
namespace Dynamics
namespace HyperbolicShadowingProblem

open scoped Topology

set_option linter.dupNamespace false in
/-- **Euclidean model space for the shadowing lemma.** For a natural number $d$, $E_d$ is the
Euclidean space $\mathbb{R}^d$, the real $d$-tuples with the Euclidean norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

set_option linter.dupNamespace false in
/-- **Hyperbolic structure.** Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a homeomorphism and let
$K \subseteq \mathbb{R}^d$. Write $DF_x$ for the derivative of a map $F$ at $x$, $T^n$ for the
$n$-fold iterate of $T$ and $T^{-n}$ for the $n$-fold iterate of $T^{-1}$. A hyperbolic structure
for $T$ on $K$ consists of the following: $T$ and $T^{-1}$ are $C^1$; $T(K) = K$; to every
$x \in \mathbb{R}^d$ are assigned linear subspaces $E^s(x)$ and $E^u(x)$ of $\mathbb{R}^d$ such that
for every $x \in K$ we have $\mathbb{R}^d = E^s(x) \oplus E^u(x)$, $DT_x(E^s(x)) = E^s(T(x))$ and
$DT_x(E^u(x)) = E^u(T(x))$; and there are real numbers $\lambda$ with $0 < \lambda < 1$ and
$C > 0$ such that for every $x \in K$ and every $n \in \mathbb{N}$,
$\|D(T^n)_x v\| \le C \lambda^n \|v\|$ for all $v \in E^s(x)$ and
$\|D(T^{-n})_x v\| \le C \lambda^n \|v\|$ for all $v \in E^u(x)$. -/
structure HyperbolicStructure (T : E d ≃ₜ E d) (K : Set (E d)) where
  contDiff_fwd : ContDiff ℝ 1 (T : E d → E d)
  contDiff_bwd : ContDiff ℝ 1 (T.symm : E d → E d)
  invariant : (T : E d → E d) '' K = K
  stable : E d → Submodule ℝ (E d)
  unstable : E d → Submodule ℝ (E d)
  isCompl_stable_unstable : ∀ x ∈ K, IsCompl (stable x) (unstable x)
  stable_invariant : ∀ x ∈ K,
    (stable x).map (fderiv ℝ (T : E d → E d) x : E d →ₗ[ℝ] E d) = stable (T x)
  unstable_invariant : ∀ x ∈ K,
    (unstable x).map (fderiv ℝ (T : E d → E d) x : E d →ₗ[ℝ] E d) = unstable (T x)
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  const : ℝ
  const_pos : 0 < const
  contract_stable : ∀ x ∈ K, ∀ v : E d, v ∈ stable x → ∀ n : ℕ,
    ‖fderiv ℝ ((T : E d → E d)^[n]) x v‖ ≤ const * rate ^ n * ‖v‖
  contract_unstable : ∀ x ∈ K, ∀ v : E d, v ∈ unstable x → ∀ n : ℕ,
    ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x v‖ ≤ const * rate ^ n * ‖v‖

set_option linter.dupNamespace false in
/-- **Hyperbolic invariant set.** Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a homeomorphism. A set
$K \subseteq \mathbb{R}^d$ is a hyperbolic invariant set for $T$ if there exists a hyperbolic
structure for $T$ on $K$. -/
def IsHyperbolic (T : E d ≃ₜ E d) (K : Set (E d)) : Prop :=
  Nonempty (HyperbolicStructure T K)

set_option linter.dupNamespace false in
/-- **Pseudo-orbit.** Let $d$ be a natural number, let $\mathbb{R}^d$ carry the Euclidean norm,
let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a map and let $\varepsilon$ be a real number. A
sequence $(x_n)_{n \in \mathbb{N}}$ in $\mathbb{R}^d$ is an $\varepsilon$-pseudo orbit of $T$
if $\|x_{n+1} - T(x_n)\| < \varepsilon$ for every $n \in \mathbb{N}$. -/
def IsPseudoOrbit (T : E d → E d) (ε : ℝ) (x : ℕ → E d) : Prop :=
  ∀ n : ℕ, ‖x (n + 1) - T (x n)‖ < ε

set_option linter.dupNamespace false in
/-- **Shadowing property.** Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a map, write $T^n$ for its
$n$-fold iterate, and let $K \subseteq \mathbb{R}^d$. The set $K$ has the shadowing property for
$T$ if there is an open set $U \subseteq \mathbb{R}^d$ containing $K$ such that for every
$\delta > 0$ there is $\varepsilon > 0$ with the following property: for every $\varepsilon$-pseudo
orbit $(x_n)_{n \in \mathbb{N}}$ of $T$ with $x_n \in U$ for all $n$, there is a point
$y \in \mathbb{R}^d$ with $\|x_n - T^n(y)\| < \delta$ for all $n \in \mathbb{N}$. -/
def HasShadowing (T : E d → E d) (K : Set (E d)) : Prop :=
  ∃ U : Set (E d), IsOpen U ∧ K ⊆ U ∧
    ∀ δ > 0, ∃ ε > 0, ∀ x : ℕ → E d,
      (∀ n, x n ∈ U) → IsPseudoOrbit T ε x →
      ∃ y : E d, ∀ n : ℕ, ‖x n - T^[n] y‖ < δ

open Function Set Metric Filter

variable {T : E d ≃ₜ E d} {K : Set (E d)}

private lemma contDiff_iterate {f : E d → E d} (hf : ContDiff ℝ 1 f) (n : ℕ) :
    ContDiff ℝ 1 f^[n] := by
  induction n with
  | zero => exact contDiff_id
  | succ n ih => exact ih.comp hf

private theorem unstable_iterate_mem (H : HyperbolicStructure T K)
    {x : E d} (hx : x ∈ K) {u : E d} (hu : u ∈ H.unstable x) (n : ℕ) :
    fderiv ℝ ((T : E d → E d)^[n]) x u ∈ H.unstable ((T : E d → E d)^[n] x) := by
  have hT : Differentiable ℝ (T : E d → E d) := H.contDiff_fwd.differentiable one_ne_zero
  have hTK : MapsTo (T : E d → E d) K K := mapsTo_iff_image_subset.mpr H.invariant.le
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    rw [Function.iterate_succ', fderiv_comp x (hT _) (hT.iterate n x)]
    rw [Function.comp_apply, ← H.unstable_invariant _ (hTK.iterate n hx)]
    exact ⟨_, ih, rfl⟩

private lemma derivative_leftInverse {F G : E d → E d} (hF : Differentiable ℝ F)
    (hG : Differentiable ℝ G) (hGF : LeftInverse G F) (x u : E d) :
    fderiv ℝ G (F x) (fderiv ℝ F x u) = u := by
  have h := fderiv_comp x (hG (F x)) (hF x)
  rw [hGF.comp_eq_id, fderiv_id] at h
  exact congrArg (fun (A : E d →L[ℝ] E d) => A u) h.symm

-- A long forward iterate contracts stable vectors and at least doubles unstable vectors.
-- Its operator norm is bounded on K, so cancellation in s + u cannot be arbitrarily strong.
private theorem bounded_components (H : HyperbolicStructure T K) (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, ∀ s ∈ H.stable x, ∀ u ∈ H.unstable x,
      ‖s‖ ≤ B * ‖s + u‖ ∧ ‖u‖ ≤ B * ‖s + u‖ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (show 0 < (1 / 2 : ℝ) / H.const by exact div_pos (by norm_num) H.const_pos) H.rate_lt_one
  have ha : H.const * H.rate ^ n ≤ 1 / 2 := by
    rw [mul_comm]
    exact ((lt_div_iff₀ H.const_pos).mp hn).le
  have hT := contDiff_iterate H.contDiff_fwd n
  obtain ⟨M, hM⟩ := hK.bddAbove_image (hT.continuous_fderiv one_ne_zero).norm.continuousOn
  refine ⟨max M 0 + 3, by positivity, ?_⟩
  intro x hx s hs u hu
  let A := fderiv ℝ ((T : E d → E d)^[n]) x
  have hsA : ‖A s‖ ≤ (1 / 2) * ‖s‖ :=
    (H.contract_stable x hx s hs n).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hTK : MapsTo (T : E d → E d) K K := mapsTo_iff_image_subset.mpr H.invariant.le
  have huA := H.contract_unstable _ (hTK.iterate n hx) _ (unstable_iterate_mem H hx hu n) n
  have hleft : LeftInverse (T.symm : E d → E d) T := T.symm_apply_apply
  rw [derivative_leftInverse (hT.differentiable one_ne_zero)
    ((H.contDiff_bwd.differentiable one_ne_zero).iterate n) (hleft.iterate n)] at huA
  have huA' : ‖u‖ ≤ (1 / 2) * ‖A u‖ :=
    huA.trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  have hAu : ‖A u‖ ≤ ‖A (s + u)‖ + ‖A s‖ := by
    simpa using norm_sub_le (A (s + u)) (A s)
  have hsv : ‖s‖ ≤ ‖s + u‖ + ‖u‖ := by simpa using norm_sub_le (s + u) u
  have hAv : ‖A (s + u)‖ ≤ max M 0 * ‖s + u‖ :=
    (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right
      ((hM (mem_image_of_mem _ hx)).trans (le_max_left _ _)) (norm_nonneg _))
  have hprod := mul_nonneg (le_max_right M 0) (norm_nonneg (s + u))
  constructor <;> linarith [norm_nonneg (s + u)]

private lemma uniform_near_compact {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {L : Set X} (hc : IsCompact L) {f : X → Y} (hf : Continuous f) {a : ℝ} (ha : 0 < a) :
    ∃ r > 0, ∀ p ∈ L, ∀ x, dist p x < r → dist (f p) (f x) < a := by
  have h := hc.uniformContinuousAt_of_continuousAt f (fun _ _ => hf.continuousAt)
    (dist_mem_uniformity ha)
  obtain ⟨r, hr, h⟩ := Metric.mem_uniformity_dist.mp h
  exact ⟨r, hr, fun p hp x hx => h hx hp⟩

private lemma uniform_iterates {T : E d → E d} (hT : Continuous T) {L : Set (E d)}
    (hc : IsCompact L) (N : ℕ) {a : ℝ} (ha : 0 < a) : ∃ r > 0,
    ∀ j ≤ N, ∀ p ∈ L, ∀ x, dist p x < r → dist (T^[j] p) (T^[j] x) < a := by
  induction N with
  | zero => exact ⟨a, ha, by simp⟩
  | succ N ih =>
    obtain ⟨r, hr, h⟩ := ih
    obtain ⟨t, ht, h'⟩ := uniform_near_compact hc (hT.iterate (N + 1)) ha
    refine ⟨min r t, lt_min hr ht, fun j hj p hp x hx => ?_⟩
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact h j (Nat.le_of_lt_succ hj) p hp x (lt_min_iff.mp hx).1
    · exact h' p hp x (lt_min_iff.mp hx).2

private lemma finite_pseudo_orbit {T : E d → E d} (hT : Continuous T) {L : Set (E d)}
    (hc : IsCompact L) (N : ℕ) {a : ℝ} (ha : 0 < a) : ∃ e > 0,
    ∀ x : ℕ → E d, (∀ n, x n ∈ L) → IsPseudoOrbit T e x →
    ∀ n, ∀ j ≤ N, dist (T^[j] (x n)) (x (n + j)) < a := by
  induction N generalizing a with
  | zero => exact ⟨1, one_pos, fun _ _ _ _ j hj => by simpa [Nat.eq_zero_of_le_zero hj] using ha⟩
  | succ N ih =>
    obtain ⟨e, he, h⟩ := ih (half_pos ha)
    obtain ⟨t, ht, ht'⟩ := uniform_near_compact (hc.image hT) (hT.iterate N) (half_pos ha)
    refine ⟨min e t, lt_min he ht, fun x hx hpo n j hj => ?_⟩
    have hp : IsPseudoOrbit T e x := fun n => (hpo n).trans_le (min_le_left _ _)
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact (h x hx hp n j (Nat.le_of_lt_succ hj)).trans (half_lt_self ha)
    · have hfirst : dist (T (x n)) (x (n + 1)) < t := by
        rw [dist_comm, dist_eq_norm]
        exact (hpo n).trans_le (min_le_right _ _)
      have hA := ht' (T (x n)) (mem_image_of_mem T (hx n)) _ hfirst
      have hB := h x hx hp (n + 1) N le_rfl
      rw [iterate_succ_apply, show n + (N + 1) = (n + 1) + N by omega]
      exact (dist_triangle _ _ _).trans_lt ((add_lt_add hA hB).trans_eq (add_halves a))

-- Sample at multiples of N and use finite-time error bounds at the intermediate times.
private lemma shadow_of_iterate {T : E d → E d} (hT : Continuous T) (hK : IsCompact K)
    (N : ℕ) (hN : 0 < N) (hF : HasShadowing T^[N] K) : HasShadowing T K := by
  obtain ⟨U, hU, hKU, h⟩ := hF
  obtain ⟨r, hr, hc⟩ := hK.exists_isCompact_cthickening
  refine ⟨U ∩ thickening r K, hU.inter isOpen_thickening,
    subset_inter hKU (self_subset_thickening hr _), fun δ hδ => ?_⟩
  obtain ⟨t, ht, ht'⟩ := uniform_iterates hT hc N (half_pos hδ)
  obtain ⟨e, he, hshadow⟩ := h t ht
  obtain ⟨ε, hε, herr⟩ := finite_pseudo_orbit hT hc N (lt_min (half_pos hδ) he)
  refine ⟨ε, hε, fun x hx hpo => ?_⟩
  have hL (n : ℕ) := thickening_subset_cthickening r K (hx n).2
  have hx' := herr x hL hpo
  let z (n : ℕ) := x (N * n)
  obtain ⟨y, hy⟩ := hshadow z (fun n => (hx _).1) (fun n => by
    have h' := (hx' (N * n) N le_rfl).trans_le (min_le_right _ _)
    simpa only [z, Nat.mul_succ, ← dist_eq_norm, dist_comm] using h')
  refine ⟨y, fun n => ?_⟩
  let j := n % N
  let k := n / N
  have hj : j ≤ N := (Nat.mod_lt _ hN).le
  have hn : j + N * k = n := Nat.mod_add_div n N
  have h1 : dist (x n) (T^[j] (x (N * k))) < δ / 2 := by
    rw [dist_comm, ← hn]
    simpa only [Nat.add_comm j (N * k)] using (hx' (N * k) j hj).trans_le (min_le_left _ _)
  have h2 := ht' j hj (z k) (hL _) ((T^[N])^[k] y) (by simpa only [dist_eq_norm] using hy k)
  have h3 := (dist_triangle _ _ _).trans_lt ((add_lt_add h1 h2).trans_eq (add_halves δ))
  rwa [← iterate_mul, ← iterate_add_apply, hn, dist_eq_norm] at h3

-- Geometrically decreasing corrections converge at each time to a point of a single orbit.
private lemma shadow_of_refinement {F : E d → E d} (hF : Continuous F) (z : ℕ → E d)
    {C e r : ℝ} (hC : 0 < C) (he : 0 < e) (her : 2 * (C * e) ≤ r)
    (hz : ∀ n, dist (F (z n)) (z (n + 1)) ≤ e)
    (step : ∀ w : ℕ → E d, ∀ b : ℝ, 0 ≤ b → b ≤ e →
      (∀ n, dist (z n) (w n) ≤ r) → (∀ n, dist (F (w n)) (w (n + 1)) ≤ b) →
      ∃ v : ℕ → E d, (∀ n, dist (w n) (v n) ≤ C * b) ∧
        ∀ n, dist (F (v n)) (v (n + 1)) ≤ b / 2) :
    ∃ y, ∀ n, dist (z n) (F^[n] y) ≤ 2 * (C * e) := by
  let a : ℝ := 1 / 2
  have ha : 0 < a := by norm_num [a]
  have ha' : a < 1 := by norm_num [a]
  -- At stage k the accumulated displacement is bounded by a partial geometric sum.
  let P (k : ℕ) (w : ℕ → E d) := (∀ n, dist (z n) (w n) ≤ 2 * (C * e) * (1 - a ^ k)) ∧
    ∀ n, dist (F (w n)) (w (n + 1)) ≤ e * a ^ k
  have next (k : ℕ) (w : Subtype (P k)) : ∃ v : Subtype (P (k + 1)),
      ∀ n, dist (w.val n) (v.val n) ≤ (C * e) * a ^ k := by
    obtain ⟨w', hw, hw'⟩ := step w.val (e * a ^ k) (by positivity)
      (mul_le_of_le_one_right he.le (pow_le_one₀ ha.le ha'.le)) (fun n =>
        (w.property.1 n).trans ((mul_le_of_le_one_right (by positivity)
          (sub_le_self _ (pow_nonneg ha.le k))).trans her)) w.property.2
    refine ⟨⟨w', ?_, ?_⟩, fun n => by simpa only [mul_assoc] using hw n⟩
    · intro n
      exact (dist_triangle _ (w.val n) _).trans (by
        have h := w.property.1 n
        rw [pow_succ]
        dsimp only [a] at *
        linarith [hw n])
    · intro n
      rw [pow_succ]
      simpa [a, mul_assoc, div_eq_mul_inv] using hw' n
  let w (k : ℕ) : Subtype (P k) := Nat.rec ⟨z, by simpa [P] using hz⟩
    (fun k w => (next k w).choose) k
  let f (n k : ℕ) := (w k).val n
  have hdist (n k : ℕ) : dist (f n k) (f n (k + 1)) ≤ (C * e) * a ^ k :=
    (next k (w k)).choose_spec n
  choose y hy using fun n =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric a (C * e) ha' (hdist n))
  have hzero : Tendsto (fun k : ℕ => e * a ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha').const_mul e
  have hrec (n : ℕ) : F (y n) = y (n + 1) := by
    apply dist_le_zero.mp
    exact le_of_tendsto_of_tendsto' ((hF.continuousAt.tendsto.comp (hy n)).dist (hy (n + 1)))
      hzero (fun k => (w k).property.2 n)
  have horbit (n : ℕ) : F^[n] (y 0) = y n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [iterate_succ_apply', ih, hrec]
  refine ⟨y 0, fun n => ?_⟩
  rw [horbit]
  have h := dist_le_of_le_geometric_of_tendsto₀ a (C * e) ha' (hdist n) (hy n)
  change dist (z n) (y n) ≤ _ at h
  convert h using 1
  dsimp [a]
  ring

private lemma improve_orbit {F G : E d → E d} {B R η b : ℝ} (hB : 0 < B)
    (hb : 0 ≤ b) (hinc : (B + 1) * b ≤ R / 4) (hη : 0 < η) (hηB : η * (B + 1) ≤ 1 / 4)
    (z p w : ℕ → E d) (hp : ∀ n, p n ∈ K) (hG : MapsTo G K K)
    (hzp : ∀ n, dist (z n) (p n) < R / 4)
    (hzq : ∀ n, dist (z n) (G (p (n + 1))) < R / 4)
    (hwz : ∀ n, dist (z n) (w n) ≤ R / 4) (hw : ∀ n, dist (F (w n)) (w (n + 1)) ≤ b)
    (hsplit : ∀ x ∈ K, ∀ v : E d, ∃ s u : E d, s + u = v ∧ ‖s‖ ≤ B * ‖v‖ ∧
      ‖fderiv ℝ F x s‖ ≤ 1 / 8 * ‖v‖ ∧ ‖fderiv ℝ G x u‖ ≤ 1 / 8 * ‖v‖)
    (hFG : ∀ p u, fderiv ℝ F (G p) (fderiv ℝ G p u) = u)
    (hlin : ∀ p ∈ K, ∀ x ∈ ball p R, ∀ y ∈ ball p R,
      ‖F y - F x - fderiv ℝ F p (y - x)‖ ≤ η * ‖y - x‖) :
    ∃ v : ℕ → E d, (∀ n, dist (w n) (v n) ≤ (B + 1) * b) ∧
      ∀ n, dist (F (v n)) (v (n + 1)) ≤ b / 2 := by
  -- Split the incoming error at each nearby point of K. Add its stable component at arrival
  -- and pull its unstable component back to correct the departure point.
  let error (n : ℕ) := F (w n) - w (n + 1)
  have he (n : ℕ) : ‖error n‖ ≤ b := hw n
  -- At time zero there is no incoming constraint, so the same bounded split can be used there.
  choose s u hsum hs hs' hu using fun n => hsplit (p n) (hp n) (error (n - 1))
  let t (n : ℕ) := fderiv ℝ G (p (n + 1)) (u (n + 1))
  have hsu (n : ℕ) : s (n + 1) + u (n + 1) = error n := by simpa using hsum (n + 1)
  have hsB (n : ℕ) : ‖s n‖ ≤ B * b := (hs n).trans (by gcongr; exact he _)
  have hsmall (n : ℕ) : ‖fderiv ℝ F (p n) (s n)‖ ≤ b / 8 := by
    calc
      _ ≤ 1 / 8 * ‖error (n - 1)‖ := hs' n
      _ ≤ 1 / 8 * b := by gcongr; exact he _
      _ = _ := by ring
  have ht (n : ℕ) : ‖t n‖ ≤ b / 8 := by
    calc
      _ ≤ 1 / 8 * ‖error ((n + 1) - 1)‖ := hu _
      _ ≤ 1 / 8 * b := by gcongr; exact he _
      _ = _ := by ring
  let v (n : ℕ) := w n + (s n - t n)
  have hst (n : ℕ) : ‖s n - t n‖ ≤ (B + 1) * b :=
    (norm_sub_le ..).trans (by linarith [hsB n, ht n])
  refine ⟨v, fun n => by rw [dist_comm]; simpa [v, dist_eq_norm] using hst n, fun n => ?_⟩
  have hball {q : E d} (hq : dist (z n) q < R / 4) (a : E d) (ha : ‖a‖ ≤ (B + 1) * b) :
      w n + a ∈ ball q R := by
    apply mem_ball.mpr
    have h1 := dist_triangle (w n + a) (w n) q
    have h2 := dist_triangle (w n) (z n) q
    rw [dist_comm (w n) (z n)] at h2
    rw [dist_eq_norm (w n + a) (w n), add_sub_cancel_left] at h1
    linarith [hwz n, dist_nonneg (x := z n) (y := q)]
  have hsinc : ‖s n‖ ≤ (B + 1) * b := by linarith [hsB n]
  have hwball : w n ∈ ball (p n) R := by
    simpa using hball (hzp n) 0 (by simpa using mul_nonneg (by linarith : 0 ≤ B + 1) hb)
  -- Linearize the stable displacement at p n and the unstable one at G (p (n + 1)).
  have h1 := hlin (p n) (hp n) _ hwball _ (hball (hzp n) (s n) hsinc)
  simp only [add_sub_cancel_left] at h1
  have h2 := hlin (G (p (n + 1))) (hG (hp _))
    _ (hball (hzq n) (s n) hsinc) _ (hball (hzq n) _ (hst n))
  have hd : w n + (s n - t n) - (w n + s n) = -t n := by abel
  rw [hd, map_neg, sub_neg_eq_add, norm_neg] at h2
  change ‖F (v n) - F (w n + s n) + fderiv ℝ F _ (fderiv ℝ G _ _)‖ ≤ _ at h2
  rw [hFG] at h2
  let a := F (w n + s n) - F (w n) - fderiv ℝ F (p n) (s n)
  let c := F (v n) - F (w n + s n) + u (n + 1)
  have hid : F (v n) - v (n + 1) = c + a + fderiv ℝ F (p n) (s n) + t (n + 1) := by
    dsimp only [v, a, c]
    have heq := hsu n
    dsimp only [error] at heq
    linear_combination (norm := abel) -heq
  rw [dist_eq_norm, hid]
  have htotal : η * ‖s n‖ + η * ‖t n‖ ≤ b / 4 := by
    calc
      _ = η * (‖s n‖ + ‖t n‖) := by ring
      _ ≤ η * ((B + 1) * b) := mul_le_mul_of_nonneg_left (by linarith [hsB n, ht n]) hη.le
      _ = (η * (B + 1)) * b := by ring
      _ ≤ (1 / 4) * b := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖c‖ + ‖a‖ + ‖fderiv ℝ F (p n) (s n)‖ + ‖t (n + 1)‖ := by
      grw [norm_add_le, norm_add_le, norm_add_le]
    _ ≤ _ := by linarith [show ‖a‖ ≤ _ from h1, show ‖c‖ ≤ _ from h2, hsmall n, ht (n + 1)]

set_option linter.dupNamespace false in
/-- **Anosov–Bowen shadowing lemma.** Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a homeomorphism and
let $K \subseteq \mathbb{R}^d$ be a compact set that is a hyperbolic invariant set for $T$. Then $K$
has the shadowing property for $T$.

Source: D.V. Anosov, 'Geodesic flows on closed Riemannian manifolds with negative curvature', Trudy
Mat. Inst. Steklov. 90 (1967); R. Bowen, 'ω-limit sets for Axiom A diffeomorphisms', J. Differential
Equations 18 (1975) 333–339. Listed as §67 in O. Knill, *Some Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `anosov_bowen_shadowing`. -/
public theorem hyperbolic_has_shadowing
    (T : E d ≃ₜ E d) (K : Set (E d))
    (_hKc : IsCompact K) (_hK : IsHyperbolic T K) :
    HasShadowing (T : E d → E d) K := by
  obtain ⟨H⟩ := _hK
  -- Pass to an iterate for which even the projected errors contract by a factor of eight.
  obtain ⟨B, hB, hcomp⟩ := bounded_components H _hKc
  have hconst := H.const_pos
  have hrate := H.rate_pos
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
    (show 0 < (1 / 8 : ℝ) / (H.const * B) by positivity) H.rate_lt_one
  let N := m + 1
  have hN : H.const * H.rate ^ N * B ≤ 1 / 8 := calc
    _ = H.rate * (H.rate ^ m * (H.const * B)) := by dsimp [N]; ring
    _ ≤ H.rate ^ m * (H.const * B) := mul_le_of_le_one_left (by positivity) H.rate_lt_one.le
    _ ≤ _ := ((lt_div_iff₀ (mul_pos hconst hB)).mp hm).le
  let F := (T : E d → E d)^[N]
  let G := (T.symm : E d → E d)^[N]
  have hF : ContDiff ℝ 1 F := contDiff_iterate H.contDiff_fwd N
  have hG := T.symm.continuous.iterate N
  have hback : MapsTo G K K := by
    apply MapsTo.iterate (f := (T.symm : E d → E d)) _ N
    intro x hx
    obtain ⟨y, hy, rfl⟩ := H.invariant.ge hx
    simpa using hy
  have hleft : LeftInverse F G :=
    (show LeftInverse (T : E d → E d) T.symm from T.apply_symm_apply).iterate N
  have hFG := derivative_leftInverse ((H.contDiff_bwd.differentiable one_ne_zero).iterate N)
    (hF.differentiable one_ne_zero) hleft
  have hsplit (p : E d) (hp : p ∈ K) (v : E d) : ∃ s u : E d, s + u = v ∧
      ‖s‖ ≤ B * ‖v‖ ∧ ‖fderiv ℝ F p s‖ ≤ 1 / 8 * ‖v‖ ∧ ‖fderiv ℝ G p u‖ ≤ 1 / 8 * ‖v‖ := by
    have hc := H.isCompl_stable_unstable p hp
    let s := (H.stable p).projection _ hc v
    let u := (H.unstable p).projection _ hc.symm v
    have hs : s ∈ H.stable p := Submodule.projection_apply_mem ..
    have hu : u ∈ H.unstable p := Submodule.projection_apply_mem ..
    have hsu : s + u = v := Submodule.projection_add_projection_eq_self hc v
    obtain ⟨h₁, h₂⟩ := hcomp p hp s hs u hu
    rw [hsu] at h₁ h₂
    have bound {r : ℝ} (hr : r ≤ B * ‖v‖) : H.const * H.rate ^ N * r ≤ 1 / 8 * ‖v‖ := calc
      _ ≤ H.const * H.rate ^ N * (B * ‖v‖) := by gcongr
      _ = (H.const * H.rate ^ N * B) * ‖v‖ := by ring
      _ ≤ _ := by gcongr
    exact ⟨s, u, hsu, h₁, (H.contract_stable p hp s hs N).trans (bound h₁),
      (H.contract_unstable p hp u hu N).trans (bound h₂)⟩
  let η : ℝ := (1 / 4) / (B + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hηB : η * (B + 1) ≤ 1 / 4 := by
    rw [div_mul_cancel₀ _ (by positivity : B + 1 ≠ 0)]
  obtain ⟨R, hR, hderiv⟩ := uniform_near_compact _hKc (hF.continuous_fderiv one_ne_zero) hη
  have hlin (p : E d) (hp : p ∈ K) (x : E d) (hx : x ∈ ball p R) (y : E d)
      (hy : y ∈ ball p R) : ‖F y - F x - fderiv ℝ F p (y - x)‖ ≤ η * ‖y - x‖ := by
    apply (convex_ball p R).norm_image_sub_le_of_norm_fderiv_le'
      (fun z _ => hF.differentiable one_ne_zero z) _ hx hy
    intro z hz
    rw [← dist_eq_norm, dist_comm]
    exact (hderiv p hp z (by simpa [dist_comm] using mem_ball.mp hz)).le
  obtain ⟨t, ht, htG⟩ := uniform_near_compact _hKc hG (show 0 < R / 4 by positivity)
  let r := min (R / 4) (t / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  apply shadow_of_iterate T.continuous _hKc N (Nat.succ_pos _)
  refine ⟨thickening r K, isOpen_thickening, self_subset_thickening hr _, fun δ hδ => ?_⟩
  let e := min (t / 2) (min (R / (8 * (B + 1))) (δ / (4 * (B + 1))))
  have he : 0 < e := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have heR : 2 * ((B + 1) * e) ≤ R / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * (B + 1))).mp
      ((min_le_right _ _).trans (min_le_left _ _) : e ≤ _)
    linarith
  have heδ : 2 * ((B + 1) * e) < δ := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (B + 1))).mp
      ((min_le_right _ _).trans (min_le_right _ _) : e ≤ _)
    linarith
  refine ⟨e, he, fun z hz hpo => ?_⟩
  choose p hp hzp using fun n => mem_thickening_iff.mp (hz n)
  have hzF (n : ℕ) : dist (F (z n)) (z (n + 1)) < e := by
    rw [dist_comm, dist_eq_norm]
    exact hpo n
  have hzq (n : ℕ) : dist (z n) (G (p (n + 1))) < R / 4 := by
    rw [dist_comm]
    -- Compare the inverse images at the next pseudo-orbit point.
    have hg : G (F (z n)) = z n :=
      (show LeftInverse (T.symm : E d → E d) T from T.symm_apply_apply).iterate N _
    rw [← hg]
    apply htG _ (hp _)
    calc
      _ ≤ dist (p (n + 1)) (z (n + 1)) + dist (z (n + 1)) (F (z n)) := dist_triangle ..
      _ < t := by
        rw [dist_comm (p (n + 1)), dist_comm (z (n + 1)) (F (z n))]
        have hr' := (hzp (n + 1)).trans_le (min_le_right _ _)
        have he' : e ≤ t / 2 := min_le_left _ _
        linarith [hzF n]
  obtain ⟨y, hy⟩ := shadow_of_refinement hF.continuous z (by positivity : 0 < B + 1) he heR
    (fun n => (hzF n).le) (fun w b hb hbe hwz hw =>
      improve_orbit hB hb (by
        calc
          (B + 1) * b ≤ (B + 1) * e := by gcongr
          _ ≤ R / 4 := by linarith [mul_nonneg (by positivity : 0 ≤ B + 1) he.le])
        hη hηB z p w hp hback (fun n => (hzp n).trans_le (min_le_left _ _)) hzq
        hwz hw hsplit hFG hlin)
  exact ⟨y, fun n => (hy n).trans_lt heδ⟩

end HyperbolicShadowingProblem
end Dynamics

end MathlibExt.Dynamics.HyperbolicShadowingWanted
