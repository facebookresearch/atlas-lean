/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Dynamics/FurstenbergTopological.lean` (leanprover/lean-eval),
problem `furstenberg_topological`, at commit 38361be884302c7edce1908c4aef8296eb2cb27e
(manifest `manifests/problems/furstenberg_topological.toml`, rev 1, submitter Kim Morrison):
the definition of a multiply recurrent point and the statement of the recurrence theorem,
with their docstrings from `WantedExt/Dynamics/FurstenbergTopologicalWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS moved the declarations to the
`MathlibExt.Dynamics.FurstenbergTopologicalWanted` namespace in a wanted module, replacing
the lean-eval marker with Batteries' `theorem_wanted`. ATLAS subsequently supplied the
proof and moved both declarations to this module with the same names, statements and docstrings.
-/
module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Order.Filter.AtTopBot.Finite
import Mathlib.Tactic.Ring
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Furstenberg–Weiss topological multiple recurrence

We define multiply recurrent points and prove that every homeomorphism of a nonempty
compact metric space has one. In a minimal closed invariant subsystem, finitely many
inverse images of an open set cover the space. A monochromatic arithmetic progression
of orbit times yields a simultaneous return to that open set. Baire category then gives
a point with arbitrarily accurate simultaneous returns at arbitrarily large times.
-/

@[expose] public section

namespace MathlibExt.Dynamics.FurstenbergTopologicalWanted
namespace Dynamics

open Filter Function Set Topology

set_option linter.dupNamespace false in
/-- **Multiply recurrent point.** Let $X$ be a topological space and $T \colon X \to X$ a map.
A point $x \in X$ is multiply recurrent for $T$ if for every integer $d \ge 1$ there is a
strictly increasing sequence of natural numbers $(n_k)$ such that $T^{j n_k}(x) \to x$ as
$k \to \infty$ for every integer $j$ with $1 \le j \le d$, where $T^{m}$ denotes the $m$-th
iterate of $T$. -/
def IsMultiplyRecurrent {X : Type*} [TopologicalSpace X]
    (T : X → X) (x : X) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ d →
        Tendsto (fun k : ℕ => T^[j * n k] x) atTop (𝓝 x)

private theorem exists_minimal_closed_invariant {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [Nonempty X] (f : X → X) :
    ∃ Y : Set X, Minimal (fun s => IsClosed s ∧ s.Nonempty ∧ MapsTo f s s) Y := by
  let S : Set (Set X) := {s | IsClosed s ∧ s.Nonempty ∧ MapsTo f s s}
  have lowerBound (c : Set (Set X)) (hc : c ⊆ S) (hchain : IsChain (· ⊆ ·) c)
      (hne : c.Nonempty) : ∃ t ∈ S, ∀ s ∈ c, t ⊆ s := by
    have : Nonempty c := hne.coe_sort
    have hclosed (s : Set X) (hs : s ∈ c) : IsClosed s := (hc hs).1
    have hdescending : IsChain (· ≥ ·) c := hchain.symm
    refine ⟨⋂₀ c, ⟨isClosed_sInter hclosed, ?_, ?_⟩, fun s hs => sInter_subset_of_mem hs⟩
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        hdescending.directedOn (fun _ hs => (hc hs).2.1)
        (fun s hs => (hclosed s hs).isCompact) hclosed
    · intro x hx
      exact mem_sInter.2 fun s hs => (hc hs).2.2 (mem_sInter.1 hx s hs)
  obtain ⟨Y, _, hY⟩ := zorn_superset_nonempty S lowerBound univ
    ⟨isClosed_univ, univ_nonempty, mapsTo_univ _ _⟩
  exact ⟨Y, hY⟩

private theorem denseRange_iterate_restrict {X : Type*} [TopologicalSpace X]
    {f : X → X} (hf : Continuous f) {Y : Set X}
    (hY : Minimal (fun s => IsClosed s ∧ s.Nonempty ∧ MapsTo f s s) Y) (y : Y) :
    DenseRange (fun n : ℕ => (hY.prop.2.2.restrict f Y Y)^[n] y) := by
  let orbit := range fun n : ℕ => f^[n] (y : X)
  have hsubset : orbit ⊆ Y := by
    rintro _ ⟨n, rfl⟩
    exact hY.prop.2.2.iterate n y.property
  have hmap : MapsTo f orbit orbit := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n + 1, iterate_succ_apply' f n y⟩
  have horbit : closure orbit = Y :=
    hY.eq_of_le ⟨isClosed_closure, (range_nonempty _).mono subset_closure, hmap.closure hf⟩
      (closure_minimal hsubset hY.prop.1)
  change Dense (range _)
  rw [IsEmbedding.subtypeVal.isInducing.dense_iff, ← range_comp']
  simp only [MapsTo.coe_iterate_restrict]
  change ∀ x : Y, (x : X) ∈ closure orbit
  rw [horbit]
  exact fun x => x.property

-- Colour the orbit of one point by a finite cover of inverse images of the target set.
private theorem exists_iterates_mem_open {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] {f : X → X} (hf : Continuous f)
    (hdense : ∀ x : X, DenseRange (fun n : ℕ => f^[n] x))
    {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) (d q : ℕ) :
    ∃ x : X, ∃ n ≥ q, ∀ j ≤ d, f^[j * n] x ∈ U := by
  classical
  have hcover : univ ⊆ ⋃ i : ℕ, (f^[i]) ⁻¹' U := by
    intro x _
    obtain ⟨i, hi⟩ := (hdense x).exists_mem_open hU hne
    exact mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover _ (fun i => hU.preimage (hf.iterate i))
    hcover
  let z : X := Classical.choice ‹Nonempty X›
  have hcolor (m : ℕ) : ∃ i : I, f^[i.val] (f^[q * m] z) ∈ U := by
    obtain ⟨i, hi, hm⟩ := mem_iUnion₂.1 (hI (mem_univ (f^[q * m] z)))
    exact ⟨⟨i, hi⟩, hm⟩
  choose color hcolor using hcolor
  obtain ⟨a, ha, b, c, hc⟩ := Combinatorics.exists_mono_homothetic_copy (Finset.range (d + 1)) color
  refine ⟨f^[q * b + c.val] z, q * a, Nat.le_mul_of_pos_right q ha, ?_⟩
  intro j hj
  have hcj := hc j (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
  rw [Nat.nsmul_eq_mul] at hcj
  have hstep := hcolor (a * j + b)
  rw [hcj, ← iterate_add_apply] at hstep
  rw [← iterate_add_apply,
    show j * (q * a) + (q * b + c.val) = c.val + q * (a * j + b) by ring]
  exact hstep

private theorem exists_multiplyRecurrent_of_denseRange {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] {f : X → X} (hf : Continuous f)
    (hdense : ∀ x : X, DenseRange (fun n : ℕ => f^[n] x)) :
    ∃ x : X, IsMultiplyRecurrent f x := by
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  let V (k : ℕ) : Set X := ⋃ n : {n : ℕ // k < n}, ⋂ j : Fin (k + 1),
    {x | dist (f^[j.val * n.val] x) x < ε k}
  have hVopen (k : ℕ) : IsOpen (V k) :=
    isOpen_iUnion fun n => isOpen_iInter_of_finite fun j =>
      isOpen_lt ((hf.iterate (j.val * n.val)).dist continuous_id) continuous_const
  have hVdense (k : ℕ) : Dense (V k) := by
    refine dense_iff_inter_open.2 fun U hU ⟨z, hz⟩ => ?_
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
    let δ := min r (ε k / 2)
    have hδ : 0 < δ := lt_min hr (by dsimp [ε]; positivity)
    obtain ⟨x, n, hn, hx⟩ := exists_iterates_mem_open hf hdense Metric.isOpen_ball
      ⟨z, Metric.mem_ball_self hδ⟩ k (k + 1)
    have hx₀ : x ∈ Metric.ball z δ := by simpa using hx 0 (Nat.zero_le _)
    refine ⟨x, hball (Metric.ball_subset_ball (min_le_left _ _) hx₀), ?_⟩
    refine mem_iUnion.2 ⟨⟨n, hn⟩, mem_iInter.2 fun j => ?_⟩
    have hj := Metric.mem_ball.1 (hx j.val (Nat.le_of_lt_succ j.isLt))
    have hxz := Metric.mem_ball.1 hx₀
    change dist (f^[j.val * n] x) x < ε k
    calc
      _ ≤ dist (f^[j.val * n] x) z + dist x z := dist_triangle_right _ _ _
      _ < ε k / 2 + ε k / 2 :=
        add_lt_add (hj.trans_le (min_le_right _ _)) (hxz.trans_le (min_le_right _ _))
      _ = ε k := add_halves _
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen_nat hVopen hVdense).nonempty
  have htimes (k : ℕ) : ∃ n > k, ∀ j : Fin (k + 1), dist (f^[j.val * n] x) x < ε k := by
    obtain ⟨n, hn⟩ := mem_iUnion.1 (mem_iInter.1 hx k)
    exact ⟨n, n.property, mem_iInter.1 hn⟩
  choose n hn hclose using htimes
  obtain ⟨φ, hφ, hnφ⟩ := strictMono_subseq_of_id_le fun k => (hn k).le
  refine ⟨x, fun _ _ => ⟨n ∘ φ, hnφ, fun j _ _ => ?_⟩⟩
  have hlim : Tendsto (fun k => f^[j * n k] x) atTop (𝓝 x) := by
    refine Metric.tendsto_nhds.2 fun r hr => ?_
    have hε : ∀ᶠ k in atTop, ε k < r :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hr)
    filter_upwards [eventually_ge_atTop j, hε] with k hj hk
    exact (hclose k ⟨j, Nat.lt_succ_of_le hj⟩).trans hk
  exact hlim.comp hφ.tendsto_atTop

set_option linter.dupNamespace false in
/-- **Furstenberg–Weiss multiple recurrence for a single homeomorphism.** Every homeomorphism
$T$ of a nonempty compact metric space $X$ has a multiply recurrent point: there is a point
$x \in X$ such that for every integer $d \ge 1$ there is a strictly increasing sequence of
natural numbers $(n_k)$ with $T^{j n_k}(x) \to x$ as $k \to \infty$ for every integer $j$ with
$1 \le j \le d$, where $T^{m}$ denotes the $m$-th iterate of $T$.

Source: H. Furstenberg and B. Weiss, *Topological dynamics and combinatorial number theory*, Journal
d'Analyse Mathématique 34 (1978), 61-85. Listed as §56 (main theorem) in O. Knill, *Some Fundamental
Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via
leanprover/lean-eval@38361be, problem `furstenberg_topological`. -/
theorem furstenberg_topological_recurrence {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] (T : X ≃ₜ X) :
    ∃ x : X, IsMultiplyRecurrent (T : X → X) x := by
  obtain ⟨Y, hY⟩ := exists_minimal_closed_invariant (T : X → X)
  have : CompactSpace Y := isCompact_iff_compactSpace.1 hY.prop.1.isCompact
  have : Nonempty Y := hY.prop.2.1.coe_sort
  let f : Y → Y := hY.prop.2.2.restrict T Y Y
  have hf : Continuous f := T.continuous.restrict hY.prop.2.2
  obtain ⟨x, hx⟩ := exists_multiplyRecurrent_of_denseRange hf
    (denseRange_iterate_restrict T.continuous hY)
  refine ⟨x.val, fun d hd => ?_⟩
  obtain ⟨n, hn, hlim⟩ := hx d hd
  refine ⟨n, hn, fun j hj hjd => ?_⟩
  simpa only [comp_def, f, MapsTo.coe_iterate_restrict] using
    (continuous_subtype_val.tendsto x).comp (hlim j hj hjd)

end Dynamics

end MathlibExt.Dynamics.FurstenbergTopologicalWanted
