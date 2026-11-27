/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Dynamics/PoincareBendixson.lean` (leanprover/lean-eval,
https://github.com/leanprover/lean-eval), problem `poincare_bendixson`, at commit
38361be884302c7edce1908c4aef8296eb2cb27e (manifest `manifests/problems/poincare_bendixson.toml`,
rev 1, submitter Kim Morrison, status archived): the definition `Plane` and the statement of
`poincare_bendixson`, with the docstrings and comments they had in the former wanted module
`WantedExt/Dynamics/PoincareBendixsonWanted.lean`.
Copyright 2026 Lean FRO, LLC.
Authors: Kim Morrison
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: converted each
`@[eval_problem]` theorem into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with `Batteries.Util.ProofWanted`, inlined any
`LeanEval` helper modules, and placed the declarations in the
`MathlibExt.Dynamics.PoincareBendixsonWanted` namespace. Mathematical statements are unchanged.
Later change (ATLAS, 2026): the `theorem_wanted` was proved and the declarations moved from
`WantedExt/Dynamics/PoincareBendixsonWanted.lean` to this `MathlibExt` module with unchanged names,
statements and docstrings, and the imports of `Batteries.Util.ProofWanted` and of all of Mathlib
were replaced by narrower Mathlib and ATLAS imports.

The rest of this file is new ATLAS work, not adapted from lean-eval: the proof of
`poincare_bendixson`, the private lemmas it uses, the module documentation and the linter options.
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import MathlibExt.Analysis.Complex.WindingNumber
import MathlibExt.Analysis.ODE.MaximalSolution

/-!
# The Poincaré–Bendixson theorem

`poincare_bendixson`: for a `C¹` vector field `F` on the Euclidean plane and a curve `γ` that is an
integral curve of `F` on `[0, ∞)`, either the forward orbit is unbounded, or the ω-limit set
`⋂ s, closure (γ '' [s, ∞))` contains an equilibrium of `F`, or it is the range of a non-constant
periodic integral curve of `F`.

§63 of Knill's *Some Fundamental Theorems in Mathematics*. For a `C¹`
autonomous vector field `F : ℝ² → ℝ²` and a forward integral curve `γ`
on `[0, ∞)`, one of three alternatives holds: the forward orbit is
unbounded; the ω-limit set `⋂ s, closure (γ '' [s, ∞))` contains an
equilibrium of `F`; or the ω-limit set equals the range of a
non-constant periodic integral curve of `F`.

The bounded branch uses "ω-limit contains an equilibrium" rather than
"γ converges to an equilibrium": planar orbits in a bounded forward-
invariant region may accumulate on continua of equilibria or polycycles
without converging to any single point. The non-degeneracy `F (β 0) ≠ 0`
excludes a constant equilibrium curve from vacuously satisfying the
periodic branch. The periodic-branch conclusion is range-of-periodic-
orbit; "limit cycle" in the strict sense (isolated, attracting nearby
trajectories) is not asserted.

## Proof outline

The plane is identified with `ℂ` through the linear isometry `Complex.orthonormalBasisOneI.repr`.
Suppose that the forward orbit lies in the closed disc of radius `R` and that the ω-limit set `ω`
contains no zero of `F`.

* **A global flow.** `F` is Lipschitz on the closed disc of radius `R + 1`, being `C¹` on a compact
  convex set. Extending its real and imaginary parts (McShane) gives a globally Lipschitz field `G`
  equal to `F` on that disc, whose solutions exist on all of `ℝ` and are unique
  (`ode_global_exists_of_global_lipschitz`). The curve `γ` follows the flow of `G` on `[0, ∞)`;
  `ω` is compact, nonempty, connected and invariant under the flow (Grönwall's inequality in both
  time directions), and `G = F` on `ω`.
* **Transversals.** At a point `p` with `F p ≠ 0`, the segment through `p` orthogonal to `F p` is
  crossed by every trajectory in the direction of `F p`: `t ↦ ⟪x t - p, F p⟫` increases while the
  trajectory `x` stays near `p`. Hence crossings are separated in time, and a trajectory passing
  near a point of the open segment crosses the segment nearby, by the intermediate value theorem.
  This replaces the flow-box theorem.
* **Monotone crossings.** If a trajectory crosses a transversal at times `t₀ < t₁`, with no crossing
  in between, at positions `s₀ < s₁`, then every later crossing lies beyond `s₁`. In place of the
  Jordan curve theorem the argument uses the winding number `Complex.windingNumber` of the closed
  piecewise `C¹` curve made of the trajectory from `t₀` to `t₁` and the segment back to the first
  crossing point. It is locally constant off the curve, and an explicit computation of the
  integral over the segment (an arctangent) shows that it takes different values on the two sides
  of the segment. After `t₁` the trajectory starts on the side into which the flow points; it can
  meet neither the trajectory arc (uniqueness of solutions) nor the segment (it would have to come
  from the other side), so its winding number never changes. That value differs from the one on
  the part of the transversal before `s₀`.
* **Conclusion.** Monotonicity forces `ω` to meet the open transversal in at most one point. For
  `y ∈ ω`, the orbit of `y` stays in `ω` and accumulates at some `z ∈ ω`, so it crosses a
  transversal at `z` twice, at points of `ω`; these coincide, and the orbit of `y` is periodic. If
  `ω` were larger than this orbit, connectedness of `ω` would give points of `ω` off the orbit
  arbitrarily close to it; their orbits would cross a transversal at a point of the orbit at the
  same point of `ω`, putting them on the orbit.

## Implementation notes

The definition and the statement keep the full names they had in the former wanted module, so the
namespace still reads `PoincareBendixsonWanted` and repeats `Dynamics`; the `dupNamespace` linter
is turned off for these two declarations only.

## References

* H. Poincaré, *Mémoire sur les courbes définies par une équation différentielle*, Journal de
  Mathématiques 7 (1881), 8 (1882), 1 (1885), 2 (1886).
* I. Bendixson, *Sur les courbes définies par des équations différentielles*, Acta Mathematica 24
  (1901), 1-88.
* O. Knill, *Some Fundamental Theorems in Mathematics*, §63
  (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
* F. Immler and Y. K. Tan, *The Poincaré–Bendixson theorem*, Archive of Formal Proofs
  (https://www.isa-afp.org/entries/Poincare_Bendixson.html), a formalization in Isabelle/HOL that
  uses John Harrison's Jordan curve theorem.
* Problem `poincare_bendixson` of the lean-eval benchmark (leanprover/lean-eval), from which the
  definition and the statement are taken.
-/

set_option autoImplicit false

namespace MathlibExt.Dynamics.PoincareBendixsonWanted
namespace Dynamics

open Filter Topology Set

set_option linter.dupNamespace false in
/-- **The Euclidean plane.** The ambient space is the plane $\mathbb{R}^2$ with its Euclidean
inner product and norm. -/
public abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ### The flow of a globally Lipschitz field -/

section

open Set Filter Topology Metric
open scoped NNReal

variable {G : ℂ → ℂ} {K : ℝ≥0}

private theorem existsUnique_sol (hG : LipschitzWith K G) (x₀ : ℂ) :
    ∃! φ : ℝ → ℂ, φ 0 = x₀ ∧ ∀ t, HasDerivAt φ (G (φ t)) t :=
  MathlibExt.Analysis.ODE.MaximalSolutionWanted.ode_global_exists_of_global_lipschitz
    (fun _ => G) 0 x₀ K (hG.continuous.comp continuous_snd) (fun _ => hG)

/-- The flow of a globally Lipschitz field: `flow hG x₀` is the solution of `x' = G x` on all of
`ℝ` with `x 0 = x₀`. -/
private noncomputable def flow (hG : LipschitzWith K G) (x₀ : ℂ) : ℝ → ℂ :=
  (existsUnique_sol hG x₀).exists.choose

private theorem flow_zero (hG : LipschitzWith K G) (x₀ : ℂ) : flow hG x₀ 0 = x₀ :=
  (existsUnique_sol hG x₀).exists.choose_spec.1

private theorem hasDerivAt_flow (hG : LipschitzWith K G) (x₀ : ℂ) (t : ℝ) :
    HasDerivAt (flow hG x₀) (G (flow hG x₀ t)) t :=
  (existsUnique_sol hG x₀).exists.choose_spec.2 t

private theorem continuous_flow (hG : LipschitzWith K G) (x₀ : ℂ) : Continuous (flow hG x₀) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_flow hG x₀ t).continuousAt

private theorem eq_flow (hG : LipschitzWith K G) {x₀ : ℂ} {φ : ℝ → ℂ} (h0 : φ 0 = x₀)
    (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) : φ = flow hG x₀ :=
  (existsUnique_sol hG x₀).unique ⟨h0, hφ⟩ ⟨flow_zero hG x₀, hasDerivAt_flow hG x₀⟩

private theorem hasDerivAt_shift {φ : ℝ → ℂ} (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) (a : ℝ) :
    ∀ u, HasDerivAt (fun u => φ (a + u)) (G (φ (a + u))) u :=
  fun u => (hφ (a + u)).comp_const_add a u

private theorem sol_shift (hG : LipschitzWith K G) {φ ψ : ℝ → ℂ}
    (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) (hψ : ∀ t, HasDerivAt ψ (G (ψ t)) t) {a b : ℝ}
    (h : φ a = ψ b) (u : ℝ) :
    φ (a + u) = ψ (b + u) := by
  have e1 := eq_flow hG (φ := fun u => φ (a + u)) (x₀ := φ a) (by simp) (hasDerivAt_shift hφ a)
  have e2 := eq_flow hG (φ := fun u => ψ (b + u)) (x₀ := φ a) (by simp [h]) (hasDerivAt_shift hψ b)
  exact congrFun (e1.trans e2.symm) u

private theorem flow_add (hG : LipschitzWith K G) (x₀ : ℂ) (s t : ℝ) :
    flow hG x₀ (s + t) = flow hG (flow hG x₀ s) t := by
  have := sol_shift hG (hasDerivAt_flow hG x₀) (hasDerivAt_flow hG (flow hG x₀ s)) (a := s) (b := 0)
    (flow_zero hG _).symm t
  rwa [zero_add] at this

private theorem dist_flow_le_of_nonneg (hG : LipschitzWith K G) (x y : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    dist (flow hG x t) (flow hG y t) ≤ dist x y * Real.exp (K * t) := by
  have := dist_le_of_trajectories_ODE (v := fun _ => G) (K := K) (fun _ => hG)
    ((continuous_flow hG x).continuousOn) (fun s _ => (hasDerivAt_flow hG x s).hasDerivWithinAt)
    ((continuous_flow hG y).continuousOn) (fun s _ => (hasDerivAt_flow hG y s).hasDerivWithinAt)
    (a := 0) (b := t) (δ := dist x y) (by rw [flow_zero, flow_zero]) t ⟨ht, le_rfl⟩
  simpa using this

private theorem dist_flow_le_of_nonpos (hG : LipschitzWith K G) (x y : ℂ) {t : ℝ} (ht : t ≤ 0) :
    dist (flow hG x t) (flow hG y t) ≤ dist x y * Real.exp (K * (-t)) := by
  have hrev : ∀ z : ℂ, ∀ u, HasDerivAt (fun u => flow hG z (-u)) (-G (flow hG z (-u))) u := by
    intro z u
    have := (hasDerivAt_flow hG z (-u)).scomp u (hasDerivAt_neg u)
    rw [neg_one_smul] at this
    exact this
  have hcont : ∀ z : ℂ, Continuous fun u => flow hG z (-u) :=
    fun z => (continuous_flow hG z).comp continuous_neg
  have := dist_le_of_trajectories_ODE (v := fun _ z => -G z) (K := K) (fun _ => hG.neg)
    ((hcont x).continuousOn) (fun s _ => (hrev x s).hasDerivWithinAt)
    ((hcont y).continuousOn) (fun s _ => (hrev y s).hasDerivWithinAt)
    (a := 0) (b := -t) (δ := dist x y) (by simp [flow_zero]) (-t) ⟨by linarith, le_rfl⟩
  simpa using this

private theorem dist_flow_le (hG : LipschitzWith K G) (x y : ℂ) (t : ℝ) :
    dist (flow hG x t) (flow hG y t) ≤ dist x y * Real.exp (K * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact dist_flow_le_of_nonneg hG x y ht
  · rw [abs_of_nonpos ht]
    exact dist_flow_le_of_nonpos hG x y ht

private theorem eq_flow_of_isIntegralCurveOn (hG : LipschitzWith K G) {γ : ℝ → ℂ}
    (hγ : IsIntegralCurveOn γ (fun _ x => G x) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    γ t = flow hG (γ 0) t := by
  refine ODE_solution_unique (v := fun _ => G) (fun _ => hG)
    (hγ.continuousOn.mono Icc_subset_Ici_self)
    (fun s hs => (hγ s hs.1).mono (Ici_subset_Ici.2 hs.1))
    ((continuous_flow hG _).continuousOn) (fun s _ => (hasDerivAt_flow hG _ s).hasDerivWithinAt)
    (flow_zero hG _).symm ⟨ht, le_rfl⟩

/-! ### ω-limit sets -/

/-- The ω-limit set `⋂ s, closure (γ '' [s, ∞))` of a curve `γ`, as in the statement. -/
private noncomputable def omegaSet {X : Type*} [TopologicalSpace X] (γ : ℝ → X) : Set X :=
  ⋂ s : ℝ, closure (γ '' Ici s)

private theorem mem_omegaSet_iff {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {y : X} :
    y ∈ omegaSet γ ↔ ∀ ε > 0, ∀ S : ℝ, ∃ t ≥ S, dist (γ t) y < ε := by
  simp only [omegaSet, mem_iInter, Metric.mem_closure_iff, mem_image, mem_Ici]
  constructor
  · intro h ε hε S
    obtain ⟨b, ⟨t, ht, rfl⟩, hb⟩ := h S ε hε
    exact ⟨t, ht, by rwa [dist_comm]⟩
  · intro h S ε hε
    obtain ⟨t, ht, hd⟩ := h ε hε S
    exact ⟨γ t, ⟨t, ht, rfl⟩, by rwa [dist_comm]⟩

private theorem omegaSet_congr {X : Type*} [PseudoMetricSpace X] {γ φ : ℝ → X}
    (h : ∀ t, 0 ≤ t → γ t = φ t) : omegaSet γ = omegaSet φ := by
  ext y
  simp only [mem_omegaSet_iff]
  constructor
  · intro hy ε hε S
    obtain ⟨t, ht, hd⟩ := hy ε hε (max S 0)
    exact ⟨t, le_of_max_le_left ht, by rwa [← h t (le_of_max_le_right ht)]⟩
  · intro hy ε hε S
    obtain ⟨t, ht, hd⟩ := hy ε hε (max S 0)
    exact ⟨t, le_of_max_le_left ht, by rwa [h t (le_of_max_le_right ht)]⟩

private theorem isClosed_omegaSet (γ : ℝ → ℂ) : IsClosed (omegaSet γ) :=
  isClosed_iInter fun _ => isClosed_closure

private theorem omegaSet_subset_closure {γ : ℝ → ℂ} (s : ℝ) : omegaSet γ ⊆ closure (γ '' Ici s) :=
  iInter_subset _ s

private theorem omegaSet_subset_closedBall {γ : ℝ → ℂ} {R : ℝ} (hR : ∀ t, 0 ≤ t → ‖γ t‖ ≤ R) :
    omegaSet γ ⊆ closedBall 0 R := by
  refine (omegaSet_subset_closure 0).trans (closure_minimal ?_ isClosed_closedBall)
  rintro _ ⟨t, ht, rfl⟩
  simpa using hR t ht

private theorem isCompact_omegaSet {γ : ℝ → ℂ} {R : ℝ} (hR : ∀ t, 0 ≤ t → ‖γ t‖ ≤ R) :
    IsCompact (omegaSet γ) :=
  (isCompact_closedBall 0 R).of_isClosed_subset (isClosed_omegaSet γ)
    (omegaSet_subset_closedBall hR)

private theorem exists_cluster {ψ : ℝ → ℂ} {S : Set ℂ} (hS : IsCompact S)
    (h : ∀ t, 0 ≤ t → ψ t ∈ S) :
    ∃ z ∈ S, z ∈ omegaSet ψ := by
  obtain ⟨z, hzS, φ, hφ, hlim⟩ := hS.tendsto_subseq (x := fun n : ℕ => ψ n)
    fun n => h n (Nat.cast_nonneg n)
  refine ⟨z, hzS, mem_omegaSet_iff.2 fun ε hε T => ?_⟩
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  obtain ⟨n, hn⟩ := exists_nat_ge T
  refine ⟨φ (max N n), ?_, hN _ (le_max_left _ _)⟩
  calc T ≤ n := hn
    _ ≤ (max N n : ℕ) := by exact_mod_cast le_max_right N n
    _ ≤ φ (max N n) := by exact_mod_cast hφ.id_le _

private theorem omegaSet_nonempty {γ : ℝ → ℂ} {R : ℝ} (hR : ∀ t, 0 ≤ t → ‖γ t‖ ≤ R) :
    (omegaSet γ).Nonempty := by
  obtain ⟨z, -, hz⟩ := exists_cluster (isCompact_closedBall (0 : ℂ) R)
    (ψ := γ) fun t ht => by simpa using hR t ht
  exact ⟨z, hz⟩

private theorem flow_mem_omegaSet (hG : LipschitzWith K G) {γ : ℝ → ℂ}
    (hγ : ∀ t, 0 ≤ t → γ t = flow hG (γ 0) t) {y : ℂ} (hy : y ∈ omegaSet γ) (t : ℝ) :
    flow hG y t ∈ omegaSet γ := by
  rw [mem_omegaSet_iff] at hy ⊢
  intro ε hε S
  have hC : 0 < Real.exp (K * |t|) := Real.exp_pos _
  obtain ⟨τ, hτ, hd⟩ := hy (ε / Real.exp (K * |t|)) (div_pos hε hC) (max S 0 + |t|)
  have hτ0 : 0 ≤ τ := by linarith [le_max_right S 0, abs_nonneg t]
  have hτt : 0 ≤ τ + t := by linarith [le_max_right S 0, neg_abs_le t]
  refine ⟨τ + t, by linarith [le_max_left S 0, neg_abs_le t], ?_⟩
  rw [hγ _ hτt, flow_add, ← hγ _ hτ0]
  calc dist (flow hG (γ τ) t) (flow hG y t) ≤ dist (γ τ) y * Real.exp (K * |t|) :=
        dist_flow_le hG _ _ t
    _ < ε / Real.exp (K * |t|) * Real.exp (K * |t|) := mul_lt_mul_of_pos_right hd hC
    _ = ε := div_mul_cancel₀ _ hC.ne'

private theorem omegaSet_eq_iInter_nat (γ : ℝ → ℂ) :
    omegaSet γ = ⋂ n : ℕ, closure (γ '' Ici (n : ℝ)) := by
  apply Subset.antisymm
  · exact subset_iInter fun n => omegaSet_subset_closure _
  · refine subset_iInter fun s => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge s
    exact (iInter_subset _ n).trans (closure_mono (image_mono (Ici_subset_Ici.2 hn)))

private theorem isPreconnected_omegaSet {γ : ℝ → ℂ} (hc : ContinuousOn γ (Ici 0)) {R : ℝ}
    (hR : ∀ t, 0 ≤ t → ‖γ t‖ ≤ R) : IsPreconnected (omegaSet γ) := by
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hsub hdisj
  have hωc := isCompact_omegaSet hR
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := SeparatedNhds.of_isCompact_isCompact
    (hωc.inter_right hu) (hωc.inter_right hv) (by
      rw [Set.disjoint_iff]
      rintro y ⟨⟨hy, hyu⟩, ⟨-, hyv⟩⟩
      have : y ∈ omegaSet γ ∩ (u ∩ v) := ⟨hy, hyu, hyv⟩
      rw [hdisj] at this
      exact this)
  -- some tail closure lies in `U ∪ V`
  have hcl : ∀ n : ℕ, closure (γ '' Ici (n : ℝ)) ⊆ closedBall 0 R := fun n =>
    closure_minimal (by rintro _ ⟨t, ht, rfl⟩; simpa using hR t ((Nat.cast_nonneg n).trans ht))
      isClosed_closedBall
  obtain ⟨N, hN⟩ : ∃ N : ℕ, closure (γ '' Ici (N : ℝ)) ⊆ U ∪ V := by
    by_contra hcon
    push Not at hcon
    have hne : ∀ n : ℕ, (closure (γ '' Ici (n : ℝ)) \ (U ∪ V)).Nonempty := fun n =>
      Set.nonempty_iff_ne_empty.2 fun h => hcon n (sdiff_eq_empty.1 h)
    obtain ⟨y, hy⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun n : ℕ => closure (γ '' Ici (n : ℝ)) \ (U ∪ V))
      (fun n => sdiff_subset_sdiff_left (closure_mono (image_mono (Ici_subset_Ici.2
        (by push_cast; linarith))))) hne
      ((isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
        (isClosed_closure.sdiff (hU.union hV)) (sdiff_subset.trans (hcl 0)))
      (fun n => isClosed_closure.sdiff (hU.union hV))
    rw [mem_iInter] at hy
    have hyω : y ∈ omegaSet γ := by
      rw [omegaSet_eq_iInter_nat, mem_iInter]
      exact fun n => (hy n).1
    rcases hsub hyω with hyu | hyv
    · exact (hy 0).2 (Or.inl (hAU ⟨hyω, hyu⟩))
    · exact (hy 0).2 (Or.inr (hBV ⟨hyω, hyv⟩))
  have hpre : IsPreconnected (closure (γ '' Ici (N : ℝ))) :=
    (isPreconnected_Ici.image γ (hc.mono (Ici_subset_Ici.2 (Nat.cast_nonneg N)))).closure
  have hωN : omegaSet γ ⊆ closure (γ '' Ici (N : ℝ)) := omegaSet_subset_closure _
  rcases hpre.subset_or_subset hU hV hUV hN with h | h
  · left
    intro y hy
    rcases hsub hy with hyu | hyv
    · exact hyu
    · exact absurd (h (hωN hy)) (Set.disjoint_left.1 hUV.symm (hBV ⟨hy, hyv⟩))
  · right
    intro y hy
    rcases hsub hy with hyu | hyv
    · exact absurd (h (hωN hy)) (Set.disjoint_left.1 hUV (hAU ⟨hy, hyu⟩))
    · exact hyv

end

/-! ### A priori bounds -/

section

open Set Filter Topology Metric ComplexConjugate
open scoped NNReal

/-- A solution of `x' = V x` that starts at distance `d` from `q` stays within `M (τ - a)` of its
starting point up to time `b`, as long as `‖V‖ ≤ M` on the closed ball of radius `R` about `q` and
`d + M (b - a) < R`. -/
private theorem stay_fwd {V : ℂ → ℂ} {φ : ℝ → ℂ} (hφ : ∀ t, HasDerivAt φ (V (φ t)) t) {q : ℂ}
    {R M : ℝ} (hM : ∀ y ∈ closedBall q R, ‖V y‖ ≤ M) (hM0 : 0 ≤ M) {a b : ℝ}
    (h : dist (φ a) q + M * (b - a) < R) : ∀ τ ∈ Icc a b, dist (φ τ) (φ a) ≤ M * (τ - a) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hball : ∀ τ ∈ Icc a b, dist (φ τ) q < R := by
    by_contra hcon
    push Not at hcon
    obtain ⟨τ', hτ', hτ'R⟩ := hcon
    set S := {τ ∈ Icc a b | R ≤ dist (φ τ) q} with hS_def
    have hS_closed : IsClosed S :=
      isClosed_Icc.inter (isClosed_le continuous_const (hφc.dist continuous_const))
    have hS_ne : S.Nonempty := ⟨τ', hτ', hτ'R⟩
    have hS_bdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
    have hτ₁S : sInf S ∈ S := hS_closed.csInf_mem hS_ne hS_bdd
    have hlt : ∀ σ ∈ Ico a (sInf S), dist (φ σ) q < R := fun σ hσ => by
      by_contra h'
      push Not at h'
      have : σ ∈ S := ⟨⟨hσ.1, hσ.2.le.trans hτ₁S.1.2⟩, h'⟩
      exact absurd (csInf_le hS_bdd this) (not_le.2 hσ.2)
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (a := a) (b := sInf S) (f := φ)
      (f' := fun σ => V (φ σ)) (C := M) (fun σ _ => (hφ σ).hasDerivWithinAt)
      (fun σ hσ => hM _ (mem_closedBall.2 (hlt σ hσ).le)) (sInf S) ⟨hτ₁S.1.1, le_rfl⟩
    have h2 : M * (sInf S - a) ≤ M * (b - a) :=
      mul_le_mul_of_nonneg_left (by linarith [hτ₁S.1.2]) hM0
    have : dist (φ (sInf S)) q < R := by
      calc dist (φ (sInf S)) q ≤ dist (φ (sInf S)) (φ a) + dist (φ a) q := dist_triangle _ _ _
        _ ≤ M * (sInf S - a) + dist (φ a) q := by rw [dist_eq_norm]; linarith [hmvt]
        _ < R := by linarith
    exact absurd hτ₁S.2 (not_le.2 this)
  intro τ hτ
  have := norm_image_sub_le_of_norm_deriv_le_segment' (a := a) (b := b) (f := φ)
    (f' := fun σ => V (φ σ)) (C := M) (fun σ _ => (hφ σ).hasDerivWithinAt)
    (fun σ hσ => hM _ (mem_closedBall.2 (hball σ (Ico_subset_Icc_self hσ)).le)) τ hτ
  rwa [dist_eq_norm]

private theorem stay {V : ℂ → ℂ} {φ : ℝ → ℂ} (hφ : ∀ t, HasDerivAt φ (V (φ t)) t) {q : ℂ}
    {R M : ℝ} (hM : ∀ y ∈ closedBall q R, ‖V y‖ ≤ M) (hM0 : 0 ≤ M) {t ε : ℝ}
    (h : dist (φ t) q + M * ε < R) : ∀ τ, |τ - t| ≤ ε → dist (φ τ) (φ t) ≤ M * |τ - t| := by
  intro τ hτ
  rcases le_total t τ with htτ | hτt
  · have := stay_fwd hφ hM hM0 (a := t) (b := t + ε) (by simpa using h) τ
      ⟨htτ, by linarith [le_abs_self (τ - t)]⟩
    rwa [abs_of_nonneg (by linarith)]
  · have hψ : ∀ u, HasDerivAt (fun u => φ (-u)) ((fun y => -V y) ((fun u => φ (-u)) u)) u := by
      intro u
      have := (hφ (-u)).scomp u (hasDerivAt_neg u)
      rw [neg_one_smul] at this
      exact this
    have hM' : ∀ y ∈ closedBall q R, ‖(fun y => -V y) y‖ ≤ M := fun y hy => by
      simpa using hM y hy
    have := stay_fwd hψ hM' hM0 (a := -t) (b := -t + ε) (by simpa using h) (-τ)
      ⟨by linarith, by linarith [neg_abs_le (τ - t)]⟩
    simp only [neg_neg] at this
    rw [abs_of_nonpos (by linarith)]
    have e : M * (-τ - -t) = M * -(τ - t) := by ring
    linarith

/-! ### Transversals -/

private theorem normsq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Transversal data at a point `p` with `G p ≠ 0`: a radius `r` such that `G` stays within
`‖G p‖ / 2` of `G p` on the closed ball of radius `r` about `p`, and the half-length `δ` of the
transversal segment through `p` orthogonal to `G p`, which lies in the ball of radius `r / 4`. -/
private structure TData (G : ℂ → ℂ) (p : ℂ) : Type where
  r : ℝ
  δ : ℝ
  hr : 0 < r
  hδ : 0 < δ
  hGp : G p ≠ 0
  hball : ∀ y ∈ closedBall p r, ‖G y - G p‖ ≤ ‖G p‖ / 2
  hδr : δ * ‖G p‖ ≤ r / 4

namespace TData

variable {G : ℂ → ℂ} {p : ℂ} (T : TData G p)

/-- The direction `i G p` of the transversal. -/
private noncomputable def w (_ : TData G p) : ℂ := Complex.I * G p
/-- The line through `p` orthogonal to `G p`, parametrized by `s ↦ p + s i G p`. -/
private noncomputable def ℓ (s : ℝ) : ℂ := p + (s : ℂ) * T.w
/-- The transversal segment `ℓ '' [-δ, δ]`. -/
private noncomputable def L : Set ℂ := T.ℓ '' Icc (-T.δ) T.δ
/-- The signed distance `⟪y - p, G p⟫` to the line of the transversal, up to the factor `‖G p‖`. -/
private noncomputable def g (_ : TData G p) (y : ℂ) : ℝ := ((y - p) * conj (G p)).re
/-- The position on the line of the transversal: `pos (ℓ s) = s`. -/
private noncomputable def pos (y : ℂ) : ℝ := ((y - p) * conj T.w).re / ‖G p‖ ^ 2
/-- A bound for `‖G‖` on the closed ball of radius `r` about `p`. -/
private noncomputable def M (_ : TData G p) : ℝ := 2 * ‖G p‖
/-- A lower bound for `⟪G y, G p⟫` on the closed ball of radius `r` about `p`. -/
private noncomputable def c (_ : TData G p) : ℝ := ‖G p‖ ^ 2 / 2

include T in
private theorem norm_pos : 0 < ‖G p‖ := norm_pos_iff.2 T.hGp
private theorem M_pos : 0 < T.M := by unfold M; linarith [T.norm_pos]
private theorem c_pos : 0 < T.c := by unfold c; have := T.norm_pos; positivity


private theorem g_ℓ (s : ℝ) : T.g (T.ℓ s) = 0 := by
  simp only [g, ℓ, w, add_sub_cancel_left, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  ring

private theorem pos_ℓ (s : ℝ) : T.pos (T.ℓ s) = s := by
  have h := T.norm_pos
  simp only [pos, ℓ, w, add_sub_cancel_left, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
  rw [normsq (G p)]
  have : (G p).re ^ 2 + (G p).im ^ 2 ≠ 0 := by rw [← normsq (G p)]; positivity
  field_simp
  ring

private theorem ℓ_pos {y : ℂ} (hy : T.g y = 0) : T.ℓ (T.pos y) = y := by
  have h := T.norm_pos
  have hne : (G p).re ^ 2 + (G p).im ^ 2 ≠ 0 := by rw [← normsq (G p)]; positivity
  simp only [g, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sub_re,
    Complex.sub_im] at hy
  apply Complex.ext
  · simp only [ℓ, pos, w, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    rw [normsq (G p)]
    field_simp
    linear_combination (-(G p).re) * hy
  · simp only [ℓ, pos, w, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    rw [normsq (G p)]
    field_simp
    linear_combination (-(G p).im) * hy

private theorem ℓ_injective : Function.Injective T.ℓ := fun s s' h => by
  rw [← T.pos_ℓ s, ← T.pos_ℓ s', h]

private theorem norm_w : ‖T.w‖ = ‖G p‖ := by simp [w]

private theorem dist_ℓ (s s' : ℝ) : dist (T.ℓ s) (T.ℓ s') = |s - s'| * ‖G p‖ := by
  rw [dist_eq_norm, ℓ, ℓ, add_sub_add_left_eq_sub, ← sub_mul, norm_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, T.norm_w]

private theorem ℓ_zero : T.ℓ 0 = p := by simp [ℓ]

private theorem dist_ℓ_p (s : ℝ) : dist (T.ℓ s) p = |s| * ‖G p‖ := by
  have := T.dist_ℓ s 0
  rwa [T.ℓ_zero, sub_zero] at this

private theorem dist_ℓ_p_le {s : ℝ} (hs : |s| ≤ T.δ) : dist (T.ℓ s) p ≤ T.r / 4 := by
  rw [T.dist_ℓ_p]
  exact (mul_le_mul_of_nonneg_right hs (norm_nonneg _)).trans T.hδr

private theorem continuous_ℓ : Continuous T.ℓ := by unfold ℓ; fun_prop
private theorem continuous_g : Continuous T.g := by unfold g; fun_prop
private theorem continuous_pos : Continuous T.pos := by unfold pos; fun_prop

private theorem isCompact_L : IsCompact T.L := isCompact_Icc.image T.continuous_ℓ
private theorem isClosed_L : IsClosed T.L := T.isCompact_L.isClosed

private theorem mem_L_iff {y : ℂ} : y ∈ T.L ↔ T.g y = 0 ∧ |T.pos y| ≤ T.δ := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨T.g_ℓ s, by rw [T.pos_ℓ]; exact abs_le.2 hs⟩
  · rintro ⟨hg, hpos⟩
    exact ⟨T.pos y, abs_le.1 hpos, T.ℓ_pos hg⟩

private theorem ℓ_mem_L {s : ℝ} (hs : |s| ≤ T.δ) : T.ℓ s ∈ T.L := ⟨s, abs_le.1 hs, rfl⟩

private theorem dist_p_le_of_mem_L {y : ℂ} (hy : y ∈ T.L) : dist y p ≤ T.r / 4 := by
  obtain ⟨s, hs, rfl⟩ := hy
  exact T.dist_ℓ_p_le (abs_le.2 hs)

private theorem g_sub (y y' : ℂ) : T.g y - T.g y' = ((y - y') * conj (G p)).re := by
  simp only [g, ← Complex.sub_re, ← sub_mul]
  ring_nf

private theorem abs_g_sub_le (y y' : ℂ) : |T.g y - T.g y'| ≤ ‖y - y'‖ * ‖G p‖ := by
  rw [T.g_sub]
  exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, Complex.norm_conj])

private theorem bounds {y : ℂ} (hy : y ∈ closedBall p T.r) :
    ‖G y‖ ≤ T.M ∧ T.c ≤ (G y * conj (G p)).re := by
  have h1 := T.hball y hy
  have hn := T.norm_pos
  constructor
  · calc ‖G y‖ = ‖G p + (G y - G p)‖ := by ring_nf
      _ ≤ ‖G p‖ + ‖G y - G p‖ := norm_add_le _ _
      _ ≤ T.M := by unfold M; linarith
  · have e : (G y * conj (G p)).re = ‖G p‖ ^ 2 + ((G y - G p) * conj (G p)).re := by
      rw [sub_mul, Complex.sub_re, Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
      ring
    have h2 : |((G y - G p) * conj (G p)).re| ≤ ‖G p‖ / 2 * ‖G p‖ :=
      (Complex.abs_re_le_norm _).trans (by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    rw [e]
    unfold c
    nlinarith [neg_abs_le ((G y - G p) * conj (G p)).re]

private theorem hasDerivAt_g_comp {φ : ℝ → ℂ} {φ' : ℂ} {t : ℝ} (h : HasDerivAt φ φ' t) :
    HasDerivAt (fun t => T.g (φ t)) ((φ' * conj (G p)).re) t := by
  have := (Complex.reCLM.hasFDerivAt (x := (φ t - p) * conj (G p))).comp_hasDerivAt t
    ((h.sub_const p).mul_const (conj (G p)))
  have e : (fun t => T.g (φ t)) = ⇑Complex.reCLM ∘ fun y => (φ y - p) * conj (G p) := by
    funext t
    simp [g]
  rw [e]
  convert this using 1
  rw [Complex.reCLM_apply]

private theorem g_incr {φ : ℝ → ℂ} (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) {a b : ℝ} (hab : a ≤ b)
    (hin : ∀ σ ∈ Icc a b, φ σ ∈ closedBall p T.r) : T.c * (b - a) ≤ T.g (φ b) - T.g (φ a) := by
  rcases hab.eq_or_lt with rfl | hab'
  · simp
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun t => T.g (φ t))
    (fun t => (G (φ t) * conj (G p)).re) hab' ((T.continuous_g.comp hφc).continuousOn)
    (fun x _ => T.hasDerivAt_g_comp (hφ x))
  have hb := (T.bounds (hin ξ (Ioo_subset_Icc_self hξ))).2
  rw [hξeq] at hb
  have hba : 0 < b - a := by linarith
  rw [le_div_iff₀ hba] at hb
  linarith

private theorem g_strict {φ : ℝ → ℂ} (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) {a b : ℝ} (hab : a < b)
    (hin : ∀ σ ∈ Icc a b, φ σ ∈ closedBall p T.r) : T.g (φ a) < T.g (φ b) := by
  have := T.g_incr hφ hab.le hin
  have : 0 < T.c * (b - a) := mul_pos T.c_pos (by linarith)
  linarith

private theorem bound_M (y : ℂ) (hy : y ∈ closedBall p T.r) : ‖G y‖ ≤ T.M := (T.bounds hy).1

private theorem sep {φ : ℝ → ℂ} (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) {τ₁ τ₂ : ℝ} (h12 : τ₁ < τ₂)
    (h1 : φ τ₁ ∈ T.L) (h2 : φ τ₂ ∈ T.L) : T.r / (2 * T.M) ≤ τ₂ - τ₁ := by
  by_contra hlt
  push Not at hlt
  have hM := T.M_pos
  have hr := T.hr
  have hd1 := T.dist_p_le_of_mem_L h1
  have hMε : T.M * (τ₂ - τ₁) < T.r / 2 := by
    calc T.M * (τ₂ - τ₁) < T.M * (T.r / (2 * T.M)) := mul_lt_mul_of_pos_left hlt hM
      _ = T.r / 2 := by field_simp
  have hstay := stay hφ T.bound_M hM.le (t := τ₁) (ε := τ₂ - τ₁) (by linarith)
  have hin : ∀ σ ∈ Icc τ₁ τ₂, φ σ ∈ closedBall p T.r := by
    intro σ hσ
    have h3 := hstay σ (by rw [abs_of_nonneg (by linarith [hσ.1])]; linarith [hσ.2])
    rw [abs_of_nonneg (by linarith [hσ.1])] at h3
    have h4 : T.M * (σ - τ₁) ≤ T.M * (τ₂ - τ₁) :=
      mul_le_mul_of_nonneg_left (by linarith [hσ.2]) hM.le
    rw [mem_closedBall]
    linarith [dist_triangle (φ σ) (φ τ₁) p]
  have := T.g_strict hφ h12 hin
  rw [(T.mem_L_iff.1 h1).1, (T.mem_L_iff.1 h2).1] at this
  exact lt_irrefl _ this

private theorem next_crossing {φ : ℝ → ℂ} (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) {τ₁ τ' : ℝ}
    (h1 : φ τ₁ ∈ T.L) (h1' : τ₁ < τ') (h' : φ τ' ∈ T.L) :
    ∃ τ₂, τ₁ < τ₂ ∧ τ₂ ≤ τ' ∧ φ τ₂ ∈ T.L ∧ ∀ τ ∈ Ioo τ₁ τ₂, φ τ ∉ T.L := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hθ : 0 < T.r / (2 * T.M) := div_pos T.hr (by linarith [T.M_pos])
  set S := Ici (τ₁ + T.r / (2 * T.M)) ∩ φ ⁻¹' T.L with hS_def
  have hS_closed : IsClosed S := isClosed_Ici.inter (T.isClosed_L.preimage hφc)
  have hτ'S : τ' ∈ S := ⟨by have := T.sep hφ h1' h1 h'; simp only [mem_Ici]; linarith, h'⟩
  have hS_bdd : BddBelow S := ⟨τ₁ + T.r / (2 * T.M), fun x hx => hx.1⟩
  have hmem : sInf S ∈ S := hS_closed.csInf_mem ⟨τ', hτ'S⟩ hS_bdd
  refine ⟨sInf S, by have := hmem.1; simp only [mem_Ici] at this; linarith,
    csInf_le hS_bdd hτ'S, hmem.2, fun τ hτ hτL => ?_⟩
  have hτS : τ ∈ S := ⟨by have := T.sep hφ hτ.1 h1 hτL; simp only [mem_Ici]; linarith, hτL⟩
  exact absurd (csInf_le hS_bdd hτS) (not_le.2 hτ.2)

/-- **Flow box by the intermediate value theorem.** A solution passing close enough to a point `q`
of the line of the transversal crosses that line within a short time, close to `q`. -/
private theorem crossing_near {q : ℂ} (hq : T.g q = 0) (hqp : dist q p ≤ T.r / 4) {η : ℝ}
    (hη : 0 < η) (hηr : η ≤ T.r / 4) :
    ∃ ε > 0, ∃ ρ > 0, ∀ φ : ℝ → ℂ, (∀ t, HasDerivAt φ (G (φ t)) t) → ∀ t,
      dist (φ t) q < ρ → ∃ τ, |τ - t| < ε ∧ T.g (φ τ) = 0 ∧ dist (φ τ) q < η := by
  have hM := T.M_pos
  have hc := T.c_pos
  have hn := T.norm_pos
  have hr := T.hr
  set ε := η / (4 * T.M) with hε_def
  have hε : 0 < ε := div_pos hη (by linarith)
  have hMε : T.M * ε = η / 4 := by rw [hε_def]; field_simp
  set ρ := min (η / 4) (T.c * ε / (2 * ‖G p‖)) with hρ_def
  have hρ : 0 < ρ := lt_min (by linarith) (div_pos (mul_pos hc hε) (by linarith))
  refine ⟨ε, hε, ρ, hρ, fun φ hφ t ht => ?_⟩
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hρ1 : ρ ≤ η / 4 := min_le_left _ _
  have hρ2 : ρ ≤ T.c * ε / (2 * ‖G p‖) := min_le_right _ _
  have htp : dist (φ t) p < T.r / 2 := by
    linarith [dist_triangle (φ t) q p]
  have hstay := stay hφ T.bound_M hM.le (t := t) (ε := ε) (by linarith)
  have hin : ∀ σ ∈ Icc (t - ε) (t + ε), φ σ ∈ closedBall p T.r := by
    intro σ hσ
    have habs : |σ - t| ≤ ε := abs_le.2 ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have h3 := hstay σ habs
    have h4 : T.M * |σ - t| ≤ T.M * ε := mul_le_mul_of_nonneg_left habs hM.le
    rw [mem_closedBall]
    linarith [dist_triangle (φ σ) (φ t) p]
  have hgt : |T.g (φ t)| < T.c * ε / 2 := by
    have := T.abs_g_sub_le (φ t) q
    rw [hq, sub_zero, ← dist_eq_norm] at this
    calc |T.g (φ t)| ≤ dist (φ t) q * ‖G p‖ := this
      _ < ρ * ‖G p‖ := mul_lt_mul_of_pos_right ht hn
      _ ≤ T.c * ε / (2 * ‖G p‖) * ‖G p‖ := mul_le_mul_of_nonneg_right hρ2 hn.le
      _ = T.c * ε / 2 := by field_simp
  have hup := T.g_incr hφ (a := t) (b := t + ε) (by linarith)
    fun σ hσ => hin σ ⟨by linarith [hσ.1], hσ.2⟩
  have hdown := T.g_incr hφ (a := t - ε) (b := t) (by linarith)
    fun σ hσ => hin σ ⟨hσ.1, by linarith [hσ.2]⟩
  have hcε : 0 < T.c * ε := mul_pos hc hε
  have hpos : 0 < T.g (φ (t + ε)) := by
    have : T.c * (t + ε - t) = T.c * ε := by ring
    linarith [neg_abs_le (T.g (φ t))]
  have hneg : T.g (φ (t - ε)) < 0 := by
    have : T.c * (t - (t - ε)) = T.c * ε := by ring
    linarith [le_abs_self (T.g (φ t))]
  obtain ⟨τ, hτ, hτ0⟩ := intermediate_value_Icc (by linarith : t - ε ≤ t + ε)
    ((T.continuous_g.comp hφc).continuousOn) ⟨hneg.le, hpos.le⟩
  have hτ0' : T.g (φ τ) = 0 := hτ0
  have hτlt : |τ - t| < ε := by
    rcases eq_or_ne τ (t + ε) with h | h
    · rw [h] at hτ0'; linarith
    rcases eq_or_ne τ (t - ε) with h' | h'
    · rw [h'] at hτ0'; linarith
    exact abs_lt.2 ⟨by linarith [lt_of_le_of_ne hτ.1 (Ne.symm h')],
      by linarith [lt_of_le_of_ne hτ.2 h]⟩
  refine ⟨τ, hτlt, hτ0', ?_⟩
  have h3 := hstay τ hτlt.le
  have h4 : T.M * |τ - t| ≤ T.M * ε := mul_le_mul_of_nonneg_left hτlt.le hM.le
  linarith [dist_triangle (φ τ) (φ t) q]

private theorem crossing_near_L {σ : ℝ} (hσ : |σ| < T.δ) {η' : ℝ} (hη' : 0 < η') :
    ∃ ε > 0, ∃ ρ > 0, ∀ φ : ℝ → ℂ, (∀ t, HasDerivAt φ (G (φ t)) t) → ∀ t,
      dist (φ t) (T.ℓ σ) < ρ → ∃ τ, |τ - t| < ε ∧ φ τ ∈ T.L ∧ |T.pos (φ τ) - σ| < η' := by
  have hn := T.norm_pos
  set η := min (T.r / 4) (min (η' * ‖G p‖) ((T.δ - |σ|) * ‖G p‖)) with hη_def
  have hη : 0 < η := lt_min (by linarith [T.hr]) (lt_min (mul_pos hη' hn)
    (mul_pos (by linarith) hn))
  obtain ⟨ε, hε, ρ, hρ, h⟩ := T.crossing_near (T.g_ℓ σ) (T.dist_ℓ_p_le hσ.le) hη
    (min_le_left _ _)
  refine ⟨ε, hε, ρ, hρ, fun φ hφ t ht => ?_⟩
  obtain ⟨τ, hτ, hg, hd⟩ := h φ hφ t ht
  have hφτ := T.ℓ_pos hg
  rw [← hφτ, T.dist_ℓ] at hd
  have h1 : |T.pos (φ τ) - σ| * ‖G p‖ < η' * ‖G p‖ :=
    lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : |T.pos (φ τ) - σ| * ‖G p‖ < (T.δ - |σ|) * ‖G p‖ :=
    lt_of_lt_of_le hd ((min_le_right _ _).trans (min_le_right _ _))
  have h1' := lt_of_mul_lt_mul_right h1 hn.le
  have h2' := lt_of_mul_lt_mul_right h2 hn.le
  refine ⟨τ, hτ, T.mem_L_iff.2 ⟨hg, ?_⟩, h1'⟩
  have := abs_sub_abs_le_abs_sub (T.pos (φ τ)) σ
  linarith

end TData

private theorem exists_TData {G : ℂ → ℂ} (hG : Continuous G) {p : ℂ} (hp : G p ≠ 0) :
    Nonempty (TData G p) := by
  have hn : 0 < ‖G p‖ := norm_pos_iff.2 hp
  obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.1 hG.continuousAt (‖G p‖ / 2) (by positivity)
  refine ⟨⟨r / 2, r / (8 * ‖G p‖), by positivity, by positivity, hp, fun y hy => ?_, ?_⟩⟩
  · rw [← dist_eq_norm]
    exact (hball (lt_of_le_of_lt (mem_closedBall.1 hy) (by linarith))).le
  · field_simp
    linarith

end

/-! ### The jump of the winding number across a segment -/

section

open Set Filter Topology MeasureTheory
open scoped Real

private theorem inv_sub_inv_eq (a ε : ℝ) (hε : 0 < ε) :
    ((a : ℂ) - ε * Complex.I)⁻¹ - ((a : ℂ) + ε * Complex.I)⁻¹ =
      ((2 * ε / (a ^ 2 + ε ^ 2) : ℝ) : ℂ) * Complex.I := by
  have h1 : (a : ℂ) - ε * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h2 : (a : ℂ) + ε * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h3 : ((a : ℂ) ^ 2 + (ε : ℂ) ^ 2) ≠ 0 := by
    have : (a ^ 2 + ε ^ 2 : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [inv_sub_inv h1 h2]
  have : ((a : ℂ) - ε * Complex.I) * ((a : ℂ) + ε * Complex.I) = (a : ℂ) ^ 2 + (ε : ℂ) ^ 2 := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [this]
  push_cast
  field_simp
  ring

private theorem integral_two_eps_div (c ε : ℝ) (hε : 0 < ε) :
    ∫ t in (0 : ℝ)..1, 2 * ε / ((t - c) ^ 2 + ε ^ 2) =
      2 * (Real.arctan ((1 - c) / ε) + Real.arctan (c / ε)) := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t => 2 * Real.arctan ((t - c) / ε))
      (2 * ε / ((t - c) ^ 2 + ε ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun t => (t - c) / ε) (1 / ε) t :=
      ((hasDerivAt_id t).sub_const c).div_const ε
    have h2 := ((Real.hasDerivAt_arctan ((t - c) / ε)).comp t h1).const_mul 2
    refine h2.congr_deriv ?_
    have hε' : ε ≠ 0 := hε.ne'
    field_simp
    ring
  have hcont : Continuous fun t : ℝ => 2 * ε / ((t - c) ^ 2 + ε ^ 2) :=
    continuous_const.div (((continuous_id.sub continuous_const).pow 2).add continuous_const)
      fun t => by positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
  simp only [zero_sub, neg_div, Real.arctan_neg]
  ring

private theorem seg_integrand_eq (p₀ p₁ : ℂ) (hd : p₀ ≠ p₁) (c s t : ℝ) :
    ((AffineMap.lineMap p₁ p₀ t - (p₁ + c * (p₀ - p₁) + s * (Complex.I * (p₀ - p₁))))⁻¹ •
      ContinuousLinearMap.id ℂ ℂ) (p₀ - p₁) = (((t - c : ℝ) : ℂ) - s * Complex.I)⁻¹ := by
  have hd' : p₀ - p₁ ≠ 0 := sub_ne_zero.2 hd
  rw [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    AffineMap.lineMap_apply_module, Complex.real_smul, Complex.real_smul]
  have : ((1 - t : ℝ) : ℂ) * p₁ + (t : ℂ) * p₀ -
      (p₁ + c * (p₀ - p₁) + s * (Complex.I * (p₀ - p₁))) =
      (((t - c : ℝ) : ℂ) - s * Complex.I) * (p₀ - p₁) := by
    push_cast
    ring
  rw [this, mul_inv, mul_assoc, inv_mul_cancel₀ hd', mul_one]

/-- The integrals of `(ζ - z)⁻¹` along the segment from `p₁` to `p₀`, for the points `z` at
distance `ε |p₀ - p₁|` on either side of the point `p₁ + c (p₀ - p₁)`, differ by
`2 (arctan ((1 - c) / ε) + arctan (c / ε)) i`. -/
private theorem seg_diff (p₀ p₁ : ℂ) (hd : p₀ ≠ p₁) (c ε : ℝ) (hε : 0 < ε) :
    (∫ᶜ ζ in Path.segment p₁ p₀,
        (ζ - (p₁ + c * (p₀ - p₁) + ε * (Complex.I * (p₀ - p₁))))⁻¹ • ContinuousLinearMap.id ℂ ℂ) -
      (∫ᶜ ζ in Path.segment p₁ p₀,
        (ζ - (p₁ + c * (p₀ - p₁) + (-ε : ℝ) * (Complex.I * (p₀ - p₁))))⁻¹ •
          ContinuousLinearMap.id ℂ ℂ) =
      ((2 * (Real.arctan ((1 - c) / ε) + Real.arctan (c / ε)) : ℝ) : ℂ) * Complex.I := by
  rw [curveIntegral_segment, curveIntegral_segment]
  have e1 : ∀ s : ℝ, (∫ t in (0 : ℝ)..1,
      ((AffineMap.lineMap p₁ p₀ t - (p₁ + c * (p₀ - p₁) + s * (Complex.I * (p₀ - p₁))))⁻¹ •
        ContinuousLinearMap.id ℂ ℂ) (p₀ - p₁)) =
      ∫ t in (0 : ℝ)..1, (((t - c : ℝ) : ℂ) - s * Complex.I)⁻¹ :=
    fun s => intervalIntegral.integral_congr fun t _ => seg_integrand_eq p₀ p₁ hd c s t
  rw [e1 ε, e1 (-ε)]
  have hne : ∀ s : ℝ, s ≠ 0 → ∀ t : ℝ, ((t - c : ℝ) : ℂ) - s * Complex.I ≠ 0 := by
    intro s hs t h
    have := congrArg Complex.im h
    simp only [Complex.ofReal_sub, Complex.sub_im, Complex.ofReal_im, sub_self,
      Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
      add_zero, zero_sub, Complex.zero_im, neg_eq_zero] at this
    exact hs this
  have hint : ∀ s : ℝ, s ≠ 0 → IntervalIntegrable
      (fun t : ℝ => (((t - c : ℝ) : ℂ) - s * Complex.I)⁻¹) volume 0 1 := by
    intro s hs
    refine (Continuous.inv₀ ?_ (hne s hs)).intervalIntegrable 0 1
    fun_prop
  rw [← intervalIntegral.integral_sub (hint ε hε.ne') (hint (-ε) (neg_ne_zero.2 hε.ne'))]
  have e2 : ∀ t : ℝ, (((t - c : ℝ) : ℂ) - ε * Complex.I)⁻¹ -
      (((t - c : ℝ) : ℂ) - ((-ε : ℝ) : ℂ) * Complex.I)⁻¹ =
      ((2 * ε / ((t - c) ^ 2 + ε ^ 2) : ℝ) : ℂ) * Complex.I := by
    intro t
    have := inv_sub_inv_eq (t - c) ε hε
    push_cast at this ⊢
    rw [← this]
    ring_nf
  simp_rw [e2]
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    integral_two_eps_div c ε hε]



private theorem contDiffOn_segment_extend (a b : ℂ) :
    ContDiffOn ℝ 1 (Path.segment a b).extend (Icc 0 1) :=
  (by fun_prop : ContDiff ℝ 1 fun t : ℝ => (1 - t) • a + t • b).contDiffOn.congr fun t ht => by
    rw [Path.eqOn_extend_segment a b ht, AffineMap.lineMap_apply_module]

private theorem curveIntegrable_inv_sub {x y : ℂ} (γ : Path x y)
    (hγ : ContDiffOn ℝ 1 γ.extend (Icc 0 1)) {w : ℂ} (hw : w ∉ range γ) :
    CurveIntegrable (fun ζ => (ζ - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ) γ := by
  refine ContinuousOn.curveIntegrable_of_contDiffOn (s := range γ) ?_ hγ fun t => mem_range_self t
  refine ((continuousOn_id.sub continuousOn_const).inv₀ ?_).smul continuousOn_const
  intro ζ hζ hzero
  apply hw
  have hz' : ζ = w := sub_eq_zero.1 hzero
  rw [← hz']
  exact hζ

/-- **The winding number jumps across the segment.** For the closed curve made of a `C¹` path `A`
from `p₀` to `p₁` and the segment from `p₁` back to `p₀`, the winding numbers at points close to an
interior point of the segment, on its two sides, differ: the segment contributes nearly `±π i` on
each side, while the contribution of `A` is continuous there. -/
private theorem windingNumber_jump {p₀ p₁ : ℂ} (A : Path p₀ p₁)
    (hA : ContDiffOn ℝ 1 A.extend (Icc 0 1)) (hd : p₀ ≠ p₁) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hq : p₁ + c * (p₀ - p₁) ∉ range A) :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      Complex.windingNumber (A.trans (Path.segment p₁ p₀))
          (p₁ + c * (p₀ - p₁) + (ε : ℂ) * (Complex.I * (p₀ - p₁))) ≠
        Complex.windingNumber (A.trans (Path.segment p₁ p₀))
          (p₁ + c * (p₀ - p₁) + (-ε : ℝ) * (Complex.I * (p₀ - p₁))) := by
  have hd' : p₀ - p₁ ≠ 0 := sub_ne_zero.2 hd
  set q := p₁ + c * (p₀ - p₁) with hq_def
  set C := A.trans (Path.segment p₁ p₀) with hC_def
  set z : ℝ → ℂ := fun s => q + s * (Complex.I * (p₀ - p₁)) with hz_def
  set h : ℂ → ℂ := fun w => ∫ᶜ ζ in A, (1 / (ζ - w)) • ContinuousLinearMap.id ℂ ℂ with hh_def
  have hA' : A.IsPiecewiseC1 := Path.IsPiecewiseC1.of_contDiffOn hA
  have hopen : IsOpen (range A)ᶜ := (isCompact_range A.continuous).isClosed.isOpen_compl
  have hcont : ContinuousAt h q :=
    ((Complex.differentiableOn_curveIntegral_div_sub hA' (φ := fun _ => 1)
      continuousOn_const).differentiableAt (hopen.mem_nhds hq)).continuousAt
  have hzc : Continuous z := by
    simp only [hz_def]
    fun_prop
  have hz0 : z 0 = q := by simp [hz_def]
  have hzp : Tendsto z (𝓝[>] 0) (𝓝 q) := by
    rw [← hz0]
    exact hzc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzm : Tendsto (fun s => z (-s)) (𝓝[>] 0) (𝓝 q) := by
    have h1 := ((hzc.comp continuous_neg).tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have h2 : (z ∘ fun s : ℝ => -s) 0 = q := by simp [hz_def]
    rw [h2] at h1
    exact h1
  have hevA : ∀ᶠ ε in 𝓝[>] (0 : ℝ), z ε ∉ range A ∧ z (-ε) ∉ range A :=
    (hzp.eventually (hopen.mem_nhds hq)).and (hzm.eventually (hopen.mem_nhds hq))
  have hseg : ∀ s : ℝ, s ≠ 0 → z s ∉ range (Path.segment p₁ p₀) := by
    intro s hs hmem
    rw [Path.range_segment, segment_eq_image_lineMap] at hmem
    obtain ⟨θ, -, hθ⟩ := hmem
    rw [AffineMap.lineMap_apply_module, Complex.real_smul, Complex.real_smul] at hθ
    have : (((θ - c : ℝ) : ℂ) - s * Complex.I) * (p₀ - p₁) = 0 := by
      rw [← sub_eq_zero.2 hθ]
      simp only [hz_def, hq_def]
      push_cast
      ring
    rcases mul_eq_zero.1 this with h0 | h0
    · have := congrArg Complex.im h0
      simp only [Complex.ofReal_sub, Complex.sub_im, Complex.ofReal_im, sub_self,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
        add_zero, zero_sub, Complex.zero_im, neg_eq_zero] at this
      exact hs this
    · exact hd' h0
  have hsplit : ∀ w, w ∉ range A → w ∉ range (Path.segment p₁ p₀) →
      2 * π * Complex.I * Complex.windingNumber C w =
        h w + ∫ᶜ ζ in Path.segment p₁ p₀, (ζ - w)⁻¹ • ContinuousLinearMap.id ℂ ℂ := by
    intro w hwA hws
    rw [Complex.windingNumber, mul_inv_cancel_left₀ Complex.two_pi_I_ne_zero, hC_def,
      curveIntegral_trans (curveIntegrable_inv_sub A hA hwA)
        (curveIntegrable_inv_sub _ (contDiffOn_segment_extend p₁ p₀) hws)]
    simp only [hh_def, one_div]
  have hkey : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      2 * π * Complex.I * (Complex.windingNumber C (z ε) - Complex.windingNumber C (z (-ε))) =
        (h (z ε) - h (z (-ε))) +
          ((2 * (Real.arctan ((1 - c) / ε) + Real.arctan (c / ε)) : ℝ) : ℂ) * Complex.I := by
    filter_upwards [hevA, self_mem_nhdsWithin] with ε hε hεpos
    have hεpos' : (0 : ℝ) < ε := hεpos
    rw [mul_sub, hsplit _ hε.1 (hseg ε hεpos'.ne'),
      hsplit _ hε.2 (hseg (-ε) (neg_ne_zero.2 hεpos'.ne')), ← seg_diff p₀ p₁ hd c ε hεpos']
    simp only [hz_def, hq_def]
    ring
  have hlim : Tendsto (fun ε : ℝ => (h (z ε) - h (z (-ε))) +
      ((2 * (Real.arctan ((1 - c) / ε) + Real.arctan (c / ε)) : ℝ) : ℂ) * Complex.I)
      (𝓝[>] 0) (𝓝 ((h q - h q) + ((2 * (π / 2 + π / 2) : ℝ) : ℂ) * Complex.I)) := by
    have harc : ∀ a : ℝ, 0 < a → Tendsto (fun ε : ℝ => Real.arctan (a / ε)) (𝓝[>] 0)
        (𝓝 (π / 2)) := by
      intro a ha
      have : Tendsto (fun ε : ℝ => a / ε) (𝓝[>] 0) atTop := by
        simp only [div_eq_mul_inv]
        exact tendsto_inv_nhdsGT_zero.const_mul_atTop ha
      exact (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp this
    refine ((hcont.tendsto.comp hzp).sub (hcont.tendsto.comp hzm)).add
      (Tendsto.mul_const _ (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (((harc _ (by linarith)).add (harc _ hc0)).const_mul 2)))
  have hval : (h q - h q) + ((2 * (π / 2 + π / 2) : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I := by
    push_cast
    ring
  rw [hval] at hlim
  filter_upwards [hkey, (hlim.eventually_ne Complex.two_pi_I_ne_zero)] with ε h1 h2 heq
  rw [← h1, heq, sub_self, mul_zero] at h2
  exact h2 rfl

end

/-! ### Monotonicity of successive crossings -/

section

open Set Filter Topology Metric ComplexConjugate
open scoped NNReal

private theorem exists_pos_le_dist {K : Set ℂ} (hK : IsCompact K) {y : ℂ} (hy : y ∉ K) :
    ∃ ρ > 0, ∀ z ∈ K, ρ ≤ dist z y := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun z hz => absurd hz (notMem_empty z)⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne
    (continuous_id.dist continuous_const).continuousOn
  refine ⟨dist z₀ y, dist_pos.2 fun h => hy (h ▸ hz₀), fun z hz => ?_⟩
  have := hmin hz
  simpa using this

/-- The arc of a curve between two times, as a path. -/
private noncomputable def arcPath (φ : ℝ → ℂ) (hφc : Continuous φ) (t₀ t₁ : ℝ) :
    Path (φ t₀) (φ t₁) where
  toFun u := φ (t₀ + (u : ℝ) * (t₁ - t₀))
  continuous_toFun := hφc.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))
  source' := by simp
  target' := by simp

private theorem arcPath_extend {φ : ℝ → ℂ} (hφc : Continuous φ) (t₀ t₁ : ℝ) {u : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) : (arcPath φ hφc t₀ t₁).extend u = φ (t₀ + u * (t₁ - t₀)) := by
  rw [Path.extend_apply _ hu]
  rfl

private theorem range_arcPath {φ : ℝ → ℂ} (hφc : Continuous φ) {t₀ t₁ : ℝ} (h : t₀ < t₁) :
    range (arcPath φ hφc t₀ t₁) = φ '' Icc t₀ t₁ := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨t₀ + (u : ℝ) * (t₁ - t₀), ⟨?_, ?_⟩, rfl⟩
    · nlinarith [u.2.1]
    · nlinarith [u.2.2]
  · rintro ⟨τ, hτ, rfl⟩
    have hd : 0 < t₁ - t₀ := by linarith
    refine ⟨⟨(τ - t₀) / (t₁ - t₀), div_nonneg (by linarith [hτ.1]) hd.le,
      (div_le_one hd).2 (by linarith [hτ.2])⟩, ?_⟩
    change φ (t₀ + (τ - t₀) / (t₁ - t₀) * (t₁ - t₀)) = φ τ
    congr 1
    field_simp
    ring

private theorem contDiff_sol {G : ℂ → ℂ} (hG : Continuous G) {φ : ℝ → ℂ}
    (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) : ContDiff ℝ 1 φ := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  rw [contDiff_one_iff_deriv]
  refine ⟨fun t => (hφ t).differentiableAt, ?_⟩
  have : deriv φ = fun t => G (φ t) := funext fun t => (hφ t).deriv
  rw [this]
  exact hG.comp hφc

private theorem contDiffOn_arcPath {G : ℂ → ℂ} (hG : Continuous G) {φ : ℝ → ℂ}
    (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) (hφc : Continuous φ) (t₀ t₁ : ℝ) :
    ContDiffOn ℝ 1 (arcPath φ hφc t₀ t₁).extend (Icc 0 1) :=
  ((contDiff_sol hG hφ).comp (contDiff_const.add (contDiff_id.mul contDiff_const))).contDiffOn.congr
    fun _ hu => arcPath_extend hφc t₀ t₁ hu

private theorem dist_add_real_mul (y z : ℂ) (a : ℝ) : dist (y + (a : ℂ) * z) y = |a| * ‖z‖ := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]

namespace TData

variable {G : ℂ → ℂ} {p : ℂ} (T : TData G p)

private theorem ℓ_eq_lineMap : (T.ℓ : ℝ → ℂ) = ⇑(AffineMap.lineMap p (p + T.w) : ℝ →ᵃ[ℝ] ℂ) := by
  funext s
  rw [AffineMap.lineMap_apply_module', Complex.real_smul, ℓ]
  ring

private theorem segment_eq {s₀ s₁ : ℝ} (h : s₀ ≤ s₁) :
    segment ℝ (T.ℓ s₁) (T.ℓ s₀) = T.ℓ '' Icc s₀ s₁ := by
  rw [T.ℓ_eq_lineMap, ← image_segment, segment_eq_uIcc, uIcc_of_ge h]

private theorem g_combo (x y : ℂ) {a b : ℝ} (hab : a + b = 1) :
    T.g (a • x + b • y) = a * T.g x + b * T.g y := by
  simp only [g, Complex.real_smul]
  have hab' : (a : ℂ) + b = 1 := by exact_mod_cast hab
  have : (a : ℂ) * x + (b : ℂ) * y - p = (a : ℂ) * (x - p) + (b : ℂ) * (y - p) := by
    linear_combination p * hab'
  rw [this, add_mul, Complex.add_re, mul_assoc, mul_assoc, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]

private theorem convex_g_pos : Convex ℝ {z : ℂ | 0 < T.g z} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at hx hy ⊢
  rw [T.g_combo x y hab]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    rw [hab]
    simpa using hy
  · nlinarith [mul_pos ha' hx, mul_nonneg hb hy.le]

private theorem convex_g_neg : Convex ℝ {z : ℂ | T.g z < 0} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq] at hx hy ⊢
  rw [T.g_combo x y hab]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    rw [hab]
    simpa using hy
  · nlinarith [mul_pos ha' (neg_pos.2 hx), mul_nonneg hb (neg_pos.2 hy).le]

private theorem g_add (y : ℂ) (a : ℝ) : T.g (y + (a : ℂ) * G p) = T.g y + a * ‖G p‖ ^ 2 := by
  simp only [g]
  rw [show y + (a : ℂ) * G p - p = (y - p) + (a : ℂ) * G p by ring, add_mul, Complex.add_re,
    mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]

private theorem I_mul_ℓ_sub (s₀ s₁ : ℝ) :
    Complex.I * (T.ℓ s₀ - T.ℓ s₁) = ((s₁ - s₀ : ℝ) : ℂ) * G p := by
  simp only [ℓ, w]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem ℓ_mid (s₀ s₁ : ℝ) :
    T.ℓ s₁ + ((1 / 2 : ℝ) : ℂ) * (T.ℓ s₀ - T.ℓ s₁) = T.ℓ ((s₀ + s₁) / 2) := by
  simp only [ℓ]
  push_cast
  ring

private theorem local_sides {φ : ℝ → ℂ} (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) {τ₀ : ℝ}
    (h0 : φ τ₀ ∈ T.L) {ρ : ℝ} (hρ : 0 < ρ) : ∃ u₀ > 0, ∀ u, 0 < u → u ≤ u₀ →
      (T.g (φ (τ₀ - u)) < 0 ∧ dist (φ (τ₀ - u)) (φ τ₀) < ρ) ∧
      (0 < T.g (φ (τ₀ + u)) ∧ dist (φ (τ₀ + u)) (φ τ₀) < ρ) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hr := T.hr
  obtain ⟨u₁, hu₁, hcont⟩ := Metric.continuousAt_iff.1 hφc.continuousAt (min ρ (T.r / 2))
    (lt_min hρ (by linarith))
  refine ⟨u₁ / 2, half_pos hu₁, fun u hu hu' => ?_⟩
  have h2 := T.dist_p_le_of_mem_L h0
  have hclose : ∀ σ, |σ - τ₀| ≤ u → dist (φ σ) (φ τ₀) < min ρ (T.r / 2) := fun σ hσ =>
    hcont (by rw [Real.dist_eq]; linarith)
  have hin : ∀ σ ∈ Icc (τ₀ - u) (τ₀ + u), φ σ ∈ closedBall p T.r := by
    intro σ hσ
    have h1 := hclose σ (abs_le.2 ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
    rw [mem_closedBall]
    linarith [dist_triangle (φ σ) (φ τ₀) p, min_le_right ρ (T.r / 2)]
  have hg0 := (T.mem_L_iff.1 h0).1
  have hd : ∀ σ, |σ - τ₀| ≤ u → dist (φ σ) (φ τ₀) < ρ := fun σ hσ =>
    lt_of_lt_of_le (hclose σ hσ) (min_le_left _ _)
  refine ⟨⟨?_, hd _ (by rw [abs_of_nonpos (by linarith)]; linarith)⟩,
    ⟨?_, hd _ (by rw [abs_of_nonneg (by linarith)]; linarith)⟩⟩
  · have := T.g_strict hφ (a := τ₀ - u) (b := τ₀) (by linarith)
      fun σ hσ => hin σ ⟨hσ.1, by linarith [hσ.2]⟩
    linarith
  · have := T.g_strict hφ (a := τ₀) (b := τ₀ + u) (by linarith)
      fun σ hσ => hin σ ⟨by linarith [hσ.1], hσ.2⟩
    linarith

end TData

namespace TData

variable {G : ℂ → ℂ} {p : ℂ} (T : TData G p)

/-- **Monotonicity of crossings.** If a trajectory crosses the transversal at times `t₀ < t₁`, with
no crossing in between, at positions `s₀ < s₁`, then every later crossing lies beyond `s₁`. The
winding number of the closed curve made of the trajectory from `t₀` to `t₁` and the segment from
`φ t₁` back to `φ t₀` takes different values `a` and `b` on the two sides of the segment
(`windingNumber_jump`). The trajectory after `t₁` starts where it is `b` and never meets the curve
again, while it is `a` on the part of the transversal before `s₀`. -/
private theorem crossing_monotone {K : ℝ≥0} (hG : LipschitzWith K G) {φ : ℝ → ℂ}
    (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) {t₀ t₁ : ℝ} (h01 : t₀ < t₁)
    (h0 : φ t₀ ∈ T.L) (h1 : φ t₁ ∈ T.L) (hno : ∀ τ ∈ Ioo t₀ t₁, φ τ ∉ T.L)
    (hlt : T.pos (φ t₀) < T.pos (φ t₁)) {t₂ : ℝ} (h12 : t₁ < t₂) (h2 : φ t₂ ∈ T.L) :
    T.pos (φ t₁) < T.pos (φ t₂) := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  have hn := T.norm_pos
  have hr := T.hr
  set s₀ := T.pos (φ t₀) with hs₀_def
  set s₁ := T.pos (φ t₁) with hs₁_def
  have hp₀ : φ t₀ = T.ℓ s₀ := (T.ℓ_pos (T.mem_L_iff.1 h0).1).symm
  have hp₁ : φ t₁ = T.ℓ s₁ := (T.ℓ_pos (T.mem_L_iff.1 h1).1).symm
  have hs₀ : |s₀| ≤ T.δ := (T.mem_L_iff.1 h0).2
  have hs₁ : |s₁| ≤ T.δ := (T.mem_L_iff.1 h1).2
  have hne : φ t₀ ≠ φ t₁ := fun h => by
    rw [hp₀, hp₁] at h
    exact hlt.ne (T.ℓ_injective h)
  have hg₀ : T.g (φ t₀) = 0 := (T.mem_L_iff.1 h0).1
  have hg₁ : T.g (φ t₁) = 0 := (T.mem_L_iff.1 h1).1
  -- crossings on the arc
  have hF1 : ∀ τ ∈ Icc t₀ t₁, φ τ ∈ T.L → τ = t₀ ∨ τ = t₁ := by
    intro τ hτ hL
    rcases hτ.1.eq_or_lt with h | h
    · exact Or.inl h.symm
    rcases hτ.2.eq_or_lt with h' | h'
    · exact Or.inr h'
    exact absurd hL (hno τ ⟨h, h'⟩)
  have hF2 : ∀ τ ∈ Icc t₀ t₁, ∀ σ, |σ| ≤ T.δ → φ τ = T.ℓ σ → σ = s₀ ∨ σ = s₁ := by
    intro τ hτ σ hσ heq
    rcases hF1 τ hτ (heq ▸ T.ℓ_mem_L hσ) with rfl | rfl
    · left
      rw [hs₀_def, heq, T.pos_ℓ]
    · right
      rw [hs₁_def, heq, T.pos_ℓ]
  -- the closed curve
  set A := arcPath φ hφc t₀ t₁ with hA_def
  have hAc : ContDiffOn ℝ 1 A.extend (Icc 0 1) := contDiffOn_arcPath hG.continuous hφ hφc t₀ t₁
  have hArange : range A = φ '' Icc t₀ t₁ := range_arcPath hφc h01
  set C := A.trans (Path.segment (φ t₁) (φ t₀)) with hC_def
  have hC : C.IsPiecewiseC1 :=
    (Path.IsPiecewiseC1.of_contDiffOn hAc).trans (Path.isPiecewiseC1_segment _ _)
  have hCrange : range C = φ '' Icc t₀ t₁ ∪ T.ℓ '' Icc s₀ s₁ := by
    rw [hC_def, Path.trans_range, hArange, Path.range_segment, hp₁, hp₀, T.segment_eq hlt.le]
  set W := Complex.windingNumber C with hW_def
  have hWc : ∀ S : Set ℂ, IsPreconnected S → S ⊆ (range C)ᶜ → ∀ z ∈ S, ∀ w ∈ S, W w = W z :=
    fun S hS hSC z hz w hw => Complex.windingNumber_eq_of_isPreconnected hC hS hSC hz hw
  have hCg : ∀ z ∈ range C, T.g z ≠ 0 → ∃ τ ∈ Icc t₀ t₁, φ τ = z := by
    intro z hz hgz
    rw [hCrange] at hz
    rcases hz with hz | ⟨σ, -, rfl⟩
    · exact hz
    · exact absurd (T.g_ℓ σ) hgz
  have hHBpos : ∀ y ρ, IsPreconnected (ball y ρ ∩ {z | 0 < T.g z}) := fun y ρ =>
    ((convex_ball y ρ).inter T.convex_g_pos).isPreconnected
  have hHBneg : ∀ y ρ, IsPreconnected (ball y ρ ∩ {z | T.g z < 0}) := fun y ρ =>
    ((convex_ball y ρ).inter T.convex_g_neg).isPreconnected
  -- the region near `φ t₁`
  obtain ⟨u₁, hu₁, hside₁⟩ := T.local_sides hφ h1 one_pos
  set σ₁ := min u₁ (t₁ - t₀) with hσ₁_def
  have hσ₁ : 0 < σ₁ := lt_min hu₁ (by linarith)
  have hp₁K₁ : φ t₁ ∉ φ '' Icc t₀ (t₁ - σ₁) := by
    rintro ⟨τ, hτ, heq⟩
    have hτ' : τ ∈ Icc t₀ t₁ := ⟨hτ.1, by linarith [hτ.2]⟩
    rcases hF1 τ hτ' (heq ▸ h1) with rfl | rfl
    · exact hne heq
    · linarith [hτ.2]
  obtain ⟨ρ₁, hρ₁, hρ₁K⟩ := exists_pos_le_dist (isCompact_Icc.image hφc) hp₁K₁
  have hHB₁ : ball (φ t₁) ρ₁ ∩ {z | 0 < T.g z} ⊆ (range C)ᶜ := by
    rintro z ⟨hzb, hzg⟩ hzC
    simp only [mem_ofPred_eq] at hzg
    obtain ⟨τ, hτ, rfl⟩ := hCg z hzC (ne_of_gt hzg)
    rcases le_or_gt τ (t₁ - σ₁) with hτ' | hτ'
    · have := hρ₁K (φ τ) ⟨τ, ⟨hτ.1, hτ'⟩, rfl⟩
      rw [mem_ball] at hzb
      linarith
    · rcases hτ.2.eq_or_lt with h | h
      · rw [h, hg₁] at hzg
        exact lt_irrefl _ hzg
      · have := (hside₁ (t₁ - τ) (by linarith) (by linarith [min_le_left u₁ (t₁ - t₀)])).1.1
        rw [sub_sub_cancel] at this
        linarith
  -- the region near `φ t₀`
  obtain ⟨u₀, hu₀, hside₀⟩ := T.local_sides hφ h0 one_pos
  set σ₀ := min u₀ (t₁ - t₀) with hσ₀_def
  have hσ₀ : 0 < σ₀ := lt_min hu₀ (by linarith)
  have hp₀K₀ : φ t₀ ∉ φ '' Icc (t₀ + σ₀) t₁ := by
    rintro ⟨τ, hτ, heq⟩
    have hτ' : τ ∈ Icc t₀ t₁ := ⟨by linarith [hτ.1], hτ.2⟩
    rcases hF1 τ hτ' (heq ▸ h0) with rfl | rfl
    · linarith [hτ.1]
    · exact hne heq.symm
  obtain ⟨ρ₀, hρ₀, hρ₀K⟩ := exists_pos_le_dist (isCompact_Icc.image hφc) hp₀K₀
  have hHB₀ : ball (φ t₀) ρ₀ ∩ {z | T.g z < 0} ⊆ (range C)ᶜ := by
    rintro z ⟨hzb, hzg⟩ hzC
    simp only [mem_ofPred_eq] at hzg
    obtain ⟨τ, hτ, rfl⟩ := hCg z hzC (ne_of_lt hzg)
    rcases le_or_gt (t₀ + σ₀) τ with hτ' | hτ'
    · have := hρ₀K (φ τ) ⟨τ, ⟨hτ', hτ.2⟩, rfl⟩
      rw [mem_ball] at hzb
      linarith
    · rcases hτ.1.eq_or_lt with h | h
      · rw [← h, hg₀] at hzg
        exact lt_irrefl _ hzg
      · have := (hside₀ (τ - t₀) (by linarith) (by linarith [min_le_left u₀ (t₁ - t₀)])).2.1
        rw [add_sub_cancel] at this
        linarith
  -- the open segment
  have hRA_ne : (range A).Nonempty := range_nonempty A
  set ρ : ℝ → ℝ := fun σ => infDist (T.ℓ σ) (range A) with hρ_def
  have hρc : Continuous ρ := (continuous_infDist_pt _).comp T.continuous_ℓ
  have hAcl : IsClosed (range A) := (isCompact_range A.continuous).isClosed
  have hσδ : ∀ σ ∈ Icc s₀ s₁, |σ| ≤ T.δ := fun σ hσ =>
    abs_le.2 ⟨by linarith [(abs_le.1 hs₀).1, hσ.1], by linarith [(abs_le.1 hs₁).2, hσ.2]⟩
  have hℓnotA : ∀ σ ∈ Ioo s₀ s₁, T.ℓ σ ∉ range A := by
    intro σ hσ hmem
    rw [hArange] at hmem
    obtain ⟨τ, hτ, heq⟩ := hmem
    rcases hF2 τ hτ σ (hσδ σ (Ioo_subset_Icc_self hσ)) heq with h | h
    · linarith [hσ.1]
    · linarith [hσ.2]
  have hρpos : ∀ σ ∈ Ioo s₀ s₁, 0 < ρ σ := fun σ hσ =>
    (infDist_pos_iff_notMem_closure hRA_ne).1 (by rw [hAcl.closure_eq]; exact hℓnotA σ hσ)
  have hρle : ∀ σ τ, τ ∈ Icc t₀ t₁ → ρ σ ≤ dist (T.ℓ σ) (φ τ) := fun σ τ hτ =>
    infDist_le_dist_of_mem (by rw [hArange]; exact ⟨τ, hτ, rfl⟩)
  have hHBσ : ∀ σ, ∀ z ∈ ball (T.ℓ σ) (ρ σ), T.g z ≠ 0 → z ∉ range C := by
    intro σ z hz hgz hzC
    obtain ⟨τ, hτ, rfl⟩ := hCg z hzC hgz
    have := hρle σ τ hτ
    rw [mem_ball, dist_comm] at hz
    linarith
  -- the curves `cp` and `cm` beside the open segment
  set cp : ℝ → ℂ := fun σ => T.ℓ σ + ((ρ σ / (2 * ‖G p‖) : ℝ) : ℂ) * G p with hcp_def
  set cm : ℝ → ℂ := fun σ => T.ℓ σ + ((-(ρ σ / (2 * ‖G p‖)) : ℝ) : ℂ) * G p with hcm_def
  have hℓc := T.continuous_ℓ
  have hcpc : Continuous cp := by
    simp only [hcp_def]
    fun_prop
  have hcmc : Continuous cm := by
    simp only [hcm_def]
    fun_prop
  have hcp_g : ∀ σ ∈ Ioo s₀ s₁, 0 < T.g (cp σ) := by
    intro σ hσ
    simp only [hcp_def]
    rw [T.g_add, T.g_ℓ]
    have := hρpos σ hσ
    positivity
  have hcm_g : ∀ σ ∈ Ioo s₀ s₁, T.g (cm σ) < 0 := by
    intro σ hσ
    simp only [hcm_def]
    rw [T.g_add, T.g_ℓ]
    have := hρpos σ hσ
    have : 0 < ρ σ / (2 * ‖G p‖) * ‖G p‖ ^ 2 := by positivity
    linarith
  have hcp_d : ∀ σ ∈ Ioo s₀ s₁, dist (cp σ) (T.ℓ σ) < ρ σ := by
    intro σ hσ
    simp only [hcp_def]
    have := hρpos σ hσ
    rw [dist_add_real_mul, abs_of_nonneg (by positivity)]
    field_simp
    linarith
  have hcm_d : ∀ σ ∈ Ioo s₀ s₁, dist (cm σ) (T.ℓ σ) < ρ σ := by
    intro σ hσ
    simp only [hcm_def]
    have := hρpos σ hσ
    rw [dist_add_real_mul, abs_neg, abs_of_nonneg (by positivity)]
    field_simp
    linarith
  have hcp_C : ∀ σ ∈ Ioo s₀ s₁, cp σ ∉ range C := fun σ hσ =>
    hHBσ σ _ (mem_ball.2 (hcp_d σ hσ)) (hcp_g σ hσ).ne'
  have hcm_C : ∀ σ ∈ Ioo s₀ s₁, cm σ ∉ range C := fun σ hσ =>
    hHBσ σ _ (mem_ball.2 (hcm_d σ hσ)) (hcm_g σ hσ).ne
  have hWcp : ∀ σ ∈ Ioo s₀ s₁, ∀ σ' ∈ Ioo s₀ s₁, W (cp σ') = W (cp σ) := by
    intro σ hσ σ' hσ'
    exact hWc (cp '' Ioo s₀ s₁) (isPreconnected_Ioo.image cp hcpc.continuousOn)
      (by rintro _ ⟨τ, hτ, rfl⟩; exact hcp_C τ hτ) _ ⟨σ, hσ, rfl⟩ _ ⟨σ', hσ', rfl⟩
  have hWcm : ∀ σ ∈ Ioo s₀ s₁, ∀ σ' ∈ Ioo s₀ s₁, W (cm σ') = W (cm σ) := by
    intro σ hσ σ' hσ'
    exact hWc (cm '' Ioo s₀ s₁) (isPreconnected_Ioo.image cm hcmc.continuousOn)
      (by rintro _ ⟨τ, hτ, rfl⟩; exact hcm_C τ hτ) _ ⟨σ, hσ, rfl⟩ _ ⟨σ', hσ', rfl⟩
  have hWHBneg : ∀ σ ∈ Ioo s₀ s₁, ∀ z ∈ ball (T.ℓ σ) (ρ σ), T.g z < 0 → W z = W (cm σ) := by
    intro σ hσ z hz hgz
    exact hWc _ (hHBneg _ _) (fun y hy => hHBσ σ y hy.1 (ne_of_lt hy.2)) _
      ⟨mem_ball.2 (hcm_d σ hσ), hcm_g σ hσ⟩ _ ⟨hz, hgz⟩
  have hWHBpos : ∀ σ ∈ Ioo s₀ s₁, ∀ z ∈ ball (T.ℓ σ) (ρ σ), 0 < T.g z → W z = W (cp σ) := by
    intro σ hσ z hz hgz
    exact hWc _ (hHBpos _ _) (fun y hy => hHBσ σ y hy.1 (ne_of_gt hy.2)) _
      ⟨mem_ball.2 (hcp_d σ hσ), hcp_g σ hσ⟩ _ ⟨hz, hgz⟩
  -- the jump of the winding number across the segment
  set σm := (s₀ + s₁) / 2 with hσm_def
  have hσm : σm ∈ Ioo s₀ s₁ := ⟨by linarith, by linarith⟩
  have hq : φ t₁ + ((1 / 2 : ℝ) : ℂ) * (φ t₀ - φ t₁) = T.ℓ σm := by
    rw [hp₀, hp₁, T.ℓ_mid]
  have hIq : Complex.I * (φ t₀ - φ t₁) = ((s₁ - s₀ : ℝ) : ℂ) * G p := by
    rw [hp₀, hp₁, T.I_mul_ℓ_sub]
  have hjump := windingNumber_jump A hAc hne (c := 1 / 2) (by norm_num) (by norm_num)
    (by rw [hq]; exact hℓnotA σm hσm)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε * (s₁ - s₀) * ‖G p‖ < ρ σm := by
    have hcont : Continuous fun ε : ℝ => ε * (s₁ - s₀) * ‖G p‖ := by fun_prop
    have h0' : (fun ε : ℝ => ε * (s₁ - s₀) * ‖G p‖) 0 < ρ σm := by
      simp only [zero_mul]
      exact hρpos σm hσm
    exact (hcont.continuousAt.eventually_lt continuousAt_const h0').filter_mono
      nhdsWithin_le_nhds
  obtain ⟨ε, hεjump, hεsmall, hεpos⟩ := (hjump.and (hsmall.and self_mem_nhdsWithin)).exists
  have hεpos' : (0 : ℝ) < ε := hεpos
  have hab : W (cm σm) ≠ W (cp σm) := by
    have e1 : φ t₁ + ((1 / 2 : ℝ) : ℂ) * (φ t₀ - φ t₁) + (ε : ℂ) * (Complex.I * (φ t₀ - φ t₁)) =
        T.ℓ σm + ((ε * (s₁ - s₀) : ℝ) : ℂ) * G p := by
      rw [hq, hIq]
      push_cast
      ring
    have e2 : φ t₁ + ((1 / 2 : ℝ) : ℂ) * (φ t₀ - φ t₁) +
        ((-ε : ℝ) : ℂ) * (Complex.I * (φ t₀ - φ t₁)) =
        T.ℓ σm + ((-(ε * (s₁ - s₀)) : ℝ) : ℂ) * G p := by
      rw [hq, hIq]
      push_cast
      ring
    have hd01 : 0 < s₁ - s₀ := by linarith
    have hplus : W (T.ℓ σm + ((ε * (s₁ - s₀) : ℝ) : ℂ) * G p) = W (cp σm) := by
      refine hWHBpos σm hσm _ ?_ ?_
      · rw [mem_ball, dist_add_real_mul, abs_of_nonneg (by positivity)]
        exact hεsmall
      · rw [T.g_add, T.g_ℓ]
        positivity
    have hminus : W (T.ℓ σm + ((-(ε * (s₁ - s₀)) : ℝ) : ℂ) * G p) = W (cm σm) := by
      refine hWHBneg σm hσm _ ?_ ?_
      · rw [mem_ball, dist_add_real_mul, abs_neg, abs_of_nonneg (by positivity)]
        exact hεsmall
      · rw [T.g_add, T.g_ℓ]
        have : 0 < ε * (s₁ - s₀) * ‖G p‖ ^ 2 := by positivity
        linarith
    intro h
    apply hεjump
    rw [hW_def] at hplus hminus h
    rw [e1, e2, hplus, hminus, h]
  set a := W (cm σm) with ha_def
  set b := W (cp σm) with hb_def
  -- `W = b` beside `φ t₁` on the positive side
  have hWHB₁ : ∀ z ∈ ball (φ t₁) ρ₁, 0 < T.g z → W z = b := by
    set σn := s₁ - min ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖)) with hσn_def
    have hmin1 := min_le_left ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖))
    have hmin2 := min_le_right ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖))
    have hminpos : 0 < min ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖)) :=
      lt_min (by linarith) (by positivity)
    have hσn : σn ∈ Ioo s₀ s₁ := ⟨by linarith, by linarith⟩
    have hd1 : dist (T.ℓ σn) (φ t₁) = min ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖)) * ‖G p‖ := by
      rw [hp₁, T.dist_ℓ, hσn_def, show s₁ - min ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖)) - s₁ =
        -min ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖)) by ring, abs_neg, abs_of_pos hminpos]
    have hd2 : min ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖)) * ‖G p‖ ≤ ρ₁ / 2 := by
      calc min ((s₁ - s₀) / 2) (ρ₁ / (2 * ‖G p‖)) * ‖G p‖ ≤ ρ₁ / (2 * ‖G p‖) * ‖G p‖ :=
            mul_le_mul_of_nonneg_right hmin2 hn.le
        _ = ρ₁ / 2 := by field_simp
    have hρn : ρ σn ≤ dist (T.ℓ σn) (φ t₁) := hρle σn t₁ ⟨h01.le, le_rfl⟩
    have hcpn : cp σn ∈ ball (φ t₁) ρ₁ ∩ {z | 0 < T.g z} := by
      refine ⟨?_, hcp_g σn hσn⟩
      rw [mem_ball]
      have := hcp_d σn hσn
      linarith [dist_triangle (cp σn) (T.ℓ σn) (φ t₁)]
    intro z hz hgz
    rw [hb_def, hWcp σn hσn σm hσm]
    exact hWc _ (hHBpos _ _) hHB₁ _ hcpn _ ⟨hz, hgz⟩
  -- `W = a` beside `φ t₀` on the negative side
  have hWHB₀ : ∀ z ∈ ball (φ t₀) ρ₀, T.g z < 0 → W z = a := by
    set σn := s₀ + min ((s₁ - s₀) / 2) (ρ₀ / (2 * ‖G p‖)) with hσn_def
    have hmin1 := min_le_left ((s₁ - s₀) / 2) (ρ₀ / (2 * ‖G p‖))
    have hmin2 := min_le_right ((s₁ - s₀) / 2) (ρ₀ / (2 * ‖G p‖))
    have hminpos : 0 < min ((s₁ - s₀) / 2) (ρ₀ / (2 * ‖G p‖)) :=
      lt_min (by linarith) (by positivity)
    have hσn : σn ∈ Ioo s₀ s₁ := ⟨by linarith, by linarith⟩
    have hd1 : dist (T.ℓ σn) (φ t₀) = min ((s₁ - s₀) / 2) (ρ₀ / (2 * ‖G p‖)) * ‖G p‖ := by
      rw [hp₀, T.dist_ℓ, hσn_def, add_sub_cancel_left, abs_of_pos hminpos]
    have hd2 : min ((s₁ - s₀) / 2) (ρ₀ / (2 * ‖G p‖)) * ‖G p‖ ≤ ρ₀ / 2 := by
      calc min ((s₁ - s₀) / 2) (ρ₀ / (2 * ‖G p‖)) * ‖G p‖ ≤ ρ₀ / (2 * ‖G p‖) * ‖G p‖ :=
            mul_le_mul_of_nonneg_right hmin2 hn.le
        _ = ρ₀ / 2 := by field_simp
    have hρn : ρ σn ≤ dist (T.ℓ σn) (φ t₀) := hρle σn t₀ ⟨le_rfl, h01.le⟩
    have hcmn : cm σn ∈ ball (φ t₀) ρ₀ ∩ {z | T.g z < 0} := by
      refine ⟨?_, hcm_g σn hσn⟩
      rw [mem_ball]
      have := hcm_d σn hσn
      linarith [dist_triangle (cm σn) (T.ℓ σn) (φ t₀)]
    intro z hz hgz
    rw [ha_def, hWcm σn hσn σm hσm]
    exact hWc _ (hHBneg _ _) hHB₀ _ hcmn _ ⟨hz, hgz⟩
  have hWHBσ : ∀ σ ∈ Ioo s₀ s₁, ∀ z ∈ ball (T.ℓ σ) (ρ σ), T.g z < 0 → W z = a := by
    intro σ hσ z hz hgz
    rw [hWHBneg σ hσ z hz hgz, ha_def, hWcm σm hσm σ hσ]
  -- the trajectory after `t₁` starts on the positive side of `φ t₁`
  obtain ⟨v₁, hv₁, hsideP⟩ := T.local_sides hφ h1 hρ₁
  have hstart : ∀ u, 0 < u → u ≤ v₁ → φ (t₁ + u) ∉ range C ∧ W (φ (t₁ + u)) = b := by
    intro u hu hu'
    have hs := (hsideP u hu hu').2
    exact ⟨hHB₁ ⟨mem_ball.2 hs.2, hs.1⟩, hWHB₁ _ (mem_ball.2 hs.2) hs.1⟩
  -- the trajectory never returns to the curve
  have hfree : ∀ τ, t₁ < τ → φ τ ∉ range C := by
    by_contra hcon
    push Not at hcon
    obtain ⟨τ', hτ', hτ'C⟩ := hcon
    set E := Ici (t₁ + v₁) ∩ φ ⁻¹' (range C) with hE_def
    have hEcl : IsClosed E :=
      isClosed_Ici.inter ((isCompact_range C.continuous).isClosed.preimage hφc)
    have hτ'E : τ' ∈ E := by
      refine ⟨?_, hτ'C⟩
      by_contra hlt'
      simp only [mem_Ici, not_le] at hlt'
      exact (hstart (τ' - t₁) (by linarith) (by linarith)).1 (by rwa [add_sub_cancel])
    have hEbdd : BddBelow E := ⟨t₁ + v₁, fun x hx => hx.1⟩
    have htE : sInf E ∈ E := hEcl.csInf_mem ⟨τ', hτ'E⟩ hEbdd
    set tS := sInf E with htS_def
    have htS : t₁ + v₁ < tS := by
      refine lt_of_le_of_ne htE.1 fun h => ?_
      have := htE.2
      rw [← h] at this
      exact (hstart v₁ hv₁ le_rfl).1 this
    have hgap : ∀ τ ∈ Ioo t₁ tS, φ τ ∉ range C := by
      intro τ hτ hτC
      rcases le_or_gt τ (t₁ + v₁) with h | h
      · exact (hstart (τ - t₁) (by linarith [hτ.1]) (by linarith)).1 (by rwa [add_sub_cancel])
      · exact absurd (csInf_le hEbdd ⟨h.le, hτC⟩) (not_le.2 hτ.2)
    have hWgap : ∀ τ ∈ Ioo t₁ tS, W (φ τ) = b := by
      intro τ hτ
      rw [← (hstart v₁ hv₁ le_rfl).2]
      exact hWc (φ '' Ioo t₁ tS) (isPreconnected_Ioo.image φ hφc.continuousOn)
        (by rintro _ ⟨σ, hσ, rfl⟩; exact hgap σ hσ) _ ⟨t₁ + v₁, ⟨by linarith, htS⟩, rfl⟩
        _ ⟨τ, hτ, rfl⟩
    by_cases hAS : φ tS ∈ φ '' Icc t₀ t₁
    · obtain ⟨τ', hτ', heq⟩ := hAS
      rcases hτ'.1.eq_or_lt with h | h
      · -- the trajectory returns to `φ t₀`
        have heq' : φ tS = φ t₀ := by rw [← heq, ← h]
        obtain ⟨w₀, hw₀, hsideQ⟩ := T.local_sides hφ h0 hρ₀
        set u := min w₀ ((tS - t₁) / 2) with hu_def
        have hu : 0 < u := lt_min hw₀ (by linarith)
        have hu1 := min_le_left w₀ ((tS - t₁) / 2)
        have hu2 := min_le_right w₀ ((tS - t₁) / 2)
        have key : φ (tS - u) = φ (t₀ - u) := by
          have := sol_shift hG hφ hφ (a := tS) (b := t₀) heq' (-u)
          simpa [sub_eq_add_neg] using this
        have hs := (hsideQ u hu hu1).1
        have hWa : W (φ (t₀ - u)) = a := hWHB₀ _ (mem_ball.2 hs.2) hs.1
        have hWb : W (φ (tS - u)) = b := hWgap _ ⟨by linarith, by linarith⟩
        rw [key, hWa] at hWb
        exact hab hWb
      · -- the trajectory meets the arc at an interior or final point
        set u := min ((τ' - t₀) / 2) ((tS - t₁) / 2) with hu_def
        have hu : 0 < u := lt_min (by linarith) (by linarith)
        have hu1 := min_le_left ((τ' - t₀) / 2) ((tS - t₁) / 2)
        have hu2 := min_le_right ((τ' - t₀) / 2) ((tS - t₁) / 2)
        have key : φ (tS - u) = φ (τ' - u) := by
          have := sol_shift hG hφ hφ (a := tS) (b := τ') heq.symm (-u)
          simpa [sub_eq_add_neg] using this
        have hmem : φ (τ' - u) ∈ range C := by
          rw [hCrange]
          exact Or.inl ⟨τ' - u, ⟨by linarith, by linarith [hτ'.2]⟩, rfl⟩
        exact hgap (tS - u) ⟨by linarith, by linarith⟩ (key ▸ hmem)
    · -- the trajectory meets the open segment
      have hseg : φ tS ∈ T.ℓ '' Icc s₀ s₁ := by
        have := htE.2
        simp only [mem_preimage] at this
        rw [hCrange] at this
        rcases this with h | h
        · exact absurd h hAS
        · exact h
      obtain ⟨σ, hσ, heq⟩ := hseg
      have hσ' : σ ∈ Ioo s₀ s₁ := by
        refine ⟨lt_of_le_of_ne hσ.1 ?_, lt_of_le_of_ne hσ.2 ?_⟩
        · rintro rfl
          exact hAS ⟨t₀, ⟨le_rfl, h01.le⟩, by rw [← heq, hp₀]⟩
        · rintro rfl
          exact hAS ⟨t₁, ⟨h01.le, le_rfl⟩, by rw [← heq, hp₁]⟩
      have hLS : φ tS ∈ T.L := heq ▸ T.ℓ_mem_L (hσδ σ hσ)
      obtain ⟨w₁, hw₁, hsideS⟩ := T.local_sides hφ hLS (hρpos σ hσ')
      set u := min w₁ ((tS - t₁) / 2) with hu_def
      have hu : 0 < u := lt_min hw₁ (by linarith)
      have hu1 := min_le_left w₁ ((tS - t₁) / 2)
      have hu2 := min_le_right w₁ ((tS - t₁) / 2)
      have hs := (hsideS u hu hu1).1
      have hWa : W (φ (tS - u)) = a :=
        hWHBσ σ hσ' _ (by rw [mem_ball, heq]; exact hs.2) hs.1
      have hWb : W (φ (tS - u)) = b := hWgap _ ⟨by linarith, by linarith⟩
      exact hab (hWa.symm.trans hWb)
  -- the winding number along the rest of the trajectory
  have hWt₂ : W (φ t₂) = b := by
    rw [← (hstart v₁ hv₁ le_rfl).2]
    exact hWc (φ '' Ioi t₁) (isPreconnected_Ioi.image φ hφc.continuousOn)
      (by rintro _ ⟨σ, hσ, rfl⟩; exact hfree σ hσ) _ ⟨t₁ + v₁, by simp only [mem_Ioi]; linarith,
        rfl⟩ _ ⟨t₂, h12, rfl⟩
  -- conclusion
  by_contra hle
  push Not at hle
  set s₂ := T.pos (φ t₂) with hs₂_def
  have hp₂ : φ t₂ = T.ℓ s₂ := (T.ℓ_pos (T.mem_L_iff.1 h2).1).symm
  have hs₂ : |s₂| ≤ T.δ := (T.mem_L_iff.1 h2).2
  have hs₂₀ : s₂ < s₀ := by
    by_contra h'
    push Not at h'
    apply hfree t₂ h12
    rw [hCrange, hp₂]
    exact Or.inr ⟨s₂, ⟨h', hle⟩, rfl⟩
  -- the part of the transversal before `φ t₀` misses the curve
  have hΛ : T.ℓ '' Ico (-T.δ) s₀ ⊆ (range C)ᶜ := by
    rintro _ ⟨σ, hσ, rfl⟩ hmem
    have hσabs : |σ| ≤ T.δ := abs_le.2 ⟨hσ.1, by linarith [(abs_le.1 hs₀).2, hσ.2]⟩
    rw [hCrange] at hmem
    rcases hmem with ⟨τ, hτ, heq⟩ | ⟨σ', hσ', heq⟩
    · rcases hF2 τ hτ σ hσabs heq with h | h
      · linarith [hσ.2]
      · linarith [hσ.2]
    · have := T.ℓ_injective heq
      linarith [hσ.2, hσ'.1]
  set κ := min ((s₀ - s₂) / 2) (ρ₀ / (4 * ‖G p‖)) with hκ_def
  have hκ1 := min_le_left ((s₀ - s₂) / 2) (ρ₀ / (4 * ‖G p‖))
  have hκ2 := min_le_right ((s₀ - s₂) / 2) (ρ₀ / (4 * ‖G p‖))
  have hκ : 0 < κ := lt_min (by linarith) (by positivity)
  set y₀ := T.ℓ (s₀ - κ) with hy₀_def
  have hy₀Λ : y₀ ∈ T.ℓ '' Ico (-T.δ) s₀ :=
    ⟨s₀ - κ, ⟨by linarith [(abs_le.1 hs₂).1], by linarith⟩, rfl⟩
  set ε₀ := ρ₀ / (4 * ‖G p‖) with hε₀_def
  have hε₀ : 0 < ε₀ := by positivity
  have hdy₀ : dist y₀ (φ t₀) = κ * ‖G p‖ := by
    rw [hy₀_def, hp₀, T.dist_ℓ, show s₀ - κ - s₀ = -κ by ring, abs_neg, abs_of_pos hκ]
  have hκn : κ * ‖G p‖ ≤ ρ₀ / 4 := by
    calc κ * ‖G p‖ ≤ ρ₀ / (4 * ‖G p‖) * ‖G p‖ := mul_le_mul_of_nonneg_right hκ2 hn.le
      _ = ρ₀ / 4 := by field_simp
  have hε₀n : ε₀ * ‖G p‖ = ρ₀ / 4 := by
    rw [hε₀_def]
    field_simp
  set y₁ := y₀ + ((-ε₀ : ℝ) : ℂ) * G p with hy₁_def
  have hseg_sub : segment ℝ y₀ y₁ ⊆ (range C)ᶜ := by
    rw [segment_eq_image']
    rintro _ ⟨θ, hθ, rfl⟩
    dsimp only
    have hz : y₀ + θ • (y₁ - y₀) = y₀ + ((-(θ * ε₀)) : ℝ) * G p := by
      rw [hy₁_def, Complex.real_smul]
      push_cast
      ring
    rw [hz]
    rcases hθ.1.eq_or_lt with h | h
    · rw [← h]
      simp only [zero_mul, neg_zero, Complex.ofReal_zero, add_zero]
      exact hΛ hy₀Λ
    · apply hHB₀
      refine ⟨?_, ?_⟩
      · rw [mem_ball]
        have hd := dist_add_real_mul y₀ (G p) (-(θ * ε₀))
        rw [abs_neg, abs_of_pos (mul_pos h hε₀)] at hd
        have : θ * ε₀ * ‖G p‖ ≤ ε₀ * ‖G p‖ := by
          have := hθ.2
          have : 0 ≤ ε₀ * ‖G p‖ := by positivity
          nlinarith
        linarith [dist_triangle (y₀ + ((-(θ * ε₀) : ℝ) : ℂ) * G p) y₀ (φ t₀)]
      · simp only [mem_ofPred_eq]
        rw [T.g_add, hy₀_def, T.g_ℓ]
        have : 0 < θ * ε₀ * ‖G p‖ ^ 2 := by positivity
        linarith
  have hWy₁ : W y₁ = a := by
    apply hWHB₀
    · rw [mem_ball, hy₁_def]
      have hd := dist_add_real_mul y₀ (G p) (-ε₀)
      rw [abs_neg, abs_of_pos hε₀] at hd
      linarith [dist_triangle (y₀ + ((-ε₀ : ℝ) : ℂ) * G p) y₀ (φ t₀)]
    · rw [hy₁_def, T.g_add, hy₀_def, T.g_ℓ]
      have : 0 < ε₀ * ‖G p‖ ^ 2 := by positivity
      linarith
  have hWy₀ : W y₀ = a := by
    rw [← hWy₁]
    exact hWc _ ((convex_segment y₀ y₁).isPreconnected) hseg_sub _ (right_mem_segment ℝ y₀ y₁)
      _ (left_mem_segment ℝ y₀ y₁)
  have hWΛ : W (φ t₂) = a := by
    rw [← hWy₀]
    exact hWc _ ((isPreconnected_Ico).image T.ℓ T.continuous_ℓ.continuousOn) hΛ _ hy₀Λ _
      (by rw [hp₂]; exact ⟨s₂, ⟨(abs_le.1 hs₂).1, hs₂₀⟩, rfl⟩)
  exact hab (hWΛ.symm.trans hWt₂)

end TData

end

/-! ### The argument for a globally Lipschitz field -/

section

open Set Filter Topology Metric ComplexConjugate
open scoped NNReal

variable {G : ℂ → ℂ} {K : ℝ≥0}

private theorem TData.exists_crossing_late {p : ℂ} (T : TData G p) {φ : ℝ → ℂ}
    (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) {σ : ℝ} (hσ : |σ| < T.δ) (hω : T.ℓ σ ∈ omegaSet φ)
    {η : ℝ} (hη : 0 < η) (S : ℝ) :
    ∃ τ ≥ S, φ τ ∈ T.L ∧ |T.pos (φ τ) - σ| < η := by
  obtain ⟨ε, hε, ρ, hρ, h⟩ := T.crossing_near_L hσ hη
  obtain ⟨t, ht, hd⟩ := mem_omegaSet_iff.1 hω ρ hρ (S + ε)
  obtain ⟨τ, hτ, hL, hpos⟩ := h φ hφ t hd
  exact ⟨τ, by linarith [(abs_lt.1 hτ).1], hL, hpos⟩

/-- **The ω-limit set meets the open transversal in at most one point**, by monotonicity of the
crossings of the trajectory. -/
private theorem TData.omega_unique {p : ℂ} (T : TData G p) (hG : LipschitzWith K G) {φ : ℝ → ℂ}
    (hφ : ∀ t, HasDerivAt φ (G (φ t)) t) {σ₁ σ₂ : ℝ} (hσ₁ : |σ₁| < T.δ) (hσ₂ : |σ₂| < T.δ)
    (h₁ : T.ℓ σ₁ ∈ omegaSet φ) (h₂ : T.ℓ σ₂ ∈ omegaSet φ) : σ₁ = σ₂ := by
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun t => (hφ t).continuousAt
  suffices key : ∀ σ₁ σ₂, |σ₁| < T.δ → |σ₂| < T.δ → T.ℓ σ₁ ∈ omegaSet φ →
      T.ℓ σ₂ ∈ omegaSet φ → ¬σ₁ < σ₂ by
    rcases lt_trichotomy σ₁ σ₂ with h | h | h
    · exact absurd h (key σ₁ σ₂ hσ₁ hσ₂ h₁ h₂)
    · exact h
    · exact absurd h (key σ₂ σ₁ hσ₂ hσ₁ h₂ h₁)
  intro σ₁ σ₂ hσ₁ hσ₂ h₁ h₂ hlt
  set η := (σ₂ - σ₁) / 3 with hη_def
  have hη : 0 < η := div_pos (sub_pos.2 hlt) three_pos
  obtain ⟨a, -, ha, ha'⟩ := T.exists_crossing_late hφ hσ₁ h₁ hη 0
  obtain ⟨b, hb, hbL, hb'⟩ := T.exists_crossing_late hφ hσ₂ h₂ hη (a + 1)
  obtain ⟨c, hc, hcL, hc'⟩ := T.exists_crossing_late hφ hσ₁ h₁ hη (b + 1)
  set U := Icc a b ∩ (φ ⁻¹' T.L ∩ {τ | T.pos (φ τ) ≤ σ₁ + η}) with hU_def
  have hUcl : IsClosed U := isClosed_Icc.inter ((T.isClosed_L.preimage hφc).inter
    (isClosed_le (T.continuous_pos.comp hφc) continuous_const))
  have haU : a ∈ U := ⟨⟨le_rfl, by linarith⟩, ha,
    show T.pos (φ a) ≤ σ₁ + η by linarith [(abs_lt.1 ha').2]⟩
  have hUbdd : BddAbove U := ⟨b, fun x hx => hx.1.2⟩
  have huU : sSup U ∈ U := hUcl.csSup_mem ⟨a, haU⟩ hUbdd
  have hub : sSup U < b := by
    refine lt_of_le_of_ne huU.1.2 fun h => ?_
    have := huU.2.2
    simp only [mem_ofPred_eq] at this
    rw [h] at this
    linarith [(abs_lt.1 hb').1]
  obtain ⟨v, huv, hvb, hvL, hnov⟩ := T.next_crossing hφ huU.2.1 hub hbL
  have hvpos : σ₁ + η < T.pos (φ v) := by
    by_contra hle
    push Not at hle
    have hvU : v ∈ U := ⟨⟨by linarith [huU.1.1], hvb⟩, hvL, hle⟩
    exact absurd (le_csSup hUbdd hvU) (not_le.2 huv)
  have huη : T.pos (φ (sSup U)) ≤ σ₁ + η := huU.2.2
  have hmono := T.crossing_monotone hG hφ huv huU.2.1 hvL hnov (lt_of_le_of_lt huη hvpos)
    (t₂ := c) (by linarith) hcL
  linarith [(abs_lt.1 hc').2]

/-- **Poincaré–Bendixson for a globally Lipschitz field on `ℂ`.** If a forward solution of
`x' = G x` is bounded and its ω-limit set contains no zero of `G`, then the ω-limit set is the range
of a periodic solution. -/
private theorem pb_core (hG : LipschitzWith K G) {γ : ℝ → ℂ}
    (hγ : IsIntegralCurveOn γ (fun _ x => G x) (Ici 0)) {R : ℝ} (hR : ∀ t, 0 ≤ t → ‖γ t‖ ≤ R)
    (hreg : ∀ y ∈ omegaSet γ, G y ≠ 0) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∃ β : ℝ → ℂ, (∀ t, HasDerivAt β (G (β t)) t) ∧
      (∀ t, β (t + T₀) = β t) ∧ β 0 ∈ omegaSet γ ∧ omegaSet γ = range β := by
  set φ := flow hG (γ 0) with hφ_def
  have hφ : ∀ t, HasDerivAt φ (G (φ t)) t := hasDerivAt_flow hG (γ 0)
  have hφc : Continuous φ := continuous_flow hG (γ 0)
  have hγφ : ∀ t, 0 ≤ t → γ t = φ t := fun t ht => eq_flow_of_isIntegralCurveOn hG hγ ht
  have hωeq : omegaSet γ = omegaSet φ := omegaSet_congr hγφ
  have hRφ : ∀ t, 0 ≤ t → ‖φ t‖ ≤ R := fun t ht => by rw [← hγφ t ht]; exact hR t ht
  rw [hωeq] at hreg ⊢
  set ω := omegaSet φ with hω_def
  have hωc : IsCompact ω := isCompact_omegaSet hRφ
  have hωne : ω.Nonempty := omegaSet_nonempty hRφ
  have hφφ : ∀ t, 0 ≤ t → φ t = flow hG (φ 0) t := fun t _ => by
    rw [hφ_def, flow_zero]
  have hinv : ∀ y ∈ ω, ∀ t, flow hG y t ∈ ω := fun y hy t => flow_mem_omegaSet hG hφφ hy t
  have hconn : IsPreconnected ω := isPreconnected_omegaSet hφc.continuousOn hRφ
  have huniq : ∀ q (T : TData G q) (σ₁ σ₂ : ℝ), |σ₁| < T.δ → |σ₂| < T.δ → T.ℓ σ₁ ∈ ω →
      T.ℓ σ₂ ∈ ω → σ₁ = σ₂ := fun q T σ₁ σ₂ h₁ h₂ h₁' h₂' =>
    T.omega_unique hG hφ h₁ h₂ h₁' h₂'
  -- a periodic orbit through a point of `ω`
  obtain ⟨y, hy⟩ := hωne
  set ψ := flow hG y with hψ_def
  have hψ : ∀ t, HasDerivAt ψ (G (ψ t)) t := hasDerivAt_flow hG y
  have hψc : Continuous ψ := continuous_flow hG y
  have hψω : ∀ t, ψ t ∈ ω := hinv y hy
  obtain ⟨z, hzω, hzψ⟩ := exists_cluster hωc (ψ := ψ) fun t _ => hψω t
  obtain ⟨T⟩ := exists_TData hG.continuous (hreg z hzω)
  have hδ0 : |(0 : ℝ)| < T.δ := by simpa using T.hδ
  have hzψ' : T.ℓ 0 ∈ omegaSet ψ := by rw [T.ℓ_zero]; exact hzψ
  obtain ⟨τ₁, -, hL₁, hp₁⟩ := T.exists_crossing_late hψ hδ0 hzψ' T.hδ 0
  obtain ⟨τ₂, hτ₂, hL₂, hp₂⟩ := T.exists_crossing_late hψ hδ0 hzψ' T.hδ (τ₁ + 1)
  rw [sub_zero] at hp₁ hp₂
  have hψ₁ : ψ τ₁ = T.ℓ (T.pos (ψ τ₁)) := (T.ℓ_pos (T.mem_L_iff.1 hL₁).1).symm
  have hψ₂ : ψ τ₂ = T.ℓ (T.pos (ψ τ₂)) := (T.ℓ_pos (T.mem_L_iff.1 hL₂).1).symm
  have heqpos := huniq z T _ _ hp₁ hp₂ (hψ₁ ▸ hψω τ₁) (hψ₂ ▸ hψω τ₂)
  have heq : ψ τ₂ = ψ τ₁ := by rw [hψ₂, hψ₁, heqpos]
  have hT₀ : 0 < τ₂ - τ₁ := by linarith
  have hper : ∀ t, ψ (t + (τ₂ - τ₁)) = ψ t := by
    intro t
    have := sol_shift hG hψ hψ heq (t - τ₁)
    rwa [show τ₂ + (t - τ₁) = t + (τ₂ - τ₁) by ring, show τ₁ + (t - τ₁) = t by ring] at this
  -- `ω` is the periodic orbit
  have hrange_sub : range ψ ⊆ ω := by
    rintro _ ⟨t, rfl⟩
    exact hψω t
  have hO_closed : IsClosed (range ψ) :=
    (Function.Periodic.compact_of_continuous hper hT₀.ne' hψc).isClosed
  have hωsub : ω ⊆ range ψ := by
    by_contra hns
    have hclose : ∃ q ∈ range ψ, ∀ ε > 0, ∃ w ∈ ω, w ∉ range ψ ∧ dist w q < ε := by
      by_contra hcon
      push Not at hcon
      choose! ε hε hεw using hcon
      have hU : IsOpen (⋃ q ∈ range ψ, ball q (ε q)) := isOpen_biUnion fun q _ => isOpen_ball
      have hcover : ω ⊆ (⋃ q ∈ range ψ, ball q (ε q)) ∪ (range ψ)ᶜ := fun w _ => by
        by_cases h : w ∈ range ψ
        · exact Or.inl (mem_biUnion h (mem_ball_self (hε w h)))
        · exact Or.inr h
      have hU' : (ω ∩ ⋃ q ∈ range ψ, ball q (ε q)).Nonempty :=
        ⟨ψ 0, hψω 0, mem_biUnion (mem_range_self 0) (mem_ball_self (hε _ (mem_range_self 0)))⟩
      have hV' : (ω ∩ (range ψ)ᶜ).Nonempty := by
        rw [not_subset] at hns
        obtain ⟨w, hw, hw'⟩ := hns
        exact ⟨w, hw, hw'⟩
      obtain ⟨w, hw, hwU, hwV⟩ := hconn _ _ hU hO_closed.isOpen_compl hcover hU' hV'
      obtain ⟨q, hq, hwq⟩ := mem_iUnion₂.1 hwU
      exact absurd (hεw q hq w hw hwV) (not_le.2 (mem_ball.1 hwq))
    obtain ⟨q, hq, hclose⟩ := hclose
    obtain ⟨Tq⟩ := exists_TData hG.continuous (hreg q (hrange_sub hq))
    have hδq : |(0 : ℝ)| < Tq.δ := by simpa using Tq.hδ
    obtain ⟨ε, -, ρ, hρ, hcross⟩ := Tq.crossing_near_L hδq Tq.hδ
    obtain ⟨w, hwω, hwO, hwd⟩ := hclose ρ hρ
    obtain ⟨τ, -, hτL, hτpos⟩ := hcross (flow hG w) (hasDerivAt_flow hG w) 0
      (by rw [flow_zero, Tq.ℓ_zero]; exact hwd)
    rw [sub_zero] at hτpos
    have hfw : flow hG w τ = Tq.ℓ (Tq.pos (flow hG w τ)) :=
      (Tq.ℓ_pos (Tq.mem_L_iff.1 hτL).1).symm
    have h0 := huniq q Tq _ 0 hτpos hδq (hfw ▸ hinv w hwω τ)
      (by rw [Tq.ℓ_zero]; exact hrange_sub hq)
    have hfq : flow hG w τ = q := by rw [hfw, h0, Tq.ℓ_zero]
    obtain ⟨tq, rfl⟩ := hq
    have := sol_shift hG (hasDerivAt_flow hG w) hψ hfq (-τ)
    rw [add_neg_cancel, flow_zero] at this
    exact hwO ⟨tq + -τ, this.symm⟩
  refine ⟨τ₂ - τ₁, hT₀, ψ, hψ, hper, ?_, Subset.antisymm hωsub hrange_sub⟩
  rw [hψ_def, flow_zero]
  exact hy

end

/-! ### Vector fields of class `C¹` on `ℂ` -/

section

open Set Filter Topology Metric
open scoped NNReal

/-- A `C¹` field agrees on a closed disc with a globally Lipschitz field: extend the real and
imaginary parts of its restriction to the disc (McShane). -/
private theorem exists_lipschitz_ext {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (R : ℝ) :
    ∃ (K : ℝ≥0) (G : ℂ → ℂ), LipschitzWith K G ∧ EqOn F G (closedBall 0 R) := by
  obtain ⟨K, hK⟩ := hF.contDiffOn.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (0 : ℂ) R) (isCompact_closedBall 0 R)
  have hre1 : LipschitzWith 1 Complex.re := LipschitzWith.of_dist_le_mul fun z w => by
    simpa [Real.dist_eq, dist_eq_norm] using Complex.abs_re_le_norm (z - w)
  have him1 : LipschitzWith 1 Complex.im := LipschitzWith.of_dist_le_mul fun z w => by
    simpa [Real.dist_eq, dist_eq_norm] using Complex.abs_im_le_norm (z - w)
  have hre : LipschitzOnWith K (fun z => (F z).re) (closedBall 0 R) := by
    have := hre1.comp_lipschitzOnWith hK
    rw [one_mul] at this
    exact this
  have him : LipschitzOnWith K (fun z => (F z).im) (closedBall 0 R) := by
    have := him1.comp_lipschitzOnWith hK
    rw [one_mul] at this
    exact this
  obtain ⟨g₁, hg₁, hg₁F⟩ := hre.extend_real
  obtain ⟨g₂, hg₂, hg₂F⟩ := him.extend_real
  refine ⟨2 * K, fun z => (g₁ z : ℂ) + (g₂ z : ℂ) * Complex.I, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun z w => ?_
    rw [dist_eq_norm]
    calc ‖(g₁ z : ℂ) + (g₂ z : ℂ) * Complex.I - ((g₁ w : ℂ) + (g₂ w : ℂ) * Complex.I)‖
        = ‖((g₁ z - g₁ w : ℝ) : ℂ) + ((g₂ z - g₂ w : ℝ) : ℂ) * Complex.I‖ := by
          push_cast
          ring_nf
      _ ≤ ‖((g₁ z - g₁ w : ℝ) : ℂ)‖ + ‖((g₂ z - g₂ w : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = dist (g₁ z) (g₁ w) + dist (g₂ z) (g₂ w) := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, Real.dist_eq, Real.dist_eq]
      _ ≤ K * dist z w + K * dist z w :=
          add_le_add (hg₁.dist_le_mul z w) (hg₂.dist_le_mul z w)
      _ = ↑(2 * K) * dist z w := by
          push_cast
          ring
  · intro z hz
    simp only
    rw [← hg₁F hz, ← hg₂F hz]
    exact (Complex.re_add_im (F z)).symm

/-- The theorem for fields on `ℂ`. -/
private theorem pb_complex (F : ℂ → ℂ) (hF : ContDiff ℝ 1 F) (γ : ℝ → ℂ)
    (hγ : IsIntegralCurveOn γ (fun _ x => F x) (Set.Ici 0)) :
    ¬ Bornology.IsBounded (γ '' Set.Ici 0)
    ∨ (∃ x₀, F x₀ = 0 ∧ x₀ ∈ ⋂ s : ℝ, closure (γ '' Set.Ici s))
    ∨ (∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → ℂ,
        IsIntegralCurve β (fun _ x => F x) ∧
        (∀ t, β (t + T) = β t) ∧
        F (β 0) ≠ 0 ∧
        (⋂ s : ℝ, closure (γ '' Set.Ici s)) = Set.range β) := by
  by_cases hb : Bornology.IsBounded (γ '' Set.Ici 0)
  swap
  · exact Or.inl hb
  right
  by_cases heq : ∃ x₀, F x₀ = 0 ∧ x₀ ∈ ⋂ s : ℝ, closure (γ '' Set.Ici s)
  · exact Or.inl heq
  right
  push Not at heq
  obtain ⟨R₀, hR₀⟩ := hb.subset_closedBall 0
  have hR : ∀ t, 0 ≤ t → ‖γ t‖ ≤ max R₀ 0 := fun t ht => by
    have := hR₀ ⟨t, ht, rfl⟩
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨K, G, hG, hGF⟩ := exists_lipschitz_ext hF (max R₀ 0 + 1)
  have hγb : ∀ t, 0 ≤ t → γ t ∈ closedBall (0 : ℂ) (max R₀ 0 + 1) := fun t ht => by
    rw [mem_closedBall, dist_zero_right]
    linarith [hR t ht]
  have hγG : IsIntegralCurveOn γ (fun _ x => G x) (Ici 0) := fun t ht => by
    have : HasDerivWithinAt γ (F (γ t)) (Ici 0) t := hγ t ht
    change HasDerivWithinAt γ (G (γ t)) (Ici 0) t
    rwa [hGF (hγb t ht)] at this
  have hωR : omegaSet γ ⊆ closedBall 0 (max R₀ 0 + 1) :=
    (omegaSet_subset_closedBall hR).trans (closedBall_subset_closedBall (by linarith))
  have hreg : ∀ y ∈ omegaSet γ, G y ≠ 0 := fun y hy hGy => by
    rw [← hGF (hωR hy)] at hGy
    exact heq y hGy hy
  obtain ⟨T, hT, β, hβ, hper, hβ0, hrange⟩ := pb_core hG hγG hR hreg
  have hβω : ∀ t, β t ∈ omegaSet γ := fun t => by rw [hrange]; exact mem_range_self t
  refine ⟨T, hT, β, fun t => ?_, hper, fun h0 => hreg _ hβ0 ?_, hrange⟩
  · change HasDerivAt β (F (β t)) t
    rw [hGF (hωR (hβω t))]
    exact hβ t
  · rw [← hGF (hωR hβ0)]
    exact h0

end

/-! ### The theorem -/

/- **Poincaré–Bendixson theorem.** For a `C¹` autonomous vector field
`F : ℝ² → ℝ²` and a forward integral curve `γ` on `[0, ∞)`, either the
forward orbit is unbounded, or the ω-limit set contains an equilibrium
of `F`, or the ω-limit set equals the range of a non-constant periodic
integral curve of `F`. -/
set_option linter.dupNamespace false in
/-- **Poincaré–Bendixson theorem.** Let $F \colon \mathbb{R}^2 \to \mathbb{R}^2$ be a continuously
differentiable vector field on the Euclidean plane, and let
$\gamma \colon \mathbb{R} \to \mathbb{R}^2$ be a curve such that for every $t \ge 0$ the derivative
of $\gamma$ at $t$ within $[0, \infty)$ is $F(\gamma(t))$. Let
$\omega(\gamma) = \bigcap_{s \in \mathbb{R}} \overline{\gamma([s, \infty))}$ be the $\omega$-limit
set of $\gamma$. Then at least one of the following holds: the forward orbit
$\gamma([0, \infty))$ is unbounded; $\omega(\gamma)$ contains a point $x_0$ with $F(x_0) = 0$; or
there are a real number $T > 0$ and a curve $\beta \colon \mathbb{R} \to \mathbb{R}^2$ with
$\beta'(t) = F(\beta(t))$ and $\beta(t + T) = \beta(t)$ for every real $t$ and with
$F(\beta(0)) \ne 0$, such that $\omega(\gamma)$ equals the range of $\beta$.

Source: H. Poincaré, *Mémoire sur les courbes définies par une équation différentielle*, Journal de
Mathématiques 7 (1881), 8 (1882), 1 (1885), 2 (1886); I. Bendixson, *Sur les courbes définies par
des équations différentielles*, Acta Mathematica 24 (1901), 1-88. Listed as §63 in O. Knill, *Some
Fundamental Theorems in Mathematics*
(https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). The Isabelle/HOL/AFP
entry by Fabian Immler and Yong Kiam Tan (https://www.isa-afp.org/entries/Poincare_Bendixson.html)
uses John Harrison's Jordan curve theorem. Via leanprover/lean-eval@38361be, problem
`poincare_bendixson`. -/
public theorem poincare_bendixson
    (F : Plane → Plane) (_hF : ContDiff ℝ 1 F)
    (γ : ℝ → Plane)
    (_hγ : IsIntegralCurveOn γ (fun _ x => F x) (Set.Ici 0)) :
    ¬ Bornology.IsBounded (γ '' Set.Ici 0)
    ∨ (∃ x₀, F x₀ = 0 ∧ x₀ ∈ ⋂ s : ℝ, closure (γ '' Set.Ici s))
    ∨ (∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → Plane,
        IsIntegralCurve β (fun _ x => F x) ∧
        (∀ t, β (t + T) = β t) ∧
        F (β 0) ≠ 0 ∧
        (⋂ s : ℝ, closure (γ '' Set.Ici s)) = Set.range β) := by
  set e : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm with he_def
  set F' : ℂ → ℂ := fun z => e (F (e.symm z)) with hF'_def
  set γ' : ℝ → ℂ := fun t => e (γ t) with hγ'_def
  have hF' : ContDiff ℝ 1 F' := e.contDiff.comp (_hF.comp e.symm.contDiff)
  have hγ' : IsIntegralCurveOn γ' (fun _ x => F' x) (Ici 0) := by
    intro t ht
    have h1 := (e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
      (x := γ t)).comp_hasDerivWithinAt t (_hγ t ht)
    have h2 : F' (γ' t) = e (F (γ t)) := by simp [hF'_def, hγ'_def]
    change HasDerivWithinAt γ' (F' (γ' t)) (Ici 0) t
    rw [h2]
    exact h1
  have hω : ∀ y : Plane, y ∈ (⋂ s : ℝ, closure (γ '' Ici s)) ↔
      e y ∈ ⋂ s : ℝ, closure (γ' '' Ici s) := by
    intro y
    have h1 := mem_omegaSet_iff (γ := γ) (y := y)
    have h2 := mem_omegaSet_iff (γ := γ') (y := e y)
    simp only [omegaSet] at h1 h2
    rw [h1, h2]
    simp only [hγ'_def, LinearIsometryEquiv.dist_map]
  rcases pb_complex F' hF' γ' hγ' with h | h | h
  · left
    intro hb
    apply h
    have : γ' '' Ici 0 = e '' (γ '' Ici 0) := by rw [image_image]
    rw [this]
    exact e.lipschitzWith.isBounded_image hb
  · right
    left
    obtain ⟨x₀, hx₀, hmem⟩ := h
    refine ⟨e.symm x₀, ?_, ?_⟩
    · have : e (F (e.symm x₀)) = 0 := hx₀
      exact e.map_eq_zero_iff.1 this
    · rw [hω, LinearIsometryEquiv.apply_symm_apply]
      exact hmem
  · right
    right
    obtain ⟨T, hT, β, hβ, hper, hne, hrange⟩ := h
    refine ⟨T, hT, fun t => e.symm (β t), ?_, fun t => by simp only [hper], ?_, ?_⟩
    · intro t
      have h1 := (e.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
        (x := β t)).comp_hasDerivAt t (hβ t)
      have h2 : F (e.symm (β t)) = e.symm (F' (β t)) := by simp [hF'_def]
      change HasDerivAt (fun t => e.symm (β t)) (F (e.symm (β t))) t
      rw [h2]
      exact h1
    · intro h0
      apply hne
      simp [hF'_def, h0]
    · ext y
      rw [hω, hrange]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, by simp [ht]⟩
      · rintro ⟨t, rfl⟩
        exact ⟨t, by simp⟩

end Dynamics

end MathlibExt.Dynamics.PoincareBendixsonWanted
