/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# LaSalle's invariance principle for ordinary differential equations

Let `K` be a compact set that is forward invariant for the autonomous equation `x' = f x`
(`IsForwardInvariant`: through every point of `K` there is a forward solution on `[0, ∞)` staying
in `K`), with `f` Lipschitz on `K`. Let `V` have Fréchet derivative `V' x` at every `x ∈ K` (for
example `V` of class `C¹`) with orbital derivative `V' x (f x) ≤ 0` on `K`. Then every forward
solution `γ` that stays in `K` converges to the largest forward-invariant subset `M` of
`{x ∈ K | V' x (f x) = 0}`: its ω-limit set (the cluster points of `γ t` as `t → ∞`) is nonempty
and contained in `M`, and `γ t` eventually enters every open set containing `M`. The same holds
with `M` the largest *invariant* subset (solutions on all of `ℝ`), which can be smaller.

The proof works with the trajectory directly. `V ∘ γ` is nonincreasing and bounded below on `K`,
so `V` is constant on the ω-limit set. The ω-limit set is forward invariant: if `γ (tₙ) → y`,
Grönwall's inequality (`dist_le_of_trajectories_ODE_of_mem`) gives
`dist (γ (tₙ + s)) (φ s) ≤ dist (γ tₙ) y · e^{L s}` for the solution `φ` from `y`
(`mapClusterPt_of_mapClusterPt`). So `V` is constant along solutions from ω-limit points, which
forces `V' (f) = 0` there. The ω-limit set is also backward invariant: if `γ (tₙ) → y`, a cluster
point `z` of `γ (tₙ - s)` flows to `y` in time `s` (`exists_mapClusterPt_forall_eq`), and gluing
such backward steps gives a solution through `y` on all of `ℝ` inside the ω-limit set
(`isInvariant_setOf_mapClusterPt`).

## Main results

* `lasalle_of_antitoneOn`: the principle with no derivative of `V`: `V` continuous on `K` and
  nonincreasing along `γ`, and `Z` any set containing every `x ∈ K` from which some solution in
  `K` keeps `V` constant.
* `lasalle_of_hasFDerivAt`, `lasalle`: the classical statement with `M ⊆ {V' = 0}`, for `V`
  differentiable on `K`, respectively `V` of class `C¹` with `V' = fderiv ℝ V`.
* `tendsto_of_lasalle`: convergence `γ t → x₀` when `M ⊆ {x₀}`.
* `largestForwardInvariantSubset` and its universal property.
* `isInvariant_setOf_mapClusterPt`: the ω-limit set is invariant in both time directions: through
  each of its points runs a solution on all of `ℝ` that stays in it.
* `lasalle_invariant_of_antitoneOn`, `lasalle_invariant_of_hasFDerivAt`, `lasalle_invariant`,
  `tendsto_of_lasalle_invariant`: the same statements with `M` the largest *invariant* subset
  (`largestInvariantSubset`, solutions on all of `ℝ`), the classical form of the principle.

The application to reversible Michaelis–Menten kinetics, convergence of every solution to the
equilibrium of its compatibility class, is in
`Domains.Biology.Dynamics.ReversibleMichaelisMenten.LaSalle`.

## Scope

* The `lasalle*` theorems take `M` to be the largest *forward*-invariant subset of `{V' = 0}`, as
  in `Flow.lasalle`. The `lasalle_invariant*` theorems take the largest invariant subset
  (solutions on all of `ℝ`), which can be strictly smaller
  (`MathlibExtTest.Analysis.ODE.LaSalle.largestInvariantSubset_neg`: `x' = -x` on `[0, 1]`), so
  their conclusion is stronger. Only forward solutions through `K` are assumed; the backward
  halves of the solutions through ω-limit points are constructed, from compactness of `K` and
  uniqueness of forward solutions.
* `f` must be Lipschitz on `K` (this gives continuous dependence on initial data), and the
  forward solutions through points of `K` are taken as a hypothesis, not constructed.
* Compactness of `K` is needed: `MathlibExtTest.Analysis.ODE.LaSalle.noncompact_counterexample`
  (`x' = 1` on `[0, ∞)` with `V = e^{-x}`) satisfies every other hypothesis while its ω-limit set
  is empty.

## Relation to `MathlibExt.Dynamics.LaSalle`

`Flow.lasalle` is the same principle for a continuous semiflow `Flow ℝ≥0 X`. An ODE has such a
semiflow only after existence, uniqueness and joint continuity are proved on the whole state
space. This file works with solutions of `x' = f x` given by `IsIntegralCurveOn`, which is the
form the Lyapunov results (`MathlibExt.Analysis.ODE.LyapunovStability`) and the biological models
use, and it derives the `{V' = 0}` form from the derivative of `V`.

## References

* J. P. LaSalle, *Some extensions of Liapunov's second method*, IRE Trans. Circuit Theory 7
  (1960) 520–527.
* H. K. Khalil, *Nonlinear Systems*, 3rd ed., Prentice Hall (2002), §4.2, Theorem 4.4.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

namespace MathlibExt.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A set `A` is **forward invariant** for the autonomous field `f` if through every point of
`A` there is a forward solution of `x' = f x` on `[0, ∞)` that stays in `A`. (Where forward
solutions are unique this is the usual "every solution starting in `A` stays in `A`", together
with existence of those solutions.) -/
def IsForwardInvariant (f : E → E) (A : Set E) : Prop :=
  ∀ x ∈ A, ∃ φ : ℝ → E, IsIntegralCurveOn φ (fun _ => f) (Ici 0) ∧ φ 0 = x ∧
    ∀ t, 0 ≤ t → φ t ∈ A

/-- The **largest forward-invariant subset** of `Z` for the field `f`: the union of all
forward-invariant subsets of `Z` (`isForwardInvariant_largestForwardInvariantSubset`,
`subset_largestForwardInvariantSubset`). -/
def largestForwardInvariantSubset (f : E → E) (Z : Set E) : Set E :=
  ⋃₀ {A | A ⊆ Z ∧ IsForwardInvariant f A}

variable {f : E → E} {Z A : Set E}

/-- The largest forward-invariant subset of `Z` lies in `Z`. -/
theorem largestForwardInvariantSubset_subset : largestForwardInvariantSubset f Z ⊆ Z :=
  sUnion_subset fun _ hA => hA.1

/-- Every forward-invariant subset of `Z` lies in the largest one. -/
theorem subset_largestForwardInvariantSubset (hAZ : A ⊆ Z) (hA : IsForwardInvariant f A) :
    A ⊆ largestForwardInvariantSubset f Z :=
  subset_sUnion_of_mem ⟨hAZ, hA⟩

/-- The largest forward-invariant subset of `Z` is forward invariant. -/
theorem isForwardInvariant_largestForwardInvariantSubset :
    IsForwardInvariant f (largestForwardInvariantSubset f Z) := by
  rintro x ⟨A, ⟨hAZ, hA⟩, hxA⟩
  obtain ⟨φ, hφ, hφ0, hφA⟩ := hA x hxA
  exact ⟨φ, hφ, hφ0, fun t ht => subset_largestForwardInvariantSubset hAZ hA (hφA t ht)⟩

/-- A set `A` is **invariant** for the autonomous field `f` if through every point of `A` there
is a solution of `x' = f x` on all of `ℝ` (an entire solution, forward and backward in time) that
stays in `A`. -/
def IsInvariant (f : E → E) (A : Set E) : Prop :=
  ∀ x ∈ A, ∃ φ : ℝ → E, IsIntegralCurve φ (fun _ => f) ∧ φ 0 = x ∧ ∀ t, φ t ∈ A

/-- An invariant set is forward invariant: restrict the entire solutions to `[0, ∞)`. -/
theorem IsInvariant.isForwardInvariant (hA : IsInvariant f A) : IsForwardInvariant f A := by
  intro x hx
  obtain ⟨φ, hφ, hφ0, hφA⟩ := hA x hx
  exact ⟨φ, hφ.isIntegralCurveOn _, hφ0, fun t _ => hφA t⟩

/-- The **largest invariant subset** of `Z` for the field `f`: the union of all invariant
subsets of `Z` (`isInvariant_largestInvariantSubset`, `subset_largestInvariantSubset`). -/
def largestInvariantSubset (f : E → E) (Z : Set E) : Set E :=
  ⋃₀ {A | A ⊆ Z ∧ IsInvariant f A}

/-- The largest invariant subset of `Z` lies in `Z`. -/
theorem largestInvariantSubset_subset : largestInvariantSubset f Z ⊆ Z :=
  sUnion_subset fun _ hA => hA.1

/-- Every invariant subset of `Z` lies in the largest one. -/
theorem subset_largestInvariantSubset (hAZ : A ⊆ Z) (hA : IsInvariant f A) :
    A ⊆ largestInvariantSubset f Z :=
  subset_sUnion_of_mem ⟨hAZ, hA⟩

/-- The largest invariant subset of `Z` is invariant. -/
theorem isInvariant_largestInvariantSubset : IsInvariant f (largestInvariantSubset f Z) := by
  rintro x ⟨A, ⟨hAZ, hA⟩, hxA⟩
  obtain ⟨φ, hφ, hφ0, hφA⟩ := hA x hxA
  exact ⟨φ, hφ, hφ0, fun t => subset_largestInvariantSubset hAZ hA (hφA t)⟩

/-- The largest invariant subset of `Z` lies in the largest forward-invariant subset. -/
theorem largestInvariantSubset_subset_largestForwardInvariantSubset :
    largestInvariantSubset f Z ⊆ largestForwardInvariantSubset f Z :=
  subset_largestForwardInvariantSubset largestInvariantSubset_subset
    isInvariant_largestInvariantSubset.isForwardInvariant

/-- A cluster point of `u` along `F` lies in every closed set that eventually contains `u`. -/
theorem mem_of_mapClusterPt_of_eventually_mem {X ι : Type*} [TopologicalSpace X]
    {F : Filter ι} {u : ι → X} {x : X} {C : Set X} (hx : MapClusterPt x F u)
    (hC : IsClosed C) (hu : ∀ᶠ i in F, u i ∈ C) : x ∈ C := by
  by_contra hxC
  have := (mapClusterPt_iff_frequently.1 hx _ (hC.isOpen_compl.mem_nhds hxC)).and_eventually hu
  exact this.exists.elim fun _ h => h.1 h.2

variable {γ φ : ℝ → E} {K : Set E} {L : ℝ≥0}

/-- **Continuous dependence along the tail (Grönwall).** If `γ` and `φ` are forward solutions
of `x' = f x` that stay in `K`, where `f` is `L`-Lipschitz, then for `t, s ≥ 0`,
`dist (γ (t + s)) (φ s) ≤ dist (γ t) (φ 0) * exp (L s)`. -/
theorem dist_shift_le (hf : LipschitzOnWith L f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hφ : IsIntegralCurveOn φ (fun _ => f) (Ici 0)) (hφK : ∀ t, 0 ≤ t → φ t ∈ K)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    dist (γ (t + s)) (φ s) ≤ dist (γ t) (φ 0) * Real.exp (L * s) := by
  have hsub : Icc t (t + s) ⊆ Ici 0 := fun u hu => le_trans ht hu.1
  have key := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f) (s := fun _ => K)
    (f := γ) (g := fun u => φ (u - t)) (a := t) (b := t + s) (K := L)
    (fun _ _ => hf) (hγ.continuousOn.mono hsub)
    (fun u hu => (hγ u (hsub (Ico_subset_Icc_self hu))).mono
      (Ici_subset_Ici.2 (hsub (Ico_subset_Icc_self hu))))
    (fun u hu => hγK u (hsub (Ico_subset_Icc_self hu)))
    (hφ.continuousOn.comp (continuousOn_id.sub continuousOn_const)
      (fun u hu => by simp only [mem_Ici]; linarith [hu.1]))
    (fun u hu => by
      have h0 : 0 ≤ u - t := by linarith [hu.1]
      have hd := (hφ (u - t) h0).mono (Ici_subset_Ici.2 h0)
      have hc : HasDerivWithinAt (fun u => u - t) 1 (Ici u) u :=
        (hasDerivWithinAt_id u _).sub_const t
      have := hd.scomp u hc (fun w hw => by simp only [mem_Ici] at hw ⊢; linarith)
      rw [one_smul] at this
      exact this)
    (fun u hu => hφK _ (by linarith [hu.1])) le_rfl (t + s) ⟨by linarith, le_rfl⟩
  simpa using key

/-- **The ω-limit set is forward invariant.** Let `γ` be a forward solution of `x' = f x` that
stays in `K`, with `f` Lipschitz on `K`. If `y` is a cluster point of `γ t` as `t → ∞`, then
every forward solution `φ` from `y` that stays in `K` consists of cluster points of `γ`. -/
theorem mapClusterPt_of_mapClusterPt (hf : LipschitzOnWith L f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    {y : E} (hy : MapClusterPt y atTop γ)
    (hφ : IsIntegralCurveOn φ (fun _ => f) (Ici 0)) (hφ0 : φ 0 = y)
    (hφK : ∀ t, 0 ≤ t → φ t ∈ K) {s : ℝ} (hs : 0 ≤ s) : MapClusterPt (φ s) atTop γ := by
  rw [mapClusterPt_iff_frequently]
  intro n hn
  obtain ⟨ε, hε, hεn⟩ := Metric.mem_nhds_iff.1 hn
  have hexp : 0 < Real.exp (L * s) := Real.exp_pos _
  have hfr := (mapClusterPt_iff_frequently.1 hy _
    (ball_mem_nhds y (div_pos hε hexp))).and_eventually (eventually_ge_atTop 0)
  refine (tendsto_atTop_add_const_right atTop s tendsto_id).frequently (hfr.mono ?_)
  rintro t ⟨hty, ht⟩
  apply hεn
  rw [mem_ball]
  calc dist (γ (id t + s)) (φ s) ≤ dist (γ t) (φ 0) * Real.exp (L * s) :=
        dist_shift_le hf hγ hγK hφ hφK ht hs
    _ < ε / Real.exp (L * s) * Real.exp (L * s) := by
        rw [hφ0]; exact mul_lt_mul_of_pos_right (mem_ball.1 hty) hexp
    _ = ε := div_mul_cancel₀ _ hexp.ne'

/-- **Backward step in the ω-limit set.** Let `K` be compact, `f` Lipschitz on `K`, and `γ` a
forward solution of `x' = f x` that stays in `K`. For every cluster point `y` of `γ t` as
`t → ∞` and every `s ≥ 0` there is a cluster point `z` such that every forward solution from `z`
that stays in `K` is at `y` at time `s`. -/
theorem exists_mapClusterPt_forall_eq (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    {y : E} (hy : MapClusterPt y atTop γ) {s : ℝ} (hs : 0 ≤ s) :
    ∃ z, MapClusterPt z atTop γ ∧ ∀ φ : ℝ → E, IsIntegralCurveOn φ (fun _ => f) (Ici 0) →
      φ 0 = z → (∀ t, 0 ≤ t → φ t ∈ K) → φ s = y := by
  -- the times at which `γ` approaches `y`
  have hF : (atTop ⊓ comap γ (𝓝 y)).NeBot :=
    neBot_inf_comap_iff_map.2 (by rw [inf_comm]; exact hy.clusterPt.neBot)
  have hγy : Tendsto γ (atTop ⊓ comap γ (𝓝 y)) (𝓝 y) := tendsto_comap.mono_left inf_le_right
  have hshift : Tendsto (fun t => t - s) (atTop ⊓ comap γ (𝓝 y)) atTop :=
    (tendsto_atTop_atTop.2 fun b => ⟨b + s, fun a ha => by linarith⟩).mono_left inf_le_left
  have hge : ∀ᶠ t in atTop ⊓ comap γ (𝓝 y), 0 ≤ t - s :=
    hshift.eventually (eventually_ge_atTop 0)
  obtain ⟨z, -, hz⟩ := hK.exists_mapClusterPt_of_frequently
    (hge.mono fun t ht => hγK (t - s) ht).frequently
  refine ⟨z, MapClusterPt.of_comp (u := γ) hshift hz, fun φ hφ hφ0 hφK => ?_⟩
  refine eq_of_forall_dist_le fun ε hε => ?_
  have hexp : 0 < Real.exp (L * s) := Real.exp_pos _
  have hfr := (mapClusterPt_iff_frequently.1 hz _ (ball_mem_nhds z (div_pos (half_pos hε) hexp))
    ).and_eventually (hge.and (hγy.eventually (ball_mem_nhds y (half_pos hε))))
  obtain ⟨t, htz, hts, hty⟩ := hfr.exists
  have hd : dist (γ t) (φ s) ≤ dist (γ (t - s)) (φ 0) * Real.exp (L * s) := by
    have := dist_shift_le hf hγ hγK hφ hφK hts hs
    rwa [sub_add_cancel] at this
  have hd' : dist (γ (t - s)) (φ 0) * Real.exp (L * s) < ε / 2 := by
    rw [hφ0]
    calc dist (γ (t - s)) z * Real.exp (L * s) < ε / 2 / Real.exp (L * s) * Real.exp (L * s) :=
          mul_lt_mul_of_pos_right (mem_ball.1 htz) hexp
      _ = ε / 2 := div_mul_cancel₀ _ hexp.ne'
  calc dist (φ s) y ≤ dist (φ s) (γ t) + dist (γ t) y := dist_triangle _ _ _
    _ ≤ ε / 2 + ε / 2 := by
        rw [dist_comm]; exact add_le_add (hd.trans hd'.le) (mem_ball.1 hty).le
    _ = ε := add_halves ε

/-- **The ω-limit set is invariant** (two-sided). Let `K` be compact and forward invariant for
`x' = f x`, with `f` Lipschitz on `K`, and let `γ` be a forward solution that stays in `K`. Then
through every cluster point of `γ t` as `t → ∞` there is a solution on all of `ℝ` consisting of
cluster points of `γ`.

The backward half of the solution is glued from backward steps of length `1`
(`exists_mapClusterPt_forall_eq`); uniqueness of forward solutions in `K` (Grönwall,
`dist_shift_le`) makes the pieces agree on their overlaps. -/
theorem isInvariant_setOf_mapClusterPt (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K) :
    IsInvariant f {y | MapClusterPt y atTop γ} := by
  set Ω := {y | MapClusterPt y atTop γ}
  have hΩK : ∀ y ∈ Ω, y ∈ K := fun y hy =>
    mem_of_mapClusterPt_of_eventually_mem hy hK.isClosed ((eventually_ge_atTop 0).mono hγK)
  choose! sol hsol hsol0 hsolK using hinv
  -- forward solutions from `Ω` stay in `Ω`
  have hsolΩ : ∀ y ∈ Ω, ∀ t, 0 ≤ t → sol y t ∈ Ω := fun y hy t ht =>
    mapClusterPt_of_mapClusterPt hf hγ hγK hy (hsol y (hΩK y hy)) (hsol0 y (hΩK y hy))
      (hsolK y (hΩK y hy)) ht
  -- one backward step of length `1`
  have hback : ∀ y ∈ Ω, ∃ z ∈ Ω, sol z 1 = y := by
    intro y hy
    obtain ⟨z, hz, hzy⟩ := exists_mapClusterPt_forall_eq hK hf hγ hγK hy zero_le_one
    exact ⟨z, hz, hzy _ (hsol z (hΩK z hz)) (hsol0 z (hΩK z hz)) (hsolK z (hΩK z hz))⟩
  choose! back hbackΩ hback1 using hback
  have hstep : ∀ q ∈ Ω, ∀ u, 0 ≤ u → sol (back q) (u + 1) = sol q u := by
    intro q hq u hu
    have hb := hΩK _ (hbackΩ q hq)
    have := dist_shift_le hf (hsol _ hb) (hsolK _ hb) (hsol q (hΩK q hq)) (hsolK q (hΩK q hq))
      zero_le_one hu
    rw [hback1 q hq, hsol0 q (hΩK q hq), dist_self, zero_mul, add_comm] at this
    exact dist_le_zero.1 this
  intro y hy
  -- the backward orbit `p n = back^[n] y`, with `sol (p (n + 1)) 1 = p n`
  obtain ⟨p, hp0, hpS⟩ : ∃ p : ℕ → E, p 0 = y ∧ ∀ n, p (n + 1) = back (p n) :=
    ⟨fun n => back^[n] y, rfl, fun n => Function.iterate_succ_apply' back n y⟩
  have hpΩ : ∀ n, p n ∈ Ω := by
    intro n
    induction n with
    | zero => rw [hp0]; exact hy
    | succ n ih => rw [hpS]; exact hbackΩ _ ih
  -- the pieces `t ↦ sol (p n) (t + n)` agree where they are defined
  have hcons : ∀ n m : ℕ, n ≤ m → ∀ t : ℝ, 0 ≤ t + n →
      sol (p m) (t + m) = sol (p n) (t + n) := by
    intro n m hnm t ht
    induction m, hnm using Nat.le_induction with
    | base => rfl
    | succ m hnm ih =>
      have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
      have hm : (0 : ℝ) ≤ t + m := by linarith
      rw [hpS, Nat.cast_succ, ← add_assoc, hstep _ (hpΩ m) _ hm, ih]
  have hN : ∀ t : ℝ, 0 ≤ t + (⌈-t⌉₊ : ℝ) := fun t => by linarith [Nat.le_ceil (-t)]
  refine ⟨fun t => sol (p ⌈-t⌉₊) (t + ⌈-t⌉₊), fun t => ?_, ?_,
    fun t => hsolΩ _ (hpΩ _) _ (hN t)⟩
  · obtain ⟨n, hnt, htn⟩ : ∃ n : ℕ, ⌈-t⌉₊ ≤ n ∧ -(n : ℝ) < t :=
      ⟨⌈-t⌉₊ + 1, Nat.le_succ _, by push_cast; linarith [hN t]⟩
    have htn' : 0 < t + n := by linarith
    have heq : (fun u => sol (p ⌈-u⌉₊) (u + ⌈-u⌉₊)) =ᶠ[𝓝 t] fun u => sol (p n) (u + n) := by
      filter_upwards [Ioi_mem_nhds htn] with u hu
      have hun : ⌈-u⌉₊ ≤ n := Nat.ceil_le.2 (by rw [mem_Ioi] at hu; linarith)
      exact (hcons _ _ hun u (hN u)).symm
    have hd : HasDerivAt (sol (p n)) (f (sol (p n) (t + n))) (t + n) :=
      (hsol _ (hΩK _ (hpΩ n)) _ htn'.le).hasDerivAt (Ici_mem_nhds htn')
    rw [hcons _ _ hnt t (hN t)] at hd
    exact (hd.comp_add_const t (n : ℝ)).congr_of_eventuallyEq heq
  · simpa [hp0] using hsol0 y (hΩK y hy)

omit [NormedSpace ℝ E] in
/-- The ω-limit set of a forward solution that stays in a compact set `K` is nonempty. -/
theorem nonempty_setOf_mapClusterPt (hK : IsCompact K) (hγK : ∀ t, 0 ≤ t → γ t ∈ K) :
    {y | MapClusterPt y atTop γ}.Nonempty := by
  obtain ⟨y, -, hy⟩ := hK.exists_mapClusterPt_of_frequently
    ((eventually_ge_atTop 0).mono hγK).frequently
  exact ⟨y, hy⟩

omit [NormedSpace ℝ E] in
/-- A forward solution that stays in a compact set `K` eventually enters every open set `U`
containing a set `M` that contains its ω-limit set. -/
theorem eventually_mem_of_setOf_mapClusterPt_subset (hK : IsCompact K)
    (hγK : ∀ t, 0 ≤ t → γ t ∈ K) {M U : Set E} (hsub : {y | MapClusterPt y atTop γ} ⊆ M)
    (hU : IsOpen U) (hMU : M ⊆ U) : ∀ᶠ t in atTop, γ t ∈ U := by
  have hev : ∀ᶠ t in atTop, γ t ∈ K := (eventually_ge_atTop 0).mono hγK
  by_contra hnot
  have hfr : ∃ᶠ t in atTop, γ t ∈ K \ U :=
    ((not_eventually.1 hnot).and_eventually hev).mono fun _ h => ⟨h.2, h.1⟩
  obtain ⟨y, hyKU, hy⟩ := (hK.diff hU).exists_mapClusterPt_of_frequently hfr
  exact hyKU.2 (hMU (hsub hy))

variable {V : E → ℝ}

omit [NormedSpace ℝ E] in
/-- **`V` is constant on the ω-limit set.** If `γ` stays in a compact set `K` on which `V` is
continuous and `V ∘ γ` is nonincreasing on `[0, ∞)`, then `V` equals `⨅ t ≥ 0, V (γ t)` at every
cluster point of `γ t` as `t → ∞`. -/
theorem eq_iInf_of_mapClusterPt (hK : IsCompact K) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hVc : ∀ x ∈ K, ContinuousAt V x) (hanti : AntitoneOn (fun t => V (γ t)) (Ici 0))
    {y : E} (hy : MapClusterPt y atTop γ) : V y = ⨅ t : Ici (0 : ℝ), V (γ t) := by
  have hyK : y ∈ K :=
    mem_of_mapClusterPt_of_eventually_mem hy hK.isClosed ((eventually_ge_atTop 0).mono hγK)
  have : Nonempty (Ici (0 : ℝ)) := ⟨⟨0, le_rfl⟩⟩
  have hbdd : BddBelow (range fun t : Ici (0 : ℝ) => V (γ t)) := by
    obtain ⟨m, hm⟩ := (hK.image_of_continuousOn
      fun x hx => (hVc x hx).continuousWithinAt).bddBelow
    exact ⟨m, by rintro _ ⟨t, rfl⟩; exact hm ⟨_, hγK t t.2, rfl⟩⟩
  have hy' := MapClusterPt.continuousAt_comp (hVc y hyK) hy
  have hmem : ∀ T, 0 ≤ T → V y ∈ Icc (⨅ t : Ici (0 : ℝ), V (γ t)) (V (γ T)) := by
    intro T hT
    refine mem_of_mapClusterPt_of_eventually_mem hy' isClosed_Icc ?_
    filter_upwards [eventually_ge_atTop T] with t ht
    exact ⟨ciInf_le hbdd ⟨t, hT.trans ht⟩, hanti (mem_Ici.2 hT) (mem_Ici.2 (hT.trans ht)) ht⟩
  exact le_antisymm (le_ciInf fun T => (hmem T T.2).2) (hmem 0 le_rfl).1

/-- **LaSalle's invariance principle, trajectory form.** Let `K` be compact and forward invariant
for `x' = f x`, with `f` Lipschitz on `K`, and let `γ` be a forward solution that stays in `K`.
Let `V` be continuous at every point of `K` and nonincreasing along `γ`. Let `Z` contain every
`x ∈ K` from which some forward solution in `K` keeps `V` constant. Then the ω-limit set
`{y | MapClusterPt y atTop γ}` is nonempty and contained in the largest forward-invariant subset
`M` of `Z`, and `γ t` eventually enters every open set containing `M`.

No derivative of `V` is needed; `lasalle_of_hasFDerivAt` and `lasalle` derive the
classical `{V' = 0}` form. -/
theorem lasalle_of_antitoneOn (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hVc : ∀ x ∈ K, ContinuousAt V x) (hanti : AntitoneOn (fun t => V (γ t)) (Ici 0))
    (hZ : ∀ x ∈ K, ∀ φ : ℝ → E, IsIntegralCurveOn φ (fun _ => f) (Ici 0) → φ 0 = x →
      (∀ t, 0 ≤ t → φ t ∈ K) → (∀ t, 0 ≤ t → V (φ t) = V x) → x ∈ Z) :
    {y | MapClusterPt y atTop γ}.Nonempty ∧
      {y | MapClusterPt y atTop γ} ⊆ largestForwardInvariantSubset f Z ∧
      ∀ U : Set E, IsOpen U → largestForwardInvariantSubset f Z ⊆ U →
        ∀ᶠ t in atTop, γ t ∈ U := by
  have hΩK : ∀ y, MapClusterPt y atTop γ → y ∈ K := fun y hy =>
    mem_of_mapClusterPt_of_eventually_mem hy hK.isClosed ((eventually_ge_atTop 0).mono hγK)
  -- the ω-limit set is forward invariant and lies in `Z`
  have hΩinv : IsForwardInvariant f {y | MapClusterPt y atTop γ} := by
    intro y hy
    obtain ⟨φ, hφ, hφ0, hφK⟩ := hinv y (hΩK y hy)
    exact ⟨φ, hφ, hφ0, fun s hs => mapClusterPt_of_mapClusterPt hf hγ hγK hy hφ hφ0 hφK hs⟩
  have hΩZ : {y | MapClusterPt y atTop γ} ⊆ Z := by
    intro y hy
    obtain ⟨φ, hφ, hφ0, hφK⟩ := hinv y (hΩK y hy)
    refine hZ y (hΩK y hy) φ hφ hφ0 hφK fun t ht => ?_
    rw [eq_iInf_of_mapClusterPt hK hγK hVc hanti
        (mapClusterPt_of_mapClusterPt hf hγ hγK hy hφ hφ0 hφK ht),
      eq_iInf_of_mapClusterPt hK hγK hVc hanti hy]
  have hsub := subset_largestForwardInvariantSubset hΩZ hΩinv
  exact ⟨nonempty_setOf_mapClusterPt hK hγK, hsub, fun U hU hMU =>
    eventually_mem_of_setOf_mapClusterPt_subset hK hγK hsub hU hMU⟩

/-- **LaSalle's invariance principle with two-sided invariance, trajectory form.** Under the
hypotheses of `lasalle_of_antitoneOn`, let `Z` contain every `x ∈ K` through which some solution
on all of `ℝ` stays in `K` and keeps `V` constant. Then the ω-limit set of `γ` is nonempty and
contained in the largest invariant subset `M` of `Z`, and `γ t` eventually enters every open set
containing `M`.

The hypothesis on `Z` asks only about entire solutions, so it is weaker than the one in
`lasalle_of_antitoneOn`, and `M` is contained in the largest forward-invariant subset of `Z`
(`largestInvariantSubset_subset_largestForwardInvariantSubset`). -/
theorem lasalle_invariant_of_antitoneOn (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hVc : ∀ x ∈ K, ContinuousAt V x) (hanti : AntitoneOn (fun t => V (γ t)) (Ici 0))
    (hZ : ∀ x ∈ K, ∀ φ : ℝ → E, IsIntegralCurve φ (fun _ => f) → φ 0 = x →
      (∀ t, φ t ∈ K) → (∀ t, V (φ t) = V x) → x ∈ Z) :
    {y | MapClusterPt y atTop γ}.Nonempty ∧
      {y | MapClusterPt y atTop γ} ⊆ largestInvariantSubset f Z ∧
      ∀ U : Set E, IsOpen U → largestInvariantSubset f Z ⊆ U →
        ∀ᶠ t in atTop, γ t ∈ U := by
  have hΩK : ∀ y, MapClusterPt y atTop γ → y ∈ K := fun y hy =>
    mem_of_mapClusterPt_of_eventually_mem hy hK.isClosed ((eventually_ge_atTop 0).mono hγK)
  have hΩinv := isInvariant_setOf_mapClusterPt hK hf hinv hγ hγK
  have hΩZ : {y | MapClusterPt y atTop γ} ⊆ Z := by
    intro y hy
    obtain ⟨φ, hφ, hφ0, hφΩ⟩ := hΩinv y hy
    refine hZ y (hΩK y hy) φ hφ hφ0 (fun t => hΩK _ (hφΩ t)) fun t => ?_
    rw [eq_iInf_of_mapClusterPt hK hγK hVc hanti (hφΩ t),
      eq_iInf_of_mapClusterPt hK hγK hVc hanti hy]
  have hsub := subset_largestInvariantSubset hΩZ hΩinv
  exact ⟨nonempty_setOf_mapClusterPt hK hγK, hsub, fun U hU hMU =>
    eventually_mem_of_setOf_mapClusterPt_subset hK hγK hsub hU hMU⟩

variable {V' : E → E →L[ℝ] ℝ}

/-- **LaSalle's invariance principle** (LaSalle 1960; Khalil 2002, Theorem 4.4), with a
Fréchet derivative `V' x` of `V` at each point of `K`. Let `K` be compact and forward invariant
for `x' = f x`, with `f` Lipschitz on `K`, let the orbital derivative satisfy `V' x (f x) ≤ 0`
on `K`, and let `γ` be a forward solution that stays in `K`. Then the ω-limit set of `γ` is
nonempty and contained in the largest forward-invariant subset `M` of
`{x ∈ K | V' x (f x) = 0}`, and `γ t` eventually enters every open set containing `M`. -/
theorem lasalle_of_hasFDerivAt (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hV : ∀ x ∈ K, HasFDerivAt V (V' x) x) (hdV : ∀ x ∈ K, V' x (f x) ≤ 0) :
    {y | MapClusterPt y atTop γ}.Nonempty ∧
      {y | MapClusterPt y atTop γ} ⊆
        largestForwardInvariantSubset f {x | x ∈ K ∧ V' x (f x) = 0} ∧
      ∀ U : Set E, IsOpen U → largestForwardInvariantSubset f {x | x ∈ K ∧ V' x (f x) = 0} ⊆ U →
        ∀ᶠ t in atTop, γ t ∈ U := by
  refine lasalle_of_antitoneOn hK hf hinv hγ hγK (fun x hx => (hV x hx).continuousAt) ?_ ?_
  · refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun t => V' (γ t) (f (γ t))) (convex_Ici 0)
      (fun t ht => (hV _ (hγK t ht)).continuousAt.comp_continuousWithinAt
        (hγ.continuousWithinAt ht)) (fun t ht => ?_) (fun t ht => ?_)
    · rw [interior_Ici] at ht
      exact ((hV _ (hγK t (le_of_lt ht))).comp_hasDerivWithinAt t
        (hγ t (le_of_lt ht))).mono interior_subset
    · rw [interior_Ici] at ht
      exact hdV _ (hγK t (le_of_lt ht))
  · intro x hx φ hφ hφ0 hφK hconst
    have h1 : HasDerivWithinAt (fun t => V (φ t)) (V' (φ 0) (f (φ 0))) (Ici 0) 0 :=
      (hV _ (hφK 0 le_rfl)).comp_hasDerivWithinAt 0 (hφ 0 le_rfl)
    have h2 : HasDerivWithinAt (fun t => V (φ t)) 0 (Ici 0) 0 :=
      (hasDerivWithinAt_const 0 (Ici 0) (V x)).congr (fun t ht => hconst t ht)
        (hconst 0 le_rfl)
    have := (uniqueDiffWithinAt_Ici 0).eq_deriv _ h1 h2
    rw [hφ0] at this
    exact ⟨hx, this⟩

/-- **LaSalle's invariance principle for a `C¹` Lyapunov-like function** (LaSalle 1960;
Khalil 2002, Theorem 4.4). Let `K` be compact and forward invariant for `x' = f x`, with `f`
Lipschitz on `K`; let `V` be `C¹` with `fderiv ℝ V x (f x) ≤ 0` on `K`; and let `γ` be a forward
solution that stays in `K`. Then the ω-limit set of `γ` is nonempty and contained in the largest
forward-invariant subset `M` of `{x ∈ K | fderiv ℝ V x (f x) = 0}`, and `γ t` eventually enters
every open set containing `M`. -/
theorem lasalle (hK : IsCompact K) (hf : LipschitzOnWith L f K) (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hV : ContDiff ℝ 1 V) (hdV : ∀ x ∈ K, fderiv ℝ V x (f x) ≤ 0) :
    {y | MapClusterPt y atTop γ}.Nonempty ∧
      {y | MapClusterPt y atTop γ} ⊆
        largestForwardInvariantSubset f {x | x ∈ K ∧ fderiv ℝ V x (f x) = 0} ∧
      ∀ U : Set E, IsOpen U →
        largestForwardInvariantSubset f {x | x ∈ K ∧ fderiv ℝ V x (f x) = 0} ⊆ U →
        ∀ᶠ t in atTop, γ t ∈ U :=
  lasalle_of_hasFDerivAt hK hf hinv hγ hγK
    (fun x _ => (hV.differentiable one_ne_zero x).hasFDerivAt) hdV

/-- **Convergence to an equilibrium from LaSalle's principle.** Under the hypotheses of
`lasalle_of_hasFDerivAt`, if the largest forward-invariant subset of `{x ∈ K | V' x (f x) = 0}`
is contained in `{x₀}`, then `γ t → x₀`. -/
theorem tendsto_of_lasalle (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hV : ∀ x ∈ K, HasFDerivAt V (V' x) x) (hdV : ∀ x ∈ K, V' x (f x) ≤ 0) {x₀ : E}
    (hM : largestForwardInvariantSubset f {x | x ∈ K ∧ V' x (f x) = 0} ⊆ {x₀}) :
    Tendsto γ atTop (𝓝 x₀) :=
  tendsto_nhds.2 fun U hU hx => (lasalle_of_hasFDerivAt hK hf hinv hγ hγK hV hdV).2.2 U hU
    (hM.trans (singleton_subset_iff.2 hx))

/-- **LaSalle's invariance principle with two-sided invariance** (LaSalle 1960; Khalil 2002,
Theorem 4.4), with a Fréchet derivative `V' x` of `V` at each point of `K`. Under the hypotheses
of `lasalle_of_hasFDerivAt`, the ω-limit set of `γ` is nonempty and contained in the largest
invariant subset `M` of `{x ∈ K | V' x (f x) = 0}` (solutions on all of `ℝ`), and `γ t` eventually
enters every open set containing `M`. -/
theorem lasalle_invariant_of_hasFDerivAt (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hV : ∀ x ∈ K, HasFDerivAt V (V' x) x) (hdV : ∀ x ∈ K, V' x (f x) ≤ 0) :
    {y | MapClusterPt y atTop γ}.Nonempty ∧
      {y | MapClusterPt y atTop γ} ⊆
        largestInvariantSubset f {x | x ∈ K ∧ V' x (f x) = 0} ∧
      ∀ U : Set E, IsOpen U → largestInvariantSubset f {x | x ∈ K ∧ V' x (f x) = 0} ⊆ U →
        ∀ᶠ t in atTop, γ t ∈ U := by
  have hL := lasalle_of_hasFDerivAt hK hf hinv hγ hγK hV hdV
  have hsub := subset_largestInvariantSubset (hL.2.1.trans largestForwardInvariantSubset_subset)
    (isInvariant_setOf_mapClusterPt hK hf hinv hγ hγK)
  exact ⟨hL.1, hsub, fun U hU hMU =>
    eventually_mem_of_setOf_mapClusterPt_subset hK hγK hsub hU hMU⟩

/-- **LaSalle's invariance principle with two-sided invariance for a `C¹` function**
(LaSalle 1960; Khalil 2002, Theorem 4.4). Under the hypotheses of `lasalle`, the ω-limit set of
`γ` is nonempty and contained in the largest invariant subset `M` of
`{x ∈ K | fderiv ℝ V x (f x) = 0}`, and `γ t` eventually enters every open set containing `M`. -/
theorem lasalle_invariant (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hV : ContDiff ℝ 1 V) (hdV : ∀ x ∈ K, fderiv ℝ V x (f x) ≤ 0) :
    {y | MapClusterPt y atTop γ}.Nonempty ∧
      {y | MapClusterPt y atTop γ} ⊆
        largestInvariantSubset f {x | x ∈ K ∧ fderiv ℝ V x (f x) = 0} ∧
      ∀ U : Set E, IsOpen U →
        largestInvariantSubset f {x | x ∈ K ∧ fderiv ℝ V x (f x) = 0} ⊆ U →
        ∀ᶠ t in atTop, γ t ∈ U :=
  lasalle_invariant_of_hasFDerivAt hK hf hinv hγ hγK
    (fun x _ => (hV.differentiable one_ne_zero x).hasFDerivAt) hdV

/-- **Convergence to an equilibrium from the two-sided LaSalle principle.** Under the hypotheses
of `lasalle_of_hasFDerivAt`, if the largest invariant subset of `{x ∈ K | V' x (f x) = 0}` is
contained in `{x₀}`, then `γ t → x₀`. -/
theorem tendsto_of_lasalle_invariant (hK : IsCompact K) (hf : LipschitzOnWith L f K)
    (hinv : IsForwardInvariant f K)
    (hγ : IsIntegralCurveOn γ (fun _ => f) (Ici 0)) (hγK : ∀ t, 0 ≤ t → γ t ∈ K)
    (hV : ∀ x ∈ K, HasFDerivAt V (V' x) x) (hdV : ∀ x ∈ K, V' x (f x) ≤ 0) {x₀ : E}
    (hM : largestInvariantSubset f {x | x ∈ K ∧ V' x (f x) = 0} ⊆ {x₀}) :
    Tendsto γ atTop (𝓝 x₀) :=
  tendsto_nhds.2 fun U hU hx => (lasalle_invariant_of_hasFDerivAt hK hf hinv hγ hγK hV hdV).2.2
    U hU (hM.trans (singleton_subset_iff.2 hx))

end MathlibExt.Analysis.ODE
