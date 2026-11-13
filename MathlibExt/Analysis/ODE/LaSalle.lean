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
public import MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
public import MathlibExt.Biology.Dynamics.ComplexBalanced
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# LaSalle's invariance principle for ordinary differential equations

Let `K` be a compact set that is forward invariant for the autonomous equation `x' = f x`
(`IsForwardInvariant`: through every point of `K` there is a forward solution on `[0, ∞)` staying
in `K`), with `f` Lipschitz on `K`. Let `V` have Fréchet derivative `V' x` at every `x ∈ K` (for
example `V` of class `C¹`) with orbital derivative `V' x (f x) ≤ 0` on `K`. Then every forward
solution `γ` that stays in `K` converges to the largest forward-invariant subset `M` of
`{x ∈ K | V' x (f x) = 0}`: its ω-limit set (the cluster points of `γ t` as `t → ∞`) is nonempty
and contained in `M`, and `γ t` eventually enters every open set containing `M`.

The proof works with the trajectory directly. `V ∘ γ` is nonincreasing and bounded below on `K`,
so `V` is constant on the ω-limit set. The ω-limit set is forward invariant: if `γ (tₙ) → y`,
Grönwall's inequality (`dist_le_of_trajectories_ODE_of_mem`) gives
`dist (γ (tₙ + s)) (φ s) ≤ dist (γ tₙ) y · e^{L s}` for the solution `φ` from `y`
(`mapClusterPt_of_mapClusterPt`). So `V` is constant along solutions from ω-limit points, which
forces `V' (f) = 0` there.

## Main results

* `lasalle_of_antitoneOn`: the principle with no derivative of `V`: `V` continuous on `K` and
  nonincreasing along `γ`, and `Z` any set containing every `x ∈ K` from which some solution in
  `K` keeps `V` constant.
* `lasalle_of_hasFDerivAt`, `lasalle`: the classical statement with `M ⊆ {V' = 0}`, for `V`
  differentiable on `K`, respectively `V` of class `C¹` with `V' = fderiv ℝ V`.
* `tendsto_of_lasalle`: convergence `γ t → x₀` when `M ⊆ {x₀}`.
* `largestForwardInvariantSubset` and its universal property.
* Application, reversible Michaelis–Menten kinetics `E + S ⇌ C ⇌ E + P`
  (`MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten`):
  - `mmNetwork`, `massActionField_mmNetwork`, `isComplexBalanced_mmNetwork`: the mechanism as a
    mass-action network whose equilibria are complex balanced;
  - the Lyapunov function is the **pseudo-Helmholtz function**
    `G = ReactionNetwork.pseudoHelmholtz x*`; `helmholtzRate_mmNetwork_nonpos` is `V' ≤ 0` (the
    Horn–Jackson inequality `ReactionNetwork.helmholtzRate_nonpos` for `mmNetwork`), and
    `IsSolution.antitoneOn_pseudoHelmholtz` is monotonicity along solutions;
  - `IsSolution.pos`: solutions with nonnegative data and positive totals are strictly positive
    for `t > 0`;
  - `IsSolution.tendsto_equilibrium`: **every solution with nonnegative data and positive totals
    converges to the unique (positive) equilibrium of its compatibility class.**

## Scope

* `M` is the largest *forward*-invariant subset of `{V' = 0}`, as in `Flow.lasalle`. The
  classical statement uses the largest invariant subset (solutions on all of `ℝ`), which is
  smaller, so that version of the conclusion is stronger; it is not proved here.
* `f` must be Lipschitz on `K` (this gives continuous dependence on initial data), and the
  forward solutions through points of `K` are taken as a hypothesis, not constructed.
* Compactness of `K` is needed: `MathlibExtTest.Analysis.ODE.LaSalle.noncompact_counterexample`
  (`x' = 1` on `[0, ∞)` with `V = e^{-x}`) satisfies every other hypothesis while its ω-limit set
  is empty.
* The Michaelis–Menten application uses `lasalle_of_antitoneOn`, not `lasalle_of_hasFDerivAt`:
  `G` involves `log`, so it is not differentiable on the boundary of the orthant, which meets the
  compatibility class. Instead `IsSolution.pos` shows that a solution in the class along which `G`
  is constant is positive at `t = 2`, where `G' = 0` makes it an equilibrium.
* Global convergence for general complex-balanced mass-action systems (the global attractor
  conjecture) is not proved; the boundary argument here is specific to this four-species system.

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
* F. Horn and R. Jackson, *General mass action kinetics*, Arch. Rational Mech. Anal. 47 (1972)
  81–116.
* A. Cornish-Bowden, *Fundamentals of Enzyme Kinetics*, 4th ed., Wiley-Blackwell (2012), ch. 2.
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

variable {V : E → ℝ}

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
  have hev : ∀ᶠ t in atTop, γ t ∈ K := (eventually_ge_atTop 0).mono hγK
  have hΩK : ∀ y, MapClusterPt y atTop γ → y ∈ K := fun y hy =>
    mem_of_mapClusterPt_of_eventually_mem hy hK.isClosed hev
  -- `V` is constant on the ω-limit set
  have : Nonempty (Ici (0 : ℝ)) := ⟨⟨0, le_rfl⟩⟩
  have hbdd : BddBelow (range fun t : Ici (0 : ℝ) => V (γ t)) := by
    obtain ⟨m, hm⟩ := (hK.image_of_continuousOn
      fun x hx => (hVc x hx).continuousWithinAt).bddBelow
    exact ⟨m, by rintro _ ⟨t, rfl⟩; exact hm ⟨_, hγK t t.2, rfl⟩⟩
  have hVy : ∀ y, MapClusterPt y atTop γ → V y = ⨅ t : Ici (0 : ℝ), V (γ t) := by
    intro y hy
    have hy' := MapClusterPt.continuousAt_comp (hVc y (hΩK y hy)) hy
    have hmem : ∀ T, 0 ≤ T → V y ∈ Icc (⨅ t : Ici (0 : ℝ), V (γ t)) (V (γ T)) := by
      intro T hT
      refine mem_of_mapClusterPt_of_eventually_mem hy' isClosed_Icc ?_
      filter_upwards [eventually_ge_atTop T] with t ht
      exact ⟨ciInf_le hbdd ⟨t, hT.trans ht⟩, hanti (mem_Ici.2 hT) (mem_Ici.2 (hT.trans ht)) ht⟩
    exact le_antisymm (le_ciInf fun T => (hmem T T.2).2) (hmem 0 le_rfl).1
  -- the ω-limit set is forward invariant and lies in `Z`
  have hΩinv : IsForwardInvariant f {y | MapClusterPt y atTop γ} := by
    intro y hy
    obtain ⟨φ, hφ, hφ0, hφK⟩ := hinv y (hΩK y hy)
    exact ⟨φ, hφ, hφ0, fun s hs => mapClusterPt_of_mapClusterPt hf hγ hγK hy hφ hφ0 hφK hs⟩
  have hΩZ : {y | MapClusterPt y atTop γ} ⊆ Z := by
    intro y hy
    obtain ⟨φ, hφ, hφ0, hφK⟩ := hinv y (hΩK y hy)
    refine hZ y (hΩK y hy) φ hφ hφ0 hφK fun t ht => ?_
    rw [hVy _ (mapClusterPt_of_mapClusterPt hf hγ hγK hy hφ hφ0 hφK ht), hVy y hy]
  have hsub := subset_largestForwardInvariantSubset hΩZ hΩinv
  refine ⟨?_, hsub, fun U hU hMU => ?_⟩
  · obtain ⟨y, -, hy⟩ := hK.exists_mapClusterPt_of_frequently hev.frequently
    exact ⟨y, hy⟩
  · by_contra hnot
    have hfr : ∃ᶠ t in atTop, γ t ∈ K \ U :=
      ((not_eventually.1 hnot).and_eventually hev).mono fun _ h => ⟨h.2, h.1⟩
    obtain ⟨y, hyKU, hy⟩ := (hK.diff hU).exists_mapClusterPt_of_frequently hfr
    exact hyKU.2 (hMU (hsub hy))

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

end MathlibExt.Analysis.ODE

/-! ### Application: reversible Michaelis–Menten kinetics -/

namespace MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten

open MathlibExt.Analysis.ODE MathlibExt.Biology.Dynamics.ComplexBalanced
open MathlibExt.Biology.Dynamics.ComplexBalanced.ReactionNetwork (pseudoHelmholtz)
open MathlibExt.Biology.Dynamics.MichaelisMenten (substrateRate complexRate mmCurve)

variable {k₁ kb k₂ kb₂ : ℝ} {s c e p : ℝ → ℝ}

/-- The reversible Michaelis–Menten mechanism `E + S ⇌ C ⇌ E + P` as a mass-action reaction
network on the species `s, c, e, p` (indices `0, 1, 2, 3`, as in `revField`). Reactions:
`0 : E + S → C`, `1 : C → E + S`, `2 : C → E + P`, `3 : E + P → C`. -/
def mmNetwork : ReactionNetwork (Fin 4) (Fin 4) where
  src := ![![1, 0, 1, 0], ![0, 1, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 1]]
  prod := ![![0, 1, 0, 0], ![1, 0, 1, 0], ![0, 0, 1, 1], ![0, 1, 0, 0]]

/-- The rate constants of `mmNetwork`: `k₁` (binding), `kb` (unbinding of `S`), `k₂`
(catalysis), `kb₂` (rebinding of `P`). -/
def mmRates (k₁ kb k₂ kb₂ : ℝ) : Fin 4 → ℝ := ![k₁, kb, k₂, kb₂]

/-- The mass-action field of `mmNetwork` is the reversible Michaelis–Menten field. -/
theorem massActionField_mmNetwork :
    mmNetwork.massActionField (mmRates k₁ kb k₂ kb₂) = revField k₁ kb k₂ kb₂ := by
  ext x i
  fin_cases i <;>
    simp [ReactionNetwork.massActionField, mmNetwork, mmRates, Fin.sum_univ_four,
      Fin.prod_univ_four, revField, substrateRate, revComplexRate, complexRate,
      revProductRate] <;> ring

/-- **Equilibria are complex balanced.** Every zero of `revField` (a detailed-balanced state,
`revField_eq_zero_iff`) is a complex-balanced state of `mmNetwork`. -/
theorem isComplexBalanced_mmNetwork {x : Fin 4 → ℝ} (hx : revField k₁ kb k₂ kb₂ x = 0) :
    mmNetwork.IsComplexBalanced (mmRates k₁ kb k₂ kb₂) x := by
  obtain ⟨h1, h2⟩ := revField_eq_zero_iff.1 hx
  have hr : ∀ r, mmNetwork.rate (mmRates k₁ kb k₂ kb₂) x r =
      ![k₁ * x 0 * x 2, kb * x 1, k₂ * x 1, kb₂ * x 2 * x 3] r := by
    intro r
    fin_cases r <;> simp [ReactionNetwork.rate, mmNetwork, mmRates, Fin.prod_univ_four] <;> ring
  have e12 : mmNetwork.src 2 = mmNetwork.src 1 := rfl
  have p0 : mmNetwork.prod 0 = mmNetwork.src 1 := rfl
  have p1 : mmNetwork.prod 1 = mmNetwork.src 0 := rfl
  have p2 : mmNetwork.prod 2 = mmNetwork.src 3 := rfl
  have p3 : mmNetwork.prod 3 = mmNetwork.src 1 := rfl
  intro z
  rw [Finset.sum_filter, Finset.sum_filter]
  simp only [Fin.sum_univ_four, hr, e12, p0, p1, p2, p3]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  split_ifs <;> linarith

/-- The terms of the pseudo-Helmholtz gap: for `a > 0` and `y ≥ 0`,
`y (log y - log a - 1) + a ≥ 0`, with equality only at `y = a`. -/
private theorem helmholtz_gap_pos {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) (hne : y ≠ a) :
    0 < y * (Real.log y - Real.log a - 1) + a := by
  rcases hy.eq_or_lt with rfl | hy
  · simpa using ha
  have hne' : a / y ≠ 1 := fun h => hne ((div_eq_one_iff_eq hy.ne').1 h).symm
  have hlt := Real.log_lt_sub_one_of_pos (div_pos ha hy) hne'
  rw [Real.log_div ha.ne' hy.ne'] at hlt
  have := mul_lt_mul_of_pos_left hlt hy
  rw [mul_sub, mul_sub, mul_div_cancel₀ _ hy.ne'] at this
  nlinarith

private theorem helmholtz_gap_nonneg {a y : ℝ} (ha : 0 < a) (hy : 0 ≤ y) :
    0 ≤ y * (Real.log y - Real.log a - 1) + a := by
  rcases eq_or_ne y a with rfl | hne
  · simp
  · exact (helmholtz_gap_pos ha hy hne).le

/-- **Gibbs inequality for the pseudo-Helmholtz function.** For a positive reference state
`cstar` and a nonnegative state `y`, `pseudoHelmholtz cstar y = pseudoHelmholtz cstar cstar`
only if `y = cstar`. -/
theorem eq_of_pseudoHelmholtz_eq {cstar y : Fin 4 → ℝ} (hcstar : ∀ i, 0 < cstar i)
    (hy : ∀ i, 0 ≤ y i) (h : pseudoHelmholtz cstar y = pseudoHelmholtz cstar cstar) :
    y = cstar := by
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
  have hgap : pseudoHelmholtz cstar y - pseudoHelmholtz cstar cstar =
      ∑ j, (y j * (Real.log (y j) - Real.log (cstar j) - 1) + cstar j) := by
    unfold pseudoHelmholtz
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hpos : 0 < ∑ j, (y j * (Real.log (y j) - Real.log (cstar j) - 1) + cstar j) :=
    Finset.sum_pos' (fun j _ => helmholtz_gap_nonneg (hcstar j) (hy j))
      ⟨i, Finset.mem_univ _, helmholtz_gap_pos (hcstar i) (hy i) hi⟩
  rw [← hgap, h, sub_self] at hpos
  exact lt_irrefl _ hpos

/-- `x t e^{a t}` is nondecreasing when `x' ≥ -a x`, so positivity of `x` persists. -/
private theorem pos_of_pos_of_deriv_ge {x x' : ℝ → ℝ} {a : ℝ}
    (hd : ∀ t, 0 ≤ t → HasDerivAt x (x' t) t) (hb : ∀ t, 0 ≤ t → -a * x t ≤ x' t)
    {t₀ t : ℝ} (h₀ : 0 ≤ t₀) (ht : t₀ ≤ t) (hpos : 0 < x t₀) : 0 < x t := by
  have hmono : MonotoneOn (fun τ => x τ * Real.exp (a * τ)) (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun τ => (x' τ + a * x τ) * Real.exp (a * τ)) (convex_Ici 0) ?_ ?_ ?_
    · intro τ hτ
      exact ((hd τ hτ).continuousAt.mul (by fun_prop)).continuousWithinAt
    · intro τ hτ
      rw [interior_Ici] at hτ
      have he : HasDerivAt (fun τ => Real.exp (a * τ)) (Real.exp (a * τ) * a) τ := by
        simpa using ((hasDerivAt_id' τ).const_mul a).exp
      have : HasDerivAt (fun τ => x τ * Real.exp (a * τ))
          (x' τ * Real.exp (a * τ) + x τ * (Real.exp (a * τ) * a)) τ :=
        (hd τ (le_of_lt hτ)).mul he
      convert this.hasDerivWithinAt using 1
      ring
    · intro τ hτ
      rw [interior_Ici] at hτ
      exact mul_nonneg (by linarith [hb τ (le_of_lt hτ)]) (Real.exp_pos _).le
  have h1 : 0 < x t₀ * Real.exp (a * t₀) := mul_pos hpos (Real.exp_pos _)
  have h2 := hmono (mem_Ici.2 h₀) (mem_Ici.2 (h₀.trans ht)) ht
  exact (pos_iff_pos_of_mul_pos (h1.trans_le h2)).2 (Real.exp_pos _)

/-- A function constant on an open interval has derivative `0` inside it. -/
private theorem deriv_eq_zero_of_eqOn_Ioo {x : ℝ → ℝ} {d a b C τ : ℝ} (hx : HasDerivAt x d τ)
    (hz : ∀ u ∈ Ioo a b, x u = C) (hτ : τ ∈ Ioo a b) : d = 0 :=
  hx.unique ((hasDerivAt_const τ C).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds hτ.1 hτ.2) hz))

/-- **Strict positivity.** For positive rate constants, nonnegative initial data and positive
totals `E_T = e₀ + c₀`, `S_T = s₀ + c₀ + p₀`, every solution has all four coordinates strictly
positive at every `t > 0`, even if some start at `0`. -/
theorem IsSolution.pos (h : IsSolution k₁ kb k₂ kb₂ s c e p) (hk₁ : 0 < k₁) (hkb : 0 < kb)
    (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂) (hs₀ : 0 ≤ s 0) (hc₀ : 0 ≤ c 0) (he₀ : 0 ≤ e 0)
    (hp₀ : 0 ≤ p 0) (hE : 0 < e 0 + c 0) (hS : 0 < s 0 + c 0 + p 0) {t : ℝ} (ht : 0 < t) :
    0 < s t ∧ 0 < c t ∧ 0 < e t ∧ 0 < p t := by
  have hnn := fun τ (hτ : 0 ≤ τ) => h.nonneg hk₁.le hkb.le hk₂.le hkb₂.le hs₀ hc₀ he₀ hp₀ hτ
  have hEc := fun τ (hτ : 0 ≤ τ) => h.enzyme_conservation hτ
  have hSc := fun τ (hτ : 0 ≤ τ) => h.substrate_conservation hτ
  -- positivity of each coordinate persists forward in time
  have hs_p : ∀ τ, 0 ≤ τ → τ ≤ t → 0 < s τ → 0 < s t := fun τ hτ hτt hpos =>
    pos_of_pos_of_deriv_ge (a := k₁ * (e 0 + c 0)) h.hasDerivAt_substrate (fun u hu => by
      obtain ⟨hsu, hcu, heu, hpu⟩ := hnn u hu
      rw [← hEc u hu]
      simp only [substrateRate]
      nlinarith [mul_nonneg (mul_nonneg hk₁.le hcu) hsu, mul_nonneg hkb.le hcu]) hτ hτt hpos
  have hc_p : ∀ τ, 0 ≤ τ → τ ≤ t → 0 < c τ → 0 < c t := fun τ hτ hτt hpos =>
    pos_of_pos_of_deriv_ge (a := kb + k₂) h.hasDerivAt_complex (fun u hu => by
      obtain ⟨hsu, hcu, heu, hpu⟩ := hnn u hu
      simp only [revComplexRate, complexRate]
      nlinarith [mul_nonneg (mul_nonneg hk₁.le heu) hsu, mul_nonneg (mul_nonneg hkb₂.le heu) hpu])
      hτ hτt hpos
  have he_p : ∀ τ, 0 ≤ τ → τ ≤ t → 0 < e τ → 0 < e t := fun τ hτ hτt hpos =>
    pos_of_pos_of_deriv_ge (a := (k₁ + kb₂) * (s 0 + c 0 + p 0)) h.hasDerivAt_enzyme
      (fun u hu => by
        obtain ⟨hsu, hcu, heu, hpu⟩ := hnn u hu
        rw [← hSc u hu]
        simp only [revComplexRate, complexRate]
        nlinarith [mul_nonneg (mul_nonneg hk₁.le heu) (add_nonneg hcu hpu),
          mul_nonneg (mul_nonneg hkb₂.le heu) (add_nonneg hsu hcu),
          mul_nonneg (add_nonneg hkb.le hk₂.le) hcu]) hτ hτt hpos
  have hp_p : ∀ τ, 0 ≤ τ → τ ≤ t → 0 < p τ → 0 < p t := fun τ hτ hτt hpos =>
    pos_of_pos_of_deriv_ge (a := kb₂ * (e 0 + c 0)) h.hasDerivAt_product (fun u hu => by
      obtain ⟨hsu, hcu, heu, hpu⟩ := hnn u hu
      rw [← hEc u hu]
      simp only [revProductRate]
      nlinarith [mul_nonneg hk₂.le hcu, mul_nonneg (mul_nonneg hkb₂.le hcu) hpu]) hτ hτt hpos
  -- a coordinate that vanishes at `t` vanishes on `[0, t]`
  have zero_on : ∀ x : ℝ → ℝ, (∀ τ, 0 ≤ τ → 0 ≤ x τ) →
      (∀ τ, 0 ≤ τ → τ ≤ t → 0 < x τ → 0 < x t) → ¬ 0 < x t → ∀ u ∈ Ioo 0 t, x u = 0 :=
    fun x hx hpers hxt u hu => le_antisymm (not_lt.1 fun hpos =>
      hxt (hpers u hu.1.le hu.2.le hpos)) (hx u hu.1.le)
  have hm : t / 2 ∈ Ioo 0 t := ⟨by linarith, by linarith⟩
  -- `c ≡ 0` on `(0, t)` is impossible
  have hc_ne : ¬ ∀ u ∈ Ioo 0 t, c u = 0 := by
    intro hc0
    have hd := deriv_eq_zero_of_eqOn_Ioo (h.hasDerivAt_complex _ hm.1.le) hc0 hm
    obtain ⟨hsu, -, heu, hpu⟩ := hnn _ hm.1.le
    have hEm := hEc _ hm.1.le
    have hSm := hSc _ hm.1.le
    rw [hc0 _ hm] at hEm hSm
    simp only [revComplexRate, complexRate, hc0 _ hm] at hd
    have he' : e (t / 2) = e 0 + c 0 := by linarith
    rw [he'] at hd
    have hA := mul_nonneg (mul_nonneg hk₁.le hE.le) hsu
    have hB := mul_nonneg (mul_nonneg hkb₂.le hE.le) hpu
    have h1 : k₁ * (e 0 + c 0) * s (t / 2) = 0 := by linarith
    have h2 : kb₂ * (e 0 + c 0) * p (t / 2) = 0 := by linarith
    have hs' := (mul_eq_zero.1 h1).resolve_left (mul_pos hk₁ hE).ne'
    have hp' := (mul_eq_zero.1 h2).resolve_left (mul_pos hkb₂ hE).ne'
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hst
    have hs0 := zero_on s (fun τ hτ => (hnn τ hτ).1) hs_p hst
    refine hc_ne fun u hu => ?_
    have hd := deriv_eq_zero_of_eqOn_Ioo (h.hasDerivAt_substrate u hu.1.le) hs0 hu
    simp only [substrateRate, hs0 u hu] at hd
    have : kb * c u = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hkb.ne'
  · by_contra hct
    exact hc_ne (zero_on c (fun τ hτ => (hnn τ hτ).2.1) hc_p hct)
  · by_contra het
    have he0 := zero_on e (fun τ hτ => (hnn τ hτ).2.2.1) he_p het
    have hd := deriv_eq_zero_of_eqOn_Ioo (h.hasDerivAt_enzyme _ hm.1.le) he0 hm
    have hEm := hEc _ hm.1.le
    simp only [revComplexRate, complexRate, he0 _ hm] at hd hEm
    nlinarith [add_pos hkb hk₂]
  · by_contra hpt
    have hp0 := zero_on p (fun τ hτ => (hnn τ hτ).2.2.2) hp_p hpt
    refine hc_ne fun u hu => ?_
    have hd := deriv_eq_zero_of_eqOn_Ioo (h.hasDerivAt_product u hu.1.le) hp0 hu
    simp only [revProductRate, hp0 u hu] at hd
    have : k₂ * c u = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_left hk₂.ne'

/-- **The orbital derivative of the pseudo-Helmholtz function.** Along any curve with
`φ' = revField (φ t)` at a time where `φ t > 0`, `G = pseudoHelmholtz cstar` has derivative
`mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar (φ t)`. -/
theorem hasDerivAt_pseudoHelmholtz_revField (cstar : Fin 4 → ℝ) {φ : ℝ → Fin 4 → ℝ} {t : ℝ}
    (hφ : HasDerivAt φ (revField k₁ kb k₂ kb₂ (φ t)) t) (hpos : ∀ i, 0 < φ t i) :
    HasDerivAt (fun τ => pseudoHelmholtz cstar (φ τ))
      (mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar (φ t)) t :=
  mmNetwork.hasDerivAt_pseudoHelmholtz cstar (by rw [massActionField_mmNetwork]; exact hφ) hpos

/-- **`V' ≤ 0` for reversible Michaelis–Menten.** For positive rate constants and a positive
equilibrium `cstar` (a zero of `revField`), the orbital derivative of the pseudo-Helmholtz
function `G = pseudoHelmholtz cstar` is `≤ 0` at every positive state, and it vanishes exactly
at the equilibria. This is the Horn–Jackson inequality `ReactionNetwork.helmholtzRate_nonpos`
for `mmNetwork`, whose hypothesis (complex balance of `cstar`) is detailed balance,
`revField_eq_zero_iff`. -/
theorem helmholtzRate_mmNetwork_nonpos (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂)
    (hkb₂ : 0 < kb₂) {cstar x : Fin 4 → ℝ} (hcstar : ∀ i, 0 < cstar i)
    (hf : revField k₁ kb k₂ kb₂ cstar = 0) (hx : ∀ i, 0 < x i) :
    mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar x ≤ 0 ∧
      (mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar x = 0 ↔
        revField k₁ kb k₂ kb₂ x = 0) := by
  have hk : ∀ r, 0 < mmRates k₁ kb k₂ kb₂ r := fun r => by
    fin_cases r <;> simp [mmRates, hk₁, hkb, hk₂, hkb₂]
  refine ⟨mmNetwork.helmholtzRate_nonpos hk hcstar (isComplexBalanced_mmNetwork hf) hx, ?_⟩
  rw [mmNetwork.helmholtzRate_eq_zero_iff hk hcstar (isComplexBalanced_mmNetwork hf) hx,
    massActionField_mmNetwork]

/-- The pseudo-Helmholtz function is continuous on the whole space (with `0 log 0 = 0`). -/
theorem continuous_pseudoHelmholtz (cstar : Fin 4 → ℝ) : Continuous (pseudoHelmholtz cstar) := by
  unfold pseudoHelmholtz
  refine continuous_finsetSum _ fun i _ => ?_
  have : (fun y : Fin 4 → ℝ => y i * (Real.log (y i) - Real.log (cstar i) - 1)) =
      fun y => y i * Real.log (y i) - y i * (Real.log (cstar i) + 1) := by
    funext y; ring
  rw [this]
  exact (Real.continuous_mul_log.comp (continuous_apply i)).sub
    ((continuous_apply i).mul continuous_const)

/-- **The pseudo-Helmholtz function is a Lyapunov function for reversible Michaelis–Menten.**
For positive rate constants, a positive equilibrium `cstar`, nonnegative initial data and
positive totals, `t ↦ pseudoHelmholtz cstar (s t, c t, e t, p t)` is nonincreasing on
`[0, ∞)`, also for solutions that start on the boundary of the orthant. -/
theorem IsSolution.antitoneOn_pseudoHelmholtz (h : IsSolution k₁ kb k₂ kb₂ s c e p)
    (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂) (hs₀ : 0 ≤ s 0)
    (hc₀ : 0 ≤ c 0) (he₀ : 0 ≤ e 0) (hp₀ : 0 ≤ p 0) (hE : 0 < e 0 + c 0)
    (hS : 0 < s 0 + c 0 + p 0) {cstar : Fin 4 → ℝ} (hcstar : ∀ i, 0 < cstar i)
    (hf : revField k₁ kb k₂ kb₂ cstar = 0) :
    AntitoneOn (fun t => pseudoHelmholtz cstar (mmCurve s c e p t)) (Ici 0) := by
  have hd := isSolution_iff_hasDerivAt_mmCurve.1 h
  have hpos : ∀ t, 0 < t → ∀ i, 0 < mmCurve s c e p t i := fun t ht i => by
    obtain ⟨h1, h2, h3, h4⟩ := h.pos hk₁ hkb hk₂ hkb₂ hs₀ hc₀ he₀ hp₀ hE hS ht
    fin_cases i <;> simpa [mmCurve]
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun t => mmNetwork.helmholtzRate (mmRates k₁ kb k₂ kb₂) cstar (mmCurve s c e p t))
    (convex_Ici 0) ((continuous_pseudoHelmholtz cstar).comp_continuousOn
      fun t ht => (hd t ht).continuousAt.continuousWithinAt) (fun t ht => ?_) (fun t ht => ?_)
  · rw [interior_Ici] at ht
    exact (hasDerivAt_pseudoHelmholtz_revField cstar (hd t (le_of_lt ht))
      (hpos t ht)).hasDerivWithinAt
  · rw [interior_Ici] at ht
    exact (helmholtzRate_mmNetwork_nonpos hk₁ hkb hk₂ hkb₂ hcstar hf (hpos t ht)).1

/-- **Global convergence for reversible Michaelis–Menten kinetics, via LaSalle.** For positive
rate constants, every solution with nonnegative initial data and positive totals
`E_T = e₀ + c₀`, `S_T = s₀ + c₀ + p₀` converges to the unique equilibrium `x*` of its
compatibility class (`existsUnique_equilibrium`), which is positive.

Proof: `lasalle_of_antitoneOn` on the compact, convex, forward-invariant class
`K = {x ≥ 0 | x₂ + x₁ = E_T, x₀ + x₁ + x₃ = S_T}` with the Lyapunov function
`G = pseudoHelmholtz x*` (`IsSolution.antitoneOn_pseudoHelmholtz`). A solution in `K` along
which `G` is constant is positive at `t = 2` (`IsSolution.pos`), so there its orbital derivative
vanishes, hence it sits at an equilibrium of the class, i.e. at `x*`; since `G` is constant, the
Gibbs inequality `eq_of_pseudoHelmholtz_eq` forces the starting point to be `x*` as well. So
the largest forward-invariant set on which `G` is constant is `{x*}`. -/
theorem IsSolution.tendsto_equilibrium (h : IsSolution k₁ kb k₂ kb₂ s c e p)
    (hk₁ : 0 < k₁) (hkb : 0 < kb) (hk₂ : 0 < k₂) (hkb₂ : 0 < kb₂) (hs₀ : 0 ≤ s 0)
    (hc₀ : 0 ≤ c 0) (he₀ : 0 ≤ e 0) (hp₀ : 0 ≤ p 0) (hE : 0 < e 0 + c 0)
    (hS : 0 < s 0 + c 0 + p 0) :
    ∃ xs : Fin 4 → ℝ, (∀ i, 0 < xs i) ∧ xs 2 + xs 1 = e 0 + c 0 ∧
      xs 0 + xs 1 + xs 3 = s 0 + c 0 + p 0 ∧ revField k₁ kb k₂ kb₂ xs = 0 ∧
      Tendsto (mmCurve s c e p) atTop (𝓝 xs) := by
  obtain ⟨xs, ⟨hxs0, hxsE, hxsS, hxsf⟩, huniq⟩ :=
    existsUnique_equilibrium hk₁ hkb hk₂ hkb₂ hE hS
  have hxs := pos_of_equilibrium hk₁ hkb hk₂ hkb₂ hE hS hxs0 hxsE hxsS hxsf
  have hanti := h.antitoneOn_pseudoHelmholtz hk₁ hkb hk₂ hkb₂ hs₀ hc₀ he₀ hp₀ hE hS hxs hxsf
  set ET := e 0 + c 0
  set ST := s 0 + c 0 + p 0
  set K : Set (Fin 4 → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ x 2 + x 1 = ET ∧ x 0 + x 1 + x 3 = ST}
    with hKdef
  -- the compatibility class is compact and convex
  have hKclosed : IsClosed K := by
    refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
    · have : {x : Fin 4 → ℝ | ∀ i, 0 ≤ x i} = Ici 0 := by ext x; simp [Pi.le_def]
      have hc0 : IsClosed {x : Fin 4 → ℝ | ∀ i, 0 ≤ x i} := by rw [this]; exact isClosed_Ici
      exact hc0
    · exact isClosed_eq (by fun_prop) continuous_const
    · exact isClosed_eq (by fun_prop) continuous_const
  have hKc : IsCompact K := by
    refine (isCompact_Icc (a := (0 : Fin 4 → ℝ)) (b := fun _ => ET + ST)).of_isClosed_subset
      hKclosed ?_
    rintro x ⟨hx, hxE, hxS⟩
    refine ⟨fun i => hx i, fun i => ?_⟩
    have := hx 0; have := hx 1; have := hx 2; have := hx 3
    fin_cases i <;> simp <;> linarith
  have hKconv : Convex ℝ K := by
    rintro x ⟨hx, hxE, hxS⟩ y ⟨hy, hyE, hyS⟩ a b ha hb hab
    refine ⟨fun i => ?_, ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a * hxE + b * hyE + ET * hab
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination a * hxS + b * hyS + ST * hab
  -- the field is Lipschitz on the class
  have hcd : ContDiff ℝ 1 (revField k₁ kb k₂ kb₂) := revField_contDiff
  obtain ⟨C, hC⟩ :=
    hKc.exists_bound_of_continuousOn (hcd.continuous_fderiv one_ne_zero).continuousOn
  have hlip : LipschitzOnWith ⟨max C 0, le_max_right _ _⟩ (revField k₁ kb k₂ kb₂) K :=
    hKconv.lipschitzOnWith_of_nnnorm_fderiv_le (fun x _ => hcd.differentiable one_ne_zero x)
      (fun x hx => NNReal.coe_le_coe.1 ((hC x hx).trans (le_max_left _ _)))
  -- the class is forward invariant
  have hinv : IsForwardInvariant (revField k₁ kb k₂ kb₂) K := by
    rintro x ⟨hx, hxE, hxS⟩
    obtain ⟨s', c', e', p', hsol, hs', hc', he', hp', hnn', hE', hS'⟩ :=
      exists_isSolution_nonneg hk₁.le hkb.le hk₂.le hkb₂.le (hx 0) (hx 1) (hx 2) (hx 3)
    refine ⟨mmCurve s' c' e' p',
      fun t ht => (isSolution_iff_hasDerivAt_mmCurve.1 hsol t ht).hasDerivWithinAt, ?_,
      fun t ht => ?_⟩
    · ext i; fin_cases i <;> simp [mmCurve, hs', hc', he', hp']
    · obtain ⟨h1, h2, h3, h4⟩ := hnn' t ht
      refine ⟨fun i => ?_, ?_, ?_⟩
      · fin_cases i <;> simpa [mmCurve]
      · simp only [mmCurve, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        rw [hE' t ht, hxE]
      · simp only [mmCurve, Fin.isValue, Matrix.cons_val, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        rw [hS' t ht, hxS]
  -- the given solution
  have hγ : IsIntegralCurveOn (mmCurve s c e p) (fun _ => revField k₁ kb k₂ kb₂) (Ici 0) :=
    fun t ht => (isSolution_iff_hasDerivAt_mmCurve.1 h t ht).hasDerivWithinAt
  have hγK : ∀ t, 0 ≤ t → mmCurve s c e p t ∈ K := fun t ht => by
    obtain ⟨h1, h2, h3, h4⟩ := h.nonneg hk₁.le hkb.le hk₂.le hkb₂.le hs₀ hc₀ he₀ hp₀ ht
    refine ⟨fun i => ?_, ?_, ?_⟩
    · fin_cases i <;> simpa [mmCurve]
    · simpa [mmCurve] using h.enzyme_conservation ht
    · simpa [mmCurve] using h.substrate_conservation ht
  -- a solution in the class along which `G` is constant starts at `xs`
  have hZ : ∀ x ∈ K, ∀ φ : ℝ → Fin 4 → ℝ,
      IsIntegralCurveOn φ (fun _ => revField k₁ kb k₂ kb₂) (Ici 0) → φ 0 = x →
      (∀ t, 0 ≤ t → φ t ∈ K) → (∀ t, 0 ≤ t → pseudoHelmholtz xs (φ t) = pseudoHelmholtz xs x) →
      x ∈ ({xs} : Set (Fin 4 → ℝ)) := by
    intro x hx φ hφ hφ0 hφK hconst
    have hφd : ∀ t, 0 < t → HasDerivAt φ (revField k₁ kb k₂ kb₂ (φ t)) t := fun t ht =>
      (hφ t ht.le).hasDerivAt (Ici_mem_nhds ht)
    have hψ : IsSolution k₁ kb k₂ kb₂ (fun t => φ (t + 1) 0) (fun t => φ (t + 1) 1)
        (fun t => φ (t + 1) 2) (fun t => φ (t + 1) 3) := by
      rw [isSolution_iff_hasDerivAt_mmCurve]
      have hc : mmCurve (fun t => φ (t + 1) 0) (fun t => φ (t + 1) 1) (fun t => φ (t + 1) 2)
          (fun t => φ (t + 1) 3) = fun t => φ (t + 1) := by
        funext t; ext i; fin_cases i <;> rfl
      rw [hc]
      intro t ht
      exact HasDerivAt.comp_add_const t 1 (hφd (t + 1) (by linarith))
    obtain ⟨h1K, h1E, h1S⟩ := hφK 1 zero_le_one
    have hpos2 := hψ.pos hk₁ hkb hk₂ hkb₂ (by simpa using h1K 0) (by simpa using h1K 1)
      (by simpa using h1K 2) (by simpa using h1K 3) (by simp only [zero_add]; linarith)
      (by simp only [zero_add]; linarith) one_pos
    norm_num at hpos2
    have hp2 : ∀ i, 0 < φ 2 i := fun i => by
      fin_cases i
      · exact hpos2.1
      · exact hpos2.2.1
      · exact hpos2.2.2.1
      · exact hpos2.2.2.2
    have hrate := deriv_eq_zero_of_eqOn_Ioo
      (hasDerivAt_pseudoHelmholtz_revField xs (hφd 2 two_pos) hp2) (a := 0) (b := 3)
      (fun u hu => hconst u hu.1.le) ⟨two_pos, by norm_num⟩
    have hf2 : revField k₁ kb k₂ kb₂ (φ 2) = 0 :=
      ((helmholtzRate_mmNetwork_nonpos hk₁ hkb hk₂ hkb₂ hxs hxsf hp2).2).1 hrate
    have heq : φ 2 = xs := huniq _ ⟨(hφK 2 two_pos.le).1, (hφK 2 two_pos.le).2.1,
      (hφK 2 two_pos.le).2.2, hf2⟩
    have hG : pseudoHelmholtz xs x = pseudoHelmholtz xs xs := by
      rw [← hconst 2 two_pos.le, heq]
    exact eq_of_pseudoHelmholtz_eq hxs hx.1 hG
  have res := lasalle_of_antitoneOn hKc hlip hinv hγ hγK
    (fun x _ => (continuous_pseudoHelmholtz xs).continuousAt) hanti hZ
  exact ⟨xs, hxs, hxsE, hxsS, hxsf, tendsto_nhds.2 fun U hU hx => res.2.2 U hU
    (largestForwardInvariantSubset_subset.trans (singleton_subset_iff.2 hx))⟩

end MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten
