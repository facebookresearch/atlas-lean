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

The application to reversible Michaelis–Menten kinetics, convergence of every solution to the
equilibrium of its compatibility class, is in
`MathlibExt.Biology.Dynamics.ReversibleMichaelisMenten.LaSalle`.

## Scope

* `M` is the largest *forward*-invariant subset of `{V' = 0}`, as in `Flow.lasalle`. The
  classical statement uses the largest invariant subset (solutions on all of `ℝ`), which is
  smaller, so that version of the conclusion is stronger; it is not proved here.
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
