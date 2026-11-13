/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

open scoped Topology Pointwise

namespace MathlibExt.Analysis.Convex.KarushKuhnTucker

/-!
# Karush–Kuhn–Tucker conditions

A finite-dimensional Gordan alternative (strict linear solvability versus a
nontrivial nonnegative dependence), proved by strictly separating the negative
orthant from the range-plus-nonnegative-orthant sum, implies the
inequality-only KKT theorem: at a feasible local minimum satisfying LICQ on
the active constraints, a strict descent direction would contradict local
minimality along `t ↦ x + t • d`, so the alternative supplies nonnegative
multipliers with complementarity and stationarity.

Conversely, for convex problems the KKT conditions are sufficient:
`isMinOn_of_karush_kuhn_tucker_convex` shows that nonnegative multipliers with complementary
slackness and stationarity at `x` give `f x ≤ f y` for every feasible `y`, so a feasible `x` is a
global minimizer on the feasible set, with no constraint qualification (Boyd and Vandenberghe,
*Convex Optimization*, §5.5.3). Its ingredient is the first-order convexity inequality
`ConvexOn.add_fderiv_sub_le`.
-/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gordan alternative for continuous linear functionals: either they are
jointly strictly negative somewhere, or some nontrivial nonnegative
combination vanishes. Proved by strictly separating the negative orthant
from the range-plus-nonneg-orthant sum. -/
private lemma gordan {ι : Type*} [Fintype ι] (ℓ : ι → E →L[ℝ] ℝ) :
    (∃ d : E, ∀ i, (ℓ i) d < 0) ∨
      ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ p ≠ 0 ∧ ∑ i, p i • ℓ i = 0 := by
  classical
  by_cases h : ∃ d : E, ∀ i, (ℓ i) d < 0
  · exact Or.inl h
  · right
    set Lmap : E →ₗ[ℝ] (ι → ℝ) := LinearMap.pi (fun i => (ℓ i).toLinearMap)
    have hLmap : ∀ d i, Lmap d i = (ℓ i) d := fun d i => rfl
    set L : Submodule ℝ (ι → ℝ) := Lmap.range with hL
    set U : Set (ι → ℝ) := {v | ∀ i, v i < 0}
    set O : Set (ι → ℝ) := {w | ∀ i, 0 ≤ w i}
    set C : Set (ι → ℝ) := (L : Set (ι → ℝ)) + O with hC
    have hLconv : Convex ℝ (L : Set (ι → ℝ)) := by
      intro x hx y hy a b ha hb _hab
      exact L.add_mem (L.smul_mem a hx) (L.smul_mem b hy)
    have hOconv : Convex ℝ O := by
      intro x hx y hy a b ha hb _hab i
      change 0 ≤ (a • x + b • y) i
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))
    have hCconv : Convex ℝ C := hLconv.add hOconv
    have hUopen : IsOpen U := by
      have hUU : U = ⋂ i, (fun v : ι → ℝ => v i) ⁻¹' (Set.Iio 0) := by
        ext v
        simp [U]
      rw [hUU]
      exact isOpen_iInter_of_finite
        (fun i => IsOpen.preimage (continuous_apply i) isOpen_Iio)
    have hUconv : Convex ℝ U := by
      intro x hx y hy a b ha hb hab i
      change (a • x + b • y) i < 0
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      have h1 : a * x i ≤ 0 := by
        have h := mul_le_mul_of_nonneg_left (le_of_lt (hx i)) ha
        rwa [mul_zero] at h
      have h2 : b * y i ≤ 0 := by
        have h := mul_le_mul_of_nonneg_left (le_of_lt (hy i)) hb
        rwa [mul_zero] at h
      by_cases ha0 : a = 0
      · subst ha0
        rw [zero_add] at hab
        rw [zero_mul, zero_add, hab, one_mul]
        exact hy i
      · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        have hlt : a * x i < 0 := mul_neg_of_pos_of_neg hapos (hx i)
        have hsum := add_lt_add_of_lt_of_le hlt h2
        rwa [add_zero] at hsum
    have hdisj : Disjoint U C := by
      rw [Set.disjoint_left]
      intro x hxU hxC
      rw [hC, Set.mem_add] at hxC
      obtain ⟨v, hvL, w, hwO, rfl⟩ := hxC
      simp only [hL] at hvL
      obtain ⟨d, rfl⟩ := hvL
      apply h
      refine ⟨d, fun i => ?_⟩
      have hvi : (Lmap d) i + w i < 0 := by
        rw [← Pi.add_apply]
        exact hxU i
      have h3 : (Lmap d) i < 0 := by linarith [hwO i]
      rw [hLmap d i] at h3
      exact h3
    obtain ⟨f, u, hUlt, hCge⟩ :=
      geometric_hahn_banach_open hUconv hUopen hCconv hdisj
    have h0C : (0 : ι → ℝ) ∈ C := by
      rw [hC, Set.mem_add]
      refine ⟨0, L.zero_mem, 0, fun i => le_refl 0, ?_⟩
      simp
    have hu0 : u ≤ 0 := by
      simpa using hCge 0 h0C
    have hscale : ∀ c : ℝ, c ≠ 0 → ∃ t : ℝ, t * c < u := by
      intro c hc
      by_cases hneg : c < 0
      · refine ⟨u / c + 1, ?_⟩
        rw [add_mul, div_mul_cancel₀ _ (ne_of_lt hneg), one_mul]
        linarith
      · have hpos : 0 < c :=
          lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hc)
        refine ⟨u / c - 1, ?_⟩
        rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hpos), one_mul]
        linarith
    have hLker : ∀ v ∈ (L : Set (ι → ℝ)), f v = 0 := by
      intro v hv
      by_contra hne
      obtain ⟨t, ht⟩ := hscale (f v) hne
      have hmem : t • v + 0 ∈ C := by
        rw [hC, Set.mem_add]
        exact ⟨t • v, L.smul_mem t hv, 0, fun i => le_refl 0, rfl⟩
      have hle := hCge _ hmem
      rw [map_add, map_smul, smul_eq_mul, map_zero, add_zero] at hle
      exact not_lt_of_ge hle ht
    set p : ι → ℝ := fun i => f (Pi.single i 1)
    have hp_apply : ∀ i, p i = f (Pi.single i 1) := fun i => rfl
    have hpi : ∀ i, 0 ≤ p i := by
      intro i
      by_contra hneg
      rw [not_le, hp_apply] at hneg
      set t : ℝ := |u / f (Pi.single i 1)| + 1 with ht
      have ht0 : 0 ≤ t := by
        rw [ht]
        positivity
      have hmem : 0 + t • Pi.single i 1 ∈ C := by
        rw [hC, Set.mem_add]
        refine ⟨0, L.zero_mem, t • Pi.single i 1, ?_, rfl⟩
        intro j
        show 0 ≤ (t • Pi.single i (1 : ℝ)) j
        rw [Pi.smul_apply, smul_eq_mul]
        apply mul_nonneg ht0
        rw [Pi.single_apply]
        split_ifs <;> simp
      have hle := hCge _ hmem
      rw [map_add, map_zero, zero_add, map_smul, smul_eq_mul] at hle
      have hlt : t * f (Pi.single i 1) < u := by
        rw [ht]
        have h1 : u / f (Pi.single i 1) < |u / f (Pi.single i 1)| + 1 :=
          lt_of_le_of_lt (le_abs_self _) (lt_add_one _)
        have h2 := mul_lt_mul_of_neg_right h1 hneg
        rw [div_mul_cancel₀ _ (ne_of_lt hneg)] at h2
        exact h2
      exact not_lt_of_ge hle hlt
    have hexpand : ∀ v : ι → ℝ, v = ∑ j, v j • Pi.single j (1 : ℝ) := by
      intro v
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k _ (fun h => absurd (Finset.mem_univ k) h)]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro b _ hb
        rw [Pi.smul_apply, Pi.single_eq_of_ne]
        · exact smul_zero _
        · exact Ne.symm hb
    have hf_expand : ∀ v : ι → ℝ, f v = ∑ i, v i * p i := by
      intro v
      conv_lhs => rw [hexpand v, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      show f (v i • Pi.single i 1) = v i * p i
      rw [map_smul, smul_eq_mul, ← hp_apply]
    have hfun : ∑ i, p i • ℓ i = 0 := by
      ext d
      change (∑ i, p i • ℓ i) d = 0
      have e1 : (∑ i, p i • ℓ i) d = ∑ i, p i * (ℓ i) d := by
        rw [sum_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_apply, smul_eq_mul]
      have e2 : ∑ i, p i * (ℓ i) d = 0 := by
        have hmem : Lmap d ∈ (L : Set (ι → ℝ)) := Lmap.mem_range_self d
        have hz := hLker _ hmem
        rw [hf_expand] at hz
        rw [← hz]
        apply Finset.sum_congr rfl
        intro i _
        rw [hLmap, mul_comm]
      rw [e1]
      exact e2
    have hnz : p ≠ 0 := by
      intro hz
      have h1' : ∑ i, (-1 : ℝ) * p i < u := by
        have h1 := hUlt (fun _ => (-1 : ℝ)) (fun i => by simp)
        rwa [hf_expand] at h1
      rw [hz] at h1'
      simp at h1'
      linarith [hu0]
    exact ⟨p, hpi, hnz, hfun⟩

/--
Inequality-only KKT necessary conditions in a finite-dimensional real normed
space: if `x` is feasible for finitely many differentiable inequality
constraints, locally minimizes `f` on the feasible set, and LICQ holds at `x`
for the active constraints, then there exist nonneg multipliers `lam` with
complementarity and stationarity
`fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x = 0`.
Source: W. Karush, Minima of Functions of Several Variables with Inequalities
as Side Conditions (M.Sc. thesis, Univ. Chicago, 1939); H. W. Kuhn and
A. W. Tucker, Nonlinear Programming, Proc. Second Berkeley Symposium (1951),
481–492, DOI 10.1525/9780520411586-036.
-/
theorem karush_kuhn_tucker_inequality
    {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {x : E}
    [FiniteDimensional ℝ E]
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (hmin : IsLocalMinOn f {y | ∀ i, g i y ≤ 0} x)
    (hLICQ : LinearIndependent ℝ
      (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x)) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i x = 0) ∧
      fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x = 0 := by
  classical
  set A : Type := {i : Fin m // g i x = 0}
  set ℓ : Option A → E →L[ℝ] ℝ := fun o =>
    match o with
    | none => fderiv ℝ f x
    | some j => fderiv ℝ (g j.val) x
  obtain (halt1 | halt2) := gordan ℓ
  · obtain ⟨d, hd⟩ := halt1
    set γ : ℝ → E := fun t => x + t • d with hγ
    have hγ0 : γ 0 = x := by simp [hγ]
    have hγderiv : HasDerivAt γ d 0 :=
      HasDerivAt.const_add x
        (by simpa using HasDerivAt.smul_const (hasDerivAt_id (0 : ℝ)) d)
    have hγcont : ContinuousAt γ 0 := hγderiv.continuousAt
    have hγtend : Filter.Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by
      rw [← hγ0]
      exact hγcont
    have hslope : ∀ (h : ℝ → ℝ) (L : ℝ), HasDerivAt h L 0 → L < 0 →
        ∀ᶠ t in 𝓝[>] (0 : ℝ), h t < h 0 := by
      intro h L hhL hL
      have htend : Filter.Tendsto (slope h 0) (𝓝[≠] (0 : ℝ)) (𝓝 L) := hhL.tendsto_slope
      have hle : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
        nhdsWithin_mono 0 (fun t ht => ne_of_gt ht)
      have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope h 0 t < 0 :=
        (htend.mono_left hle).eventually (eventually_lt_nhds hL)
      filter_upwards [hev, self_mem_nhdsWithin] with t ht_slope ht_pos
      rw [slope_def_module, sub_zero, smul_eq_mul] at ht_slope
      have hpos : 0 < t⁻¹ := inv_pos.mpr ht_pos
      have ht2 : t⁻¹ * (h t - h 0) < t⁻¹ * 0 := by
        rw [mul_zero]
        exact ht_slope
      have hsub : h t - h 0 < 0 := lt_of_mul_lt_mul_left ht2 hpos.le
      linarith
    have hfneg : fderiv ℝ f x d < 0 := hd Option.none
    have hf0 : HasFDerivAt f (fderiv ℝ f x) (γ 0) := by
      rw [hγ0]
      exact hf_diff.hasFDerivAt
    have hfderiv : HasDerivAt (fun t => f (γ t)) ((fderiv ℝ f x) d) 0 :=
      HasFDerivAt.comp_hasDerivAt 0 hf0 hγderiv
    have hflt : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (γ t) < f x := by
      have h := hslope (fun t => f (γ t)) _ hfderiv hfneg
      have h' : ∀ᶠ t in 𝓝[>] (0 : ℝ), f (γ t) < f (γ 0) := h
      rwa [hγ0] at h'
    have hact1 : ∀ j : A, ∀ᶠ t in 𝓝[>] (0 : ℝ), g j.val (γ t) ≤ 0 := by
      intro j
      have hjneg : fderiv ℝ (g j.val) x d < 0 := hd (some j)
      have hg0 : HasFDerivAt (g j.val) (fderiv ℝ (g j.val) x) (γ 0) := by
        rw [hγ0]
        exact (hg_diff j.val).hasFDerivAt
      have hjderiv : HasDerivAt (fun t => g j.val (γ t)) ((fderiv ℝ (g j.val) x) d) 0 :=
        HasFDerivAt.comp_hasDerivAt 0 hg0 hγderiv
      have h := hslope (fun t => g j.val (γ t)) _ hjderiv hjneg
      have h' : ∀ᶠ t in 𝓝[>] (0 : ℝ), g j.val (γ t) < g j.val (γ 0) := h
      rw [hγ0, j.property] at h'
      exact h'.mono (fun t ht => le_of_lt ht)
    have hact : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j : A, g j.val (γ t) ≤ 0 := by
      have hfin : ∀ s : Finset A, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j ∈ s, g j.val (γ t) ≤ 0 := by
        intro s
        induction s using Finset.induction with
        | empty =>
          exact Filter.Eventually.of_forall
            (fun t j hj => absurd hj (Finset.notMem_empty j))
        | insert a s hmem ih =>
          have h1 := hact1 a
          filter_upwards [h1, ih] with t ht1 ht2 j hj
          rw [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact ht1
          · exact ht2 j hj
      have h := hfin Finset.univ
      exact h.mono (fun t ht j => ht j (Finset.mem_univ j))
    set S_inact : Finset (Fin m) := Finset.univ.filter (fun i => g i x ≠ 0) with hS
    have hinact1 : ∀ i ∈ S_inact, ∀ᶠ t in 𝓝[>] (0 : ℝ), g i (γ t) < 0 := by
      intro i hi
      have hne : g i x ≠ 0 := by
        rw [hS, Finset.mem_filter] at hi
        exact hi.2
      have hlt : g i x < 0 := lt_of_le_of_ne (hfeas i) hne
      have gi_cont : ContinuousAt (g i) x := (hg_diff i).continuousAt
      have hev : ∀ᶠ y in 𝓝 x, g i y < 0 :=
        Filter.Tendsto.eventually gi_cont (eventually_lt_nhds hlt)
      have hev0 : ∀ᶠ t in 𝓝 (0 : ℝ), g i (γ t) < 0 := Filter.Tendsto.eventually hγtend hev
      exact eventually_nhdsWithin_of_eventually_nhds hev0
    have hinact : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ S_inact, g i (γ t) < 0 := by
      have hfin : ∀ s : Finset (Fin m),
          (∀ i ∈ s, ∀ᶠ t in 𝓝[>] (0 : ℝ), g i (γ t) < 0) →
          ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ s, g i (γ t) < 0 := by
        intro s
        induction s using Finset.induction with
        | empty =>
          intro _
          exact Filter.Eventually.of_forall
            (fun t i hi => absurd hi (Finset.notMem_empty i))
        | insert a s hmem ih =>
          intro hall
          have h1 := hall a (Finset.mem_insert_self a s)
          have h2 := ih (fun i hi => hall i (Finset.mem_insert_of_mem hi))
          filter_upwards [h1, h2] with t ht1 ht2 i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · exact ht1
          · exact ht2 i hi
      exact hfin S_inact hinact1
    have hmin' : ∀ᶠ y in 𝓝[{y | ∀ i, g i y ≤ 0}] x, f x ≤ f y := hmin
    have htrans : Filter.Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝[{y | ∀ i, g i y ≤ 0}] x) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · exact hγtend.mono_left nhdsWithin_le_nhds
      · have hcomb := hact.and (hinact.and hflt)
        refine hcomb.mono (fun t ht => ?_)
        obtain ⟨htA, htI, -⟩ := ht
        change ∀ i, g i (γ t) ≤ 0
        intro i
        by_cases hi : g i x = 0
        · exact htA ⟨i, hi⟩
        · have hmem : i ∈ S_inact := by
            rw [hS, Finset.mem_filter]
            exact ⟨Finset.mem_univ i, hi⟩
          exact le_of_lt (htI i hmem)
    have hmin_t : ∀ᶠ t in 𝓝[>] (0 : ℝ), f x ≤ f (γ t) := htrans.eventually hmin'
    have hfinal := hmin_t.and hflt
    obtain ⟨t, ht1, ht2⟩ := hfinal.exists
    exact absurd ht2 (not_lt_of_ge ht1)
  · obtain ⟨p, hp_nonneg, hp_ne, hsum⟩ := halt2
    set μ : ℝ := p Option.none with hμ
    by_cases hμ0 : μ = 0
    · exfalso
      have hnone0 : p Option.none = 0 := hμ.symm.trans hμ0
      rw [Fintype.sum_option, hnone0, zero_smul, zero_add] at hsum
      have hsumA : ∑ j : A, p (Option.some j) • fderiv ℝ (g j.val) x = 0 := hsum
      have hall0 : ∀ j : A, p (Option.some j) = 0 :=
        (Fintype.linearIndependent_iff.mp hLICQ) _ hsumA
      have hact_ne : (fun j => p (Option.some j)) ≠ 0 := by
        intro hcon
        apply hp_ne
        funext o
        cases o with
        | none =>
          simp [hnone0]
        | some j =>
          exact congrFun hcon j
      exact hact_ne (funext hall0)
    · have hμpos : 0 < μ := lt_of_le_of_ne (hp_nonneg Option.none) (Ne.symm hμ0)
      have hμne : μ ≠ 0 := ne_of_gt hμpos
      set lam : Fin m → ℝ := fun i =>
        if h : g i x = 0 then p (Option.some ⟨i, h⟩) / μ else 0 with hlam
      have hlam_val : ∀ a : A, lam a.val = p (Option.some a) / μ := by
        intro a
        simp only [hlam]
        split_ifs with h
        · show p (Option.some ⟨a.val, h⟩) / μ = p (Option.some a) / μ
          rw [show (⟨a.val, h⟩ : A) = a from Subtype.ext rfl]
        · exact absurd a.property h
      refine ⟨lam, ?_, ?_, ?_⟩
      · intro i
        simp only [hlam]
        split_ifs with h
        · exact div_nonneg (hp_nonneg _) hμpos.le
        · exact le_refl 0
      · intro i
        simp only [hlam]
        split_ifs with h
        · rw [h, mul_zero]
        · exact zero_mul _
      · rw [Fintype.sum_option] at hsum
        have hdiv : μ⁻¹ • (p Option.none • ℓ Option.none +
            ∑ j : A, p (Option.some j) • ℓ (some j)) = 0 := by
          rw [hsum, smul_zero]
        rw [smul_add, Finset.smul_sum] at hdiv
        have e_none : μ⁻¹ • (p Option.none • ℓ Option.none) = fderiv ℝ f x := by
          have h2 : μ⁻¹ • (p Option.none • ℓ Option.none) = ℓ Option.none := by
            rw [hμ.symm, smul_smul, inv_mul_cancel₀ hμne, one_smul]
          exact h2
        have e_bridge : (∑ j : A, μ⁻¹ • (p (Option.some j) • ℓ (some j))) =
            ∑ i, lam i • fderiv ℝ (g i) x := by
          have e_term : ∀ j : A, μ⁻¹ • (p (Option.some j) • ℓ (some j)) =
              (p (Option.some j) / μ) • fderiv ℝ (g j.val) x := by
            intro j
            calc μ⁻¹ • (p (Option.some j) • ℓ (some j))
                = (μ⁻¹ * p (Option.some j)) • ℓ (some j) := by rw [smul_smul]
              _ = (p (Option.some j) / μ) • ℓ (some j) := by
                  rw [div_eq_mul_inv, mul_comm]
              _ = (p (Option.some j) / μ) • fderiv ℝ (g j.val) x := by rfl
          have e_reidx : (∑ j : A, (p (Option.some j) / μ) • fderiv ℝ (g j.val) x) =
              ∑ i ∈ Finset.univ.filter (fun i => g i x = 0),
                lam i • fderiv ℝ (g i) x := by
            apply Finset.sum_nbij Subtype.val
            · intro j _
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ _, j.property⟩
            · intro a₁ _ a₂ _ hij
              exact Subtype.ext hij
            · intro b hb
              rw [Finset.mem_coe, Finset.mem_filter] at hb
              exact ⟨⟨b, hb.2⟩, Finset.mem_coe.mpr (Finset.mem_univ _), rfl⟩
            · intro j _
              rw [hlam_val]
          have e_filter : (∑ i ∈ Finset.univ.filter (fun i => g i x = 0),
                lam i • fderiv ℝ (g i) x) = ∑ i, lam i • fderiv ℝ (g i) x := by
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro i _ hi
            have hneg : ¬ g i x = 0 := fun h =>
              hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
            have hlam0 : lam i = 0 := by
              simp only [hlam, dite_eq_right hneg]
            rw [hlam0, zero_smul]
          trans ∑ j : A, (p (Option.some j) / μ) • fderiv ℝ (g j.val) x
          · exact Finset.sum_congr rfl (fun j _ => e_term j)
          · rw [e_reidx, e_filter]
        rw [e_none, e_bridge] at hdiv
        exact hdiv

end MathlibExt.Analysis.Convex.KarushKuhnTucker

/-- First-order condition for convexity: a convex function lies above its tangent line.
If `f` is convex on a convex set `s`, `x ∈ s`, `y ∈ s`, and `f` is differentiable at `x`,
then `f x + fderiv ℝ f x (y - x) ≤ f y`.
Source: S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §3.1.3, Eq. (3.2). -/
theorem ConvexOn.add_fderiv_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {f : E → ℝ} {x y : E}
    (hf : ConvexOn ℝ s f) (hx : x ∈ s) (hy : y ∈ s) (hf_diff : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
  have hconv : ConvexOn ℝ (⇑g ⁻¹' s) (f ∘ ⇑g) := hf.comp_affineMap g
  have hg0 : ⇑g (0 : ℝ) = x := AffineMap.lineMap_apply_zero x y
  have hg1 : ⇑g (1 : ℝ) = y := AffineMap.lineMap_apply_one x y
  have h0mem : (0 : ℝ) ∈ ⇑g ⁻¹' s := by
    change ⇑g (0 : ℝ) ∈ s
    rw [hg0]
    exact hx
  have h1mem : (1 : ℝ) ∈ ⇑g ⁻¹' s := by
    change ⇑g (1 : ℝ) ∈ s
    rw [hg1]
    exact hy
  have hF : HasFDerivAt f (fderiv ℝ f x) (⇑g (0 : ℝ)) := by
    rw [hg0]
    exact hf_diff.hasFDerivAt
  have hc : HasDerivAt (⇑g) (y - x) (0 : ℝ) := AffineMap.hasDerivAt_lineMap
  have hderiv : HasDerivAt (f ∘ ⇑g) (fderiv ℝ f x (y - x)) (0 : ℝ) :=
    HasFDerivAt.comp_hasDerivAt 0 hF hc
  have hslope := hconv.le_slope_of_hasDerivAt h0mem h1mem (by norm_num) hderiv
  rw [slope_def_field] at hslope
  simp only [Function.comp_apply, hg0, hg1] at hslope
  norm_num at hslope
  rw [map_sub]
  linarith

namespace MathlibExt.Analysis.Convex.KarushKuhnTucker

/--
Convex KKT sufficiency, with the sign conventions of `karush_kuhn_tucker_inequality`
(minimize `f` subject to `g i y ≤ 0`). If `f` and every `g i` are convex on the whole space and
differentiable at `x`, and multipliers `lam` satisfy `lam i ≥ 0`, complementary slackness
`lam i * g i x = 0`, and stationarity `fderiv ℝ f x + ∑ i, lam i • fderiv ℝ (g i) x = 0`, then
`f x ≤ f y` for every feasible `y`. Feasibility of `x` itself is not needed for this bound;
when `x` is feasible, it is a global minimizer on the feasible set. No constraint qualification
is needed. An affine equality constraint `a y = 0`
can be encoded as the two convex constraints `a y ≤ 0` and `-a y ≤ 0`.
Source: S. Boyd and L. Vandenberghe, *Convex Optimization* (2004), §5.5.3.
-/
theorem isMinOn_of_karush_kuhn_tucker_convex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ} {x : E} {lam : Fin m → ℝ}
    (hf_conv : ConvexOn ℝ Set.univ f) (hg_conv : ∀ i, ConvexOn ℝ Set.univ (g i))
    (hf_diff : DifferentiableAt ℝ f x) (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hlam : ∀ i, 0 ≤ lam i) (hcs : ∀ i, lam i * g i x = 0)
    (hstat : fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x = 0) :
    IsMinOn f {y | ∀ i, g i y ≤ 0} x := by
  intro y hy
  have hf_le : f x + fderiv ℝ f x (y - x) ≤ f y :=
    ConvexOn.add_fderiv_sub_le hf_conv (Set.mem_univ x) (Set.mem_univ y) hf_diff
  have hg_le : ∀ i, g i x + fderiv ℝ (g i) x (y - x) ≤ g i y := fun i =>
    ConvexOn.add_fderiv_sub_le (hg_conv i) (Set.mem_univ x) (Set.mem_univ y) (hg_diff i)
  have hstat_v :
      fderiv ℝ f x (y - x) + ∑ i : Fin m, lam i * fderiv ℝ (g i) x (y - x) = 0 := by
    have h := congrArg (fun L : E →L[ℝ] ℝ => L (y - x)) hstat
    simp only [add_apply, sum_apply, smul_apply, smul_eq_mul, zero_apply] at h
    exact h
  have hsum_le : ∑ i : Fin m, lam i * fderiv ℝ (g i) x (y - x) ≤ 0 := by
    calc ∑ i : Fin m, lam i * fderiv ℝ (g i) x (y - x)
        ≤ ∑ i : Fin m, lam i * g i y := by
          apply Finset.sum_le_sum
          intro i _
          have h1 : fderiv ℝ (g i) x (y - x) ≤ g i y - g i x := by linarith [hg_le i]
          have h2 : lam i * fderiv ℝ (g i) x (y - x) ≤ lam i * (g i y - g i x) :=
            mul_le_mul_of_nonneg_left h1 (hlam i)
          have h3 : lam i * (g i y - g i x) = lam i * g i y := by
            rw [mul_sub, hcs i, sub_zero]
          rw [h3] at h2
          exact h2
      _ ≤ 0 := by
          apply Finset.sum_nonpos
          intro i _
          have h := mul_le_mul_of_nonneg_left (hy i) (hlam i)
          simpa using h
  have hD : (0:ℝ) ≤ (fderiv ℝ f x) (y - x) := by linarith [hstat_v, hsum_le]
  change f x ≤ f y
  have h2 : f x ≤ f x + (fderiv ℝ f x) (y - x) := by
    have h := add_le_add_left hD (f x)
    simpa using h
  exact le_trans h2 hf_le

end MathlibExt.Analysis.Convex.KarushKuhnTucker


/-! ### Mixed-constraint KKT under LICQ -/

namespace MathlibExt.Analysis.Convex.KarushKuhnTucker

/--
Mixed-constraint Karush–Kuhn–Tucker necessary conditions under LICQ.
Minimize `f` subject to finitely many inequality constraints `g i y ≤ 0` and equality
constraints `h j y = 0` on a finite-dimensional real normed space. If `x` is feasible, is a
local minimum of `f` on the feasible set, `f` and every `g i` are differentiable at `x`, every
`h j` is `C¹` at `x`, and the derivatives of all equality constraints together with the
derivatives of the active inequality constraints are linearly independent (LICQ), then there
are inequality multipliers `lam ≥ 0` with complementary slackness and free equality multipliers
`mu` such that `fderiv f x + ∑ i, lam i • fderiv (g i) x + ∑ j, mu j • fderiv (h j) x = 0`.
-/
theorem karush_kuhn_tucker_mixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {m p : ℕ} {f : E → ℝ} {g : Fin m → E → ℝ}
    {h : Fin p → E → ℝ} {x : E}
    (hf_diff : DifferentiableAt ℝ f x)
    (hg_diff : ∀ i, DifferentiableAt ℝ (g i) x)
    (hh_diff : ∀ j, ContDiffAt ℝ 1 (h j) x)
    (hfeas : ∀ i, g i x ≤ 0)
    (heq : ∀ j, h j x = 0)
    (hmin : IsLocalMinOn f {y | (∀ i, g i y ≤ 0) ∧ ∀ j, h j y = 0} x)
    (hLICQ : LinearIndependent ℝ
      (Sum.elim (fun j : Fin p => fderiv ℝ (h j) x)
        (fun i : {i : Fin m // g i x = 0} => fderiv ℝ (g i.val) x))) :
    ∃ (lam : Fin m → ℝ) (mu : Fin p → ℝ), (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i * g i x = 0) ∧
      fderiv ℝ f x + ∑ i : Fin m, lam i • fderiv ℝ (g i) x +
        ∑ j : Fin p, mu j • fderiv ℝ (h j) x = 0 := by
  classical
  -- Active inequality set and equality-derivative map.
  set A : Type := { i : Fin m // g i x = 0 } with hA_def
  set H : E →L[ℝ] (Fin p → ℝ) := ContinuousLinearMap.pi (fun j => fderiv ℝ (h j) x) with hH_def
  -- Pointwise action of `H` (proved without rewriting `H` itself, so `ker` types stay put).
  have hH_apply : ∀ (v : E) (j : Fin p), H v j = (fderiv ℝ (h j) x) v := by
    intro v j
    simp [hH_def]
  -- LICQ implies the equality derivatives alone are independent.
  have hindep_h : LinearIndependent ℝ (fun j : Fin p => fderiv ℝ (h j) x) := by
    have hcomp := hLICQ.comp _ Sum.inl_injective
    simpa [Function.comp] using hcomp
  -- The nonlinear equality map is strictly differentiable with derivative `H`.
  have hH_strict : HasStrictFDerivAt (fun y j => h j y) H x := by
    have hcomp : ∀ j : Fin p, HasStrictFDerivAt (fun y => h j y) (fderiv ℝ (h j) x) x := by
      intro j
      exact ContDiffAt.hasStrictFDerivAt (hh_diff j) one_ne_zero
    have hpi := hasStrictFDerivAt_pi.mpr hcomp
    simpa [hH_def] using hpi
  -- `H` is surjective: otherwise a nonzero functional vanishes on its range,
  -- giving a nontrivial relation among the independent equality derivatives.
  have hH_surj : (↑H : E →ₗ[ℝ] (Fin p → ℝ)).range = ⊤ := by
    by_contra hne
    have hAnn_ne : (LinearMap.range (↑H : E →ₗ[ℝ] (Fin p → ℝ))).dualAnnihilator ≠ ⊥ := by
      intro hbot
      apply hne
      rw [← Submodule.dualAnnihilator_eq_bot_iff]
      exact hbot
    obtain ⟨φ, hφ_mem, hφ_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hAnn_ne
    have hφ_vanish : ∀ v : E, φ ((↑H : E →ₗ[ℝ] (Fin p → ℝ)) v) = 0 := by
      intro v
      exact (Submodule.mem_dualAnnihilator _).mp hφ_mem _ (LinearMap.mem_range_self _ _)
    -- Expand `φ` on the standard basis to get coefficients.
    set θ : Fin p → ℝ := fun j => φ (Pi.single j (1 : ℝ)) with hθ_def
    have hexpand : ∀ v : Fin p → ℝ, v = ∑ j, v j • Pi.single j (1 : ℝ) := by
      intro v
      symm
      trans ∑ j, Pi.single j (v j)
      · apply Finset.sum_congr rfl
        intro j _
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      · exact Finset.univ_sum_single v
    have hφ_expand : ∀ v : Fin p → ℝ, φ v = ∑ j, v j * θ j := by
      intro v
      conv_lhs => rw [hexpand v, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul, hθ_def]
    have hθ_relation : ∑ j, θ j • (fderiv ℝ (h j) x) = 0 := by
      ext v
      have e1 : (∑ j, θ j • (fderiv ℝ (h j) x)) v
          = ∑ j, θ j * (fderiv ℝ (h j) x) v := by
        rw [sum_apply]
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_apply, smul_eq_mul]
      have e2 : (∑ j, θ j * (fderiv ℝ (h j) x) v) = 0 := by
        have hz := hφ_vanish v
        rw [hφ_expand] at hz
        rw [← hz]
        apply Finset.sum_congr rfl
        intro j _
        have hj : ((↑H : E →ₗ[ℝ] (Fin p → ℝ)) v) j = (fderiv ℝ (h j) x) v := by
          change H v j = _
          rw [hH_apply]
        rw [hj, mul_comm]
      change (∑ j, θ j • fderiv ℝ (h j) x) v = (0 : E →L[ℝ] ℝ) v
      rw [e1]
      have hzero : (0 : E →L[ℝ] ℝ) v = 0 := rfl
      rw [hzero]
      exact e2
    -- The relation forces `θ = 0` by independence.
    have hθ_zero : θ = 0 := by
      have hiff := Fintype.linearIndependent_iff (R := ℝ) (v := fun j : Fin p => fderiv ℝ (h j) x)
      have h0 := (hiff.mp hindep_h) _ hθ_relation
      funext j
      exact h0 j
    -- `θ = 0` forces `φ = 0`, contradiction.
    have hφ_zero : φ = 0 := by
      apply LinearMap.ext
      intro v
      have h := hφ_expand v
      rw [hθ_zero] at h
      simpa using h
    exact hφ_ne hφ_zero
  -- Kernel of `H` and the family of restricted functionals for Gordan.
  set K : Submodule ℝ E := LinearMap.ker (↑H : E →ₗ[ℝ] (Fin p → ℝ)) with hK_def
  set fam : Option A → (↥K →L[ℝ] ℝ) := fun o =>
    match o with
    | none => (fderiv ℝ f x).comp K.subtypeL
    | some a => (fderiv ℝ (g a.val) x).comp K.subtypeL
    with hfam_def
  have hfam_none : ∀ z : ↥K, (fam none) z = (fderiv ℝ f x) (z : E) := fun z => rfl
  have hfam_some : ∀ (a : A) (z : ↥K), (fam (some a)) z = (fderiv ℝ (g a.val) x) (z : E) :=
    fun a z => rfl
  -- The nonlinear equality map vanishes at `x`.
  have hHnl_zero : (fun y j => h j y) x = 0 := by
    funext j
    exact heq j
  -- Beta-reduced form, for rewriting inside instantiated lemma statements.
  have hHnl_zero_fun : (fun j => h j x) = 0 := hHnl_zero
  -- Linearized claim: there is no feasible descent direction.
  -- Given `d` with `H d = 0`, `f' d < 0`, `g'_A d < 0`, the implicit function
  -- theorem yields a feasible curve through `x` with velocity `d`, along which
  -- `f` strictly decreases, contradicting local minimality.
  have hnodesc : ¬∃ d : E, (∀ j, (fderiv ℝ (h j) x) d = 0)
      ∧ (fderiv ℝ f x) d < 0 ∧ (∀ a : A, (fderiv ℝ (g a.val) x) d < 0) := by
    rintro ⟨d, hd_eq, hd_f, hd_g⟩
    -- `d` lies in the kernel of `H`.
    have hd_mem : d ∈ K := by
      rw [hK_def, LinearMap.mem_ker]
      change H d = 0
      funext j
      rw [hH_apply]
      exact hd_eq j
    -- Direction in the kernel.
    set dK : ↥K := ⟨d, hd_mem⟩ with hdK_def
    -- Feasible curve: value coordinate `0`, kernel coordinate `t • dK`.
    set γ : ℝ → E :=
      fun t => hH_strict.implicitFunction (fun y j => h j y) H hH_surj 0 (t • dK) with hγ_def
    -- `γ 0 = x`.
    have hγ_zero : γ 0 = x := by
      have himg := hH_strict.implicitFunction_apply_image (f := fun y j => h j y) (f' := H) hH_surj
      rw [hHnl_zero_fun] at himg
      simp only [hγ_def, zero_smul]
      exact himg
    -- `γ` stays in the equality fiber near `0`.
    have hγ_fiber : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), (fun y j => h j y) (γ t) = 0 := by
      have hev0 := hH_strict.map_implicitFunction_eq (f := fun y j => h j y) (f' := H) hH_surj
      rw [hHnl_zero_fun] at hev0
      have h2 : Filter.Tendsto (fun t : ℝ => t • dK) (𝓝 (0 : ℝ)) (𝓝 (0 : ↥K)) := by
        have h := (continuousAt_id (x := (0 : ℝ))).tendsto.smul_const dK
        simpa using h
      have htend : Filter.Tendsto (fun t : ℝ => ((0 : Fin p → ℝ), t • dK)) (𝓝 (0 : ℝ))
          (𝓝 ((0 : Fin p → ℝ), (0 : ↥K))) :=
        tendsto_const_nhds.prodMk_nhds h2
      have h := htend.eventually hev0
      simpa [hγ_def] using h
    -- `γ` has velocity `d` at `0`.
    have hγ_deriv : HasDerivAt γ d 0 := by
      have hderiv : HasStrictFDerivAt
          (hH_strict.implicitFunction (fun y j => h j y) H hH_surj 0) K.subtypeL 0 := by
        have h := hH_strict.to_implicitFunction (f := fun y j => h j y) (f' := H) hH_surj
        rwa [hHnl_zero_fun] at h
      have hsmul : HasDerivAt (fun t : ℝ => t • dK) dK 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const dK
      have hcomp := hderiv.hasFDerivAt.comp_hasDerivAt_of_eq 0 hsmul
        (by simp : (0 : ↥K) = (fun t : ℝ => t • dK) 0)
      -- the derivative of `g 0` at `0` is the inclusion, sending `dK` to `d`
      simpa [hγ_def, Function.comp_def, Submodule.subtypeL_apply, hdK_def] using hcomp
    -- From here the descent direction contradicts minimality (see below).
    -- Continuity of `γ` at `0` and limit `x`.
    have hγ_cont : ContinuousAt γ 0 := hγ_deriv.continuousAt
    have hγ_tendsto : Filter.Tendsto γ (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa [hγ_zero] using hγ_cont.tendsto
    -- Derivatives of the compositions `f ∘ γ` and `g ∘ γ` at `0`.
    have hf_comp : HasDerivAt (fun t => f (γ t)) ((fderiv ℝ f x) d) 0 :=
      hf_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ_deriv hγ_zero.symm
    have hg_comp : ∀ a : A, HasDerivAt (fun t => g a.val (γ t)) ((fderiv ℝ (g a.val) x) d) 0 := by
      intro a
      exact (hg_diff a.val).hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ_deriv hγ_zero.symm
    -- Slope of `f ∘ γ` tends to a negative value, so `f (γ t) < f x` for small `t > 0`.
    have hIoi_sub : Set.Ioi (0 : ℝ) ⊆ {0}ᶜ := fun t ht => ne_of_gt ht
    have hslope_f : Filter.Tendsto
        (fun t => t⁻¹ • ((fun t => f (γ t)) (0 + t) - (fun t => f (γ t)) 0))
        (𝓝[>] (0 : ℝ)) (𝓝 ((fderiv ℝ f x) d)) :=
      hf_comp.tendsto_slope_zero.mono_left (nhdsWithin_mono 0 hIoi_sub)
    have hev_f : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f (γ t) < f x := by
      have hneg : Set.Iio (0 : ℝ) ∈ 𝓝 ((fderiv ℝ f x) d) := Iio_mem_nhds hd_f
      have hev := hslope_f.eventually hneg
      filter_upwards [hev, self_mem_nhdsWithin] with t ht_slope ht_pos
      simp only [zero_add] at ht_slope
      have ht0 : (0 : ℝ) < t := ht_pos
      rw [hγ_zero, smul_eq_mul] at ht_slope
      have ht_inv : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht0
      have hsub : f (γ t) - f x < 0 := by
        have h := mul_neg_iff.mp ht_slope
        rcases h with ⟨-, hlt⟩ | ⟨hlt, -⟩
        · exact hlt
        · exact absurd hlt (not_lt_of_gt ht_inv)
      linarith
    -- Likewise each active `g` becomes strictly negative for small `t > 0`.
    have hev_g : ∀ a : A, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), g a.val (γ t) < 0 := by
      intro a
      have hs' : Filter.Tendsto
          (fun t => t⁻¹ • ((fun t => g a.val (γ t)) (0 + t) - (fun t => g a.val (γ t)) 0))
          (𝓝[>] (0 : ℝ)) (𝓝 ((fderiv ℝ (g a.val) x) d)) :=
        (hg_comp a).tendsto_slope_zero.mono_left (nhdsWithin_mono 0 hIoi_sub)
      have hneg : Set.Iio (0 : ℝ) ∈ 𝓝 ((fderiv ℝ (g a.val) x) d) := Iio_mem_nhds (hd_g a)
      have hev := hs'.eventually hneg
      filter_upwards [hev, self_mem_nhdsWithin] with t ht_slope ht_pos
      simp only [zero_add] at ht_slope
      have ht0 : (0 : ℝ) < t := ht_pos
      have ha0 : g a.val x = 0 := a.property
      rw [hγ_zero, smul_eq_mul] at ht_slope
      have ht_inv : (0 : ℝ) < t⁻¹ := inv_pos.mpr ht0
      have hsub : g a.val (γ t) - g a.val x < 0 := by
        have h := mul_neg_iff.mp ht_slope
        rcases h with ⟨-, hlt⟩ | ⟨hlt, -⟩
        · exact hlt
        · exact absurd hlt (not_lt_of_gt ht_inv)
      linarith
    -- Inactive inequalities stay negative by continuity.
    have hev_inact : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ i : Fin m, g i x < 0 → g i (γ t) < 0 := by
      have h2 : ∀ i : Fin m, ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g i x < 0 → g i (γ t) < 0 := by
        intro i
        by_cases hi : g i x < 0
        · have hgc : ContinuousAt (g i) (γ 0) := by
            rw [hγ_zero]
            exact (hg_diff i).continuousAt
          have hcont_i : Filter.Tendsto (fun t => g i (γ t)) (𝓝 (0 : ℝ)) (𝓝 (g i x)) := by
            have h := (hgc.comp hγ_cont).tendsto
            simpa [Function.comp_def, hγ_zero] using h
          have hmem : Set.Iio (0 : ℝ) ∈ 𝓝 (g i x) := Iio_mem_nhds hi
          have h := hcont_i.eventually hmem
          filter_upwards [h] with t ht _
          exact ht
        · exact Filter.Eventually.of_forall fun t hcon => (hi hcon).elim
      exact Filter.eventually_all.mpr h2
    -- Hence `γ t` is feasible for small `t > 0`.
    have hγ_mem : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (∀ i, g i (γ t) ≤ 0) ∧ ∀ j, h j (γ t) = 0 := by
      have h1 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ a : A, g a.val (γ t) < 0 :=
        Filter.eventually_all.mpr hev_g
      have h2 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), ∀ i : Fin m, g i x < 0 → g i (γ t) < 0 :=
        hev_inact.filter_mono nhdsWithin_le_nhds
      have h3 : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (fun y j => h j y) (γ t) = 0 :=
        hγ_fiber.filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, h2, h3] with t ht1 ht2 ht3
      refine ⟨?_, fun j => ?_⟩
      · intro i
        by_cases hi : g i x = 0
        · have := ht1 ⟨i, hi⟩
          exact le_of_lt this
        · have hlt : g i x < 0 := lt_of_le_of_ne (hfeas i) hi
          exact le_of_lt (ht2 i hlt)
      · have := congrFun ht3 j
        simpa using this
    -- So `γ` tends to `x` within the feasible set (from the right).
    have hγ_nhdsWithin : Filter.Tendsto γ (𝓝[>] (0 : ℝ))
        (𝓝[{y | (∀ i, g i y ≤ 0) ∧ ∀ j, h j y = 0}] x) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hγ_tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [hγ_mem] with t ht
      exact ht
    -- Composing the local min with `γ` gives a one-sided local min at `0`.
    have hmin_comp : IsMinFilter (fun t => f (γ t)) (𝓝[>] (0 : ℝ)) 0 := by
      have hmin' : IsMinFilter f (𝓝[{y | (∀ i, g i y ≤ 0) ∧ ∀ j, h j y = 0}] x) (γ 0) := by
        rw [hγ_zero]
        exact hmin
      exact hmin'.comp_tendsto hγ_nhdsWithin
    -- But `f (γ t) < f (γ 0)` eventually, contradiction.
    have hcontra : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f (γ t) < (fun t => f (γ t)) 0 := by
      simpa [hγ_zero] using hev_f
    have hle : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (fun t => f (γ t)) 0 ≤ f (γ t) := hmin_comp
    obtain ⟨t, hlt, hge⟩ := (hcontra.and hle).exists
    exact absurd hge (not_le_of_gt hlt)
  -- Apply Gordan's alternative on the kernel.
  obtain hdescent | ⟨q, hq_nonneg, hq_ne, hq_sum⟩ := gordan fam
  · -- A descent direction in the kernel lifts to `E`, contradicting `hnodesc`.
    obtain ⟨z, hz⟩ := hdescent
    refine False.elim (hnodesc ⟨(z : E), ?_, ?_, ?_⟩)
    · intro j
      have hmemK : (z : E) ∈ LinearMap.ker (↑H : E →ₗ[ℝ] (Fin p → ℝ)) := z.property
      rw [LinearMap.mem_ker] at hmemK
      -- Take the `j`-th component without rewriting `H` itself (motive safety).
      have h0 : H (z : E) = 0 := hmemK
      have h1 : H (z : E) j = (0 : Fin p → ℝ) j := by rw [h0]
      rw [hH_apply] at h1
      simpa using h1
    · have h := hz none
      rw [hfam_none] at h
      exact h
    · intro a
      have h := hz (some a)
      rw [hfam_some] at h
      exact h
  · -- Nontrivial nonnegative multipliers on the kernel; extend by the equalities.
    -- Combined functional on `E` (objective plus active inequalities).
    set L0 : E →L[ℝ] ℝ := (q none) • (fderiv ℝ f x)
      + ∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x) with hL0_def
    -- `L0` vanishes on `K` by the Gordan relation.
    have hL0_vanish : ∀ z : ↥K, L0 (z : E) = 0 := by
      intro z
      have hsum := congrArg (fun L : ↥K →L[ℝ] ℝ => L z) hq_sum
      rw [sum_apply] at hsum
      have hzero : (0 : ↥K →L[ℝ] ℝ) z = 0 := rfl
      rw [hzero, Fintype.sum_option] at hsum
      simp only [smul_apply, smul_eq_mul, hfam_none, hfam_some] at hsum
      have hL0_apply : L0 (z : E)
          = q none * (fderiv ℝ f x) (z : E)
            + ∑ a : A, q (some a) * (fderiv ℝ (g a.val) x) (z : E) := by
        simp [hL0_def, add_apply, sum_apply, smul_apply, smul_eq_mul]
      rw [hL0_apply]
      exact hsum
    -- Hence `ker H ≤ ker L0`.
    have hker_le : LinearMap.ker (↑H : E →ₗ[ℝ] (Fin p → ℝ)) ≤ LinearMap.ker (L0.toLinearMap) := by
      intro v hv
      rw [LinearMap.mem_ker] at hv ⊢
      have hvK : v ∈ K := LinearMap.mem_ker.mpr hv
      exact hL0_vanish ⟨v, hvK⟩
    -- Rewrite `ker H` as an `iInf` of kernels for the Mathlib span lemma.
    have hker_eq : LinearMap.ker (↑H : E →ₗ[ℝ] (Fin p → ℝ))
        = ⨅ j, LinearMap.ker ((fderiv ℝ (h j) x).toLinearMap) := by
      have hcoe : (↑H : E →ₗ[ℝ] (Fin p → ℝ))
          = LinearMap.pi (fun j => ((fderiv ℝ (h j) x).toLinearMap)) := by
        ext v j
        change H v j = (LinearMap.pi (fun j => ((fderiv ℝ (h j) x).toLinearMap))) v j
        rw [hH_apply, LinearMap.pi_apply]
        rfl
      rw [hcoe, LinearMap.ker_pi]
    have hiInf_le : (⨅ j, LinearMap.ker ((fderiv ℝ (h j) x).toLinearMap))
        ≤ LinearMap.ker (L0.toLinearMap) := by
      rw [← hker_eq]
      exact hker_le
    -- Mathlib: vanishing on the joint kernel puts `L0` in the span; get `mu0`.
    have hmem := mem_span_of_iInf_ker_le_ker hiInf_le
    obtain ⟨mu0, hmu0⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
    -- Lift the linear relation to continuous linear maps.
    have hL0_eq : L0 = ∑ j, mu0 j • (fderiv ℝ (h j) x) := by
      ext v
      have h := congrArg (fun L : E →ₗ[ℝ] ℝ => L v) hmu0
      simpa [sum_apply, smul_eq_mul] using h.symm
    -- Stationarity at `q none`-scale, with free equality multipliers `mu' = -mu0`.
    set mu' : Fin p → ℝ := fun j => -mu0 j with hmu'_def
    have hstat0 : ((q none) • (fderiv ℝ f x) + (∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x)))
        + (∑ j, mu' j • (fderiv ℝ (h j) x)) = 0 := by
      have hL0_def' : L0 = (q none) • (fderiv ℝ f x)
          + ∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x) := rfl
      have hsum_neg : (∑ j, mu' j • (fderiv ℝ (h j) x))
          = -(∑ j, mu0 j • (fderiv ℝ (h j) x)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp [hmu'_def, neg_smul]
      rw [← hL0_def', hL0_eq, hsum_neg, add_neg_cancel]
    -- LICQ in terms of `A`.
    have hLICQ_A : LinearIndependent ℝ (Sum.elim (fun j : Fin p => fderiv ℝ (h j) x)
        (fun a : A => fderiv ℝ (g a.val) x)) := hLICQ
    -- `q none ≠ 0`: else all multipliers vanish, contradicting `q ≠ 0`.
    have hq_none_ne : q none ≠ 0 := by
      intro h0
      have hrel : (∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x))
          + (∑ j, mu' j • (fderiv ℝ (h j) x)) = 0 := by
        simpa [h0] using hstat0
      set c : (Fin p ⊕ A) → ℝ := Sum.elim mu' (fun a => q (some a)) with hc_def
      have hsum_eq : ∑ s : (Fin p ⊕ A), c s • (Sum.elim (fun j : Fin p => fderiv ℝ (h j) x)
          (fun a : A => fderiv ℝ (g a.val) x) s) = 0 := by
        rw [Fintype.sum_sum_type]
        simp only [hc_def, Sum.elim_inl, Sum.elim_inr]
        rw [add_comm]
        exact hrel
      have hc_zero : c = 0 := by
        have hiff := Fintype.linearIndependent_iff (R := ℝ)
          (v := Sum.elim (fun j : Fin p => fderiv ℝ (h j) x)
            (fun a : A => fderiv ℝ (g a.val) x))
        have h0 := (hiff.mp hLICQ_A) _ hsum_eq
        funext s
        exact h0 s
      have hq_some : ∀ a, q (some a) = 0 := by
        intro a
        have hcongr := congrFun hc_zero (Sum.inr a)
        simpa [hc_def] using hcongr
      have hq_eq_zero : q = 0 := by
        funext o
        cases o with
        | none => exact h0
        | some a => exact hq_some a
      exact hq_ne hq_eq_zero
    have hq_pos : 0 < q none := lt_of_le_of_ne (hq_nonneg none) (Ne.symm hq_none_ne)
    -- Normalized stationarity over the active set.
    have hstatA : fderiv ℝ f x
        + (∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x))
        + (∑ j, (mu' j / q none) • (fderiv ℝ (h j) x)) = 0 := by
      have hsmul : ((q none)⁻¹ : ℝ) • ((((q none) • (fderiv ℝ f x)
          + (∑ a : A, (q (some a)) • (fderiv ℝ (g a.val) x)))
          + (∑ j, mu' j • (fderiv ℝ (h j) x)))) = 0 := by
        rw [hstat0, smul_zero]
      simp only [smul_add, Finset.smul_sum, smul_smul] at hsmul
      have hcoeff_f : ((q none)⁻¹ * q none) • (fderiv ℝ f x) = fderiv ℝ f x := by
        rw [inv_mul_cancel₀ hq_none_ne, one_smul]
      have hcoeff_g : ∀ a : A, (((q none)⁻¹ * q (some a)) • (fderiv ℝ (g a.val) x))
          = ((q (some a) / q none) • (fderiv ℝ (g a.val) x)) := by
        intro a
        rw [div_eq_mul_inv, mul_comm]
      have hcoeff_h : ∀ j, (((q none)⁻¹ * mu' j) • (fderiv ℝ (h j) x))
          = ((mu' j / q none) • (fderiv ℝ (h j) x)) := by
        intro j
        rw [div_eq_mul_inv, mul_comm]
      simp only [hcoeff_f, hcoeff_g, hcoeff_h] at hsmul
      -- `hsmul` now matches the goal up to association; close by linear combination shape
      have hassoc : ((fderiv ℝ f x + (∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x)))
          + (∑ j, (mu' j / q none) • (fderiv ℝ (h j) x)))
          = (fderiv ℝ f x + (∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x))
            + (∑ j, (mu' j / q none) • (fderiv ℝ (h j) x))) := rfl
      rw [← hassoc]
      exact hsmul
    -- Extend the inequality multipliers by zero to inactive constraints.
    set lam : Fin m → ℝ := fun i => if hi : g i x = 0 then (q (some ⟨i, hi⟩) / q none) else 0
      with hlam_def
    set muF : Fin p → ℝ := fun j => mu' j / q none with hmuF_def
    refine ⟨lam, muF, ?_, ?_, ?_⟩
    · -- Nonnegativity.
      intro i
      by_cases hi : g i x = 0
      · have hlam_i : lam i = q (some ⟨i, hi⟩) / q none := by simp [hlam_def, hi]
        rw [hlam_i]
        exact div_nonneg (hq_nonneg _) (le_of_lt hq_pos)
      · have hlam_i : lam i = 0 := by simp [hlam_def, hi]
        rw [hlam_i]
    · -- Complementary slackness.
      intro i
      by_cases hi : g i x = 0
      · have hlam_i : lam i = q (some ⟨i, hi⟩) / q none := by simp [hlam_def, hi]
        rw [hlam_i, hi, mul_zero]
      · have hlam_i : lam i = 0 := by simp [hlam_def, hi]
        rw [hlam_i, zero_mul]
    · -- Stationarity: the `Fin m` sum reduces to the active sum.
      have hsum_eq : (∑ i : Fin m, lam i • (fderiv ℝ (g i) x))
          = ∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x) := by
        -- First reduce `univ` to the active filter, then biject with `A`.
        set s : Finset (Fin m) := Finset.filter (fun i => g i x = 0) Finset.univ with hs_def
        have hsub : s ⊆ Finset.univ := Finset.filter_subset _ _
        have hvanish : ∀ i ∈ Finset.univ, i ∉ s → lam i • (fderiv ℝ (g i) x) = 0 := by
          intro i _ hi
          have hne : ¬ g i x = 0 := by
            intro hcon
            apply hi
            rw [hs_def, Finset.mem_filter]
            exact ⟨Finset.mem_univ i, hcon⟩
          have hlam0 : lam i = 0 := by simp [hlam_def, hne]
          rw [hlam0, zero_smul]
        have hsub_eq : (∑ i ∈ s, lam i • (fderiv ℝ (g i) x))
            = ∑ i ∈ Finset.univ, lam i • (fderiv ℝ (g i) x) :=
          Finset.sum_subset hsub hvanish
        have hbij : (∑ a ∈ Finset.univ, (q (some a) / q none) • (fderiv ℝ (g a.val) x))
            = ∑ i ∈ s, lam i • (fderiv ℝ (g i) x) := by
          apply Finset.sum_bij (fun a _ => (a.val : Fin m))
          · -- lands in `s`
            intro a _
            rw [hs_def, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, a.property⟩
          · -- injective
            intro a₁ _ a₂ _ h12
            exact Subtype.ext h12
          · -- surjective onto `s`
            intro b hb
            rw [hs_def, Finset.mem_filter] at hb
            exact ⟨⟨b, hb.2⟩, Finset.mem_univ _, rfl⟩
          · -- values agree
            intro a _
            have hlam_a : lam a.val = q (some a) / q none := by
              have ha : g a.val x = 0 := a.property
              simp [hlam_def, ha]
            rw [hlam_a]
        -- Combine: `univ Fin m = s = univ A` (as sums).
        have huniv_eq : (∑ i : Fin m, lam i • (fderiv ℝ (g i) x))
            = ∑ i ∈ s, lam i • (fderiv ℝ (g i) x) := by
          rw [← hsub_eq]
        have hA_eq : (∑ i ∈ s, lam i • (fderiv ℝ (g i) x))
            = ∑ a : A, (q (some a) / q none) • (fderiv ℝ (g a.val) x) := by
          rw [← hbij]
        rw [huniv_eq, hA_eq]
      rw [hsum_eq]
      -- Goal now matches `hstatA` up to `muF` unfolding (definitional).
      simpa [hmuF_def] using hstatA

end MathlibExt.Analysis.Convex.KarushKuhnTucker
