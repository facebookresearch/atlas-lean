/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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

@[expose] public section

open scoped Topology Pointwise

namespace MathlibExt.Analysis.Convex.KarushKuhnTucker

/-!
# Inequality-only Karush–Kuhn–Tucker necessary conditions

A finite-dimensional Gordan alternative (strict linear solvability versus a
nontrivial nonnegative dependence), proved by strictly separating the negative
orthant from the range-plus-nonnegative-orthant sum, implies the
inequality-only KKT theorem: at a feasible local minimum satisfying LICQ on
the active constraints, a strict descent direction would contradict local
minimality along `t ↦ x + t • d`, so the alternative supplies nonnegative
multipliers with complementarity and stationarity.
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
**Karush–Kuhn–Tucker conditions for inequality constraints.** Let $E$ be a finite-dimensional
real normed space, let $f \colon E \to \mathbb{R}$ and $g_1, \dots, g_m \colon E \to \mathbb{R}$,
and let $x \in E$ be a point at which $f$ and every $g_i$ are differentiable; write $D$ for
the Fréchet derivative at $x$. Suppose that $x$ is feasible, that is $g_i(x) \le 0$ for every
$i$; that $x$ is a local minimizer of $f$ on the feasible set
$\{y \in E : g_i(y) \le 0 \text{ for every } i\}$; and that the derivatives $Dg_i(x)$ of the
active constraints, those $i$ with $g_i(x) = 0$, are linearly independent. Then there exist
multipliers $\lambda_1, \dots, \lambda_m \ge 0$ such that $\lambda_i g_i(x) = 0$ for every $i$
and $Df(x) + \sum_{i=1}^m \lambda_i Dg_i(x) = 0$.

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
