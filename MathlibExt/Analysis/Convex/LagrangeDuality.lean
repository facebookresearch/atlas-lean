/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.EReal.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Card
public import Mathlib.Order.CompleteLattice.Basic
public import MathlibExt.Analysis.Convex.FirstOrderCondition
import MathlibExt.Analysis.Convex.FinsetSum
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lagrange duality for convex programs with inequality constraints

We consider the optimization problem

  minimize `f₀ x` subject to `x ∈ D` and `f i x ≤ 0` for `i : ι`,

with a finite index set `ι`, a domain `D` in a real vector space, and real-valued objective and
constraint functions. Its *Lagrangian* is `L(x, μ) = f₀ x + ∑ i, μ i * f i x`, its *Lagrange dual
function* is `g(μ) = inf_{x ∈ D} L(x, μ)` (with values in `EReal`, since it may be `-∞`), its
*optimal value* is `p⋆ = inf {f₀ x | x ∈ D feasible}` and its *dual optimal value* is
`d⋆ = sup_{μ ≥ 0} g(μ)`.

## Main results

* `dualFunction_le_of_feasible`, `dualValue_le_primalValue`: **weak duality** `d⋆ ≤ p⋆`, with no
  convexity assumption (Boyd–Vandenberghe §5.1.3, §5.2.2).
* `exists_multiplier_of_slater`: if the problem is convex and **Slater's condition** holds
  (some `x ∈ D` has `f i x < 0` for every `i`), then every lower bound `p` on the feasible values of
  `f₀` is achieved by a dual feasible `μ ≥ 0` with `p ≤ L(x, μ)` on `D`. The proof separates the
  convex set `{(u, t) | ∃ x ∈ D, f x ≤ u, f₀ x ≤ t}` from the open quadrant `{u < 0, t < p}`
  (Boyd–Vandenberghe §5.3.2).
* `dualValue_eq_primalValue_of_slater`, `exists_dualFunction_eq_primalValue_of_slater`:
  **strong duality** `d⋆ = p⋆` under Slater's condition, with dual attainment when `p⋆ > -∞`
  (Boyd–Vandenberghe §5.2.3).
* `kkt_sufficient`: the **Karush–Kuhn–Tucker conditions are sufficient** for optimality of a
  convex differentiable problem, and certify zero duality gap (Boyd–Vandenberghe §5.5.3).
* `central_point_duality_gap`: a point on the **central path** of the logarithmic barrier method
  yields the dual feasible point `μ i = -1 / (t f i x)` and is no more than `m / t`-suboptimal,
  where `m` is the number of constraints (Boyd–Vandenberghe §11.2.2).

Equality constraints are not treated: Boyd–Vandenberghe's Slater theorem also allows affine
equality constraints, with the strictly feasible point taken in the relative interior of `D`.
-/

@[expose] public section

namespace MathlibExt.Analysis.Convex.LagrangeDuality

open Finset

variable {E ι : Type*} [Fintype ι]

section VectorSpace

/-- The **Lagrangian** `L(x, μ) = f₀ x + ∑ i, μ i * f i x` of the problem of minimizing `f₀`
subject to `f i x ≤ 0` (Boyd–Vandenberghe, *Convex Optimization*, §5.1.1, without equality
constraints). -/
def lagrangian (f₀ : E → ℝ) (f : ι → E → ℝ) (x : E) (μ : ι → ℝ) : ℝ :=
  f₀ x + ∑ i, μ i * f i x

/-- The **Lagrange dual function** `g(μ) = inf_{x ∈ D} L(x, μ)`, valued in `EReal` since it may
be `-∞` (Boyd–Vandenberghe, *Convex Optimization*, §5.1.2). -/
noncomputable def dualFunction (D : Set E) (f₀ : E → ℝ) (f : ι → E → ℝ) (μ : ι → ℝ) : EReal :=
  ⨅ x ∈ D, ((lagrangian f₀ f x μ : ℝ) : EReal)

/-- The **optimal value** `p⋆ = inf {f₀ x | x ∈ D, f i x ≤ 0 for all i}` of the primal problem,
valued in `EReal` (`⊤` if infeasible, `⊥` if unbounded below) (Boyd–Vandenberghe §4.1.1). -/
noncomputable def primalValue (D : Set E) (f₀ : E → ℝ) (f : ι → E → ℝ) : EReal :=
  ⨅ x ∈ {x | x ∈ D ∧ ∀ i, f i x ≤ 0}, ((f₀ x : ℝ) : EReal)

/-- The **dual optimal value** `d⋆ = sup_{μ ≥ 0} g(μ)` (Boyd–Vandenberghe §5.2, eq. (5.16)). -/
noncomputable def dualValue (D : Set E) (f₀ : E → ℝ) (f : ι → E → ℝ) : EReal :=
  ⨆ μ ∈ {μ : ι → ℝ | 0 ≤ μ}, dualFunction D f₀ f μ

/-- **Lagrangian lower bound.** For dual feasible `μ ≥ 0` and primal feasible `x ∈ D`, the
Lagrangian lies below the objective: `L(x, μ) ≤ f₀ x` (Boyd–Vandenberghe §5.1.3). -/
theorem lagrangian_le_of_feasible {f₀ : E → ℝ} {f : ι → E → ℝ} {x : E} {μ : ι → ℝ}
    (hμ : 0 ≤ μ) (hx : ∀ i, f i x ≤ 0) : lagrangian f₀ f x μ ≤ f₀ x := by
  have : ∑ i, μ i * f i x ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (hμ i) (hx i)
  unfold lagrangian
  linarith

/-- **Lower bound property of the dual function.** For every `μ ≥ 0` and every feasible
`x ∈ D`, `g(μ) ≤ f₀ x` (Boyd–Vandenberghe §5.1.3, eq. (5.2)). -/
theorem dualFunction_le_of_feasible {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ} {x : E}
    {μ : ι → ℝ} (hμ : 0 ≤ μ) (hxD : x ∈ D) (hx : ∀ i, f i x ≤ 0) :
    dualFunction D f₀ f μ ≤ f₀ x :=
  (iInf₂_le x hxD).trans (EReal.coe_le_coe_iff.2 (lagrangian_le_of_feasible hμ hx))

/-- **Weak duality** `d⋆ ≤ p⋆`, which holds with no convexity assumption (Boyd–Vandenberghe
§5.2.2, eq. (5.23)). -/
theorem dualValue_le_primalValue (D : Set E) (f₀ : E → ℝ) (f : ι → E → ℝ) :
    dualValue D f₀ f ≤ primalValue D f₀ f :=
  iSup₂_le fun _ hμ => le_iInf₂ fun _ hx => dualFunction_le_of_feasible hμ hx.1 hx.2

private theorem nonneg_of_forall_le_add_mul {K u c : ℝ}
    (h : ∀ r : ℝ, 0 ≤ r → u ≤ K + r * c) : 0 ≤ c := by
  by_contra! hc
  have hc0 : c ≠ 0 := hc.ne
  have h0 := h 0 le_rfl
  have hr := h ((K - u + 1) / (-c)) (div_nonneg (by linarith) (by linarith))
  have hcalc : (K - u + 1) / (-c) * c = -(K - u + 1) := by
    field_simp
  linarith

private theorem le_of_forall_sub_mul_lt {a b u : ℝ} (hb : 0 ≤ b)
    (h : ∀ ε : ℝ, 0 < ε → a - ε * b < u) : a ≤ u := by
  by_contra! hau
  have hε : 0 < (a - u) / (b + 1) := div_pos (by linarith) (by linarith)
  have h1 := h _ hε
  have h2 : (a - u) / (b + 1) * b < a - u := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

/-- **Slater's theorem, multiplier form.** Consider a convex problem: `D` convex, `f₀` and every
`f i` convex on `D`. Suppose Slater's condition holds: some `x ∈ D` has `f i x < 0` for all `i`.
If `p` is a lower bound for `f₀` on the feasible set, then there is a dual feasible `μ ≥ 0` with
`p ≤ L(x, μ)` for every `x ∈ D`, that is `p ≤ g(μ)`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§5.2.3 (Slater's condition, eq. (5.26)) and §5.3.2 (proof of strong duality under constraint
qualifications, via a separating hyperplane in the space of constraint and objective values),
specialized to problems without equality constraints. -/
theorem exists_multiplier_of_slater [AddCommGroup E] [Module ℝ E]
    {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ}
    (hf₀ : ConvexOn ℝ D f₀) (hf : ∀ i, ConvexOn ℝ D (f i))
    (hslater : ∃ x ∈ D, ∀ i, f i x < 0) (p : ℝ)
    (hp : ∀ x ∈ D, (∀ i, f i x ≤ 0) → p ≤ f₀ x) :
    ∃ μ : ι → ℝ, 0 ≤ μ ∧ ∀ x ∈ D, p ≤ lagrangian f₀ f x μ := by
  classical
  obtain ⟨x₀, hx₀D, hx₀⟩ := hslater
  -- The set `A` of achievable (constraint, objective) value bounds and the open quadrant `C`.
  let A : Set ((ι → ℝ) × ℝ) := {q | ∃ x ∈ D, (∀ i, f i x ≤ q.1 i) ∧ f₀ x ≤ q.2}
  let C : Set ((ι → ℝ) × ℝ) := (Set.univ.pi fun _ => Set.Iio (0 : ℝ)) ×ˢ Set.Iio p
  have hAconv : Convex ℝ A := by
    rintro q ⟨x, hxD, hxf, hxf₀⟩ q' ⟨x', hx'D, hx'f, hx'f₀⟩ a b ha hb hab
    refine ⟨a • x + b • x', hf₀.1 hxD hx'D ha hb hab, fun i => ?_, ?_⟩
    · have := (hf i).2 hxD hx'D ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nlinarith [hxf i, hx'f i]
    · have := hf₀.2 hxD hx'D ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
      nlinarith
  have hCconv : Convex ℝ C :=
    (convex_pi fun _ _ => convex_Iio (0 : ℝ)).prod (convex_Iio p)
  have hCopen : IsOpen C :=
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Iio).prod isOpen_Iio
  have hdisj : Disjoint C A := by
    rw [Set.disjoint_left]
    rintro q ⟨hq1, hq2⟩ ⟨x, hxD, hxf, hxf₀⟩
    have hfeas : ∀ i, f i x ≤ 0 := fun i => (hxf i).trans (hq1 i (Set.mem_univ i)).le
    have := hp x hxD hfeas
    have hq2' : q.2 < p := hq2
    linarith
  obtain ⟨φ, u, hφC, hφA⟩ := geometric_hahn_banach_open hCconv hCopen hAconv hdisj
  -- Coordinates of the separating functional.
  set ν : ι → ℝ := fun i => φ (Pi.single i 1, 0) with hν
  set μ₀ : ℝ := φ (0, 1) with hμ₀
  have hdecomp : ∀ (v : ι → ℝ) (t : ℝ), φ (v, t) = ∑ i, v i * ν i + t * μ₀ := by
    intro v t
    have hvt : ((v, t) : (ι → ℝ) × ℝ) =
        ∑ i, v i • ((Pi.single i (1 : ℝ), (0 : ℝ)) : (ι → ℝ) × ℝ) +
          t • ((0, 1) : (ι → ℝ) × ℝ) := by
      refine Prod.ext ?_ ?_
      · funext j
        simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]
    rw [hvt]
    simp only [map_add, map_sum, map_smul, smul_eq_mul, hν, hμ₀]
  have hA_mem : ∀ x ∈ D, ((fun i => f i x, f₀ x) : (ι → ℝ) × ℝ) ∈ A :=
    fun x hx => ⟨x, hx, fun _ => le_rfl, le_rfl⟩
  have hbound : ∀ x ∈ D, u ≤ ∑ i, f i x * ν i + f₀ x * μ₀ := by
    intro x hx
    have := hφA _ (hA_mem x hx)
    rwa [hdecomp] at this
  -- Nonnegativity of the coefficients, from the upward closedness of `A`.
  have hν_nonneg : 0 ≤ ν := by
    intro i
    refine nonneg_of_forall_le_add_mul (K := ∑ j, f j x₀ * ν j + f₀ x₀ * μ₀) (u := u) ?_
    intro r hr
    have hmem : ((fun j => f j x₀ + if j = i then r else 0, f₀ x₀) : (ι → ℝ) × ℝ) ∈ A := by
      refine ⟨x₀, hx₀D, fun j => ?_, le_rfl⟩
      change f j x₀ ≤ f j x₀ + if j = i then r else 0
      split_ifs <;> simp [hr]
    have := hφA _ hmem
    rw [hdecomp] at this
    simpa [add_mul, Finset.sum_add_distrib, ite_mul, add_assoc, add_comm, add_left_comm]
      using this
  have hμ₀_nonneg : 0 ≤ μ₀ := by
    refine nonneg_of_forall_le_add_mul (K := ∑ j, f j x₀ * ν j + f₀ x₀ * μ₀) (u := u) ?_
    intro r hr
    have hmem : ((fun j => f j x₀, f₀ x₀ + r) : (ι → ℝ) × ℝ) ∈ A :=
      ⟨x₀, hx₀D, fun _ => le_rfl, by linarith⟩
    have := hφA _ hmem
    rw [hdecomp] at this
    linarith
  -- `μ₀ p ≤ u`, by letting points of `C` tend to `(0, p)`.
  have hμ₀p : μ₀ * p ≤ u := by
    refine le_of_forall_sub_mul_lt (b := ∑ i, ν i + μ₀)
      (add_nonneg (Finset.sum_nonneg fun i _ => hν_nonneg i) hμ₀_nonneg) ?_
    intro ε hε
    have hmem : ((fun _ => -ε, p - ε) : (ι → ℝ) × ℝ) ∈ C :=
      ⟨fun _ _ => by simp [hε], by simp [hε]⟩
    have := hφC _ hmem
    rw [hdecomp] at this
    have hs : ∑ i, -ε * ν i = -ε * ∑ i, ν i := by rw [Finset.mul_sum]
    rw [hs] at this
    linarith
  rcases hμ₀_nonneg.lt_or_eq with hpos | hzero
  · -- Nondegenerate hyperplane: normalize by `μ₀`.
    refine ⟨fun i => ν i / μ₀, fun i => div_nonneg (hν_nonneg i) hpos.le, fun x hx => ?_⟩
    have hb := hbound x hx
    have hsum : ∑ i, ν i / μ₀ * f i x = (∑ i, f i x * ν i) / μ₀ := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    unfold lagrangian
    rw [hsum]
    have : p * μ₀ ≤ f₀ x * μ₀ + ∑ i, f i x * ν i := by linarith
    have h2 : p ≤ (f₀ x * μ₀ + ∑ i, f i x * ν i) / μ₀ := (le_div_iff₀ hpos).2 this
    have h3 : (f₀ x * μ₀ + ∑ i, f i x * ν i) / μ₀ = f₀ x + (∑ i, f i x * ν i) / μ₀ := by
      field_simp
    linarith
  · -- Vertical hyperplane: impossible under Slater's condition.
    exfalso
    have hz : μ₀ = 0 := hzero.symm
    have hu0 : 0 ≤ u := by simpa [hz] using hμ₀p
    by_cases hall : ∀ i, ν i = 0
    · have hmem : ((fun _ => -1, p - 1) : (ι → ℝ) × ℝ) ∈ C :=
        ⟨fun _ _ => by simp, by simp⟩
      have h1 := hφC _ hmem
      rw [hdecomp] at h1
      have h2 := hbound x₀ hx₀D
      simp [hall, hz] at h1 h2
      linarith
    · simp only [not_forall] at hall
      obtain ⟨i₀, hi₀⟩ := hall
      have hi₀pos : 0 < ν i₀ := lt_of_le_of_ne (hν_nonneg i₀) (Ne.symm hi₀)
      have hneg : ∑ i, f i x₀ * ν i < 0 := by
        have hle : ∀ i ∈ (Finset.univ : Finset ι), f i x₀ * ν i ≤ 0 := fun i _ =>
          mul_nonpos_of_nonpos_of_nonneg (hx₀ i).le (hν_nonneg i)
        calc ∑ i, f i x₀ * ν i < ∑ _i : ι, (0 : ℝ) :=
              Finset.sum_lt_sum hle ⟨i₀, Finset.mem_univ _, mul_neg_of_neg_of_pos (hx₀ i₀) hi₀pos⟩
          _ = 0 := by simp
      have h2 := hbound x₀ hx₀D
      rw [hz, mul_zero, add_zero] at h2
      linarith

omit [Fintype ι] in
private theorem primalValue_ne_top_of_slater {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ}
    (hslater : ∃ x ∈ D, ∀ i, f i x < 0) : primalValue D f₀ f ≠ ⊤ := by
  obtain ⟨x₀, hx₀D, hx₀⟩ := hslater
  have : primalValue D f₀ f ≤ f₀ x₀ := iInf₂_le x₀ ⟨hx₀D, fun i => (hx₀ i).le⟩
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) this

private theorem le_dualFunction_of_le_primalValue [AddCommGroup E] [Module ℝ E]
    {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ}
    (hf₀ : ConvexOn ℝ D f₀) (hf : ∀ i, ConvexOn ℝ D (f i))
    (hslater : ∃ x ∈ D, ∀ i, f i x < 0) {p : ℝ} (hp : (p : EReal) ≤ primalValue D f₀ f) :
    ∃ μ : ι → ℝ, 0 ≤ μ ∧ (p : EReal) ≤ dualFunction D f₀ f μ := by
  have hp' : ∀ x ∈ D, (∀ i, f i x ≤ 0) → p ≤ f₀ x := fun x hxD hx =>
    EReal.coe_le_coe_iff.1 (hp.trans (iInf₂_le x ⟨hxD, hx⟩))
  obtain ⟨μ, hμ, hL⟩ := exists_multiplier_of_slater hf₀ hf hslater p hp'
  exact ⟨μ, hμ, le_iInf₂ fun x hx => EReal.coe_le_coe_iff.2 (hL x hx)⟩

/-- **Strong duality under Slater's condition.** For a convex problem (`f₀` and every `f i` convex
on the convex set `D`) satisfying Slater's condition (some `x ∈ D` has `f i x < 0` for all `i`),
the dual optimal value equals the primal optimal value: `d⋆ = p⋆` in `EReal`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§5.2.3 (Slater's theorem), with proof in §5.3.2; problems without equality constraints. -/
theorem dualValue_eq_primalValue_of_slater [AddCommGroup E] [Module ℝ E]
    {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ}
    (hf₀ : ConvexOn ℝ D f₀) (hf : ∀ i, ConvexOn ℝ D (f i))
    (hslater : ∃ x ∈ D, ∀ i, f i x < 0) :
    dualValue D f₀ f = primalValue D f₀ f := by
  refine le_antisymm (dualValue_le_primalValue D f₀ f) ?_
  by_cases hbot : primalValue D f₀ f = ⊥
  · rw [hbot]; exact bot_le
  have htop := primalValue_ne_top_of_slater (f₀ := f₀) hslater
  have hcoe : ((primalValue D f₀ f).toReal : EReal) = primalValue D f₀ f :=
    EReal.coe_toReal htop hbot
  obtain ⟨μ, hμ, hle⟩ := le_dualFunction_of_le_primalValue hf₀ hf hslater hcoe.le
  rw [← hcoe]
  exact hle.trans (le_iSup₂_of_le μ hμ le_rfl)

/-- **Dual attainment under Slater's condition.** For a convex problem satisfying Slater's
condition whose optimal value is not `-∞`, some dual feasible `μ ≥ 0` attains `g(μ) = p⋆`.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§5.2.3 (Slater's condition "also implies that the dual optimal value is attained when
`d⋆ > −∞`"). -/
theorem exists_dualFunction_eq_primalValue_of_slater [AddCommGroup E] [Module ℝ E]
    {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ}
    (hf₀ : ConvexOn ℝ D f₀) (hf : ∀ i, ConvexOn ℝ D (f i))
    (hslater : ∃ x ∈ D, ∀ i, f i x < 0) (hbot : primalValue D f₀ f ≠ ⊥) :
    ∃ μ : ι → ℝ, 0 ≤ μ ∧ dualFunction D f₀ f μ = primalValue D f₀ f := by
  have htop := primalValue_ne_top_of_slater (f₀ := f₀) hslater
  have hcoe : ((primalValue D f₀ f).toReal : EReal) = primalValue D f₀ f :=
    EReal.coe_toReal htop hbot
  obtain ⟨μ, hμ, hle⟩ := le_dualFunction_of_le_primalValue hf₀ hf hslater hcoe.le
  refine ⟨μ, hμ, le_antisymm ?_ (hcoe ▸ hle)⟩
  exact (le_iSup₂_of_le (f := fun μ (_ : μ ∈ {μ : ι → ℝ | 0 ≤ μ}) => dualFunction D f₀ f μ)
    μ hμ le_rfl).trans (dualValue_le_primalValue D f₀ f)

end VectorSpace

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Lagrangian of a convex problem is convex in `x` for every `μ ≥ 0`. -/
theorem convexOn_lagrangian {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ} {μ : ι → ℝ}
    (hf₀ : ConvexOn ℝ D f₀) (hf : ∀ i, ConvexOn ℝ D (f i)) (hμ : 0 ≤ μ) :
    ConvexOn ℝ D (fun x => lagrangian f₀ f x μ) := by
  unfold lagrangian
  refine hf₀.add (FinsetSum.convexOn_finset_sum hf₀.1 _ fun i _ => ?_)
  simpa [smul_eq_mul] using (hf i).smul (hμ i)

/-- The derivative of the Lagrangian in `x`. -/
theorem hasFDerivAt_lagrangian {f₀ : E → ℝ} {f : ι → E → ℝ} {f₀' : E →L[ℝ] ℝ}
    {f' : ι → E →L[ℝ] ℝ} {x : E} (μ : ι → ℝ) (hf₀' : HasFDerivAt f₀ f₀' x)
    (hf' : ∀ i, HasFDerivAt (f i) (f' i) x) :
    HasFDerivAt (fun y => lagrangian f₀ f y μ) (f₀' + ∑ i, μ i • f' i) x := by
  unfold lagrangian
  refine hf₀'.add ?_
  have h := HasFDerivAt.sum (u := Finset.univ) (A := fun i y => μ i * f i y)
    (A' := fun i => μ i • f' i) fun i _ => (hf' i).const_mul (μ i)
  convert h using 1
  funext y
  simp [Finset.sum_apply]

/-- If the Lagrangian of a convex problem is stationary in `x` at a point `x ∈ D`, then `x`
minimizes it over `D` and the dual function equals `L(x, μ)` (Boyd–Vandenberghe §5.5.3). -/
theorem dualFunction_eq_lagrangian_of_stationary {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ}
    {f₀' : E →L[ℝ] ℝ} {f' : ι → E →L[ℝ] ℝ} {x : E} {μ : ι → ℝ}
    (hf₀ : ConvexOn ℝ D f₀) (hf : ∀ i, ConvexOn ℝ D (f i)) (hμ : 0 ≤ μ) (hxD : x ∈ D)
    (hf₀' : HasFDerivAt f₀ f₀' x) (hf' : ∀ i, HasFDerivAt (f i) (f' i) x)
    (hstat : f₀' + ∑ i, μ i • f' i = 0) :
    dualFunction D f₀ f μ = lagrangian f₀ f x μ := by
  have hd := hasFDerivAt_lagrangian μ hf₀' hf'
  rw [hstat] at hd
  have hmin := FirstOrderCondition.isMinOn_of_hasFDerivAt_eq_zero
    (convexOn_lagrangian hf₀ hf hμ) hxD hd
  refine le_antisymm (iInf₂_le x hxD) (le_iInf₂ fun y hy => ?_)
  exact EReal.coe_le_coe_iff.2 (hmin hy)

/-- **Sufficiency of the KKT conditions for convex problems.** Let `f₀` and the `f i` be convex
on `D` and differentiable at `x ∈ D`. If `x` and `μ` satisfy the Karush–Kuhn–Tucker conditions —
primal feasibility `f i x ≤ 0`, dual feasibility `μ ≥ 0`, complementary slackness
`μ i * f i x = 0`, and stationarity `Df₀(x) + ∑ i, μ i • Dfᵢ(x) = 0` — then `x` is primal optimal,
and `g(μ) = f₀ x`, so `μ` is dual optimal with zero duality gap.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§5.5.3, "KKT conditions for convex problems", without equality constraints. -/
theorem kkt_sufficient {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ}
    {f₀' : E →L[ℝ] ℝ} {f' : ι → E →L[ℝ] ℝ} {x : E} {μ : ι → ℝ}
    (hf₀ : ConvexOn ℝ D f₀) (hf : ∀ i, ConvexOn ℝ D (f i)) (hxD : x ∈ D)
    (hf₀' : HasFDerivAt f₀ f₀' x) (hf' : ∀ i, HasFDerivAt (f i) (f' i) x)
    (hfeas : ∀ i, f i x ≤ 0) (hμ : 0 ≤ μ) (hslack : ∀ i, μ i * f i x = 0)
    (hstat : f₀' + ∑ i, μ i • f' i = 0) :
    (∀ y ∈ D, (∀ i, f i y ≤ 0) → f₀ x ≤ f₀ y) ∧ dualFunction D f₀ f μ = f₀ x ∧
      primalValue D f₀ f = f₀ x := by
  have hg := dualFunction_eq_lagrangian_of_stationary hf₀ hf hμ hxD hf₀' hf' hstat
  have hL : lagrangian f₀ f x μ = f₀ x := by simp [lagrangian, hslack]
  rw [hL] at hg
  have hopt : ∀ y ∈ D, (∀ i, f i y ≤ 0) → f₀ x ≤ f₀ y := fun y hyD hy => by
    have := dualFunction_le_of_feasible (f₀ := f₀) hμ hyD hy
    rw [hg] at this
    exact EReal.coe_le_coe_iff.1 this
  refine ⟨hopt, hg, le_antisymm (iInf₂_le x ⟨hxD, hfeas⟩) (le_iInf₂ fun y hy => ?_)⟩
  exact EReal.coe_le_coe_iff.2 (hopt y hy.1 hy.2)

/-- **Duality gap of central points in the barrier method.** Let `f₀` and the `f i` be convex on
`D` and differentiable at a strictly feasible `x ∈ D` (`f i x < 0` for all `i`), and let `t > 0`.
Suppose `x` satisfies the centrality condition of the logarithmic barrier method,
`t Df₀(x) + ∑ i, (1 / (-f i x)) Dfᵢ(x) = 0`, i.e. `x` is a stationary point of
`t f₀ - ∑ i, log (-f i)`. Then `μ i = -1 / (t f i x)` is dual feasible with
`g(μ) = f₀ x - m / t`, where `m` is the number of constraints; hence `f₀ x - m / t ≤ f₀ y` for
every feasible `y`, i.e. `x` is no more than `m / t`-suboptimal.

Source: S. Boyd and L. Vandenberghe, *Convex Optimization*, Cambridge University Press, 2004,
§11.2.2, eqs. (11.7)–(11.10), without equality constraints. -/
theorem central_point_duality_gap {D : Set E} {f₀ : E → ℝ} {f : ι → E → ℝ}
    {f₀' : E →L[ℝ] ℝ} {f' : ι → E →L[ℝ] ℝ} {x : E} {t : ℝ}
    (hf₀ : ConvexOn ℝ D f₀) (hf : ∀ i, ConvexOn ℝ D (f i)) (hxD : x ∈ D)
    (hf₀' : HasFDerivAt f₀ f₀' x) (hf' : ∀ i, HasFDerivAt (f i) (f' i) x)
    (hstrict : ∀ i, f i x < 0) (ht : 0 < t)
    (hcent : t • f₀' + ∑ i, (-f i x)⁻¹ • f' i = 0) :
    (0 ≤ fun i => -(t * f i x)⁻¹) ∧
      dualFunction D f₀ f (fun i => -(t * f i x)⁻¹) = f₀ x - Fintype.card ι / t ∧
      ∀ y ∈ D, (∀ i, f i y ≤ 0) → f₀ x - Fintype.card ι / t ≤ f₀ y := by
  set μ : ι → ℝ := fun i => -(t * f i x)⁻¹ with hμdef
  have hμ : 0 ≤ μ := fun i => by
    have : t * f i x < 0 := mul_neg_of_pos_of_neg ht (hstrict i)
    simp only [hμdef, Pi.zero_apply, Left.nonneg_neg_iff]
    exact (inv_lt_zero.2 this).le
  have hstat : f₀' + ∑ i, μ i • f' i = 0 := by
    have hμi : ∀ i, μ i = t⁻¹ * (-f i x)⁻¹ := fun i => by
      simp only [hμdef, mul_inv, inv_neg, mul_neg]
    have : f₀' + ∑ i, μ i • f' i = t⁻¹ • (t • f₀' + ∑ i, (-f i x)⁻¹ • f' i) := by
      rw [smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, hμi]
    rw [this, hcent, smul_zero]
  have hg := dualFunction_eq_lagrangian_of_stationary hf₀ hf hμ hxD hf₀' hf' hstat
  have hL : lagrangian f₀ f x μ = f₀ x - Fintype.card ι / t := by
    have hterm : ∀ i, μ i * f i x = -(1 / t) := fun i => by
      have hne : f i x ≠ 0 := (hstrict i).ne
      simp only [hμdef]
      field_simp
    simp only [lagrangian, hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hL] at hg
  refine ⟨hμ, hg, fun y hyD hy => ?_⟩
  have := dualFunction_le_of_feasible (f₀ := f₀) hμ hyD hy
  rw [hg] at this
  exact EReal.coe_le_coe_iff.1 this

end Normed

end MathlibExt.Analysis.Convex.LagrangeDuality
