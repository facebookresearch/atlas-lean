/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Integration.RiemannPartition
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import MathlibExt.Analysis.Calculus.Wirtinger
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The one-dimensional P1 finite element method

We treat the two-point boundary value problem `-u'' = f` on `(0, 1)` with
`u(0) = u(1) = 0` and its Galerkin discretization by continuous piecewise
linear (P1) finite elements on a mesh `0 = x₀ < x₁ < ⋯ < xₙ = 1`.

The pinned Mathlib has no Sobolev space `H¹₀(0, 1)` on an interval, so the
weak formulation is stated with the energy form
`a(u, v) = ∫₀¹ u' v'` evaluated with `deriv` on concrete functions: the exact
solution is a classical `C²` solution, and the test and trial functions are
`C¹` functions or continuous piecewise linear functions. For a P1 function,
`deriv` takes junk values at the finitely many mesh nodes; these do not affect
any integral. The energy (semi)norm is `‖v‖_a = √(a(v, v))`.

## Main definitions

* `elementSlope`, `ramp`, `p1`: the P1 function with given nodal values, written as
  a sum of clamped ramps; `hat` is the hat-function basis and `interp` the
  nodal interpolant `I_h u`.
* `p1Space`: the P1 space with zero boundary values, as a submodule.
* `energy`: the energy form `a(u, v) = ∫₀¹ u' v'`.
* `stiffness`, `load`: the assembled stiffness matrix
  `K = ∑ᵢ (1 / hᵢ) eᵢ eᵢᵀ` and load vector `Fⱼ = ∫₀¹ f φⱼ`.
* `IsClassicalSolution`, `IsGalerkinSolution`: the continuous problem and the
  linear system `K c = F` with zero boundary values.

## Main results

* `energy_eq_integral_mul_of_contDiff`, `energy_eq_integral_mul_of_mem_p1Space`:
  the weak form `∫₀¹ u' v' = ∫₀¹ f v`.
* `energy_p1`, `energy_p1_p1`: `a(w, p1 d) = ∑ᵢ slopeᵢ(d) (w(xᵢ₊₁) - w(xᵢ))` and the
  element-wise formula for two P1 functions.
* `energy_hat_hat`: `a(φⱼ, φₖ) = Kⱼₖ`; `stiffness_castSucc_succ`,
  `stiffness_succ_succ`, and `stiffness_eq_zero` give the tridiagonal pattern
  (`-1 / hᵢ` off the diagonal, `1 / hᵢ + 1 / hᵢ₊₁` on it).
* `galerkin_orthogonality`: `a(u - u_h, v_h) = 0` for every `v_h` in the P1
  space.
* `energy_sub_galerkin_le`: best approximation in the energy norm (Céa's
  lemma for this symmetric form, with constant `1`).
* `isGalerkinSolution_nodal`, `p1_eq_interp_of_isGalerkinSolution`: in one
  dimension the Galerkin solution is the nodal interpolant of `u`.
* `integral_sq_le_of_eq_zero`, `integral_deriv_sq_le_of_eq_zero`: Wirtinger's
  inequality on `[a, b]` (from the merged `[0, π]` case) and the element estimate
  `∫ₐᵇ (g')² ≤ ((b - a) / π)² ∫ₐᵇ (g'')²` for `g(a) = g(b) = 0`.
* `energy_sub_interp_le`: `‖u - I_h u‖_a ≤ (h / π) ‖u''‖_{L²}`.
* `energy_sub_galerkin_le_mesh`, `integral_sq_sub_galerkin_le_mesh`:
  `‖u - u_h‖_a ≤ (h / π) ‖f‖_{L²}` and `‖u - u_h‖_{L²} ≤ (h / π)² ‖f‖_{L²}`
  (stated for the squares), i.e. `O(h)` in energy and `O(h²)` in `L²`. The `L²`
  bound uses nodal exactness, not the Aubin–Nitsche duality argument, so it is
  specific to one dimension.

## References

* S. C. Brenner and L. R. Scott, *The Mathematical Theory of Finite Element
  Methods*, 3rd ed., Springer, 2008, chapters 0–2.
* P. G. Ciarlet, *The Finite Element Method for Elliptic Problems*,
  North-Holland, 1978.
* L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS, 2010, ch. 6.
-/

@[expose] public section

namespace MathlibExt.Analysis.ODE.FiniteElement1D

open MeasureTheory
open MathlibExt.Analysis.Integration

variable (P : Partition (0 : ℝ) 1)

/-- The length `hᵢ = xᵢ₊₁ - xᵢ` of the `i`-th element of the mesh. -/
noncomputable def width (i : Fin P.n) : ℝ :=
  P.points i.succ - P.points i.castSucc

/-- The slope `(dᵢ₊₁ - dᵢ) / hᵢ` on the `i`-th element of the P1 function with
nodal values `d`. -/
noncomputable def elementSlope (d : Fin (P.n + 1) → ℝ) (i : Fin P.n) : ℝ :=
  (d i.succ - d i.castSucc) / width P i

/-- The clamped ramp of the `i`-th element: `0` left of `xᵢ`, `x - xᵢ` on
`[xᵢ, xᵢ₊₁]`, and `hᵢ` right of `xᵢ₊₁`. -/
noncomputable def ramp (i : Fin P.n) (x : ℝ) : ℝ :=
  max (P.points i.castSucc) (min x (P.points i.succ)) - P.points i.castSucc

/-- The continuous piecewise linear (P1) function with nodal values `d`:
`d₀ + ∑ᵢ slopeᵢ · rampᵢ(x)`. On `[0, 1]` it is linear on each element and
takes the value `dⱼ` at `xⱼ`; outside `[0, 1]` it is constant. -/
noncomputable def p1 (d : Fin (P.n + 1) → ℝ) (x : ℝ) : ℝ :=
  d 0 + ∑ i, elementSlope P d i * ramp P i x

/-- The hat function `φⱼ` of node `j`: the P1 function equal to `1` at `xⱼ`
and `0` at every other node. -/
noncomputable def hat (j : Fin (P.n + 1)) : ℝ → ℝ :=
  p1 P (Pi.single j 1)

/-- The nodal interpolant `I_h u`: the P1 function with nodal values
`u(xⱼ)`. -/
noncomputable def interp (u : ℝ → ℝ) : ℝ → ℝ :=
  p1 P fun j => u (P.points j)

/-- `p1` as a linear map from nodal values to functions. -/
noncomputable def p1Map : (Fin (P.n + 1) → ℝ) →ₗ[ℝ] ℝ → ℝ where
  toFun := p1 P
  map_add' c d := by
    funext x
    simp only [p1, elementSlope, Pi.add_apply]
    rw [add_add_add_comm, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  map_smul' a d := by
    funext x
    simp only [p1, elementSlope, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

/-- Nodal vectors with zero boundary values `d₀ = dₙ = 0`. -/
def dirichletNodal : Submodule ℝ (Fin (P.n + 1) → ℝ) :=
  LinearMap.ker (LinearMap.proj 0) ⊓ LinearMap.ker (LinearMap.proj (Fin.last P.n))

/-- The P1 finite element space `V_h` with zero boundary values: the image under
`p1Map` of the nodal vectors vanishing at both ends. -/
noncomputable def p1Space : Submodule ℝ (ℝ → ℝ) :=
  (dirichletNodal P).map (p1Map P)

/-- The energy form `a(u, v) = ∫₀¹ u'(x) v'(x) dx` of `-u'' = f`. For a P1
function, `deriv` is junk at the mesh nodes, a null set. -/
noncomputable def energy (u v : ℝ → ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, deriv u x * deriv v x

/-- The `i`-th element vector `eᵢ = δ_{i+1} - δᵢ` of the assembly. -/
noncomputable def elementVector (i : Fin P.n) : Fin (P.n + 1) → ℝ :=
  Pi.single i.succ 1 - Pi.single i.castSucc 1

/-- The assembled stiffness matrix `K = ∑ᵢ (1 / hᵢ) eᵢ eᵢᵀ` on all nodes:
each element contributes `(1 / hᵢ) [[1, -1], [-1, 1]]` at nodes `i, i + 1`. -/
noncomputable def stiffness : Matrix (Fin (P.n + 1)) (Fin (P.n + 1)) ℝ :=
  fun j k => ∑ i, elementVector P i j * elementVector P i k / width P i

/-- The load vector `Fⱼ = ∫₀¹ f φⱼ`. -/
noncomputable def load (f : ℝ → ℝ) (j : Fin (P.n + 1)) : ℝ :=
  ∫ x in (0 : ℝ)..1, f x * hat P j x

/-- `u` is a classical solution of `-u'' = f` on `(0, 1)` with
`u(0) = u(1) = 0`. We ask `u` to be `C²` on all of `ℝ`, which is no loss for
the interval problem (a `C²` function on `[0, 1]` extends), and `f` to be continuous.
The equation is stated on the open interval, as in the Dirichlet problem: requiring it
at the endpoints without regularity of `f` would be a genuine strengthening. With `f`
continuous, endpoint equality follows by continuity (`eq_Icc`), and the integral proofs
use that derived version. -/
structure IsClassicalSolution (f u : ℝ → ℝ) : Prop where
  contDiff : ContDiff ℝ 2 u
  f_cont : Continuous f
  zero_left : u 0 = 0
  zero_right : u 1 = 0
  eq : ∀ x ∈ Set.Ioo (0 : ℝ) 1, -deriv (deriv u) x = f x

/-- Endpoint equality, derived from the open-interval equation by continuity of
`-u''` and `f`: the two sides agree on `(0, 1)`, hence on its closure `[0, 1]`. -/
theorem IsClassicalSolution.eq_Icc {f u : ℝ → ℝ} (hu : IsClassicalSolution f u)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : -deriv (deriv u) x = f x := by
  have hcont1 : ContinuousOn (fun x => -deriv (deriv u) x) (Set.Icc (0 : ℝ) 1) :=
    ((contDiff_deriv_of_contDiff_two hu.contDiff).continuous_deriv le_rfl).neg.continuousOn
  have hcont2 : ContinuousOn f (Set.Icc (0 : ℝ) 1) := hu.f_cont.continuousOn
  have hEq : Set.EqOn (fun x => -deriv (deriv u) x) f (Set.Ioo (0 : ℝ) 1) :=
    fun x hx => hu.eq x hx
  have hcl : Set.Icc (0 : ℝ) 1 = closure (Set.Ioo (0 : ℝ) 1) := by
    rw [Set.closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  rw [hcl]
  exact ContinuousOn.eqOn_closure hcont1 hcont2 hEq hx

/-- The coefficient vector `c` solves the Galerkin system: zero boundary
values and `(K c)ⱼ = Fⱼ` at every interior node `j`. The Galerkin solution is
`u_h = p1 P c`. -/
def IsGalerkinSolution (f : ℝ → ℝ) (c : Fin (P.n + 1) → ℝ) : Prop :=
  c 0 = 0 ∧ c (Fin.last P.n) = 0 ∧
    ∀ j, j ≠ 0 → j ≠ Fin.last P.n → (stiffness P).mulVec c j = load P f j

/-! ### The P1 functions -/

/-- Every element has positive length. -/
theorem width_pos (i : Fin P.n) : 0 < width P i :=
  sub_pos.mpr (P.ordered (Fin.castSucc_lt_succ ..))

/-- Every element length is at most the mesh size `h`. -/
theorem width_le_mesh (i : Fin P.n) : width P i ≤ P.mesh := by
  have hn : P.n ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt)
  unfold Partition.mesh
  simp only [hn, ↓reduceDIte]
  exact Finset.le_sup' (fun i : Fin P.n => P.points i.succ - P.points i.castSucc)
    (Finset.mem_univ i)

/-- The nodal vector `d` extended to `ℕ` (by `0` past the last node). -/
private noncomputable def natExt (d : Fin (P.n + 1) → ℝ) (m : ℕ) : ℝ :=
  if h : m < P.n + 1 then d ⟨m, h⟩ else 0

private theorem natExt_fin (d : Fin (P.n + 1) → ℝ) (j : Fin (P.n + 1)) :
    natExt P d j = d j := by
  simp [natExt, j.isLt]

/-- Telescoping: `∑_{k < i} (d_{k+1} - d_k) = dᵢ - d₀`. -/
private theorem sum_lt_sub (d : Fin (P.n + 1) → ℝ) (i : Fin P.n) :
    ∑ k : Fin P.n, (if (k : ℕ) < i then d k.succ - d k.castSucc else 0) =
      d i.castSucc - d 0 := by
  have h1 : ∀ k : Fin P.n, (if (k : ℕ) < i then d k.succ - d k.castSucc else 0) =
      (fun m : ℕ => if m < i then natExt P d (m + 1) - natExt P d m else 0) k := by
    intro k
    simp only
    rw [← natExt_fin P d k.succ, ← natExt_fin P d k.castSucc]
    simp
  rw [Finset.sum_congr rfl fun k _ => h1 k, Fin.sum_univ_eq_sum_range
    (fun m : ℕ => if m < (i : ℕ) then natExt P d (m + 1) - natExt P d m else 0) P.n,
    ← Finset.sum_filter]
  have h2 : (Finset.range P.n).filter (fun m => m < (i : ℕ)) = Finset.range i := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [h2, Finset.sum_range_sub (natExt P d), ← natExt_fin P d i.castSucc,
    ← natExt_fin P d 0]
  simp

/-- On the `i`-th element, `p1 P d` is the linear function through
`(xᵢ, dᵢ)` with slope `slopeᵢ = elementSlope P d i`. -/
theorem p1_eq_of_mem_Icc (d : Fin (P.n + 1) → ℝ) (i : Fin P.n) {x : ℝ}
    (hx : x ∈ Set.Icc (P.points i.castSucc) (P.points i.succ)) :
    p1 P d x = d i.castSucc + elementSlope P d i * (x - P.points i.castSucc) := by
  have hterm : ∀ k : Fin P.n, elementSlope P d k * ramp P k x =
      (if (k : ℕ) < i then d k.succ - d k.castSucc else 0) +
        (if k = i then elementSlope P d i * (x - P.points i.castSucc) else 0) := by
    intro k
    rcases lt_trichotomy (k : ℕ) i with hk | hk | hk
    · have hle : P.points k.succ ≤ P.points i.castSucc :=
        P.ordered.monotone (Fin.le_def.mpr (by simp; omega))
      have hne : k ≠ i := fun h => by simp [h] at hk
      simp only [hk, hne, ↓reduceIte, add_zero]
      rw [ramp, min_eq_right (hle.trans hx.1),
        max_eq_right (P.ordered (Fin.castSucc_lt_succ ..)).le, elementSlope,
        show P.points k.succ - P.points k.castSucc = width P k from rfl,
        div_mul_cancel₀ _ (width_pos P k).ne']
    · have hki : k = i := Fin.ext hk
      subst hki
      simp only [lt_irrefl, ↓reduceIte, zero_add]
      rw [ramp, min_eq_left hx.2,
        max_eq_right hx.1]
    · have hle : P.points i.succ ≤ P.points k.castSucc :=
        P.ordered.monotone (Fin.le_def.mpr (by simp; omega))
      have hne : k ≠ i := fun h => by simp [h] at hk
      have hk' : ¬ (k : ℕ) < i := by omega
      simp only [hk', hne, ↓reduceIte, add_zero]
      rw [ramp,
        min_eq_left (hx.2.trans (hle.trans (P.ordered (Fin.castSucc_lt_succ ..)).le)),
        max_eq_left (hx.2.trans hle), sub_self, mul_zero]
  rw [p1, Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib, sum_lt_sub,
    Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, ↓reduceIte]
  ring

/-- `p1 P d` interpolates the nodal values. -/
theorem p1_points (d : Fin (P.n + 1) → ℝ) (j : Fin (P.n + 1)) :
    p1 P d (P.points j) = d j := by
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, rfl⟩
  · let i : Fin P.n := ⟨0, P.n_pos_of_lt zero_lt_one⟩
    have hi : i.castSucc = 0 := rfl
    have hx : P.points 0 ∈ Set.Icc (P.points i.castSucc) (P.points i.succ) := by
      rw [hi]
      refine ⟨le_rfl, ?_⟩
      have := (P.ordered (Fin.castSucc_lt_succ (i := i))).le
      rwa [hi] at this
    rw [p1_eq_of_mem_Icc P d i hx, hi]
    ring
  · have hx : P.points i.succ ∈ Set.Icc (P.points i.castSucc) (P.points i.succ) :=
      ⟨(P.ordered (Fin.castSucc_lt_succ ..)).le, le_rfl⟩
    rw [p1_eq_of_mem_Icc P d i hx, elementSlope, width,
      div_mul_cancel₀ _ (sub_pos.mpr (P.ordered (Fin.castSucc_lt_succ ..))).ne']
    ring

/-- P1 functions are continuous. -/
theorem continuous_p1 (d : Fin (P.n + 1) → ℝ) : Continuous (p1 P d) := by
  unfold p1 ramp
  fun_prop

/-- Inside an element, `p1 P d` has derivative `slopeᵢ`. -/
theorem hasDerivAt_p1 (d : Fin (P.n + 1) → ℝ) (i : Fin P.n) {x : ℝ}
    (hx : x ∈ Set.Ioo (P.points i.castSucc) (P.points i.succ)) :
    HasDerivAt (p1 P d) (elementSlope P d i) x := by
  have hlin : HasDerivAt (fun y => d i.castSucc + elementSlope P d i * (y - P.points i.castSucc))
      (elementSlope P d i) x := by
    have h1 : HasDerivAt (fun y : ℝ => y - P.points i.castSucc) 1 x :=
      (hasDerivAt_id x).sub_const _
    simpa using (h1.const_mul (elementSlope P d i)).const_add (d i.castSucc)
  refine hlin.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact p1_eq_of_mem_Icc P d i (Set.Ioo_subset_Icc_self hy)

/-- An integral over `[0, 1]` is the sum of the integrals over the elements. -/
theorem integral_eq_sum (g : ℝ → ℝ)
    (hg : ∀ i : Fin P.n, IntervalIntegrable g volume (P.points i.castSucc) (P.points i.succ)) :
    ∫ x in (0 : ℝ)..1, g x = ∑ i : Fin P.n, ∫ x in P.points i.castSucc..P.points i.succ, g x := by
  have hpt : ∀ j : Fin (P.n + 1), natExt P P.points j = P.points j := natExt_fin P P.points
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := natExt P P.points) (n := P.n) (fun k hk => by
      have := hg ⟨k, hk⟩
      rw [← hpt, ← hpt] at this
      simpa using this)
  have h0 : natExt P P.points 0 = 0 := by
    rw [show (0 : ℕ) = ((0 : Fin (P.n + 1)) : ℕ) from rfl, hpt, P.first]
  have h1 : natExt P P.points P.n = 1 := by
    rw [show P.n = ((Fin.last P.n : Fin (P.n + 1)) : ℕ) from rfl, hpt, P.last]
  rw [h0, h1] at hsum
  rw [← hsum, ← Fin.sum_univ_eq_sum_range (fun k =>
    ∫ x in natExt P P.points k..natExt P P.points (k + 1), g x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hpt k.castSucc, ← hpt k.succ]
  simp

/-- The key identity of the 1D P1 method: for `w` continuous on each element,
differentiable inside it, and with integrable derivative there,
`a(w, p1 d) = ∑ᵢ slopeᵢ(d) (w(xᵢ₊₁) - w(xᵢ))`. -/
theorem energy_p1 (w : ℝ → ℝ)
    (hcont : ∀ i : Fin P.n, ContinuousOn w (Set.Icc (P.points i.castSucc) (P.points i.succ)))
    (hdiff : ∀ i : Fin P.n, ∀ x ∈ Set.Ioo (P.points i.castSucc) (P.points i.succ),
      DifferentiableAt ℝ w x)
    (hint : ∀ i : Fin P.n,
      IntervalIntegrable (deriv w) volume (P.points i.castSucc) (P.points i.succ))
    (d : Fin (P.n + 1) → ℝ) :
    energy w (p1 P d) =
      ∑ i, elementSlope P d i * (w (P.points i.succ) - w (P.points i.castSucc)) := by
  have hle : ∀ i : Fin P.n, P.points i.castSucc ≤ P.points i.succ :=
    fun i => (P.ordered (Fin.castSucc_lt_succ ..)).le
  have heq : ∀ i : Fin P.n, Set.EqOn (fun x => deriv w x * elementSlope P d i)
      (fun x => deriv w x * deriv (p1 P d) x)
      (Set.uIoo (P.points i.castSucc) (P.points i.succ)) := by
    intro i x hx
    rw [Set.uIoo_of_le (hle i)] at hx
    simp only [(hasDerivAt_p1 P d i hx).deriv]
  rw [energy, integral_eq_sum P _ fun i => ((hint i).mul_const (elementSlope P d i)).congr_uIoo
    (heq i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_congr_uIoo (heq i), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (hle i) (hcont i)
      (fun x hx => (hdiff i x hx).hasDerivAt) (hint i), mul_comm]

/-! ### Weak form, stiffness matrix, Galerkin orthogonality -/

/-- The derivative of a `C²` function is `C¹`. -/
private theorem contDiff_deriv_of_contDiff_two {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (deriv u) :=
  (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) u from hu)).2.2

/-- Telescoping over the elements: `∑ᵢ (gᵢ₊₁ - gᵢ) = gₙ - g₀`. -/
private theorem sum_succ_sub_castSucc (g : Fin (P.n + 1) → ℝ) :
    ∑ i : Fin P.n, (g i.succ - g i.castSucc) = g (Fin.last P.n) - g 0 := by
  have h1 : ∀ i : Fin P.n, g i.succ - g i.castSucc =
      (fun m : ℕ => natExt P g (m + 1) - natExt P g m) i := by
    intro i
    simp only
    rw [← natExt_fin P g i.succ, ← natExt_fin P g i.castSucc]
    simp
  rw [Finset.sum_congr rfl fun i _ => h1 i,
    Fin.sum_univ_eq_sum_range (fun m : ℕ => natExt P g (m + 1) - natExt P g m) P.n,
    Finset.sum_range_sub (natExt P g), ← natExt_fin P g (Fin.last P.n), ← natExt_fin P g 0]
  simp

/-- Mesh nodes lie in `[0, 1]`. -/
private theorem points_mem_Icc (j : Fin (P.n + 1)) : P.points j ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 := P.ordered.monotone (Fin.zero_le j)
  have h1 := P.ordered.monotone (Fin.le_last j)
  rw [P.first] at h0
  rw [P.last] at h1
  exact ⟨h0, h1⟩

/-- An element lies in `[0, 1]`. -/
private theorem uIcc_subset_Icc (i : Fin P.n) :
    Set.uIcc (P.points i.castSucc) (P.points i.succ) ⊆ Set.Icc (0 : ℝ) 1 := by
  rw [Set.uIcc_of_le (P.ordered (Fin.castSucc_lt_succ ..)).le]
  exact Set.Icc_subset_Icc (points_mem_Icc P _).1 (points_mem_Icc P _).2


/-- Membership in the P1 space: `v = p1 P d` for nodal values `d` with
`d₀ = dₙ = 0`. -/
theorem mem_p1Space {v : ℝ → ℝ} :
    v ∈ p1Space P ↔ ∃ d, d 0 = 0 ∧ d (Fin.last P.n) = 0 ∧ p1 P d = v := by
  simp only [p1Space, dirichletNodal, Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_ker,
    LinearMap.proj_apply]
  constructor
  · rintro ⟨d, ⟨h0, hl⟩, rfl⟩
    exact ⟨d, h0, hl, rfl⟩
  · rintro ⟨d, h0, hl, rfl⟩
    exact ⟨d, ⟨h0, hl⟩, rfl⟩

/-- The hat function of an interior node lies in the P1 space. -/
theorem hat_mem_p1Space {j : Fin (P.n + 1)} (h0 : j ≠ 0) (hl : j ≠ Fin.last P.n) :
    hat P j ∈ p1Space P :=
  (mem_p1Space P).mpr ⟨Pi.single j 1, by simp [h0.symm],
    by simp [hl.symm], rfl⟩

/-- `a(u, p1 d) = ∑ᵢ slopeᵢ(d) (u(xᵢ₊₁) - u(xᵢ))` for a `C²` function `u`. -/
private theorem energy_contDiff_p1 {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (d : Fin (P.n + 1) → ℝ) :
    energy u (p1 P d) =
      ∑ i, elementSlope P d i * (u (P.points i.succ) - u (P.points i.castSucc)) :=
  energy_p1 P u (fun _ => hu.continuous.continuousOn)
    (fun _ _ _ => (hu.differentiable (by norm_num)).differentiableAt)
    (fun _ => (hu.continuous_deriv (by norm_num)).intervalIntegrable _ _) d

/-- The weak form for `C¹` test functions vanishing at `0` and `1`:
`∫₀¹ u' v' = ∫₀¹ f v`. -/
theorem energy_eq_integral_mul_of_contDiff {f u v : ℝ → ℝ} (hu : IsClassicalSolution f u)
    (hv : ContDiff ℝ 1 v) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    energy u v = ∫ x in (0 : ℝ)..1, f x * v x := by
  have hu1 := contDiff_deriv_of_contDiff_two hu.contDiff
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1)
    (u := deriv u) (u' := deriv (deriv u)) (v := v) (v' := deriv v)
    (fun x _ => ((hu1.differentiable (by norm_num)) x).hasDerivAt)
    (fun x _ => ((hv.differentiable (by norm_num)) x).hasDerivAt)
    ((hu1.continuous_deriv le_rfl).intervalIntegrable _ _)
    ((hv.continuous_deriv le_rfl).intervalIntegrable _ _)
  rw [energy, hibp, hv0, hv1, mul_zero, mul_zero, sub_zero, zero_sub,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le zero_le_one] at hx
  rw [← hu.eq_Icc x hx]
  ring

/-- The weak form for P1 test functions: `∫₀¹ u' v_h' = ∫₀¹ f v_h`. -/
theorem energy_eq_integral_mul_of_mem_p1Space {f u v : ℝ → ℝ} (hu : IsClassicalSolution f u)
    (hv : v ∈ p1Space P) :
    energy u v = ∫ x in (0 : ℝ)..1, f x * v x := by
  obtain ⟨d, hd0, hdl, rfl⟩ := (mem_p1Space P).mp hv
  have hu1 := contDiff_deriv_of_contDiff_two hu.contDiff
  have hle : ∀ i : Fin P.n, P.points i.castSucc ≤ P.points i.succ :=
    fun i => (P.ordered (Fin.castSucc_lt_succ ..)).le
  -- on each element, `f · p1 d = -u'' · (dᵢ + sᵢ (x - xᵢ))`
  have heq : ∀ i : Fin P.n, Set.EqOn
      (fun x => -deriv (deriv u) x *
        (d i.castSucc + elementSlope P d i * (x - P.points i.castSucc)))
      (fun x => f x * p1 P d x) (Set.uIcc (P.points i.castSucc) (P.points i.succ)) := by
    intro i x hx
    dsimp only
    rw [← hu.eq_Icc x (uIcc_subset_Icc P i hx), p1_eq_of_mem_Icc P d i (by
      rwa [Set.uIcc_of_le (hle i)] at hx)]
  have hcont : ∀ i : Fin P.n, Continuous
      (fun x => -deriv (deriv u) x *
        (d i.castSucc + elementSlope P d i * (x - P.points i.castSucc))) :=
    fun i => ((hu1.continuous_deriv le_rfl).neg).mul (by fun_prop)
  -- integration by parts on one element
  have hel : ∀ i : Fin P.n, ∫ x in P.points i.castSucc..P.points i.succ, f x * p1 P d x =
      elementSlope P d i * (u (P.points i.succ) - u (P.points i.castSucc)) -
        (deriv u (P.points i.succ) * d i.succ -
          deriv u (P.points i.castSucc) * d i.castSucc) := by
    intro i
    rw [← intervalIntegral.integral_congr (heq i)]
    have hL : ∀ x, HasDerivAt
        (fun x => d i.castSucc + elementSlope P d i * (x - P.points i.castSucc))
        (elementSlope P d i) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => y - P.points i.castSucc) 1 x :=
        (hasDerivAt_id x).sub_const _
      simpa using (h1.const_mul (elementSlope P d i)).const_add (d i.castSucc)
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := P.points i.castSucc) (b := P.points i.succ)
      (u := deriv u) (u' := deriv (deriv u))
      (v := fun x => d i.castSucc + elementSlope P d i * (x - P.points i.castSucc))
      (v' := fun _ => elementSlope P d i)
      (fun x _ => ((hu1.differentiable (by norm_num)) x).hasDerivAt) (fun x _ => hL x)
      ((hu1.continuous_deriv le_rfl).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _)
    have hint : ∫ x in P.points i.castSucc..P.points i.succ, deriv u x * elementSlope P d i =
        elementSlope P d i * (u (P.points i.succ) - u (P.points i.castSucc)) := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_deriv_eq_sub
        (fun x _ => (hu.contDiff.differentiable (by norm_num)) x)
        ((hu.contDiff.continuous_deriv (by norm_num)).intervalIntegrable _ _), mul_comm]
    have hneg : ∫ x in P.points i.castSucc..P.points i.succ,
        -deriv (deriv u) x * (d i.castSucc + elementSlope P d i * (x - P.points i.castSucc)) =
        -∫ x in P.points i.castSucc..P.points i.succ,
          deriv (deriv u) x * (d i.castSucc + elementSlope P d i * (x - P.points i.castSucc)) := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun x _ => ?_
      ring
    have hval : d i.castSucc + elementSlope P d i * (P.points i.succ - P.points i.castSucc) =
        d i.succ := by
      rw [elementSlope, show P.points i.succ - P.points i.castSucc = width P i from rfl,
        div_mul_cancel₀ _ (width_pos P i).ne']
      ring
    have hibp' : ∫ x in P.points i.castSucc..P.points i.succ,
        deriv (deriv u) x * (d i.castSucc + elementSlope P d i * (x - P.points i.castSucc)) =
        deriv u (P.points i.succ) * d i.succ - deriv u (P.points i.castSucc) * d i.castSucc -
          elementSlope P d i * (u (P.points i.succ) - u (P.points i.castSucc)) := by
      rw [hint, hval, sub_self, mul_zero, add_zero] at hibp
      linarith
    rw [hneg, hibp']
    ring
  have hint_el : ∀ i : Fin P.n, IntervalIntegrable (fun x => f x * p1 P d x) volume
      (P.points i.castSucc) (P.points i.succ) := by
    intro i
    refine ((hcont i).intervalIntegrable _ _).congr_uIoo fun x hx => heq i ?_
    exact Set.Ioo_subset_Icc_self hx
  rw [integral_eq_sum P _ hint_el, Finset.sum_congr rfl fun i _ => hel i, Finset.sum_sub_distrib,
    sum_succ_sub_castSucc P (fun j => deriv u (P.points j) * d j), hd0, hdl, mul_zero,
    mul_zero, sub_zero, sub_zero, energy_contDiff_p1 P hu.contDiff]

/-- The energy form of two P1 functions:
`a(p1 c, p1 d) = ∑ᵢ (cᵢ₊₁ - cᵢ)(dᵢ₊₁ - dᵢ) / hᵢ`. -/
theorem energy_p1_p1 (c d : Fin (P.n + 1) → ℝ) :
    energy (p1 P c) (p1 P d) =
      ∑ i, (c i.succ - c i.castSucc) * (d i.succ - d i.castSucc) / width P i := by
  have hint : ∀ i : Fin P.n, IntervalIntegrable (deriv (p1 P c)) volume
      (P.points i.castSucc) (P.points i.succ) := by
    intro i
    refine (continuous_const.intervalIntegrable (μ := volume) _ _).congr_uIoo
      (f := fun _ => elementSlope P c i) (g := deriv (p1 P c)) fun x hx => ?_
    rw [Set.uIoo_of_le (P.ordered (Fin.castSucc_lt_succ ..)).le] at hx
    exact (hasDerivAt_p1 P c i hx).deriv.symm
  rw [energy_p1 P (p1 P c) (fun _ => (continuous_p1 P c).continuousOn)
    (fun i x hx => (hasDerivAt_p1 P c i hx).differentiableAt) hint d]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [p1_points, p1_points, elementSlope]
  ring

/-- The quadratic form of the stiffness matrix:
`dᵀ K c = ∑ᵢ (cᵢ₊₁ - cᵢ)(dᵢ₊₁ - dᵢ) / hᵢ`. -/
theorem dotProduct_stiffness_mulVec (c d : Fin (P.n + 1) → ℝ) :
    d ⬝ᵥ (stiffness P).mulVec c =
      ∑ i, (c i.succ - c i.castSucc) * (d i.succ - d i.castSucc) / width P i := by
  have he : ∀ (i : Fin P.n) (v : Fin (P.n + 1) → ℝ),
      ∑ j, elementVector P i j * v j = v i.succ - v i.castSucc := by
    intro i v
    simp [elementVector, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]
  have h1 : d ⬝ᵥ (stiffness P).mulVec c =
      ∑ j, ∑ k, ∑ i, d j * (elementVector P i j * elementVector P i k / width P i * c k) := by
    simp [dotProduct, Matrix.mulVec, stiffness, Finset.mul_sum, Finset.sum_mul]
  rw [h1]
  simp_rw [← he]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul_sum, Finset.sum_div, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private theorem elementVector_apply (i : Fin P.n) (j : Fin (P.n + 1)) :
    elementVector P i j =
      (if (j : ℕ) = i + 1 then 1 else 0) - (if (j : ℕ) = i then 1 else 0) := by
  simp only [elementVector, Pi.sub_apply, Pi.single_apply, Fin.ext_iff, Fin.val_succ,
    Fin.val_castSucc]

/-- The stiffness matrix is the Gram matrix of the hat functions:
`a(φⱼ, φₖ) = Kⱼₖ`. -/
theorem energy_hat_hat (j k : Fin (P.n + 1)) :
    energy (hat P j) (hat P k) = stiffness P j k := by
  rw [hat, hat, energy_p1_p1, stiffness]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [elementVector, Pi.sub_apply]
  rw [Pi.single_comm j, Pi.single_comm j, Pi.single_comm k, Pi.single_comm k]

/-- The off-diagonal entry of an element: `K_{i, i+1} = -1 / hᵢ`. -/
theorem stiffness_castSucc_succ (i : Fin P.n) :
    stiffness P i.castSucc i.succ = -(width P i)⁻¹ := by
  rw [stiffness, Finset.sum_eq_single i]
  · simp only [elementVector_apply, Fin.val_castSucc, Fin.val_succ]
    simp [neg_div]
  · intro k _ hki
    have hk : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
    simp only [elementVector_apply, Fin.val_castSucc, Fin.val_succ]
    split_ifs <;> first | omega | simp
  · simp

/-- The diagonal entry at an interior node `xⱼ` shared by consecutive
elements `i` and `j`: `K = 1 / hᵢ + 1 / hⱼ`. -/
theorem stiffness_succ_succ {i j : Fin P.n} (hij : i.succ = j.castSucc) :
    stiffness P i.succ i.succ = (width P i)⁻¹ + (width P j)⁻¹ := by
  have hj : (j : ℕ) = i + 1 := by
    have := congrArg Fin.val hij
    simpa using this.symm
  have hne : i ≠ j := fun h => by subst h; omega
  rw [stiffness, Fintype.sum_eq_add i j hne]
  · simp only [elementVector_apply, Fin.val_succ, hj]
    simp
  · rintro k ⟨hki, hkj⟩
    have hk1 : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
    have hk2 : (k : ℕ) ≠ j := fun h => hkj (Fin.ext h)
    simp only [elementVector_apply, Fin.val_succ]
    split_ifs <;> first | omega | simp

/-- Entries between nodes two or more apart vanish (tridiagonality). -/
theorem stiffness_eq_zero {j k : Fin (P.n + 1)} (hjk : (j : ℕ) + 2 ≤ k) :
    stiffness P j k = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  simp only [elementVector_apply]
  split_ifs <;> first | omega | simp

/-- Inside element `i`, `deriv (u - p1 d) = u' - slopeᵢ`. -/
private theorem deriv_sub_p1 {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (d : Fin (P.n + 1) → ℝ) (i : Fin P.n) {x : ℝ}
    (hx : x ∈ Set.Ioo (P.points i.castSucc) (P.points i.succ)) :
    HasDerivAt (u - p1 P d) (deriv u x - elementSlope P d i) x :=
  ((hu.differentiable (by norm_num)).differentiableAt.hasDerivAt).sub (hasDerivAt_p1 P d i hx)

/-- `u - p1 d` satisfies the hypotheses of `energy_p1` for a `C²` function `u`. -/
private theorem energy_sub_p1_p1 {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (c d : Fin (P.n + 1) → ℝ) :
    energy (u - p1 P c) (p1 P d) = ∑ i, elementSlope P d i *
      ((u - p1 P c) (P.points i.succ) - (u - p1 P c) (P.points i.castSucc)) := by
  refine energy_p1 P _ (fun _ => (hu.continuous.sub (continuous_p1 P c)).continuousOn)
    (fun i x hx => (deriv_sub_p1 P hu c i hx).differentiableAt) (fun i => ?_) d
  have hcont : Continuous fun x => deriv u x - elementSlope P c i :=
    (hu.continuous_deriv (by norm_num)).sub continuous_const
  refine (hcont.intervalIntegrable (μ := volume) _ _).congr_uIoo
    (g := deriv (u - p1 P c)) ?_
  intro x hx
  rw [Set.uIoo_of_le (P.ordered (Fin.castSucc_lt_succ ..)).le] at hx
  exact (deriv_sub_p1 P hu c i hx).deriv.symm

/-- Row `j` of `K c` is `∑ᵢ slopeᵢ(δⱼ) (cᵢ₊₁ - cᵢ)`. -/
private theorem stiffness_mulVec_apply (c : Fin (P.n + 1) → ℝ) (j : Fin (P.n + 1)) :
    (stiffness P).mulVec c j =
      ∑ i, elementSlope P (Pi.single j 1) i * (c i.succ - c i.castSucc) := by
  have h := dotProduct_stiffness_mulVec P c (Pi.single j 1)
  rw [single_dotProduct, one_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [elementSlope]
  ring

/-- For a classical solution, `Fⱼ = a(u, φⱼ) = ∑ᵢ slopeᵢ(δⱼ) (u(xᵢ₊₁) - u(xᵢ))` at an
interior node. -/
private theorem load_eq {f u : ℝ → ℝ} (hu : IsClassicalSolution f u) {j : Fin (P.n + 1)}
    (h0 : j ≠ 0) (hl : j ≠ Fin.last P.n) :
    load P f j =
      ∑ i, elementSlope P (Pi.single j 1) i * (u (P.points i.succ) - u (P.points i.castSucc)) := by
  rw [load, ← energy_eq_integral_mul_of_mem_p1Space P hu (hat_mem_p1Space P h0 hl), hat,
    energy_contDiff_p1 P hu.contDiff]

/-- The stiffness matrix has trivial kernel on nodal vectors with zero boundary
values: `K e = 0` at interior nodes forces `e = 0`. -/
private theorem eq_zero_of_stiffness_mulVec {e : Fin (P.n + 1) → ℝ} (h0 : e 0 = 0)
    (hl : e (Fin.last P.n) = 0)
    (hK : ∀ j, j ≠ 0 → j ≠ Fin.last P.n → (stiffness P).mulVec e j = 0) : e = 0 := by
  have hsum : e ⬝ᵥ (stiffness P).mulVec e = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj0 : j = 0
    · simp [hj0, h0]
    by_cases hjl : j = Fin.last P.n
    · simp [hjl, hl]
    rw [hK j hj0 hjl, mul_zero]
  rw [dotProduct_stiffness_mulVec] at hsum
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    div_nonneg (mul_self_nonneg (e i.succ - e i.castSucc)) (width_pos P i).le).mp hsum
  have hstep : ∀ i : Fin P.n, e i.succ = e i.castSucc := by
    intro i
    have h := hterm i (Finset.mem_univ _)
    rw [div_eq_zero_iff, mul_self_eq_zero] at h
    rcases h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (width_pos P i).ne'
  funext j
  induction j using Fin.induction with
  | zero => exact h0
  | succ i ih => rw [hstep i]; exact ih

/-- The nodal values of the exact solution solve the Galerkin system. -/
theorem isGalerkinSolution_nodal {f u : ℝ → ℝ} (hu : IsClassicalSolution f u) :
    IsGalerkinSolution P f fun j => u (P.points j) := by
  refine ⟨by simp [P.first, hu.zero_left], by simp [P.last, hu.zero_right], fun j h0 hl => ?_⟩
  rw [stiffness_mulVec_apply, load_eq P hu h0 hl]

/-- The Galerkin system has at most one solution (`K` is positive definite on
nodal vectors with zero boundary values). -/
theorem isGalerkinSolution_unique {f : ℝ → ℝ} {c c' : Fin (P.n + 1) → ℝ}
    (hc : IsGalerkinSolution P f c) (hc' : IsGalerkinSolution P f c') : c = c' := by
  have h := eq_zero_of_stiffness_mulVec P (e := c - c') (by simp [hc.1, hc'.1])
    (by simp [hc.2.1, hc'.2.1]) fun j h0 hl => by
      rw [Matrix.mulVec_sub, Pi.sub_apply, hc.2.2 j h0 hl, hc'.2.2 j h0 hl, sub_self]
  exact sub_eq_zero.mp h

/-- In one dimension the P1 Galerkin solution is the nodal interpolant of the
exact solution: `u_h = I_h u`. -/
theorem p1_eq_interp_of_isGalerkinSolution {f u : ℝ → ℝ} (hu : IsClassicalSolution f u)
    {c : Fin (P.n + 1) → ℝ} (hc : IsGalerkinSolution P f c) :
    p1 P c = interp P u := by
  rw [isGalerkinSolution_unique P hc (isGalerkinSolution_nodal P hu)]
  rfl

/-- **Galerkin orthogonality**: `a(u - u_h, v_h) = 0` for every `v_h ∈ V_h`. -/
theorem galerkin_orthogonality {f u : ℝ → ℝ} (hu : IsClassicalSolution f u)
    {c : Fin (P.n + 1) → ℝ} (hc : IsGalerkinSolution P f c) {v : ℝ → ℝ}
    (hv : v ∈ p1Space P) :
    energy (u - p1 P c) v = 0 := by
  obtain ⟨d, -, -, rfl⟩ := (mem_p1Space P).mp hv
  rw [energy_sub_p1_p1 P hu.contDiff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [isGalerkinSolution_unique P hc (isGalerkinSolution_nodal P hu)]
  simp [p1_points]

/-- Element-wise form of the energy of `u - p1 d` for a `C²` function `u`:
`a(u - p1 d, u - p1 d) = ∑ᵢ ∫_{xᵢ}^{xᵢ₊₁} (u' - slopeᵢ(d))²`. -/
theorem energy_sub_p1_self {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (d : Fin (P.n + 1) → ℝ) :
    energy (u - p1 P d) (u - p1 P d) = ∑ i, ∫ x in P.points i.castSucc..P.points i.succ,
      (deriv u x - elementSlope P d i) ^ 2 := by
  have heq : ∀ i : Fin P.n, Set.EqOn (fun x => (deriv u x - elementSlope P d i) ^ 2)
      (fun x => deriv (u - p1 P d) x * deriv (u - p1 P d) x)
      (Set.uIoo (P.points i.castSucc) (P.points i.succ)) := by
    intro i x hx
    rw [Set.uIoo_of_le (P.ordered (Fin.castSucc_lt_succ ..)).le] at hx
    dsimp only
    rw [(deriv_sub_p1 P hu d i hx).deriv]
    ring
  have hc : ∀ i : Fin P.n, Continuous fun x => (deriv u x - elementSlope P d i) ^ 2 :=
    fun i => ((hu.continuous_deriv (by norm_num)).sub continuous_const).pow 2
  rw [energy, integral_eq_sum P _ fun i => ((hc i).intervalIntegrable _ _).congr_uIoo (heq i)]
  exact Finset.sum_congr rfl fun i _ => (intervalIntegral.integral_congr_uIoo (heq i)).symm

/-- The interpolation error on element `i`, extended to `ℝ` as a `C²` function:
`u(x) - (u(xᵢ) + slopeᵢ (x - xᵢ))`. -/
private noncomputable def elemErr (u : ℝ → ℝ) (i : Fin P.n) (x : ℝ) : ℝ :=
  u x - (u (P.points i.castSucc) + elementSlope P (fun j => u (P.points j)) i *
    (x - P.points i.castSucc))

private theorem contDiff_elemErr {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin P.n) :
    ContDiff ℝ 2 (elemErr P u i) :=
  hu.sub (contDiff_const.add (contDiff_const.mul (contDiff_id.sub contDiff_const)))

private theorem elemErr_left (u : ℝ → ℝ) (i : Fin P.n) :
    elemErr P u i (P.points i.castSucc) = 0 := by
  simp [elemErr]

private theorem elemErr_right (u : ℝ → ℝ) (i : Fin P.n) :
    elemErr P u i (P.points i.succ) = 0 := by
  rw [elemErr, elementSlope, show P.points i.succ - P.points i.castSucc = width P i from rfl,
    div_mul_cancel₀ _ (width_pos P i).ne']
  ring

private theorem elemErr_eq_of_mem_Icc (u : ℝ → ℝ) (i : Fin P.n) {x : ℝ}
    (hx : x ∈ Set.Icc (P.points i.castSucc) (P.points i.succ)) :
    elemErr P u i x = u x - interp P u x := by
  rw [interp, p1_eq_of_mem_Icc P _ i hx]
  rfl

private theorem deriv_elemErr {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin P.n) :
    deriv (elemErr P u i) = fun x => deriv u x - elementSlope P (fun j => u (P.points j)) i := by
  funext x
  have hlin : HasDerivAt (fun x => u (P.points i.castSucc) +
      elementSlope P (fun j => u (P.points j)) i * (x - P.points i.castSucc))
      (elementSlope P (fun j => u (P.points j)) i) x := by
    have h1 : HasDerivAt (fun y : ℝ => y - P.points i.castSucc) 1 x :=
      (hasDerivAt_id x).sub_const _
    simpa using (h1.const_mul (elementSlope P (fun j => u (P.points j)) i)).const_add
      (u (P.points i.castSucc))
  exact ((hu.differentiable (by norm_num) x).hasDerivAt.sub hlin).deriv

private theorem deriv_deriv_elemErr {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin P.n) :
    deriv (deriv (elemErr P u i)) = deriv (deriv u) := by
  rw [deriv_elemErr P hu i]
  funext x
  exact deriv_sub_const _

/-- `((hᵢ / π)²)` is at most `(h / π)²`. -/
private theorem sq_width_div_pi_le (i : Fin P.n) :
    (width P i / Real.pi) ^ 2 ≤ (P.mesh / Real.pi) ^ 2 :=
  pow_le_pow_left₀ (div_nonneg (width_pos P i).le Real.pi_pos.le)
    (div_le_div_of_nonneg_right (width_le_mesh P i) Real.pi_pos.le) 2

/-- The element integral of `(u'')²` over element `i` is nonnegative. -/
private theorem integral_sq_nonneg_elem (g : ℝ → ℝ) (i : Fin P.n) :
    0 ≤ ∫ x in P.points i.castSucc..P.points i.succ, g x ^ 2 :=
  intervalIntegral.integral_nonneg (P.ordered (Fin.castSucc_lt_succ ..)).le
    fun _ _ => sq_nonneg _

/-- **Best approximation** (Céa's lemma for the symmetric energy form, with
constant `1`): `‖u - u_h‖_a ≤ ‖u - v_h‖_a` for every `v_h ∈ V_h`. -/
theorem energy_sub_galerkin_le {f u : ℝ → ℝ} (hu : IsClassicalSolution f u)
    {c : Fin (P.n + 1) → ℝ} (hc : IsGalerkinSolution P f c) {v : ℝ → ℝ}
    (hv : v ∈ p1Space P) :
    energy (u - p1 P c) (u - p1 P c) ≤ energy (u - v) (u - v) := by
  obtain ⟨d, -, -, rfl⟩ := (mem_p1Space P).mp hv
  rw [isGalerkinSolution_unique P hc (isGalerkinSolution_nodal P hu),
    energy_sub_p1_self P hu.contDiff, energy_sub_p1_self P hu.contDiff]
  refine Finset.sum_le_sum fun i _ => ?_
  set sc := elementSlope P (fun j => u (P.points j)) i
  set sd := elementSlope P d i
  have hcu : Continuous (deriv u) := hu.contDiff.continuous_deriv (by norm_num)
  -- the difference of the two element integrals is `hᵢ (sc - sd)² ≥ 0`
  have hsq : ∀ t : ℝ, IntervalIntegrable (fun x => (deriv u x - t) ^ 2) volume
      (P.points i.castSucc) (P.points i.succ) := fun t =>
    (show Continuous fun x => (deriv u x - t) ^ 2 from
      (hcu.sub continuous_const).pow 2).intervalIntegrable _ _
  have hdiff : (∫ x in P.points i.castSucc..P.points i.succ, (deriv u x - sd) ^ 2) -
      ∫ x in P.points i.castSucc..P.points i.succ, (deriv u x - sc) ^ 2 =
      width P i * (sc - sd) ^ 2 := by
    rw [← intervalIntegral.integral_sub (hsq sd) (hsq sc)]
    have e : ∀ x, (deriv u x - sd) ^ 2 - (deriv u x - sc) ^ 2 =
        2 * (sc - sd) * deriv u x + (sd ^ 2 - sc ^ 2) := fun x => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add
      ((show Continuous fun x => 2 * (sc - sd) * deriv u x from
        continuous_const.mul hcu).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_deriv_eq_sub
        (fun x _ => (hu.contDiff.differentiable (by norm_num)) x)
        (hcu.intervalIntegrable _ _), intervalIntegral.integral_const, smul_eq_mul]
    have hsc : u (P.points i.succ) - u (P.points i.castSucc) = sc * width P i := by
      simp only [sc, elementSlope]
      rw [div_mul_cancel₀ _ (width_pos P i).ne']
    rw [hsc, show P.points i.succ - P.points i.castSucc = width P i from rfl]
    ring
  have hnn : 0 ≤ width P i * (sc - sd) ^ 2 := mul_nonneg (width_pos P i).le (sq_nonneg _)
  linarith

/-! ### Error estimates -/

/-- Wirtinger's inequality on `[a, b]`: a `C¹` function vanishing at `a` and
`b` satisfies `∫ₐᵇ g² ≤ ((b - a) / π)² ∫ₐᵇ (g')²`. -/
theorem integral_sq_le_of_eq_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hg : ContDiff ℝ 1 g)
    (ha : g a = 0) (hb : g b = 0) :
    ∫ x in a..b, g x ^ 2 ≤ ((b - a) / Real.pi) ^ 2 * ∫ x in a..b, deriv g x ^ 2 := by
  set s := (b - a) / Real.pi with hs
  have hs0 : 0 < s := div_pos (sub_pos.mpr hab) Real.pi_pos
  have hend : a + s * Real.pi = b := by
    rw [hs, div_mul_cancel₀ _ Real.pi_pos.ne']
    ring
  have hdg : ∀ x, HasDerivAt g (deriv g x) x :=
    fun x => ((hg.differentiable one_ne_zero) x).hasDerivAt
  have hlin : Continuous fun t : ℝ => a + s * t := by fun_prop
  have hF : ∀ t, HasDerivAt (fun t => g (a + s * t)) (s * deriv g (a + s * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => a + s * t) s t := by
      simpa using ((hasDerivAt_id t).const_mul s).const_add a
    have h2 := (hdg (a + s * t)).comp t h1
    rw [mul_comm] at h2
    exact h2
  have hw := MetaMathlibExt.wirtinger_inequality (fun t => g (a + s * t))
    (fun t => s * deriv g (a + s * t)) (fun t _ => (hF t).hasDerivWithinAt)
    ((continuous_const.mul ((hg.continuous_deriv le_rfl).comp hlin)).continuousOn)
    (by simp [ha]) (by simp [hend, hb])
  have h1 : ∫ t in (0 : ℝ)..Real.pi, g (a + s * t) ^ 2 = s⁻¹ * ∫ x in a..b, g x ^ 2 := by
    have := intervalIntegral.integral_comp_add_mul (fun x => g x ^ 2) (a := 0) (b := Real.pi)
      hs0.ne' a
    simpa [hend] using this
  have h2 : ∫ t in (0 : ℝ)..Real.pi, (s * deriv g (a + s * t)) ^ 2 =
      s ^ 2 * (s⁻¹ * ∫ x in a..b, deriv g x ^ 2) := by
    have := intervalIntegral.integral_comp_add_mul (fun x => deriv g x ^ 2) (a := 0)
      (b := Real.pi) hs0.ne' a
    simp only [mul_zero, add_zero, hend, smul_eq_mul] at this
    rw [← this, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [h1, h2] at hw
  have hmul := mul_le_mul_of_nonneg_left hw hs0.le
  rw [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul] at hmul
  calc ∫ x in a..b, g x ^ 2 ≤ s * (s ^ 2 * (s⁻¹ * ∫ x in a..b, deriv g x ^ 2)) := hmul
    _ = s ^ 2 * ∫ x in a..b, deriv g x ^ 2 := by
        field_simp

/-- The element estimate: a `C²` function vanishing at `a` and `b` satisfies
`∫ₐᵇ (g')² ≤ ((b - a) / π)² ∫ₐᵇ (g'')²`. -/
theorem integral_deriv_sq_le_of_eq_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ContDiff ℝ 2 g) (ha : g a = 0) (hb : g b = 0) :
    ∫ x in a..b, deriv g x ^ 2 ≤
      ((b - a) / Real.pi) ^ 2 * ∫ x in a..b, deriv (deriv g) x ^ 2 := by
  have hg1 := contDiff_deriv_of_contDiff_two hg
  have hc0 : Continuous g := hg.continuous
  have hc1 : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  have hc2 : Continuous (deriv (deriv g)) := hg1.continuous_deriv le_rfl
  have hcpos : 0 < (b - a) / Real.pi := div_pos (sub_pos.mpr hab) Real.pi_pos
  -- integration by parts: `∫ g g'' = -∫ (g')²`
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := a) (b := b)
    (u := g) (u' := deriv g) (v := deriv g) (v' := deriv (deriv g))
    (fun x _ => ((hg.differentiable (by norm_num)) x).hasDerivAt)
    (fun x _ => ((hg1.differentiable (by norm_num)) x).hasDerivAt)
    (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _)
  rw [ha, hb, zero_mul, zero_mul, sub_zero, zero_sub] at hibp
  have hgg : ∫ x in a..b, g x * deriv (deriv g) x = -∫ x in a..b, deriv g x ^ 2 := by
    rw [hibp]
    congr 1
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  generalize hc : (b - a) / Real.pi = c at hcpos ⊢
  -- `0 ≤ ∫ (g / c + c g'')² = G / c² + 2 ∫ g g'' + c² B`
  have hsq : 0 ≤ ∫ x in a..b, ((c ^ 2)⁻¹ * g x ^ 2 + 2 * (g x * deriv (deriv g) x) +
      c ^ 2 * deriv (deriv g) x ^ 2) := by
    refine intervalIntegral.integral_nonneg hab.le fun x _ => ?_
    have e : (c ^ 2)⁻¹ * g x ^ 2 + 2 * (g x * deriv (deriv g) x) +
        c ^ 2 * deriv (deriv g) x ^ 2 = (g x / c + c * deriv (deriv g) x) ^ 2 := by
      field_simp
      ring
    rw [e]
    exact sq_nonneg _
  have i1 : IntervalIntegrable (fun x => (c ^ 2)⁻¹ * g x ^ 2) volume a b :=
    (continuous_const.mul (hc0.pow 2)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => 2 * (g x * deriv (deriv g) x)) volume a b :=
    (continuous_const.mul (hc0.mul hc2)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun x => c ^ 2 * deriv (deriv g) x ^ 2) volume a b :=
    (continuous_const.mul (hc2.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, hgg] at hsq
  have hW := integral_sq_le_of_eq_zero hab (hg.of_le (by norm_num)) ha hb
  rw [hc] at hW
  have hc2pos : 0 < c ^ 2 := pow_pos hcpos 2
  have hGA : (c ^ 2)⁻¹ * ∫ x in a..b, g x ^ 2 ≤ ∫ x in a..b, deriv g x ^ 2 := by
    rw [inv_mul_le_iff₀ hc2pos]
    exact hW
  linarith

/-- **Interpolation estimate**: `‖u - I_h u‖_a² ≤ (h / π)² ‖u''‖²_{L²(0,1)}`,
with `h` the mesh size. -/
theorem energy_sub_interp_le {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) :
    energy (u - interp P u) (u - interp P u) ≤
      (P.mesh / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..1, deriv (deriv u) x ^ 2 := by
  have hc2 : Continuous fun x => deriv (deriv u) x ^ 2 :=
    ((contDiff_deriv_of_contDiff_two hu).continuous_deriv le_rfl).pow 2
  rw [interp, energy_sub_p1_self P hu,
    integral_eq_sum P _ fun i => hc2.intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := integral_deriv_sq_le_of_eq_zero (P.ordered (Fin.castSucc_lt_succ ..))
    (contDiff_elemErr P hu i) (elemErr_left P u i) (elemErr_right P u i)
  rw [deriv_deriv_elemErr P hu i, deriv_elemErr P hu i] at h
  exact h.trans (mul_le_mul_of_nonneg_right (sq_width_div_pi_le P i)
    (integral_sq_nonneg_elem P _ i))

/-- For a classical solution, `∫₀¹ (u'')² = ∫₀¹ f²`. -/
private theorem integral_deriv_deriv_sq {f u : ℝ → ℝ} (hu : IsClassicalSolution f u) :
    ∫ x in (0 : ℝ)..1, deriv (deriv u) x ^ 2 = ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le zero_le_one] at hx
  rw [← hu.eq_Icc x hx, neg_sq]

/-- **Energy error estimate**: `‖u - u_h‖_a² ≤ (h / π)² ‖f‖²_{L²(0,1)}`, so the
energy error is `O(h)`. -/
theorem energy_sub_galerkin_le_mesh {f u : ℝ → ℝ} (hu : IsClassicalSolution f u)
    {c : Fin (P.n + 1) → ℝ} (hc : IsGalerkinSolution P f c) :
    energy (u - p1 P c) (u - p1 P c) ≤
      (P.mesh / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  rw [p1_eq_interp_of_isGalerkinSolution P hu hc, ← integral_deriv_deriv_sq hu]
  exact energy_sub_interp_le P hu.contDiff

/-- The energy error estimate in norm form:
`‖u - u_h‖_a ≤ (h / π) ‖f‖_{L²(0,1)}`. -/
theorem sqrt_energy_sub_galerkin_le_mesh {f u : ℝ → ℝ} (hu : IsClassicalSolution f u)
    {c : Fin (P.n + 1) → ℝ} (hc : IsGalerkinSolution P f c) :
    √(energy (u - p1 P c) (u - p1 P c)) ≤
      P.mesh / Real.pi * √(∫ x in (0 : ℝ)..1, f x ^ 2) := by
  have hc0 : 0 ≤ P.mesh / Real.pi :=
    div_nonneg (P.mesh_pos_of_lt zero_lt_one).le Real.pi_pos.le
  calc √(energy (u - p1 P c) (u - p1 P c))
      ≤ √((P.mesh / Real.pi) ^ 2 * ∫ x in (0 : ℝ)..1, f x ^ 2) :=
        Real.sqrt_le_sqrt (energy_sub_galerkin_le_mesh P hu hc)
    _ = P.mesh / Real.pi * √(∫ x in (0 : ℝ)..1, f x ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc0]

/-- **`L²` error estimate**: `‖u - u_h‖²_{L²(0,1)} ≤ (h / π)⁴ ‖f‖²_{L²(0,1)}`,
so the `L²` error is `O(h²)`. The proof uses nodal exactness and Wirtinger's
inequality on each element, not the Aubin–Nitsche duality argument. -/
theorem integral_sq_sub_galerkin_le_mesh {f u : ℝ → ℝ} (hu : IsClassicalSolution f u)
    {c : Fin (P.n + 1) → ℝ} (hc : IsGalerkinSolution P f c) :
    ∫ x in (0 : ℝ)..1, (u x - p1 P c x) ^ 2 ≤
      (P.mesh / Real.pi) ^ 4 * ∫ x in (0 : ℝ)..1, f x ^ 2 := by
  have hu2 := hu.contDiff
  have hcu2 : Continuous (deriv (deriv u)) :=
    (contDiff_deriv_of_contDiff_two hu2).continuous_deriv le_rfl
  have hce : Continuous fun x => (u x - interp P u x) ^ 2 :=
    (hu2.continuous.sub (continuous_p1 P _)).pow 2
  have hc2 : Continuous fun x => deriv (deriv u) x ^ 2 := hcu2.pow 2
  rw [p1_eq_interp_of_isGalerkinSolution P hu hc, ← integral_deriv_deriv_sq hu,
    integral_eq_sum P _ fun i => hce.intervalIntegrable _ _,
    integral_eq_sum P _ fun i => hc2.intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlt := P.ordered (Fin.castSucc_lt_succ (i := i))
  have heq : ∫ x in P.points i.castSucc..P.points i.succ, (u x - interp P u x) ^ 2 =
      ∫ x in P.points i.castSucc..P.points i.succ, elemErr P u i x ^ 2 := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hlt.le] at hx
    rw [elemErr_eq_of_mem_Icc P u i hx]
  have h1 := integral_sq_le_of_eq_zero hlt ((contDiff_elemErr P hu2 i).of_le (by norm_num))
    (elemErr_left P u i) (elemErr_right P u i)
  have h2 := integral_deriv_sq_le_of_eq_zero hlt (contDiff_elemErr P hu2 i)
    (elemErr_left P u i) (elemErr_right P u i)
  rw [deriv_deriv_elemErr P hu2 i] at h2
  have hw := sq_width_div_pi_le P i
  have hw0 : 0 ≤ (width P i / Real.pi) ^ 2 := sq_nonneg _
  have hI := integral_sq_nonneg_elem P (deriv (deriv u)) i
  change ∫ x in P.points i.castSucc..P.points i.succ, elemErr P u i x ^ 2 ≤
      (width P i / Real.pi) ^ 2 * _ at h1
  change _ ≤ (width P i / Real.pi) ^ 2 * _ at h2
  rw [heq]
  calc ∫ x in P.points i.castSucc..P.points i.succ, elemErr P u i x ^ 2
      ≤ (width P i / Real.pi) ^ 2 * ((width P i / Real.pi) ^ 2 *
          ∫ x in P.points i.castSucc..P.points i.succ, deriv (deriv u) x ^ 2) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hw0)
    _ ≤ (P.mesh / Real.pi) ^ 2 * ((P.mesh / Real.pi) ^ 2 *
          ∫ x in P.points i.castSucc..P.points i.succ, deriv (deriv u) x ^ 2) := by
        gcongr
    _ = (P.mesh / Real.pi) ^ 4 *
          ∫ x in P.points i.castSucc..P.points i.succ, deriv (deriv u) x ^ 2 := by
        ring

end MathlibExt.Analysis.ODE.FiniteElement1D
