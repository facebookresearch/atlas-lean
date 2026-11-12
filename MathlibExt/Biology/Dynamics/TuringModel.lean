/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.PDE.SemilinearFlow.Interface
public import MathlibExt.Biology.Dynamics.TuringPatterns
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The two-species Turing reaction–diffusion system as a semilinear flow

This file instantiates the local-flow interface of
`MathlibExt.Analysis.PDE.SemilinearFlow.Interface` for the two-species reaction–diffusion system
of `MathlibExt.Biology.Dynamics.TuringPatterns`,

  `u_t = d_u Δ u + f(u, v)`,   `v_t = d_v Δ v + g(u, v)`.

## Frozen setting

The statements below are proved for an **arbitrary** compact space `K` and an **arbitrary** C₀
semigroup `H` on `C(K, ℝ)`; no statement uses the geometry of the domain or the boundary
condition. The closure `Ω̄` and the Neumann heat semigroup `e^{τ Δ_N}` are the intended
instances, and only for them is the result the Neumann problem below. The diffusion
coefficients are only required to satisfy `d_u, d_v ≥ 0`, which relaxes the `dᵢ > 0` of the
PDE-01 frozen setting (the degenerate case `dᵢ = 0` is a species that does not diffuse).

* **domain**: `Ω ⊆ ℝⁿ` a bounded open set with smooth boundary; the variable `K` below is the
  compact closure `Ω̄` (in the one-dimensional setting of `TuringPatterns`, `Ω̄ = [0, L]`).
* **boundary condition**: homogeneous Neumann (zero flux) for both species.
* **function space**: `X = C(Ω̄; ℝ²)`, written `C(K, Fin 2 → ℝ)`, with the sup norm (on `ℝ²` the
  sup norm of `Fin 2 → ℝ`).
* **diffusion**: `D = diag(d_u, d_v)` with `d_u, d_v ≥ 0`. If `H τ = e^{τ Δ_N}` is the heat
  semigroup of the Neumann Laplacian on `C(Ω̄)`, the linear part generates
  `S t = e^{t D Δ_N} = diag(H (d_u t), H (d_v t))`; this is `diffusionSemigroup H d_u d_v`.
* **reaction**: the Nemytskii operator `w ↦ (f, g) ∘ w` of `C¹` kinetics
  `(f, g) : ℝ² → ℝ²`, such as `schnakenberg a b`.

Neither Mathlib nor Atlas constructs the Neumann heat semigroup on `C(Ω̄)` (Stewart 1974/1980;
Lunardi, *Analytic Semigroups*, Ch. 3). It therefore enters as the hypothesis
`hH : IsC0Semigroup H` on the scalar semigroup; everything else is proved.
`diffusionSemigroup_apply_speciesEmb` records how `S` acts on an eigenfunction of `H`, which for
`Ω̄ = [0, L]` are the Neumann modes `cos (k_n x)`, `k_n = neumannWavenumber L n`, with
`H τ φ = e^{-k_n² τ} φ`.

## Main results

* `isC0Semigroup_diffusionSemigroup`: `diag(H (d_u t), H (d_v t))` is a C₀ semigroup on
  `C(K, ℝ²)` whenever `H` is one on `C(K, ℝ)`.
* `exists_lipschitzOnWith_closedBall_of_contDiff`: `C¹` kinetics on a finite-dimensional space
  are Lipschitz on closed balls, the hypothesis `hF` of the interface (through
  `lipschitzOnWith_nemytskii`).
* `localFlow`: local well-posedness of the Turing system in `C(K, ℝ²)`: mild solutions exist on a
  time interval uniform over a ball of initial data and depend Lipschitz-continuously on them.
  `isMildSolution_unique` and `isMildSolution_restart` give uniqueness and the semiflow identity.
* `diffusionSemigroup_apply_const`, `isMildSolution_const`: if `H` fixes constants (as the
  Neumann heat semigroup does, and the Dirichlet one does not), every homogeneous steady state of
  the kinetics is a mild solution.
* `contDiff_schnakenberg`, `schnakenberg_localFlow`: the Schnakenberg kinetics qualify.
* `not_lipschitzOnWith_giererMeinhardt` (boundary case): the Gierer–Meinhardt kinetics
  `u² / v` are not Lipschitz on the unit ball, so they do not satisfy the hypotheses on the whole
  of `C(K, ℝ²)`; a treatment needs an invariant region `v ≥ v_min > 0` or a cutoff, which is not
  done here.

## Not formalized here

The construction of the Neumann heat semigroup and its analyticity, positivity of solutions,
invariant regions, global existence, and the nonlinear consequences of the linear Turing
instability (the dispersion relation and unstable Neumann modes are in `TuringPatterns`).
-/

open Set
open scoped NNReal

@[expose] public section

namespace MathlibExt.Biology.Dynamics.TuringModel

open MathlibExt.Analysis.PDE.SemilinearFlow MathlibExt.Biology.Dynamics.TuringPatterns

variable (K : Type*) [TopologicalSpace K]

/-- The concentration field of species `i`: the coordinate map `C(K, ℝ²) → C(K, ℝ)`,
`w ↦ (x ↦ w x i)`. -/
def speciesProj (i : Fin 2) : C(K, Fin 2 → ℝ) →L[ℝ] C(K, ℝ) :=
  (ContinuousLinearMap.proj i).compLeftContinuous ℝ K

/-- A concentration field of species `i` alone: the embedding `C(K, ℝ) → C(K, ℝ²)` that puts
`φ` in coordinate `i` and `0` in the other one. -/
def speciesEmb (i : Fin 2) : C(K, ℝ) →L[ℝ] C(K, Fin 2 → ℝ) :=
  (ContinuousLinearMap.single ℝ (fun _ : Fin 2 => ℝ) i).compLeftContinuous ℝ K

variable {K}

/-- Species `i` of `w` at `x` is the coordinate `w x i`. -/
@[simp]
theorem speciesProj_apply (i : Fin 2) (w : C(K, Fin 2 → ℝ)) (x : K) :
    speciesProj K i w x = w x i := rfl

/-- The single-species field `speciesEmb K i φ` at `x` is `Pi.single i (φ x)`. -/
@[simp]
theorem speciesEmb_apply (i : Fin 2) (φ : C(K, ℝ)) (x : K) :
    speciesEmb K i φ x = Pi.single i (φ x) := rfl

/-- Species `k` of the single-species field `speciesEmb K i φ` is `φ` if `k = i` and `0`
otherwise. -/
theorem speciesProj_speciesEmb (k i : Fin 2) (φ : C(K, ℝ)) :
    speciesProj K k (speciesEmb K i φ) = if k = i then φ else 0 := by
  ext x
  by_cases h : k = i <;> simp [h]

variable [CompactSpace K]

/-- The **diffusion semigroup** `S t = diag(H (d_u t), H (d_v t))` of the Turing system on
`C(K, ℝ²)`, built from a scalar semigroup `H` on `C(K, ℝ)` (in the frozen setting the Neumann
heat semigroup `e^{τ Δ_N}`) and the diffusion coefficients `d_u, d_v ≥ 0`. -/
noncomputable def diffusionSemigroup (H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)) (du dv : ℝ≥0)
    (t : ℝ≥0) : C(K, Fin 2 → ℝ) →L[ℝ] C(K, Fin 2 → ℝ) :=
  ∑ i, speciesEmb K i ∘L H (![du, dv] i * t) ∘L speciesProj K i

/-- Pointwise formula: species `k` of `S t w` is `H (d_k t)` applied to species `k` of `w`. -/
theorem diffusionSemigroup_apply_apply (H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)) (du dv t : ℝ≥0)
    (w : C(K, Fin 2 → ℝ)) (x : K) (k : Fin 2) :
    diffusionSemigroup H du dv t w x k = H (![du, dv] k * t) (speciesProj K k w) x := by
  fin_cases k <;> simp [diffusionSemigroup, Fin.sum_univ_two]

/-- Species `k` of `S t w` is `H (d_k t)` applied to species `k` of `w`. -/
theorem speciesProj_diffusionSemigroup (H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)) (du dv t : ℝ≥0)
    (w : C(K, Fin 2 → ℝ)) (k : Fin 2) :
    speciesProj K k (diffusionSemigroup H du dv t w) =
      H (![du, dv] k * t) (speciesProj K k w) := by
  ext x
  exact diffusionSemigroup_apply_apply H du dv t w x k

private theorem coeff_le_add (du dv : ℝ≥0) (i : Fin 2) : ![du, dv] i ≤ du + dv := by
  fin_cases i
  · exact le_add_of_nonneg_right bot_le
  · exact le_add_of_nonneg_left bot_le

/-- **The Turing diffusion semigroup is C₀.** If `H` is a C₀ semigroup on `C(K, ℝ)` (in the
frozen setting, the Neumann heat semigroup), then `diag(H (d_u t), H (d_v t))` is a C₀ semigroup
on `C(K, ℝ²)` for all diffusion coefficients `d_u, d_v ≥ 0`. -/
theorem isC0Semigroup_diffusionSemigroup {H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)}
    (hH : IsC0Semigroup H) (du dv : ℝ≥0) : IsC0Semigroup (diffusionSemigroup H du dv) := by
  refine ⟨?_, fun s t => ?_, fun w => ?_, fun T => ?_⟩
  · ext w x k
    simp [diffusionSemigroup_apply_apply, hH.map_zero]
  · ext w x k
    rw [diffusionSemigroup_apply_apply, ContinuousLinearMap.comp_apply,
      diffusionSemigroup_apply_apply, speciesProj_diffusionSemigroup, mul_add, hH.map_add]
    rfl
  · simp only [diffusionSemigroup, sum_apply,
      ContinuousLinearMap.comp_apply]
    exact continuous_finsetSum _ fun i _ => (speciesEmb K i).continuous.comp
      ((hH.continuous_apply _).comp (continuous_const.mul continuous_id))
  · obtain ⟨M, hM⟩ := hH.locally_bounded ((du + dv) * T)
    refine ⟨∑ i, ‖speciesEmb K i‖ * M * ‖speciesProj K i‖, fun t ht => ?_⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    have hHi : ‖H (![du, dv] i * t)‖ ≤ M := hM _ (mul_le_mul' (coeff_le_add du dv i) ht)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_)
      (norm_nonneg _) |>.trans_eq (mul_assoc _ _ _).symm
    exact mul_le_mul_of_nonneg_right hHi (norm_nonneg _)

/-- **Eigenfunctions.** If `φ` is an eigenfunction of the scalar semigroup with
`H τ φ = e^{-q τ} φ` (for the Neumann heat semigroup on `[0, L]`: `φ = cos (k_n ·)`,
`q = k_n²`), then the single-species field `φ eᵢ` is an eigenfunction of the Turing diffusion
semigroup with rate `q dᵢ`: `S t (φ eᵢ) = e^{-q dᵢ t} φ eᵢ`. -/
theorem diffusionSemigroup_apply_speciesEmb {H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)} {q : ℝ}
    {φ : C(K, ℝ)} (hφ : ∀ τ : ℝ≥0, H τ φ = Real.exp (-(q * τ)) • φ) (du dv t : ℝ≥0)
    (i : Fin 2) :
    diffusionSemigroup H du dv t (speciesEmb K i φ) =
      Real.exp (-(q * (![du, dv] i * t : ℝ≥0))) • speciesEmb K i φ := by
  ext x k
  rw [diffusionSemigroup_apply_apply, speciesProj_speciesEmb]
  by_cases h : k = i
  · subst h
    simp [hφ]
  · simp [h]

section LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [CompactSpace K] in
/-- `C¹` kinetics on a finite-dimensional space are Lipschitz on every closed ball, so their
Nemytskii operator satisfies the hypothesis `hF` of the flow interface
(`lipschitzOnWith_nemytskii`). -/
theorem exists_lipschitzOnWith_closedBall_of_contDiff {f : E → E} (hf : ContDiff ℝ 1 f)
    (R : ℝ) : ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.closedBall 0 R) :=
  hf.contDiffOn.exists_lipschitzOnWith one_ne_zero (convex_closedBall 0 R)
    (isCompact_closedBall 0 R)

/-- **Local well-posedness of the Turing system** in `C(K, ℝ²)`. Let `H` be a C₀ semigroup on
`C(K, ℝ)` with generator `A`, let `d_u, d_v ≥ 0`, and let the kinetics `f : ℝ² → ℝ²` be `C¹`.
For every radius `r` there are a time `T > 0`, a bound `R`, a constant `C ≥ 0` and a solution map
`sol` such that for `‖x₀‖ ≤ r`, `sol x₀` is a continuous mild solution on `[0, T]` of
`w_t = D A w + f(w)`, `w 0 = x₀`, bounded by `R`, and `‖sol x₀ t - sol y₀ t‖ ≤ C ‖x₀ - y₀‖` on
`[0, T]` for `‖x₀‖, ‖y₀‖ ≤ r`. This is the Neumann problem `w_t = D Δ_N w + f(w)` exactly when
`H` is the Neumann heat semigroup `e^{τ Δ_N}`. -/
theorem localFlow {H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)} (hH : IsC0Semigroup H) (du dv : ℝ≥0)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiff ℝ 1 f) (r : ℝ) :
    ∃ T > 0, ∃ R C : ℝ, 0 ≤ C ∧ ∃ sol : C(K, Fin 2 → ℝ) → ℝ → C(K, Fin 2 → ℝ),
      (∀ x₀, ‖x₀‖ ≤ r → Continuous (sol x₀) ∧
        IsMildSolution (diffusionSemigroup H du dv) (nemytskii f hf.continuous) x₀ T (sol x₀) ∧
        ∀ t ∈ Icc 0 T, ‖sol x₀ t‖ ≤ R) ∧
      ∀ x₀ y₀, ‖x₀‖ ≤ r → ‖y₀‖ ≤ r → ∀ t ∈ Icc 0 T,
        ‖sol x₀ t - sol y₀ t‖ ≤ C * ‖x₀ - y₀‖ := by
  classical
  have hS := isC0Semigroup_diffusionSemigroup hH du dv
  have hF := lipschitzOnWith_nemytskii (K := K) hf.continuous
    (exists_lipschitzOnWith_closedBall_of_contDiff hf)
  obtain ⟨T, hT, R, hex⟩ := exists_isMildSolution hS hF r
  obtain ⟨C, hC0, hC⟩ := exists_norm_sub_le_of_norm_le hS hF R T
  refine ⟨T, hT, R, C, hC0,
    fun x₀ => if h : ‖x₀‖ ≤ r then (hex x₀ h).choose else fun _ => 0, fun x₀ hx => ?_,
    fun x₀ y₀ hx hy t ht => ?_⟩
  · simp only [hx, ↓reduceDIte]
    exact (hex x₀ hx).choose_spec
  · simp only [hx, hy, ↓reduceDIte]
    exact hC _ _ _ _ (hex x₀ hx).choose_spec.2.1 (hex y₀ hy).choose_spec.2.1
      (fun s hs => ⟨(hex x₀ hx).choose_spec.2.2 s hs, (hex y₀ hy).choose_spec.2.2 s hs⟩) t ht

/-- **Uniqueness** of mild solutions of the Turing system with `C¹` kinetics. -/
theorem isMildSolution_unique {H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)} (hH : IsC0Semigroup H)
    {du dv : ℝ≥0} {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiff ℝ 1 f)
    {x₀ : C(K, Fin 2 → ℝ)} {T : ℝ} {u v : ℝ → C(K, Fin 2 → ℝ)}
    (hu : IsMildSolution (diffusionSemigroup H du dv) (nemytskii f hf.continuous) x₀ T u)
    (hv : IsMildSolution (diffusionSemigroup H du dv) (nemytskii f hf.continuous) x₀ T v) :
    EqOn u v (Icc 0 T) :=
  hu.eqOn (isC0Semigroup_diffusionSemigroup hH du dv)
    (lipschitzOnWith_nemytskii hf.continuous (exists_lipschitzOnWith_closedBall_of_contDiff hf))
    hv

/-- **Semiflow identity** for the Turing system: restarting a mild solution at time `s` from
its state `u s` gives the shifted solution. -/
theorem isMildSolution_restart {H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)} (hH : IsC0Semigroup H)
    {du dv : ℝ≥0} {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : ContDiff ℝ 1 f)
    {x₀ : C(K, Fin 2 → ℝ)} {T : ℝ} {u : ℝ → C(K, Fin 2 → ℝ)}
    (hu : IsMildSolution (diffusionSemigroup H du dv) (nemytskii f hf.continuous) x₀ T u)
    {s : ℝ} (hs : s ∈ Icc 0 T) :
    IsMildSolution (diffusionSemigroup H du dv) (nemytskii f hf.continuous) (u s) (T - s)
      fun τ => u (s + τ) :=
  hu.restart (isC0Semigroup_diffusionSemigroup hH du dv)
    (lipschitzOnWith_nemytskii hf.continuous (exists_lipschitzOnWith_closedBall_of_contDiff hf))
    hs

end LocalFlow

/-- If the scalar semigroup fixes constants (`H τ 1 = 1`, as the Neumann heat semigroup does),
then so does the Turing diffusion semigroup: `S t c = c` for every constant field `c ∈ ℝ²`,
for all diffusion coefficients. -/
theorem diffusionSemigroup_apply_const {H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)}
    (hH1 : ∀ τ, H τ (ContinuousMap.const K 1) = ContinuousMap.const K 1) (du dv t : ℝ≥0)
    (c : Fin 2 → ℝ) :
    diffusionSemigroup H du dv t (ContinuousMap.const K c) = ContinuousMap.const K c := by
  ext x k
  have h : speciesProj K k (ContinuousMap.const K c) = c k • ContinuousMap.const K 1 := by
    ext y
    simp
  rw [diffusionSemigroup_apply_apply, h, map_smul, hH1]
  simp

/-- **Homogeneous steady states are mild solutions** when the scalar semigroup fixes constants:
if `f c = 0`, the constant field `c` is a mild solution on `[0, T]` from `c` of the Turing
system, for all diffusion coefficients. This is the base state of the Turing instability
analysis; it fails for semigroups that do not fix constants, such as the Dirichlet one. -/
theorem isMildSolution_const {H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)}
    (hH1 : ∀ τ, H τ (ContinuousMap.const K 1) = ContinuousMap.const K 1) (du dv : ℝ≥0)
    {f : (Fin 2 → ℝ) → Fin 2 → ℝ} (hf : Continuous f) {c : Fin 2 → ℝ} (hc : f c = 0)
    (T : ℝ) :
    IsMildSolution (diffusionSemigroup H du dv) (nemytskii f hf) (ContinuousMap.const K c) T
      fun _ => ContinuousMap.const K c := by
  have hF : nemytskii f hf (ContinuousMap.const K c) = 0 := by
    ext x : 1
    exact hc
  refine ⟨continuousOn_const, fun t _ => ?_, fun t _ => ?_⟩
  · simp only [hF, map_zero]
    exact intervalIntegrable_const
  · simp only [hF, map_zero, duhamel, intervalIntegral.integral_zero, add_zero,
      diffusionSemigroup_apply_const hH1]

/-! ### The Schnakenberg and Gierer–Meinhardt kinetics -/

/-- The Schnakenberg kinetics are smooth (polynomial). -/
theorem contDiff_schnakenberg (a b : ℝ) {n : WithTop ℕ∞} : ContDiff ℝ n (schnakenberg a b) := by
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ n fun x : Fin 2 → ℝ => a - x 0 + x 0 ^ 2 * x 1
    fun_prop
  · change ContDiff ℝ n fun x : Fin 2 → ℝ => b - x 0 ^ 2 * x 1
    fun_prop

/-- **Local well-posedness of the Schnakenberg–Turing system** in `C(K, ℝ²)`. -/
theorem schnakenberg_localFlow {H : ℝ≥0 → C(K, ℝ) →L[ℝ] C(K, ℝ)} (hH : IsC0Semigroup H)
    (du dv : ℝ≥0) (a b r : ℝ) :
    ∃ T > 0, ∃ R C : ℝ, 0 ≤ C ∧ ∃ sol : C(K, Fin 2 → ℝ) → ℝ → C(K, Fin 2 → ℝ),
      (∀ x₀, ‖x₀‖ ≤ r → Continuous (sol x₀) ∧
        IsMildSolution (diffusionSemigroup H du dv)
          (nemytskii (schnakenberg a b) (contDiff_schnakenberg a b (n := 1)).continuous) x₀ T
          (sol x₀) ∧
        ∀ t ∈ Icc 0 T, ‖sol x₀ t‖ ≤ R) ∧
      ∀ x₀ y₀, ‖x₀‖ ≤ r → ‖y₀‖ ≤ r → ∀ t ∈ Icc 0 T,
        ‖sol x₀ t - sol y₀ t‖ ≤ C * ‖x₀ - y₀‖ :=
  localFlow hH du dv (contDiff_schnakenberg a b (n := 1)) r

omit [CompactSpace K] in
/-- **Boundary case: Gierer–Meinhardt.** The kinetics `(a - b u + u² / v, u² - v)` are not
Lipschitz on the closed unit ball of `ℝ²`, because of the `u² / v` term near `v = 0`. So the
route `exists_lipschitzOnWith_closedBall_of_contDiff` / `lipschitzOnWith_nemytskii` to the
hypothesis `hF` of the flow interface is closed, and `localFlow` does not apply to them without
an invariant region bounding `v` away from `0`. (For nonempty `K`, restricting to constant fields
shows that the Nemytskii operator itself fails `hF`; that corollary is not formalized here.) -/
theorem not_lipschitzOnWith_giererMeinhardt (a b : ℝ) (L : ℝ≥0) :
    ¬ LipschitzOnWith L (giererMeinhardt a b) (Metric.closedBall 0 1) := by
  intro hL
  set ε : ℝ := 1 / (2 * (L + 1)) with hε
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hε0 : 0 < ε := by positivity
  have hε1 : 2 * ε ≤ 1 := by
    rw [hε, mul_one_div, div_le_one (by positivity)]; linarith
  have hmem : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → (![1, c] : Fin 2 → ℝ) ∈ Metric.closedBall 0 1 := by
    intro c hc0 hc1
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    fin_cases i <;> simp [abs_of_nonneg hc0, hc1]
  have h := hL.dist_le_mul _ (hmem ε hε0.le (by linarith)) _ (hmem (2 * ε) (by positivity) hε1)
  have hdist : dist (![1, ε] : Fin 2 → ℝ) ![1, 2 * ε] ≤ ε := by
    refine (dist_pi_le_iff hε0.le).2 fun i => ?_
    fin_cases i
    · simp [hε0.le]
    · change dist ε (2 * ε) ≤ ε
      rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith
  have hlow : dist (giererMeinhardt a b ![1, ε] 0) (giererMeinhardt a b ![1, 2 * ε] 0) ≤
      L * ε :=
    (dist_le_pi_dist _ _ 0).trans (h.trans (mul_le_mul_of_nonneg_left hdist hL0))
  have hval : dist (giererMeinhardt a b ![1, ε] 0) (giererMeinhardt a b ![1, 2 * ε] 0) =
      L + 1 := by
    simp only [giererMeinhardt, Matrix.cons_val_zero, Matrix.cons_val_one, Real.dist_eq]
    have : a - b * 1 + 1 ^ 2 / ε - (a - b * 1 + 1 ^ 2 / (2 * ε)) = L + 1 := by
      rw [hε]; field_simp; ring
    rw [this, abs_of_pos (by positivity)]
  rw [hval] at hlow
  have : (L : ℝ) * ε ≤ L / 2 := by
    rw [hε]; rw [mul_one_div, div_le_div_iff₀ (by positivity) two_pos]; nlinarith
  linarith

end MathlibExt.Biology.Dynamics.TuringModel
