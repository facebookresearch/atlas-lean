/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Dynamics.TuringPatterns
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Interval.Set.Infinite

/-!
# Turing pattern branches: finite-domain spectrum, onset and local bifurcation

This file continues `MathlibExt.Biology.Dynamics.TuringPatterns` (linear Turing analysis of the
two-species system `u_t = d_u u_xx + f(u, v)`, `v_t = d_v v_xx + g(u, v)` linearized at a
homogeneous steady state with Jacobian `J = [[f_u, f_v], [g_u, g_v]]`).

**Continuum versus finite domain.** On the whole line every real wavenumber `k` is admissible and
the unstable squared wavenumbers form the open band `(q₋, q₊)` where
`h(q) = det (J - q D) < 0`; under Turing's criterion this is a continuum. On `[0, L]` with
homogeneous Neumann boundary conditions the linearization only has the eigenvalues of the mode
matrices `J - k_n² D` at the discrete wavenumbers `k_n = n π / L` (`IsNeumannEigenvalue`), each
realized by a zero-flux Fourier mode. Hence only finitely many Neumann modes are unstable, short
domains are stable although the continuum problem is unstable, and the band can fall into a gap
between two consecutive `k_n²`, so instability is not monotone in `L`.

**Onset of a Neumann mode.** Since `h` is affine in the inhibitor diffusion `d = d_v`, an
admissible mode (`0 < f_u k² - d_u k⁴`) is unstable iff `d` exceeds its *neutral diffusion*
`d_n(k²)` (`neutralDiffusion`); the onset on `[0, L]` is governed by the discrete Neumann values.
At `d_n(k²)` the mode matrix has exactly the eigenvalues `0` and `tr (J - k² D)` (so `0` is a
simple root of its characteristic polynomial whenever this trace is nonzero, e.g. negative), under
non-resonance mode `n` is the only Neumann mode with eigenvalue `0`, and the leading real
eigenvalue crosses zero with positive speed `(d_u k⁴ - f_u k²) / tr (J - k² D)` (transversality).

**Local pattern branch.** The steady-state bifurcation from the homogeneous state at a simple
critical mode is formalized for the *reduced bifurcation equation* `Φ(a, d) = a G(a, d)` in the
critical-mode amplitude `a`. The implicit function theorem gives a unique local pattern branch
`d = φ(a)`; when `G(0, ·)` is the critical eigenvalue, transversality is derived from the Turing
data and the homogeneous state exchanges stability at `d₀`. With a reflection-symmetric reduced
map `G(a, d) = G(0, d) + a² H(a, d)`, the branch is supercritical iff `H(0, d₀) < 0`, and then it is
linearly stable in the reduced equation.

## Scope

The Lyapunov–Schmidt (or center-manifold) reduction of the reaction–diffusion PDE on `[0, L]` to
the scalar map `G` needs the PDE function-space and local-flow framework and is **not** proved
here: every branch theorem takes `G` (and its symmetric decomposition) as an explicit hypothesis.
Stability of the branch is linear stability for the reduced equation `ȧ = Φ(a, d)`.

## Main results

* `exists_eigenvector_iff`, `exists_eigenvector_iff_of_det_eq_zero`: eigenvalues of real
  `2 × 2` matrices via the characteristic polynomial.
* `isNeumannUnstable_iff`, `IsNeumannEigenvalue.exists_solution`: the Neumann spectrum.
* `setOf_isUnstableMode_infinite`, `exists_forall_not_isNeumannUnstable`,
  `not_isNeumannUnstable_of_gap`, `continuum_vs_neumann`: continuum versus finite domain.
* `isUnstableMode_iff_neutralDiffusion_lt`, `isNeumannUnstable_iff_exists_neutralDiffusion_lt`:
  onset thresholds.
* `exists_eigenvector_modeMatrix_iff_of_neutral`, `setOf_neumann_zero_eigen_eq_singleton`:
  simple zero eigenvalue at onset.
* `hasDerivAt_leadingEigenvalue_modeMatrix`, `leadingEigenvalue_crossing`: transversal crossing.
* `exists_patternBranch`, `turing_patternBranch`: local branch existence and exchange of
  stability.
* `patternBranch_direction_stability`, `turing_patternBranch_stability`: branch direction and
  stability (pitchfork).

## References

* A. M. Turing, *The chemical basis of morphogenesis*, Phil. Trans. R. Soc. Lond. B 237 (1952)
  37–72.
* M. G. Crandall and P. H. Rabinowitz, *Bifurcation from simple eigenvalues*, J. Funct. Anal. 8
  (1971) 321–340.
* M. G. Crandall and P. H. Rabinowitz, *Bifurcation, perturbation of simple eigenvalues, and
  linearized stability*, Arch. Rational Mech. Anal. 52 (1973) 161–180.
* J. D. Murray, *Mathematical Biology II*, 3rd ed., Springer (2003), ch. 2.
-/

@[expose] public section

open Matrix Filter Topology

namespace MathlibExt.Biology.Dynamics.TuringBranches

open MathlibExt.Biology.Dynamics.TuringPatterns

/-! ### Eigenvalues of real `2 × 2` matrices -/

/-- A complex number is an eigenvalue of a real `2 × 2` matrix iff it is a root of the
characteristic polynomial `μ² - (tr M) μ + det M`. -/
theorem exists_eigenvector_iff (M : Matrix (Fin 2) (Fin 2) ℝ) (μ : ℂ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.map (↑) *ᵥ v = μ • v) ↔
      μ ^ 2 - (M.trace : ℂ) * μ + (M.det : ℂ) = 0 := by
  classical
  have hdet : (μ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - M.map Complex.ofReal).det =
      μ ^ 2 - (M.trace : ℂ) * μ + (M.det : ℂ) := by
    simp [Matrix.det_fin_two, Matrix.trace_fin_two,
      Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply]
    ring
  rw [← hdet, ← exists_mulVec_eq_zero_iff]
  simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    sub_eq_zero, eq_comm]

/-- A singular real `2 × 2` matrix has exactly the eigenvalues `0` and `tr M`. -/
theorem exists_eigenvector_iff_of_det_eq_zero {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : M.det = 0)
    (μ : ℂ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.map (↑) *ᵥ v = μ • v) ↔ μ = 0 ∨ μ = M.trace := by
  rw [exists_eigenvector_iff, hM, Complex.ofReal_zero, add_zero,
    show μ ^ 2 - (M.trace : ℂ) * μ = μ * (μ - M.trace) by ring, mul_eq_zero, sub_eq_zero]

/-! ### Finite-domain spectrum versus the continuum of wavenumbers -/

/-- `μ` is an eigenvalue of the linearization `w ↦ D w_xx + J w` on `[0, L]` with homogeneous
Neumann boundary conditions: it is an eigenvalue of the mode matrix `J - k_n² D` of some
admissible Neumann wavenumber `k_n = n π / L`. Only the discrete wavenumbers `k_n` contribute;
the continuum of wavenumbers `k ∈ ℝ` of the problem on the whole line does not. (That these are
all eigenvalues of the PDE operator, i.e. completeness of the cosine basis, is not proved here;
the definition records the spectrum it induces.) -/
def IsNeumannEigenvalue (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv L : ℝ) (μ : ℂ) : Prop :=
  ∃ n : ℕ, ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
    (modeMatrix J du dv (neumannWavenumber L n)).map (↑) *ᵥ v = μ • v

/-- The homogeneous steady state is *linearly unstable on `[0, L]`* (Neumann boundary
conditions): the finite-domain linearization has an eigenvalue with positive real part. -/
def IsNeumannUnstable (J : Matrix (Fin 2) (Fin 2) ℝ) (du dv L : ℝ) : Prop :=
  ∃ μ : ℂ, 0 < μ.re ∧ IsNeumannEigenvalue J du dv L μ

/-- Finite-domain instability is instability of some Neumann mode. -/
theorem isNeumannUnstable_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv L : ℝ} :
    IsNeumannUnstable J du dv L ↔ ∃ n : ℕ, IsUnstableMode J du dv (neumannWavenumber L n) := by
  constructor
  · rintro ⟨μ, hμ, n, v, hv, h⟩
    exact ⟨n, μ, hμ, v, hv, h⟩
  · rintro ⟨n, μ, hμ, v, hv, h⟩
    exact ⟨μ, hμ, n, v, hv, h⟩

/-- Every Neumann eigenvalue is realized by a classical solution of the linearized system that
has zero flux at both ends of `[0, L]`: the Fourier mode `e^{μ t} cos(k_n x) v`. -/
theorem IsNeumannEigenvalue.exists_solution {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv L : ℝ}
    (hL : L ≠ 0) {μ : ℂ} (h : IsNeumannEigenvalue J du dv L μ) :
    ∃ (n : ℕ) (v : Fin 2 → ℂ), v ≠ 0 ∧
      IsLinearizedSolution J du dv (fourierMode μ (neumannWavenumber L n) v) ∧
      ∀ t, HasDerivAt (fourierMode μ (neumannWavenumber L n) v t) 0 0 ∧
        HasDerivAt (fourierMode μ (neumannWavenumber L n) v t) 0 L := by
  obtain ⟨n, v, hv, hμ⟩ := h
  exact ⟨n, v, hv, (fourierMode_isLinearizedSolution_iff J du dv _ μ v).2 hμ,
    fun t => hasDerivAt_fourierMode_neumannWavenumber hL n μ v t⟩

/-- Instability on a finite domain implies instability for the continuum of wavenumbers. -/
theorem IsNeumannUnstable.exists_isUnstableMode {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv L : ℝ}
    (h : IsNeumannUnstable J du dv L) : ∃ k, IsUnstableMode J du dv k := by
  obtain ⟨n, hn⟩ := isNeumannUnstable_iff.1 h
  exact ⟨_, hn⟩

/-- For `d_u, d_v > 0` and a positive discriminant, the continuum of unstable squared
wavenumbers is the whole open band `(q₋, q₊)`. -/
theorem setOf_dispersionDet_neg_eq_Ioo {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (hΔ : 0 < bandDiscriminant J du dv) :
    {q : ℝ | dispersionDet J du dv q < 0} = Set.Ioo (bandLower J du dv) (bandUpper J du dv) := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_Ioo, dispersionDet_neg_iff hdu hdv, hΔ, true_and]

/-- Under Turing's criterion the unstable band is a nonempty open interval reaching positive
squared wavenumbers. -/
private theorem band_facts {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv)
    (h : 2 * Real.sqrt (du * dv * J.det) < dv * J 0 0 + du * J 1 1) :
    0 < bandDiscriminant J du dv ∧ bandLower J du dv < bandUpper J du dv ∧
      0 < bandUpper J du dv := by
  obtain ⟨hS, hsq⟩ := two_mul_sqrt_lt_iff.1 h
  have hΔ : 0 < bandDiscriminant J du dv := by
    unfold bandDiscriminant
    linarith
  have hr : 0 < Real.sqrt (bandDiscriminant J du dv) := Real.sqrt_pos.2 hΔ
  have hp : 0 < 2 * du * dv := by positivity
  refine ⟨hΔ, ?_, ?_⟩
  · unfold bandLower bandUpper
    exact div_lt_div_of_pos_right (by linarith) hp
  · unfold bandUpper
    exact div_pos (by linarith) hp

/-- **The continuum of unstable wavenumbers is infinite.** Under Turing's criterion (and
stability without diffusion), infinitely many real wavenumbers `k` are unstable: every `k` with
`k² ∈ (max q₋ 0, q₊)` is. Contrast `finite_setOf_isUnstableMode_neumannWavenumber`: on a
finite domain only finitely many Neumann modes are unstable. -/
theorem setOf_isUnstableMode_infinite {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (htr : J.trace < 0)
    (h : 2 * Real.sqrt (du * dv * J.det) < dv * J 0 0 + du * J 1 1) :
    {k : ℝ | IsUnstableMode J du dv k}.Infinite := by
  obtain ⟨hΔ, hlt, hpos⟩ := band_facts hdu hdv h
  have hab : Real.sqrt (max (bandLower J du dv) 0) < Real.sqrt (bandUpper J du dv) :=
    Real.sqrt_lt_sqrt (le_max_right _ _) (max_lt hlt hpos)
  refine (Set.Ioo_infinite hab).mono fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := hk
  have ha := Real.sqrt_nonneg (max (bandLower J du dv) 0)
  have hk0 : 0 ≤ k := ha.trans hk1.le
  have hlo : max (bandLower J du dv) 0 < k ^ 2 := by
    have := (Real.sqrt_lt' (lt_of_le_of_lt ha hk1)).1 hk1
    exact this
  have hhi : k ^ 2 < bandUpper J du dv := (Real.lt_sqrt hk0).1 hk2
  rw [Set.mem_ofPred_eq, isUnstableMode_iff_dispersionDet_neg htr hdu.le hdv.le,
    dispersionDet_neg_iff hdu hdv]
  exact ⟨hΔ, lt_of_le_of_lt (le_max_left _ _) hlo, hhi⟩

/-- **Small domains are stable.** For `d_u, d_v > 0` and a kinetically stable state, there is
`L₁ > 0` such that no Neumann mode is unstable on any `[0, L]` with `0 < L ≤ L₁`. -/
theorem exists_forall_not_isNeumannUnstable {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (htr : J.trace < 0) (hdet : 0 < J.det) :
    ∃ L₁ : ℝ, 0 < L₁ ∧ ∀ L, 0 < L → L ≤ L₁ → ¬ IsNeumannUnstable J du dv L := by
  set Q := max (bandUpper J du dv) 1
  have hQ : 0 < Real.sqrt Q := Real.sqrt_pos.2 (lt_of_lt_of_le one_pos (le_max_right _ _))
  refine ⟨Real.pi / Real.sqrt Q, div_pos Real.pi_pos hQ, fun L hL hLle => ?_⟩
  rw [isNeumannUnstable_iff]
  rintro ⟨n, hn⟩
  refine not_isUnstableMode_neumannWavenumber_of_le hdu hdv htr hdet hL ?_ n hn
  have h1 : Real.sqrt Q ≤ Real.pi / L := by
    rw [le_div_iff₀ hL]
    rw [le_div_iff₀ hQ] at hLle
    linarith
  have h2 : Q ≤ (Real.pi / L) ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg Q) h1 2
    rwa [Real.sq_sqrt (lt_of_lt_of_le one_pos (le_max_right _ _)).le] at this
  exact (le_max_left _ _).trans h2

/-- Squared Neumann wavenumbers increase with the mode index. -/
private theorem neumann_sq_le {L : ℝ} (hL : 0 < L) {m n : ℕ} (hmn : m ≤ n) :
    (m * Real.pi / L) ^ 2 ≤ (n * Real.pi / L) ^ 2 := by
  have hm : (0 : ℝ) ≤ m * Real.pi / L := by positivity
  have h : (m : ℝ) * Real.pi / L ≤ n * Real.pi / L := by
    gcongr
  exact pow_le_pow_left₀ hm h 2

/-- **Band gaps.** If the unstable band `(q₋, q₊)` falls between two consecutive squared Neumann
wavenumbers, `(n π / L)² ≤ q₋` and `q₊ ≤ ((n + 1) π / L)²`, then no Neumann mode is unstable on
`[0, L]`, even though the continuum of wavenumbers is unstable whenever the band is nonempty. -/
theorem not_isNeumannUnstable_of_gap {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv L : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (htr : J.trace < 0) (hL : 0 < L) (n : ℕ)
    (hlo : (n * Real.pi / L) ^ 2 ≤ bandLower J du dv)
    (hhi : bandUpper J du dv ≤ ((n + 1 : ℕ) * Real.pi / L) ^ 2) :
    ¬ IsNeumannUnstable J du dv L := by
  rw [isNeumannUnstable_iff]
  rintro ⟨m, hm⟩
  rw [isUnstableMode_neumannWavenumber_iff hdu hdv htr hL] at hm
  obtain ⟨-, h1, h2⟩ := hm
  rcases le_or_gt m n with hmn | hmn
  · have := neumann_sq_le hL hmn
    linarith
  · have := neumann_sq_le hL (Nat.succ_le_of_lt hmn)
    linarith

/-- **Continuum versus finite domain.** Under Turing's criterion (stable kinetics, `d_u, d_v > 0`):
infinitely many real wavenumbers are unstable, yet on every interval `[0, L]` only finitely many
Neumann modes are, and on all short enough intervals none is, although the continuum problem is
unstable. -/
theorem continuum_vs_neumann {J : Matrix (Fin 2) (Fin 2) ℝ} {du dv : ℝ}
    (hdu : 0 < du) (hdv : 0 < dv) (htr : J.trace < 0) (hdet : 0 < J.det)
    (h : 2 * Real.sqrt (du * dv * J.det) < dv * J 0 0 + du * J 1 1) :
    {k : ℝ | IsUnstableMode J du dv k}.Infinite ∧
      (∀ L, 0 < L → {n : ℕ | IsUnstableMode J du dv (neumannWavenumber L n)}.Finite) ∧
      ∃ L₁ : ℝ, 0 < L₁ ∧ ∀ L, 0 < L → L ≤ L₁ →
        (∃ k, IsUnstableMode J du dv k) ∧ ¬ IsNeumannUnstable J du dv L := by
  refine ⟨setOf_isUnstableMode_infinite hdu hdv htr h,
    fun L hL => finite_setOf_isUnstableMode_neumannWavenumber hdu hdv hL, ?_⟩
  obtain ⟨L₁, hL₁, hstab⟩ := exists_forall_not_isNeumannUnstable hdu hdv htr hdet
  exact ⟨L₁, hL₁, fun L hL hle =>
    ⟨(exists_isUnstableMode_iff hdu hdv htr hdet).2 h, hstab L hL hle⟩⟩

/-! ### Onset of a Neumann mode as the inhibitor diffusion `d = d_v` increases -/

/-- The *neutral diffusion* of squared wavenumber `q`:
`d_n(q) = (det J - d_u g_v q) / (f_u q - d_u q²)`. Since
`det (J - k² D) = h(k²)` is affine in `d_v`, the mode of squared wavenumber `q` is neutral
(`h(q) = 0`) exactly at `d_v = d_n(q)` (when `f_u q - d_u q² ≠ 0`). For a Neumann mode
`q = k_n²` this is the diffusion at which the finite-domain eigenvalue of mode `n` crosses
zero. -/
noncomputable def neutralDiffusion (J : Matrix (Fin 2) (Fin 2) ℝ) (du q : ℝ) : ℝ :=
  (J.det - du * J 1 1 * q) / (J 0 0 * q - du * q ^ 2)

/-- `h(q) = (f_u q - d_u q²) (d_n(q) - d_v)`. -/
theorem dispersionDet_eq_mul_neutralDiffusion_sub {J : Matrix (Fin 2) (Fin 2) ℝ} {du d q : ℝ}
    (hq : J 0 0 * q - du * q ^ 2 ≠ 0) :
    dispersionDet J du d q = (J 0 0 * q - du * q ^ 2) * (neutralDiffusion J du q - d) := by
  rw [mul_sub, neutralDiffusion, mul_div_cancel₀ _ hq, dispersionDet]
  ring

/-- For an *admissible* wavenumber, `0 < f_u k² - d_u k⁴`, the mode `k` is unstable iff the
inhibitor diffusion exceeds the neutral diffusion: `d_n(k²) < d`. -/
theorem isUnstableMode_iff_neutralDiffusion_lt {J : Matrix (Fin 2) (Fin 2) ℝ} {du d k : ℝ}
    (htr : J.trace < 0) (hdu : 0 ≤ du) (hd : 0 ≤ d)
    (hk : 0 < J 0 0 * k ^ 2 - du * (k ^ 2) ^ 2) :
    IsUnstableMode J du d k ↔ neutralDiffusion J du (k ^ 2) < d := by
  rw [isUnstableMode_iff_dispersionDet_neg htr hdu hd,
    dispersionDet_eq_mul_neutralDiffusion_sub hk.ne']
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith [mul_nonneg hk.le (sub_nonneg.2 hc)]
  · intro h
    exact mul_neg_of_pos_of_neg hk (sub_neg.2 h)

/-- Inadmissible wavenumbers, `f_u k² - d_u k⁴ ≤ 0`, are never unstable when `0 < det J` and
`g_v ≤ 0`, whatever the diffusion `d ≥ 0`. -/
theorem not_isUnstableMode_of_inadmissible {J : Matrix (Fin 2) (Fin 2) ℝ} {du d k : ℝ}
    (htr : J.trace < 0) (hdu : 0 ≤ du) (hd : 0 ≤ d) (hdet : 0 < J.det) (hgv : J 1 1 ≤ 0)
    (hk : J 0 0 * k ^ 2 - du * (k ^ 2) ^ 2 ≤ 0) : ¬ IsUnstableMode J du d k := by
  rw [isUnstableMode_iff_dispersionDet_neg htr hdu hd, not_lt, dispersionDet]
  nlinarith [mul_nonneg hd (neg_nonneg.2 hk),
    mul_nonneg hdu (mul_nonneg (neg_nonneg.2 hgv) (sq_nonneg k))]

/-- **Finite-domain onset.** On `[0, L]` (with `0 < det J`, `g_v ≤ 0`, `tr J < 0`), the
homogeneous state is unstable iff some *admissible Neumann* mode has neutral diffusion below
`d`. The onset threshold is a minimum over the discrete Neumann wavenumbers, not over the
continuum of wavenumbers. -/
theorem isNeumannUnstable_iff_exists_neutralDiffusion_lt {J : Matrix (Fin 2) (Fin 2) ℝ}
    {du d L : ℝ} (htr : J.trace < 0) (hdu : 0 ≤ du) (hd : 0 ≤ d) (hdet : 0 < J.det)
    (hgv : J 1 1 ≤ 0) :
    IsNeumannUnstable J du d L ↔ ∃ n : ℕ,
      0 < J 0 0 * neumannWavenumber L n ^ 2 - du * (neumannWavenumber L n ^ 2) ^ 2 ∧
        neutralDiffusion J du (neumannWavenumber L n ^ 2) < d := by
  rw [isNeumannUnstable_iff]
  constructor
  · rintro ⟨n, hn⟩
    by_cases hk : 0 < J 0 0 * neumannWavenumber L n ^ 2 - du * (neumannWavenumber L n ^ 2) ^ 2
    · exact ⟨n, hk, (isUnstableMode_iff_neutralDiffusion_lt htr hdu hd hk).1 hn⟩
    · exact absurd hn (not_isUnstableMode_of_inadmissible htr hdu hd hdet hgv (not_lt.1 hk))
  · rintro ⟨n, hk, hn⟩
    exact ⟨n, (isUnstableMode_iff_neutralDiffusion_lt htr hdu hd hk).2 hn⟩

/-- At its neutral diffusion an admissible mode has exactly the eigenvalues `0` and
`tr (J - k² D) = tr J - k² (d_u + d)`. -/
theorem exists_eigenvector_modeMatrix_iff_of_neutral {J : Matrix (Fin 2) (Fin 2) ℝ} {du d k : ℝ}
    (hk : J 0 0 * k ^ 2 - du * (k ^ 2) ^ 2 ≠ 0) (hd : d = neutralDiffusion J du (k ^ 2))
    (μ : ℂ) :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (modeMatrix J du d k).map (↑) *ᵥ v = μ • v) ↔
      μ = 0 ∨ μ = ((J.trace - k ^ 2 * (du + d) : ℝ) : ℂ) := by
  have hdet : (modeMatrix J du d k).det = 0 := by
    rw [det_modeMatrix, dispersionDet_eq_mul_neutralDiffusion_sub hk, hd, sub_self, mul_zero]
  rw [exists_eigenvector_iff_of_det_eq_zero hdet, trace_modeMatrix]

/-- `0` is an eigenvalue of the mode matrix iff the mode is neutral, `h(k²) = 0`. -/
theorem exists_eigenvector_zero_iff {J : Matrix (Fin 2) (Fin 2) ℝ} {du d k : ℝ} :
    (∃ v : Fin 2 → ℂ, v ≠ 0 ∧ (modeMatrix J du d k).map (↑) *ᵥ v = (0 : ℂ) • v) ↔
      dispersionDet J du d (k ^ 2) = 0 := by
  rw [exists_eigenvector_iff, det_modeMatrix]
  simp

/-- **Non-resonance isolates the critical Neumann mode.** If mode `n` is neutral at `d` and no
other Neumann mode is (`h(k_m²) ≠ 0` for `m ≠ n`), then `n` is the only Neumann mode whose
mode matrix has the eigenvalue `0`. Simplicity of `0` *within* mode `n` additionally needs
`tr (J - k_n² D) ≠ 0` (`exists_eigenvector_modeMatrix_iff_of_neutral`); together these give the
spectral hypothesis of a simple-eigenvalue (Crandall–Rabinowitz) bifurcation on `[0, L]`. -/
theorem setOf_neumann_zero_eigen_eq_singleton {J : Matrix (Fin 2) (Fin 2) ℝ} {du d L : ℝ}
    {n : ℕ} (hn : dispersionDet J du d (neumannWavenumber L n ^ 2) = 0)
    (hnr : ∀ m, m ≠ n → dispersionDet J du d (neumannWavenumber L m ^ 2) ≠ 0) :
    {m : ℕ | ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      (modeMatrix J du d (neumannWavenumber L m)).map (↑) *ᵥ v = (0 : ℂ) • v} = {n} := by
  ext m
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, exists_eigenvector_zero_iff]
  constructor
  · intro h
    by_contra hm
    exact hnr m hm h
  · rintro rfl
    exact hn

/-- The *leading real eigenvalue* `(tr M + √(tr² M - 4 det M)) / 2` of a real `2 × 2` matrix;
it is an eigenvalue when the discriminant `tr² M - 4 det M` is nonnegative
(`exists_eigenvector_leadingEigenvalue`). Near a neutral Turing mode it is the critical
eigenvalue that crosses zero. -/
noncomputable def leadingEigenvalue (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M.trace + Real.sqrt (M.trace ^ 2 - 4 * M.det)) / 2

/-- With a nonnegative discriminant the leading real eigenvalue is an eigenvalue. -/
theorem exists_eigenvector_leadingEigenvalue {M : Matrix (Fin 2) (Fin 2) ℝ}
    (h : 0 ≤ M.trace ^ 2 - 4 * M.det) :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ M.map (↑) *ᵥ v = (leadingEigenvalue M : ℂ) • v := by
  rw [exists_eigenvector_iff]
  have hs := Real.sq_sqrt h
  have hr : leadingEigenvalue M ^ 2 - M.trace * leadingEigenvalue M + M.det = 0 := by
    unfold leadingEigenvalue
    nlinarith [hs]
  exact_mod_cast hr

/-- A singular matrix with negative trace has leading real eigenvalue `0`. -/
theorem leadingEigenvalue_eq_zero {M : Matrix (Fin 2) (Fin 2) ℝ} (htr : M.trace < 0)
    (hdet : M.det = 0) : leadingEigenvalue M = 0 := by
  rw [leadingEigenvalue, hdet, mul_zero, sub_zero, Real.sqrt_sq_eq_abs, abs_of_neg htr]
  ring

/-- **Transversal crossing.** At a neutral mode (`h(k²) = 0`) with negative trace, the leading
real eigenvalue of `J - k² D`, as a function of the inhibitor diffusion `d = d_v`, has derivative
`(d_u k⁴ - f_u k²) / tr (J - k² D)` at the neutral diffusion. -/
theorem hasDerivAt_leadingEigenvalue_modeMatrix {J : Matrix (Fin 2) (Fin 2) ℝ} {du d₀ k : ℝ}
    (htr : J.trace - k ^ 2 * (du + d₀) < 0) (hdet : dispersionDet J du d₀ (k ^ 2) = 0) :
    HasDerivAt (fun d => leadingEigenvalue (modeMatrix J du d k))
      ((du * (k ^ 2) ^ 2 - J 0 0 * k ^ 2) / (J.trace - k ^ 2 * (du + d₀))) d₀ := by
  set q := k ^ 2 with hq
  set a := du * q ^ 2 - J 0 0 * q with ha
  set b := J.det - du * J 1 1 * q with hb
  have hT : HasDerivAt (fun d => J.trace - q * (du + d)) (-q) d₀ := by
    simpa using (((hasDerivAt_id d₀).const_add du).const_mul q).const_sub J.trace
  have hΔ : HasDerivAt (fun d => a * d + b) a d₀ := by
    simpa using ((hasDerivAt_id d₀).const_mul a).add_const b
  have hΔ0 : a * d₀ + b = 0 := by
    rw [← hdet, dispersionDet]
    ring
  have hdisc : (J.trace - q * (du + d₀)) * (J.trace - q * (du + d₀)) - 4 * (a * d₀ + b) ≠ 0 := by
    rw [hΔ0]
    nlinarith
  set T₀ := J.trace - q * (du + d₀) with hT₀
  have key : HasDerivAt (fun d => ((J.trace - q * (du + d)) +
      Real.sqrt ((J.trace - q * (du + d)) * (J.trace - q * (du + d)) - 4 * (a * d + b))) / 2)
      ((-q + (-q * T₀ + T₀ * -q - 4 * a) / (2 * Real.sqrt (T₀ * T₀ - 4 * (a * d₀ + b)))) / 2)
      d₀ :=
    (hT.add (((hT.mul hT).sub (hΔ.const_mul 4)).sqrt hdisc)).div_const 2
  convert key using 1
  · funext d
    have h1 : (modeMatrix J du d k).trace = J.trace - q * (du + d) := trace_modeMatrix J du d k
    have h2 : (modeMatrix J du d k).det = a * d + b := by
      rw [det_modeMatrix, dispersionDet, ha, hb]
      ring
    rw [leadingEigenvalue, h1, h2, sq]
  · rw [hΔ0, mul_zero, sub_zero, Real.sqrt_mul_self_eq_abs, abs_of_neg htr]
    have hne : T₀ ≠ 0 := htr.ne
    field_simp
    ring

/-- At the neutral diffusion of an admissible wavenumber, the critical eigenvalue crosses zero
with positive speed: the leading real eigenvalue vanishes there and has positive derivative in
`d`. -/
theorem leadingEigenvalue_crossing {J : Matrix (Fin 2) (Fin 2) ℝ} {du d₀ k : ℝ}
    (htr : J.trace - k ^ 2 * (du + d₀) < 0) (hk : 0 < J 0 0 * k ^ 2 - du * (k ^ 2) ^ 2)
    (hd₀ : d₀ = neutralDiffusion J du (k ^ 2)) :
    leadingEigenvalue (modeMatrix J du d₀ k) = 0 ∧
      HasDerivAt (fun d => leadingEigenvalue (modeMatrix J du d k))
        ((du * (k ^ 2) ^ 2 - J 0 0 * k ^ 2) / (J.trace - k ^ 2 * (du + d₀))) d₀ ∧
      0 < (du * (k ^ 2) ^ 2 - J 0 0 * k ^ 2) / (J.trace - k ^ 2 * (du + d₀)) := by
  have hdet : dispersionDet J du d₀ (k ^ 2) = 0 := by
    rw [dispersionDet_eq_mul_neutralDiffusion_sub hk.ne', hd₀, sub_self, mul_zero]
  refine ⟨leadingEigenvalue_eq_zero (by rwa [trace_modeMatrix]) (by rwa [det_modeMatrix]),
    hasDerivAt_leadingEigenvalue_modeMatrix htr hdet, div_pos_of_neg_of_neg ?_ htr⟩
  linarith

/-! ### Local pattern branch of the reduced bifurcation equation

The steady states of the Turing system near the homogeneous state and the neutral diffusion
`d₀` of a simple critical Neumann mode `n` are, by a center-manifold reduction (or a
Lyapunov–Schmidt reduction along the `d`-dependent critical eigenvector `cos(k_n x) v(d)`), the
zeros of a scalar *reduced bifurcation equation* `Φ(a, d) = a · G(a, d)` in the amplitude `a` of
that mode (the factor `a` expresses that the homogeneous state `a = 0` is a steady state for
every `d`), with `G(0, d)` equal to the critical eigenvalue. (A Lyapunov–Schmidt reduction along a
fixed kernel vector only reproduces the sign and crossing slope of the critical eigenvalue, not
the exact equality used in `turing_patternBranch`.) The reduction itself needs the function-space
framework of the PDE and is **not** formalized here: the reduced map `G` enters as an explicit
hypothesis. -/

/-- A continuous linear map `ℝ → ℝ` with `f 1 ≠ 0` is invertible. -/
private theorem isInvertible_of_apply_one_ne_zero {f : ℝ →L[ℝ] ℝ} (hf : f 1 ≠ 0) :
    f.IsInvertible := by
  refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (f 1) hf), ?_⟩
  ext
  simp

/-- **Local branch existence (Crandall–Rabinowitz, reduced form).** Let
`G : ℝ × ℝ → ℝ` be strictly differentiable at `(0, d₀)` with `G (0, d₀) = 0` and transversal
`∂_d G (0, d₀) = G' (0, 1) ≠ 0`. Then there is a branch `d = φ(a)` with `φ 0 = d₀`, strictly
differentiable at `0` with slope `-∂_a G / ∂_d G`, such that near `(0, d₀)` the zeros of
`Φ(a, d) = a · G(a, d)` are exactly the trivial branch `a = 0` and the pattern branch
`d = φ(a)`. -/
theorem exists_patternBranch {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ} {d₀ : ℝ}
    (hG : HasStrictFDerivAt G G' (0, d₀)) (h0 : G (0, d₀) = 0) (htrans : G' (0, 1) ≠ 0) :
    ∃ φ : ℝ → ℝ, φ 0 = d₀ ∧ HasStrictDerivAt φ (-(G' (1, 0) / G' (0, 1))) 0 ∧
      ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), (p.1 * G p = 0 ↔ p.1 = 0 ∨ p.2 = φ p.1) := by
  have hc : (G' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ) 1 ≠ 0 := by simpa using htrans
  have heq : G' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ =
      ((ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ hc) : ℝ ≃L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) := by
    ext
    simp
  have hinv : (G' ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible :=
    isInvertible_of_apply_one_ne_zero hc
  have hiff := hG.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  have hder := hG.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv
  refine ⟨hG.implicitFunctionOfProdDomain hinv, (hiff.self_of_nhds).1 rfl, ?_, ?_⟩
  · convert hder.hasStrictDerivAt using 1
    rw [heq, ContinuousLinearMap.inverse_equiv]
    simp [div_eq_mul_inv]
  · filter_upwards [hiff] with p hp
    rw [h0] at hp
    rw [mul_eq_zero, hp]
    exact or_congr Iff.rfl eq_comm

/-- A function vanishing at `x₀` with positive derivative there is negative just to the left of
`x₀` and positive just to the right. -/
private theorem eventually_sign_of_hasDerivAt {g : ℝ → ℝ} {σ x₀ : ℝ} (hg : HasDerivAt g σ x₀)
    (h0 : g x₀ = 0) (hσ : 0 < σ) :
    (∀ᶠ x in 𝓝[<] x₀, g x < 0) ∧ ∀ᶠ x in 𝓝[>] x₀, 0 < g x := by
  have hs : ∀ᶠ x in 𝓝[≠] x₀, 0 < slope g x₀ x :=
    (hasDerivAt_iff_tendsto_slope.1 hg).eventually (lt_mem_nhds hσ)
  constructor
  · filter_upwards [nhdsWithin_mono x₀ (fun _ hx => ne_of_lt hx) hs, self_mem_nhdsWithin]
      with x hx hlt
    rw [slope_def_field, h0, sub_zero] at hx
    have hlt' : x - x₀ < 0 := sub_neg.2 hlt
    by_contra hc
    push Not at hc
    exact absurd hx (not_lt.2 (div_nonpos_of_nonneg_of_nonpos hc hlt'.le))
  · filter_upwards [nhdsWithin_mono x₀ (fun _ hx => ne_of_gt hx) hs, self_mem_nhdsWithin]
      with x hx hgt
    rw [slope_def_field, h0, sub_zero] at hx
    exact (div_pos_iff_of_pos_right (sub_pos.2 hgt)).1 hx

/-- The `d`-derivative of `G` along the trivial branch `a = 0` is `G' (0, 1)`. -/
private theorem hasDerivAt_trivialBranch {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ} {d₀ : ℝ}
    (hG : HasStrictFDerivAt G G' (0, d₀)) :
    HasDerivAt (fun d => G (0, d)) (G' (0, 1)) d₀ := by
  have hin : HasDerivAt (fun d : ℝ => ((0 : ℝ), d)) ((0 : ℝ), (1 : ℝ)) d₀ :=
    (hasDerivAt_const d₀ (0 : ℝ)).prodMk (hasDerivAt_id d₀)
  exact hG.hasFDerivAt.comp_hasDerivAt d₀ hin

/-- **Turing pattern branch and exchange of stability on the trivial branch.** Let mode `k`
be admissible (`0 < f_u k² - d_u k⁴`) with neutral diffusion `d₀ = d_n(k²)` and negative trace
there, and let `G` be a reduced bifurcation map for this mode: strictly differentiable at
`(0, d₀)` and equal on the trivial branch to the critical eigenvalue,
`G (0, d) = leadingEigenvalue (J - k² D(d))` for `d` near `d₀` (the output of a Lyapunov–Schmidt
reduction, assumed). Then the crossing is transversal (`0 < ∂_d G (0, d₀)`), a unique local
pattern branch `d = φ(a)` bifurcates from `(0, d₀)`, and the homogeneous state exchanges
stability there: its critical eigenvalue is negative for `d < d₀` and positive for `d > d₀`
near `d₀`. -/
theorem turing_patternBranch {J : Matrix (Fin 2) (Fin 2) ℝ} {du k d₀ : ℝ}
    (htr : J.trace - k ^ 2 * (du + d₀) < 0) (hk : 0 < J 0 0 * k ^ 2 - du * (k ^ 2) ^ 2)
    (hd₀ : d₀ = neutralDiffusion J du (k ^ 2)) {G : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ}
    (hG : HasStrictFDerivAt G G' (0, d₀))
    (hlin : ∀ᶠ d in 𝓝 d₀, G (0, d) = leadingEigenvalue (modeMatrix J du d k)) :
    0 < G' (0, 1) ∧
      (∃ φ : ℝ → ℝ, φ 0 = d₀ ∧ HasStrictDerivAt φ (-(G' (1, 0) / G' (0, 1))) 0 ∧
        ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), (p.1 * G p = 0 ↔ p.1 = 0 ∨ p.2 = φ p.1)) ∧
      (∀ᶠ d in 𝓝[<] d₀, G (0, d) < 0) ∧ ∀ᶠ d in 𝓝[>] d₀, 0 < G (0, d) := by
  obtain ⟨hzero, hderiv, hpos⟩ := leadingEigenvalue_crossing htr hk hd₀
  have hline := hasDerivAt_trivialBranch hG
  have hG0 : G (0, d₀) = 0 := hlin.self_of_nhds.trans hzero
  have hσ : G' (0, 1) = (du * (k ^ 2) ^ 2 - J 0 0 * k ^ 2) / (J.trace - k ^ 2 * (du + d₀)) :=
    hline.unique (hderiv.congr_of_eventuallyEq hlin)
  have hσpos : 0 < G' (0, 1) := hσ ▸ hpos
  exact ⟨hσpos, exists_patternBranch hG hG0 hσpos.ne',
    eventually_sign_of_hasDerivAt hline hG0 hσpos⟩

/-- **Direction and stability of the pattern branch (pitchfork).** Suppose the reduced map is
symmetric to second order, `G(a, d) = G(0, d) + a² H(a, d)` near `(0, d₀)` (for every critical
mode `n ≥ 1` the quadratic term of the reaction projects to zero on `cos(k_n x)` because
`∫₀ᴸ cos³(k_n x) dx = 0`, so `G` has no term linear in `a`; for odd `n` the reflection
`x ↦ L - x` even makes `G` even in `a`), with `H` continuous at `(0, d₀)`, `c = H(0, d₀) ≠ 0`,
and `H` differentiable in `a` with partial derivative `H_a` continuous at `(0, d₀)`. Let the
trivial branch cross transversally, `∂_d G(0, d₀) = σ > 0`, and let `φ` be the pattern branch of
`exists_patternBranch`. Then for small `a ≠ 0`:

* `c (φ(a) - d₀) < 0`: the branch bifurcates *supercritically* (into `d > d₀`, where the
  homogeneous state is unstable) iff `c < 0`, and subcritically iff `c > 0`;
* the branch equilibrium `a` of the reduced equation `ȧ = Φ(a, d) = a G(a, d)` at `d = φ(a)` has
  linearization `λ = ∂_a Φ(a, φ(a))` with `0 < c λ`: it is linearly stable (`λ < 0`) iff the
  bifurcation is supercritical (exchange of stability). -/
theorem patternBranch_direction_stability {G H Ha : ℝ × ℝ → ℝ} {φ : ℝ → ℝ} {d₀ σ : ℝ}
    (hφ0 : φ 0 = d₀) (hφc : ContinuousAt φ 0)
    (hzero : ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), (p.1 * G p = 0 ↔ p.1 = 0 ∨ p.2 = φ p.1))
    (hG0 : G (0, d₀) = 0) (hσ : HasDerivAt (fun d => G (0, d)) σ d₀) (hσpos : 0 < σ)
    (hsym : ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), G p = G (0, p.2) + p.1 ^ 2 * H p)
    (hH : ContinuousAt H (0, d₀)) (hc : H (0, d₀) ≠ 0)
    (hHa : ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), HasDerivAt (fun x => H (x, p.2)) (Ha p) p.1)
    (hHac : ContinuousAt Ha (0, d₀)) :
    ∀ᶠ a in 𝓝[≠] (0 : ℝ), H (0, d₀) * (φ a - d₀) < 0 ∧
      ∃ lam : ℝ, HasDerivAt (fun x => x * G (x, φ a)) lam a ∧ 0 < H (0, d₀) * lam := by
  set c := H (0, d₀) with hcdef
  have hp : Tendsto (fun a => (a, φ a)) (𝓝[≠] (0 : ℝ)) (𝓝 ((0 : ℝ), d₀)) := by
    have : Tendsto (fun a => (a, φ a)) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ), φ 0)) :=
      tendsto_id.prodMk_nhds hφc.tendsto
    rw [hφ0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hφt : Tendsto φ (𝓝[≠] (0 : ℝ)) (𝓝 d₀) := (continuous_snd.tendsto _).comp hp
  have hs : ∀ᶠ d in 𝓝 d₀, d ≠ d₀ → 0 < slope (fun d => G (0, d)) d₀ d :=
    eventually_nhdsWithin_iff.1
      ((hasDerivAt_iff_tendsto_slope.1 hσ).eventually (lt_mem_nhds hσpos))
  have hlimH : Tendsto (fun a => c * H (a, φ a)) (𝓝[≠] (0 : ℝ)) (𝓝 (c * c)) :=
    (hH.tendsto.comp hp).const_mul c
  have hlim : Tendsto (fun a => c * (2 * H (a, φ a) + a * Ha (a, φ a))) (𝓝[≠] (0 : ℝ))
      (𝓝 (c * (2 * c + 0 * Ha (0, d₀)))) :=
    (((hH.tendsto.comp hp).const_mul 2).add
      ((tendsto_id.mono_left nhdsWithin_le_nhds).mul (hHac.tendsto.comp hp))).const_mul c
  have hcc : 0 < c * c := mul_self_pos.2 hc
  have hs1 : ∀ᶠ a in 𝓝[≠] (0 : ℝ), 0 < c * H (a, φ a) := hlimH.eventually (lt_mem_nhds hcc)
  have hs2 : ∀ᶠ a in 𝓝[≠] (0 : ℝ), 0 < c * (2 * H (a, φ a) + a * Ha (a, φ a)) :=
    hlim.eventually (lt_mem_nhds (by nlinarith))
  filter_upwards [hp.eventually (eventually_eventually_nhds.2 hsym), hp.eventually hsym,
    hp.eventually hHa, hp.eventually hzero, hφt.eventually hs, hs1, hs2, self_mem_nhdsWithin]
    with a hsymN hsymA hHaA hzA hsA h1 h2 ha0
  have ha0' : a ≠ 0 := ha0
  have ha2 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha0'))
  have hGa : G (a, φ a) = 0 := (mul_eq_zero.1 (hzA.2 (Or.inr rfl))).resolve_left ha0'
  have hG0a : G (0, φ a) = -(a ^ 2 * H (a, φ a)) := by linarith
  have hcX : 0 < c * (a ^ 2 * H (a, φ a)) := by nlinarith [mul_pos ha2 h1]
  refine ⟨?_, ?_⟩
  · by_cases hφd : φ a = d₀
    · have h0' : G (0, φ a) = 0 := by rw [hφd, hG0]
      have hX : a ^ 2 * H (a, φ a) = 0 := by linarith
      rw [hX, mul_zero] at hcX
      exact absurd hcX (lt_irrefl 0)
    · have hsl := hsA hφd
      rw [slope_def_field, hG0, sub_zero] at hsl
      have hne : φ a - d₀ ≠ 0 := sub_ne_zero.2 hφd
      set sl := G (0, φ a) / (φ a - d₀) with hsldef
      have hs' : sl * (φ a - d₀) = G (0, φ a) := by
        rw [hsldef]
        field_simp
      have key : c * (φ a - d₀) * sl = -(c * (a ^ 2 * H (a, φ a))) := by
        have hre : c * (φ a - d₀) * sl = c * (sl * (φ a - d₀)) := by ring
        rw [hre, hs', hG0a]
        ring
      by_contra hcon
      push Not at hcon
      nlinarith [mul_nonneg hcon hsl.le]
  · refine ⟨a ^ 2 * (2 * H (a, φ a) + a * Ha (a, φ a)), ?_, ?_⟩
    · have hcont : Continuous fun x : ℝ => (x, φ a) := continuous_id.prodMk continuous_const
      have hev : (fun x => x * G (x, φ a)) =ᶠ[𝓝 a]
          fun x => x * (G (0, φ a) + x ^ 2 * H (x, φ a)) := by
        filter_upwards [(hcont.tendsto a).eventually hsymN] with x hx
        rw [hx]
      have hg := ((hasDerivAt_id a).mul
        (((hasDerivAt_pow 2 a).mul hHaA).const_add (G (0, φ a)))).congr_of_eventuallyEq hev
      convert hg using 1
      simp only [id, hG0a, Pi.mul_apply]
      ring
    · nlinarith

/-- **Supercritical Turing pattern branches are stable.** Combine `turing_patternBranch` with
`patternBranch_direction_stability`: for an admissible mode `k` (e.g. a Neumann mode `k_n`) at
its neutral diffusion `d₀`, a reduced map `G` (strictly differentiable, equal to the critical
eigenvalue on the trivial branch, reflection-symmetric to second order with coefficient
`c = H(0, d₀) ≠ 0`) has a local pattern branch `d = φ(a)` through `(0, d₀)` which, for small
amplitudes `a ≠ 0`, lies on the side `c (φ(a) - d₀) < 0` and has reduced linearization `λ` with
`0 < c λ`. In particular, if `c < 0` the branch exists for `d > d₀`, exactly where the
homogeneous state is unstable, and is linearly stable. -/
theorem turing_patternBranch_stability {J : Matrix (Fin 2) (Fin 2) ℝ} {du k d₀ : ℝ}
    (htr : J.trace - k ^ 2 * (du + d₀) < 0) (hk : 0 < J 0 0 * k ^ 2 - du * (k ^ 2) ^ 2)
    (hd₀ : d₀ = neutralDiffusion J du (k ^ 2)) {G H Ha : ℝ × ℝ → ℝ} {G' : ℝ × ℝ →L[ℝ] ℝ}
    (hG : HasStrictFDerivAt G G' (0, d₀))
    (hlin : ∀ᶠ d in 𝓝 d₀, G (0, d) = leadingEigenvalue (modeMatrix J du d k))
    (hsym : ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), G p = G (0, p.2) + p.1 ^ 2 * H p)
    (hH : ContinuousAt H (0, d₀)) (hc : H (0, d₀) ≠ 0)
    (hHa : ∀ᶠ p in 𝓝 ((0 : ℝ), d₀), HasDerivAt (fun x => H (x, p.2)) (Ha p) p.1)
    (hHac : ContinuousAt Ha (0, d₀)) :
    ∃ φ : ℝ → ℝ, φ 0 = d₀ ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), d₀), (p.1 * G p = 0 ↔ p.1 = 0 ∨ p.2 = φ p.1)) ∧
      (∀ᶠ d in 𝓝[<] d₀, G (0, d) < 0) ∧ (∀ᶠ d in 𝓝[>] d₀, 0 < G (0, d)) ∧
      ∀ᶠ a in 𝓝[≠] (0 : ℝ), H (0, d₀) * (φ a - d₀) < 0 ∧
        ∃ lam : ℝ, HasDerivAt (fun x => x * G (x, φ a)) lam a ∧ 0 < H (0, d₀) * lam := by
  obtain ⟨hσpos, ⟨φ, hφ0, hφd, hzero⟩, hleft, hright⟩ :=
    turing_patternBranch htr hk hd₀ hG hlin
  have hG0 : G (0, d₀) = 0 := hlin.self_of_nhds.trans (leadingEigenvalue_crossing htr hk hd₀).1
  exact ⟨φ, hφ0, hzero, hleft, hright,
    patternBranch_direction_stability hφ0 hφd.hasDerivAt.continuousAt hzero hG0
      (hasDerivAt_trivialBranch hG) hσpos hsym hH hc hHa hHac⟩

end MathlibExt.Biology.Dynamics.TuringBranches
