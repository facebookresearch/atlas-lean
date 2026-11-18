/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Sherrington–Kirkpatrick model and the Parisi functional

The Sherrington–Kirkpatrick (SK) model at inverse temperature `β` and external field `h` has
configurations `σ ∈ {-1, 1}^N` and the random Hamiltonian
`H_N(σ) = -(β / √N) ∑_{i < j} g_{ij} σ_i σ_j` (Talagrand's (1.1))
with independent standard Gaussian couplings `g_{ij}`. Its free energy is
`F_N = (1 / N) E log ∑_σ exp(H_N(σ) + h ∑_i σ_i)`: following Talagrand's (1.14), no minus sign
is put in front of `H_N` in the exponent. Since `g ↦ -g` preserves the law of the couplings, the
law of the free energy does not depend on the sign in (1.1).

The Parisi functional `P_k(m, q)` of a mixed Hamiltonian with covariance function `ξ` is built
from parameters `0 = m_0 ≤ m_1 ≤ ⋯ ≤ m_k = 1` and `0 = q_0 ≤ q_1 ≤ ⋯ ≤ q_{k+1} = 1`: with
independent centred Gaussians `z_p` of variance `ξ'(q_{p+1}) - ξ'(q_p)`,
`X_{k+1} = log ch(h + ∑_{p ≤ k} z_p)`, `X_ℓ = (1 / m_ℓ) log E_ℓ exp(m_ℓ X_{ℓ+1})` (`E_ℓ X_{ℓ+1}`
when `m_ℓ = 0`), and `P_k(m, q) = log 2 + X_0 - ½ ∑_{1 ≤ ℓ ≤ k} m_ℓ (θ(q_{ℓ+1}) - θ(q_ℓ))`
with `θ(q) = q ξ'(q) - ξ(q)`. For the SK model `ξ(x) = β² x² / 2`.

Since `X_{ℓ+1}` depends on `z_0, …, z_ℓ` only through `h + ∑_{p ≤ ℓ} z_p`, the recursion is
computed here on functions of one real variable: `f_{k+1}(y) = log ch y` and
`f_ℓ(y) = (1 / m_ℓ) log E exp(m_ℓ f_{ℓ+1}(y + z_ℓ))`, so that `X_0 = f_0(h)`.

The Parisi formula and Guerra's bound are recorded in `MathlibExt.Probability.ParisiFormulaWanted`.

## References

* M. Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), 221–263, (1.1), (1.6)–(1.14).
-/

@[expose] public section

namespace MathlibExt.Probability.SherringtonKirkpatrick

open MeasureTheory ProbabilityTheory

/-- **Ising spin of a Boolean.** `true ↦ 1`, `false ↦ -1`: a configuration `σ : Fin N → Bool`
encodes a point of `{-1, 1}^N`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- **Sherrington–Kirkpatrick Hamiltonian** (Talagrand, *The Parisi formula*, Ann. of Math. 163
(2006), (1.1)). For couplings `g` and a configuration `σ ∈ {-1, 1}^N`,
`H_N(σ) = -(β / √N) ∑_{i < j} g_{ij} σ_i σ_j`. -/
noncomputable def hamiltonian (β : ℝ) (N : ℕ) (g : Fin N → Fin N → ℝ) (σ : Fin N → Bool) : ℝ :=
  -(β / Real.sqrt N) * ∑ i, ∑ j, if i < j then g i j * spin (σ i) * spin (σ j) else 0

/-- **Law of the couplings.** All `g_{ij}` are independent standard Gaussian variables (only
those with `i < j` enter the Hamiltonian). -/
noncomputable def couplingLaw (N : ℕ) : Measure (Fin N → Fin N → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

/-- **Free energy of the SK model** (Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006),
left-hand side of (1.14) before the limit). `F_N = (1 / N) E log ∑_σ exp(H_N(σ) + h ∑_i σ_i)`. -/
noncomputable def freeEnergy (β h : ℝ) (N : ℕ) : ℝ :=
  (1 / N) * ∫ g, Real.log (∑ σ : Fin N → Bool,
    Real.exp (hamiltonian β N g σ + h * ∑ i, spin (σ i))) ∂couplingLaw N

/-- **One step of the Parisi recursion** (Talagrand, *The Parisi formula*, Ann. of Math. 163
(2006), (1.10)). Given the next function `f`, a variance `v` and a parameter `m`, it returns
`y ↦ (1 / m) log E exp(m f(y + z))` for `z ~ N(0, v)`, and `y ↦ E f(y + z)` when `m = 0`. -/
noncomputable def parisiStep (v m : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  if m = 0 then ∫ z, f (y + z) ∂gaussianReal 0 v.toNNReal
  else 1 / m * Real.log (∫ z, Real.exp (m * f (y + z)) ∂gaussianReal 0 v.toNNReal)

/-- **The Parisi recursion** (Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006),
(1.9)–(1.10)). `parisiRecursion ξ' k m q j` is the function `f_{k+1-j}`: `f_{k+1} = log ch`
and `f_ℓ = parisiStep (ξ'(q_{ℓ+1}) - ξ'(q_ℓ)) m_ℓ f_{ℓ+1}` for `ℓ = k, …, 0`. -/
noncomputable def parisiRecursion (ξ' : ℝ → ℝ) (k : ℕ) (m q : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun y => Real.log (Real.cosh y)
  | j + 1 => parisiStep (ξ' (q (k - j + 1)) - ξ' (q (k - j))) (m (k - j))
      (parisiRecursion ξ' k m q j)

/-- **Admissible Parisi parameters** (Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006),
(1.6)–(1.7)). `k ≥ 1`, `0 = m_0 ≤ m_1 ≤ ⋯ ≤ m_k = 1` and `0 = q_0 ≤ q_1 ≤ ⋯ ≤ q_{k+1} = 1`;
values of `m` and `q` at larger indices are irrelevant. -/
def IsParisiParameter (k : ℕ) (m q : ℕ → ℝ) : Prop :=
  1 ≤ k ∧ m 0 = 0 ∧ m k = 1 ∧ (∀ ℓ < k, m ℓ ≤ m (ℓ + 1)) ∧
    q 0 = 0 ∧ q (k + 1) = 1 ∧ ∀ ℓ ≤ k, q ℓ ≤ q (ℓ + 1)

/-- **The Parisi functional** (Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006),
(1.11)–(1.12)). For a covariance function `ξ`, field `h` and parameters `k, m, q`,
`P_k(m, q) = log 2 + X_0 - ½ ∑_{1 ≤ ℓ ≤ k} m_ℓ (θ(q_{ℓ+1}) - θ(q_ℓ))`, where
`X_0 = f_0(h)` is given by the Parisi recursion with `ξ'` and `θ(q) = q ξ'(q) - ξ(q)`. -/
noncomputable def parisiFunctional (ξ : ℝ → ℝ) (h : ℝ) (k : ℕ) (m q : ℕ → ℝ) : ℝ :=
  let θ : ℝ → ℝ := fun x => x * deriv ξ x - ξ x
  Real.log 2 + parisiRecursion (deriv ξ) k m q (k + 1) h -
    1 / 2 * ∑ ℓ ∈ Finset.Icc 1 k, m ℓ * (θ (q (ℓ + 1)) - θ (q ℓ))

/-- **Covariance function of the SK model** (Talagrand, *The Parisi formula*, Ann. of Math. 163
(2006), Section 1). `ξ(x) = β² x² / 2`, so that `E H_N(σ¹) H_N(σ²) = N ξ(R_{1,2}) - β² / 2`,
where `R_{1,2}` is the overlap: condition (1.3) holds with `c(N) = β² / (2N)`. -/
noncomputable def skCovariance (β : ℝ) (x : ℝ) : ℝ := β ^ 2 * x ^ 2 / 2

/-- **Replica-symmetric parameters are admissible.** For every `q₁ ∈ [0, 1]`, `k = 1`,
`m = (0, 1)` and `q = (0, q₁, 1)` satisfy (1.6)–(1.7) (Talagrand, *The Parisi formula*, Ann. of
Math. 163 (2006); `k = 1` is the "high temperature" case discussed after Theorem 1.1). -/
theorem isParisiParameter_replicaSymmetric {q₁ : ℝ} (h0 : 0 ≤ q₁) (h1 : q₁ ≤ 1) :
    IsParisiParameter 1 (fun ℓ => if ℓ = 0 then 0 else 1)
      (fun ℓ => if ℓ = 0 then 0 else if ℓ = 1 then q₁ else 1) := by
  refine ⟨le_rfl, by simp, by simp, fun ℓ hℓ => ?_, by simp, by simp, fun ℓ hℓ => ?_⟩
  · interval_cases ℓ; simp
  · interval_cases ℓ <;> simp [h0, h1]

end MathlibExt.Probability.SherringtonKirkpatrick
