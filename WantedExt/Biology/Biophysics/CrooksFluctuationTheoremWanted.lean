/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Crooks entropy-production fluctuation theorem

Crooks (1999) considers a system with stochastic, Markovian dynamics driven by a time-dependent
protocol and coupled to a heat bath at inverse temperature `β`. Here the dynamics run in discrete
time on a finite state space `σ`: a path is `x = (x_0, …, x_n)`, the forward process starts from
the density `ρ_F` and uses the transition matrices `M_0, …, M_{n-1}` of the forward protocol,
and the reverse process starts from `ρ_R` and uses the matrices `M^R_0, …, M^R_{n-1}` of the
time-reversed protocol. The time reversal of a path is `x̄(-t)`, `(x̄_n, …, x̄_0)`, where
`x ↦ x̄` is an involution of `σ` (reversing momenta). The heat absorbed from the bath is a
functional of the path and of the protocol: `Q_F[x]` under the forward protocol and `Q_R[y]`
under the time-reversed protocol, odd under time reversal in the sense
`Q_R[x̄(-t)] = -Q_F[x]`. The dynamics are **microscopically reversible** (Eq. (5)):

  `P[x | λ] = e^{-β Q_F[x]} P[x̄(-t) | λ̄]`,

relating the conditional path probabilities of the two protocols. For arbitrary positive initial
densities `ρ_F`, `ρ_R`, as here, the statements use the path functionals
`ω_F[x] = ln ρ_F(x_0) - ln ρ_R(x̄_n) - β Q_F[x]` of the forward process and
`ω_R[y] = ln ρ_R(y_0) - ln ρ_F(ȳ_n) - β Q_R[y]` of the reverse process. By microscopic
reversibility, `ω_F[x]` agrees with the log-ratio `ln (P_F[x] / P_R[x̄(-t)])` of the path
probabilities where these are positive (they vanish together), and extends it to the paths of
probability zero in both directions, where the ratio is undefined: transitions need only be
nonnegative, and with identity transitions every path that changes state is such a path.
`ω_F` is Crooks's entropy production (Eq. (6)) when the initial density of the reverse process
is the time reversal of the final density of the forward process. The fluctuation theorem
(Eq. (2)) is `P_F(+ω) = e^{ω} P_R(-ω)` for the distributions of `ω_F` and `ω_R`.
When both processes start in equilibrium (`ρ_F ∝ e^{-β E_0}`, `ρ_R(x̄) ∝ e^{-β E_1(x)}`),
`ω_F = β (W - ΔF)` with the work `W = E_1(x_n) - E_0(x_0) - Q_F[x]` (Eq. (10)), and summing the
theorem gives the nonequilibrium work relation `⟨e^{-β W}⟩ = e^{-β ΔF}` (Eq. (3)). Canonical
initial densities do not make the final forward density that of `E_1` (identity transitions keep
`ρ_F`), so `β (W - ΔF)` is the entropy production of Eq. (6) only when the forward process ends
in the equilibrium of `E_1`, as in the source, where the system relaxes to it after the driving;
the work relation holds without this.
The continuous-time version and the steady-state case of the source are not stated.

Sources: G. E. Crooks, "Entropy production fluctuation theorem and the nonequilibrium work
relation for free energy differences", Phys. Rev. E 60 (1999) 2721–2726, Eqs. (2), (3), (5), (6)
and (10) (arXiv:cond-mat/9901352).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace WantedExt.Biology.Biophysics.CrooksFluctuationTheoremWanted

open Finset

variable {σ : Type*} [Fintype σ] [DecidableEq σ] {n : ℕ}

/-- A path of `n` steps: the states `x_0, …, x_n`. -/
abbrev Path (σ : Type*) (n : ℕ) : Type _ := Fin (n + 1) → σ

/-- The time reversal `x̄(-t)` of a path: `(x̄_n, …, x̄_0)` for the involution `bar` of states. -/
def reversePath (bar : σ → σ) (x : Path σ n) : Path σ n :=
  fun j => bar (x (Fin.rev j))

/-- The path weight `∏_i M_i(x_i, x_{i+1})` of the path `x` under the matrices `M_0, …, M_{n-1}`
of a protocol, for arbitrary real entries. When every `M_i` is stochastic (nonnegative entries,
each row summing to `1`), it is the conditional probability of following `x` from `x_0`. -/
def condPathProb (M : Fin n → σ → σ → ℝ) (x : Path σ n) : ℝ :=
  ∏ i : Fin n, M i (x i.castSucc) (x i.succ)

/-- The path weight `ρ(x_0) ∏_i M_i(x_i, x_{i+1})` of the path `x` for the initial weights `ρ`
and the matrices `M`, for arbitrary real entries. When `ρ` is a probability vector and every `M_i`
is stochastic, it is the probability of `x` for the process with initial law `ρ` and transition
matrices `M`. -/
def pathProb (ρ : σ → ℝ) (M : Fin n → σ → σ → ℝ) (x : Path σ n) : ℝ :=
  ρ (x 0) * condPathProb M x

/-- The path functional `ω[x] = ln ρ(x_0) - ln ρ'(x̄_n) - β Q[x]` of a path of the process with
initial density `ρ` and heat functional `Q` (that of its own protocol), where `ρ'` is the initial
density of the other process; `ρ` and `ρ'` are arbitrary positive laws. Under microscopic
reversibility (`MicroReversible`), it agrees with the log-ratio `ln (P[x] / P'[x̄(-t)])` of the
probability of `x` under this process and that of its time reversal under the other on their
common positive support (the two probabilities vanish together), and extends it to the paths
where both vanish and the ratio is undefined: transitions need only be nonnegative, and with
identity transitions every path that changes state is such a path. It is Crooks's entropy
production (Eq. (6)) when `ρ'` is the time reversal of the final density of this process. -/
noncomputable def entropyProduction (bar : σ → σ) (ρ ρ' : σ → ℝ) (β : ℝ) (Q : Path σ n → ℝ)
    (x : Path σ n) : ℝ :=
  Real.log (ρ (x 0)) - Real.log (ρ' (bar (x (Fin.last n)))) - β * Q x

/-- The setting of Crooks (1999): `bar` is an involution of the states; the initial densities
`ρ_F` and `ρ_R` are positive probability vectors; the transition matrices `M` (forward
protocol) and `MR` (time-reversed protocol) are stochastic; the heats `QF` (forward protocol)
and `QR` (time-reversed protocol) satisfy `QR[x̄(-t)] = -QF[x]` for every path `x`; and the
dynamics are microscopically reversible:
`∏_i M_i(x_i, x_{i+1}) = e^{-β QF[x]} ∏_i MR_i(x̄_{n-i}, x̄_{n-i-1})` for every path `x`. -/
structure MicroReversible (bar : σ → σ) (β : ℝ) (ρF ρR : σ → ℝ) (M MR : Fin n → σ → σ → ℝ)
    (QF QR : Path σ n → ℝ) : Prop where
  bar_bar : ∀ s, bar (bar s) = s
  ρF_pos : ∀ s, 0 < ρF s
  ρR_pos : ∀ s, 0 < ρR s
  sum_ρF : ∑ s, ρF s = 1
  sum_ρR : ∑ s, ρR s = 1
  M_nonneg : ∀ i s s', 0 ≤ M i s s'
  MR_nonneg : ∀ i s s', 0 ≤ MR i s s'
  sum_M : ∀ i s, ∑ s', M i s s' = 1
  sum_MR : ∀ i s, ∑ s', MR i s s' = 1
  heat_reverse : ∀ x, QR (reversePath bar x) = -QF x
  micro_rev : ∀ x,
    condPathProb M x = Real.exp (-β * QF x) * condPathProb MR (reversePath bar x)

/-- **Crooks fluctuation theorem.** Assume the setting `MicroReversible` (`bar` an involution;
positive initial probability vectors `ρ_F`, `ρ_R`; stochastic matrices `M`, `MR`; forward and
reverse heats with `QR[x̄(-t)] = -QF[x]`; microscopic reversibility with `QF`). Then for every
real `ω`, the probabilities `P_F(ω) = ∑_{x : ω_F[x] = ω} P_F[x]` and
`P_R(-ω) = ∑_{y : ω_R[y] = -ω} P_R[y]` satisfy `P_F(+ω) = e^{ω} P_R(-ω)` (Crooks 1999, Eq. (2)),
where `ω_F[x] = ln ρ_F(x_0) - ln ρ_R(x̄_n) - β QF[x]` and
`ω_R[y] = ln ρ_R(y_0) - ln ρ_F(ȳ_n) - β QR[y]` are the path functionals of the forward and
reverse processes (`entropyProduction`), for arbitrary positive initial laws `ρ_F`, `ρ_R`. Each
agrees with the log-ratio of the probabilities of a path and of its time reversal on their common
positive support, and extends it to the paths where both probabilities vanish. They are Crooks's
entropy productions when `ρ_R` is the time reversal of the final density of the forward process
(and `ρ_F` that of the reverse process), as in the source.

Source: G. E. Crooks, "Entropy production fluctuation theorem and the nonequilibrium work
relation for free energy differences", Phys. Rev. E 60 (1999) 2721–2726, Eq. (2)
(arXiv:cond-mat/9901352). -/
theorem_wanted fluctuation_theorem (bar : σ → σ) (β : ℝ) (ρF ρR : σ → ℝ)
    (M MR : Fin n → σ → σ → ℝ) (QF QR : Path σ n → ℝ)
    (h : MicroReversible bar β ρF ρR M MR QF QR) (ω : ℝ) :
    ∑ x ∈ univ.filter (fun x => entropyProduction bar ρF ρR β QF x = ω), pathProb ρF M x =
      Real.exp ω *
        ∑ y ∈ univ.filter (fun y => entropyProduction bar ρR ρF β QR y = -ω), pathProb ρR MR y

/-- **Nonequilibrium work relation.** Assume the setting `MicroReversible` with `β > 0` and
canonical initial densities: `ρ_F(s) = e^{-β E_0(s)} / Z_0` and
`ρ_R(bar s) = e^{-β E_1(s)} / Z_1` for all `s`, with `Z_0 = ∑_s e^{-β E_0(s)}` and
`Z_1 = ∑_s e^{-β E_1(s)}`. Let the work be `W[x] = E_1(x_n) - E_0(x_0) - QF[x]` and
`ΔF = -β⁻¹ ln Z_1 + β⁻¹ ln Z_0`. Then the forward path functional
`ω_F[x] = ln ρ_F(x_0) - ln ρ_R(x̄_n) - β QF[x]` (`entropyProduction` with the forward heat `QF`,
which agrees with the forward path log-ratio where that is defined) is `β (W[x] - ΔF)` for every
path (Crooks 1999, Eq. (10)), and `∑_x P_F[x] e^{-β W[x]} = e^{-β ΔF}` (Eq. (3)). Canonical
initial densities do not make the final density of the forward process that of `E_1` (identity
transitions keep `ρ_F`), so `ω_F` is the entropy production of Eq. (6) only when the forward
process ends in the equilibrium of `E_1`, as in the source, where the system relaxes to it after
the driving; the work relation holds without this.

Source: G. E. Crooks, "Entropy production fluctuation theorem and the nonequilibrium work
relation for free energy differences", Phys. Rev. E 60 (1999) 2721–2726, Eqs. (10) and (3)
(arXiv:cond-mat/9901352). -/
theorem_wanted work_relation (bar : σ → σ) (β : ℝ) (hβ : 0 < β) (ρF ρR : σ → ℝ)
    (M MR : Fin n → σ → σ → ℝ) (QF QR : Path σ n → ℝ)
    (h : MicroReversible bar β ρF ρR M MR QF QR) (E₀ E₁ : σ → ℝ)
    (hρF : ∀ s, ρF s = Real.exp (-β * E₀ s) / ∑ s', Real.exp (-β * E₀ s'))
    (hρR : ∀ s, ρR (bar s) = Real.exp (-β * E₁ s) / ∑ s', Real.exp (-β * E₁ s')) :
    (∀ x : Path σ n, entropyProduction bar ρF ρR β QF x =
      β * ((E₁ (x (Fin.last n)) - E₀ (x 0) - QF x) -
        (-β⁻¹ * Real.log (∑ s', Real.exp (-β * E₁ s')) +
          β⁻¹ * Real.log (∑ s', Real.exp (-β * E₀ s'))))) ∧
      ∑ x : Path σ n, pathProb ρF M x * Real.exp (-β * (E₁ (x (Fin.last n)) - E₀ (x 0) - QF x)) =
        Real.exp (-β * (-β⁻¹ * Real.log (∑ s', Real.exp (-β * E₁ s')) +
          β⁻¹ * Real.log (∑ s', Real.exp (-β * E₀ s'))))

end WantedExt.Biology.Biophysics.CrooksFluctuationTheoremWanted
