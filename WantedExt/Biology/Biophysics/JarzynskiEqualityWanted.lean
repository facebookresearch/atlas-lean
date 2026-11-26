/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Jarzynski equality for isolated Hamiltonian systems

Let `H_λ(q, p)`, `0 ≤ λ ≤ 1`, be a family of Hamiltonians on the phase space `ℝ^d × ℝ^d`, with
partition functions `Z_λ = ∫ e^{-β H_λ}` and free energies `F_λ = -β⁻¹ ln Z_λ`. Switch `λ` from
`0` to `1` at the constant rate `1/t_s`, and let `φ_t` be the flow of the time-dependent
Hamiltonian vector field `X_t = (∂_p H_{t/t_s}, -∂_q H_{t/t_s})`. The work along the trajectory
from `z₀` is `W(z₀) = ∫_0^{t_s} (1/t_s) ∂_λ H_{t/t_s}(φ_t z₀) dt` (Jarzynski 1997, Eq. (3)).
Jarzynski's equality for the isolated system (no heat bath during switching) is
`⟨e^{-β W}⟩ = e^{-β ΔF} = Z_1 / Z_0`, the average being over initial conditions drawn from the
canonical density `Z_0⁻¹ e^{-β H_0}` (Eq. (2a)). Its proof combines Liouville's theorem (the
flow preserves phase-space volume) with the energy balance `W(z₀) = H_1(φ_{t_s} z₀) - H_0(z₀)`;
the source's density argument is replaced here by the equivalent change of variables
`z = φ_{t_s} z₀`. This module states the two prerequisite wanted lemmas (`measurePreserving_flow`
and `work_eq`); the Jarzynski equality itself is tracked as a planned roadmap page depending on
both prerequisites.

The flow is taken as data: for every `z₀` a solution on `[0, t_s]` starting at `z₀`, and every
point at every time `t ∈ [0, t_s]` lies on such a trajectory. The second condition (global
existence backwards in time) is needed for the flow maps to be onto: for `H(q, p) = -p q³`
every forward trajectory exists, but the time-`t` map is not onto. The reservoir and
Nosé–Hoover cases of the source are not stated (the stochastic case is the Crooks theorem).

Sources: C. Jarzynski, "Nonequilibrium equality for free energy differences", Phys. Rev. Lett.
78 (1997) 2690–2693, Eqs. (2a), (3) and the isolated-system argument (arXiv:cond-mat/9610209).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving

@[expose] public section

namespace WantedExt.Biology.Biophysics.JarzynskiEqualityWanted

open MeasureTheory

variable {d : ℕ}

/-- The phase space `ℝ^d × ℝ^d` of positions `q` and momenta `p`. -/
abbrev PhaseSpace (d : ℕ) : Type := (Fin d → ℝ) × (Fin d → ℝ)

/-- The Hamiltonian vector field `(∂_p H_λ, -∂_q H_λ)` at `λ = t / t_s`, for the switching time
`t_s`. -/
noncomputable def hamiltonianField (H : ℝ → PhaseSpace d → ℝ) (ts t : ℝ) (z : PhaseSpace d) :
    PhaseSpace d :=
  (fun i => fderiv ℝ (fun p => H (t / ts) (z.1, p)) z.2 (Pi.single i 1),
    fun i => -fderiv ℝ (fun q => H (t / ts) (q, z.2)) z.1 (Pi.single i 1))

/-- `φ` is a flow of the switched Hamiltonian system on `[0, t_s]`: for every `z₀`,
`t ↦ φ t z₀` solves `ż = X_t(z)` on `[0, t_s]` with `φ 0 z₀ = z₀`, and every point at every
time `t ∈ [0, t_s]` is reached by such a trajectory. -/
def IsFlow (H : ℝ → PhaseSpace d → ℝ) (ts : ℝ) (φ : ℝ → PhaseSpace d → PhaseSpace d) : Prop :=
  (∀ z₀, φ 0 z₀ = z₀ ∧ ∀ t ∈ Set.Icc 0 ts,
    HasDerivWithinAt (fun s => φ s z₀) (hamiltonianField H ts t (φ t z₀)) (Set.Icc 0 ts) t) ∧
  ∀ t ∈ Set.Icc 0 ts, Function.Surjective (φ t)

/-- The partition function `Z_λ = ∫ e^{-β H_λ(z)} dz`. -/
noncomputable def partitionFunction (H : ℝ → PhaseSpace d → ℝ) (β l : ℝ) : ℝ :=
  ∫ z, Real.exp (-β * H l z)

/-- The work `W(z₀) = ∫_0^{t_s} (1/t_s) ∂_λ H_{t/t_s}(φ_t z₀) dt` along the trajectory from
`z₀` (Jarzynski 1997, Eq. (3)). -/
noncomputable def work (H : ℝ → PhaseSpace d → ℝ) (ts : ℝ)
    (φ : ℝ → PhaseSpace d → PhaseSpace d) (z₀ : PhaseSpace d) : ℝ :=
  ∫ t in (0 : ℝ)..ts, (1 / ts) * deriv (fun l => H l (φ t z₀)) (t / ts)

/-- The standing hypotheses: `(λ, z) ↦ H_λ(z)` is `C²`, `β > 0`, `t_s > 0`, `φ` is a flow of
the switched Hamiltonian system on `[0, t_s]` (`IsFlow`), and `e^{-β H_0}` and `e^{-β H_1}` are
integrable. -/
structure Hypotheses (H : ℝ → PhaseSpace d → ℝ) (β ts : ℝ)
    (φ : ℝ → PhaseSpace d → PhaseSpace d) : Prop where
  contDiff : ContDiff ℝ 2 (fun x : ℝ × PhaseSpace d => H x.1 x.2)
  β_pos : 0 < β
  ts_pos : 0 < ts
  isFlow : IsFlow H ts φ
  integrable_zero : Integrable (fun z => Real.exp (-β * H 0 z))
  integrable_one : Integrable (fun z => Real.exp (-β * H 1 z))

/-- **Liouville's theorem** for the switched Hamiltonian flow (Jarzynski 1997, isolated case).
Under the standing hypotheses (`Hypotheses`: `H` is `C²`, `β > 0`, `t_s > 0`, `φ` a flow of the
switched Hamiltonian system on `[0, t_s]`, and integrable `e^{-β H_0}`, `e^{-β H_1}`), for every
`t ∈ [0, t_s]` the map `φ t` preserves Lebesgue measure on `ℝ^d × ℝ^d`.

Source: Jarzynski (1997), isolated-system argument. -/
theorem_wanted measurePreserving_flow (H : ℝ → PhaseSpace d → ℝ) (β ts : ℝ)
    (φ : ℝ → PhaseSpace d → PhaseSpace d) (h : Hypotheses H β ts φ) (t : ℝ)
    (ht : t ∈ Set.Icc 0 ts) :
    MeasurePreserving (φ t) volume volume

/-- **Energy balance** (Jarzynski 1997, isolated case). Under the standing hypotheses
(`Hypotheses`), for every initial point `z₀` the work equals the change of energy:
`W(z₀) = H_1(φ_{t_s} z₀) - H_0(z₀)`.

Source: Jarzynski (1997), isolated-system argument. -/
theorem_wanted work_eq (H : ℝ → PhaseSpace d → ℝ) (β ts : ℝ)
    (φ : ℝ → PhaseSpace d → PhaseSpace d) (h : Hypotheses H β ts φ) (z₀ : PhaseSpace d) :
    work H ts φ z₀ = H 1 (φ ts z₀) - H 0 z₀

end WantedExt.Biology.Biophysics.JarzynskiEqualityWanted
