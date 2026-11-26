/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The ideal free distribution is evolutionarily stable

A single species of total density `M > 0` distributes over finitely many patches with
proportions `p` in the simplex; an individual in patch `i` earns `Vᵢ(pᵢ M)`, where every patch
payoff `Vᵢ` is strictly decreasing in the patch density (Fretwell and Lucas 1969). A
distribution `p*` is an ideal free distribution (IFD) if all occupied patches give the same
payoff `V*` and no unoccupied patch gives more: `Vᵢ(pᵢ* M) = V*` when `pᵢ* > 0` and
`Vᵢ(0) ≤ V*` when `pᵢ* = 0`. Cressman and Křivan (2006, Appendix A) proved that an IFD is an
evolutionarily stable strategy of the population game in the nonlinear sense: for every
distribution `p ≠ p*`, `∑ᵢ pᵢ* Vᵢ(pᵢ M) > ∑ᵢ pᵢ Vᵢ(pᵢ M)`.

Recorded here: the ESS inequality for every IFD, with strictly decreasing patch payoffs on
`[0, ∞)`; the patch ordering and the zeros `Kᵢ` of Cressman and Křivan are not needed for the
inequality and are omitted. A distribution over the patches is a point of the simplex, the
library's `MathlibExt.Biology.Dynamics.AsymmetricESS.IsMixed`
(`Domains.Biology.Dynamics.AsymmetricESS`).

Sources: S. D. Fretwell and H. L. Lucas Jr., "On territorial behavior and other factors
influencing habitat distribution in birds. I. Theoretical development", Acta Biotheor. 19 (1969)
16–36, doi:10.1007/BF01601953; R. Cressman and V. Křivan, "Migration dynamics for the ideal free
distribution", Am. Nat. 168 (2006) 384–397, doi:10.1086/506970, Appendix A.
-/
module

public import Batteries.Util.ProofWanted
public import Domains.Biology.Dynamics.AsymmetricESS
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Monotone.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.IdealFreeDistributionWanted

open MathlibExt.Biology.Dynamics.AsymmetricESS (IsMixed)

/-- **Ideal free distribution.** `p*` is an ideal free distribution for total density `M` and
patch payoffs `V`: it is a distribution over the patches (`IsMixed p*`: every `pᵢ* ≥ 0` and
`∑ pᵢ* = 1`), and there is a payoff `V*` with `Vᵢ(pᵢ* M) = V*` for every occupied patch
(`pᵢ* > 0`) and `Vᵢ(0) ≤ V*` for every unoccupied patch (`pᵢ* = 0`). -/
def IsIFD {ι : Type*} [Fintype ι] (M : ℝ) (V : ι → ℝ → ℝ) (ps : ι → ℝ) : Prop :=
  IsMixed ps ∧ ∃ Vs : ℝ, ∀ i, (0 < ps i → V i (ps i * M) = Vs) ∧ (ps i = 0 → V i 0 ≤ Vs)

/-- **The IFD is an ESS.** Let the total density be `M > 0` and let every patch payoff `Vᵢ` be
strictly decreasing on `[0, ∞)`. If `p*` is an ideal free distribution, then for every
distribution `p ≠ p*` over the patches (`IsMixed p`: every `pᵢ ≥ 0`, `∑ pᵢ = 1`),
`∑ᵢ pᵢ Vᵢ(pᵢ M) < ∑ᵢ pᵢ* Vᵢ(pᵢ M)`.

Sources: Cressman and Křivan (2006), Appendix A; Fretwell and Lucas (1969). -/
public theorem_wanted ifd_isESS {ι : Type*} [Fintype ι] (M : ℝ) (hM : 0 < M) (V : ι → ℝ → ℝ)
    (hV : ∀ i, StrictAntiOn (V i) (Set.Ici 0)) (ps : ι → ℝ) (hps : IsIFD M V ps) (p : ι → ℝ)
    (hp : IsMixed p) (hne : p ≠ ps) :
    ∑ i, p i * V i (p i * M) < ∑ i, ps i * V i (p i * M)

end WantedExt.Biology.Ecology.IdealFreeDistributionWanted
