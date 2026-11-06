/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Onsager's 2D Ising phase transition

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.IsingPhaseTransition` — ising_2d_phase_transition (manifest `manifests/problems/ising_2d_phase_transition.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.IsingPhaseTransitionWanted` namespace. Mathematical
statements are unchanged. Source: L. Onsager, *Crystal statistics I*, Phys. Rev. 65 (1944). Knill, §158.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.IsingPhaseTransitionWanted
namespace Analysis.IsingPhaseTransition

/-!
# Onsager's 2D Ising phase transition

`ising_2d_phase_transition` (Onsager 1944): the thermodynamic-limit free energy
of the zero-field ferromagnetic square-lattice Ising model exists for every
inverse temperature and is non-analytic at a positive critical point. Trusted
helpers (`isingEnergy`, `isingPartitionFunction`, `finiteIsingFreeEnergy`, …)
are non-holes. Mathlib has no statistical-mechanics / Ising machinery.
Category-(b) candidate from §158 of the Knill survey.
-/

open Filter
open scoped BigOperators Topology

/-- **Sites of the periodic square lattice.** For a positive integer $L$, the sites of the
periodic $L \times L$ square lattice are the pairs $(i, j)$ with
$i, j \in \mathbb{Z}/L\mathbb{Z}$. -/
abbrev IsingSite (L : ℕ) [NeZero L] : Type := ZMod L × ZMod L

/-- **Numerical value of a spin.** A spin, recorded as a Boolean, has the real value $1$ if it is
true and $-1$ if it is false. -/
def spinValue (b : Bool) : ℝ := if b then 1 else -1

/-- **Right neighbour.** For a positive integer $L$, the right neighbour of a site $(i, j)$ of
the periodic $L \times L$ square lattice is $(i + 1, j)$, with addition in
$\mathbb{Z}/L\mathbb{Z}$. -/
def rightNeighbour {L : ℕ} [NeZero L] (p : IsingSite L) : IsingSite L :=
  ((p.1 + 1 : ZMod L), p.2)

/-- **Upward neighbour.** For a positive integer $L$, the upward neighbour of a site $(i, j)$ of
the periodic $L \times L$ square lattice is $(i, j + 1)$, with addition in
$\mathbb{Z}/L\mathbb{Z}$. -/
def upNeighbour {L : ℕ} [NeZero L] (p : IsingSite L) : IsingSite L :=
  (p.1, (p.2 + 1 : ZMod L))

/-- **Energy of an Ising configuration.** For a positive integer $L$, let $\sigma$ be a spin
configuration on the periodic $L \times L$ square lattice, assigning to each site $p$ a spin
$\sigma_p \in \{1, -1\}$. Its energy in the zero-field ferromagnetic Ising model with unit
coupling is

$$H_L(\sigma) = -\sum_p \left(\sigma_p \sigma_{p + e_1} + \sigma_p \sigma_{p + e_2}\right),$$

where $p$ runs over all sites, and $p + e_1$ and $p + e_2$ are obtained from $p$ by adding $1$
modulo $L$ to its first and to its second coordinate respectively. -/
noncomputable def isingEnergy (L : ℕ) [NeZero L] (σ : IsingSite L → Bool) : ℝ :=
  -((∑ p : IsingSite L, spinValue (σ p) * spinValue (σ (rightNeighbour p))) +
      ∑ p : IsingSite L, spinValue (σ p) * spinValue (σ (upNeighbour p)))

/-- **Ising partition function.** For a positive integer $L$ and real $\beta$, the partition
function of the Ising model on the periodic $L \times L$ square lattice at inverse temperature
$\beta$ is $Z_L(\beta) = \sum_\sigma e^{-\beta H_L(\sigma)}$, where $\sigma$ runs over all spin
configurations on the lattice and $H_L(\sigma)$ is the Ising energy of $\sigma$. -/
noncomputable def isingPartitionFunction (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  ∑ σ : IsingSite L → Bool, Real.exp (-β * isingEnergy L σ)

/-- **Finite-volume Ising free energy density.** For a positive integer $L$ and real $\beta$, the
free energy density of the Ising model on the periodic $L \times L$ square lattice is
$\log Z_L(\beta) / L^2$, where $Z_L(\beta)$ is the partition function at inverse temperature
$\beta$.

No factor $-1/\beta$ is included. -/
noncomputable def finiteIsingFreeEnergy (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  Real.log (isingPartitionFunction L β) / (L : ℝ) ^ 2

/-- **Ising free energy density along side lengths $n + 1$.** For a natural number $n$ and real
$\beta$, this is the finite-volume free energy density of the Ising model on the periodic
$(n + 1) \times (n + 1)$ square lattice at inverse temperature $\beta$, namely
$\log Z_{n+1}(\beta) / (n + 1)^2$, where $Z_{n+1}(\beta)$ is the partition function of that
lattice at inverse temperature $\beta$. -/
noncomputable def finiteIsingFreeEnergySeq (n : ℕ) (β : ℝ) : ℝ :=
  finiteIsingFreeEnergy (n + 1) β

/- **Onsager's 2D Ising phase transition.** The thermodynamic-limit free
energy exists for all `β` and is non-analytic at some positive `βc`. -/
/-- **Onsager's phase transition for the two-dimensional Ising model.** For a positive integer $L$
and real $\beta$, let $Z_L(\beta)$ be the partition function of the zero-field ferromagnetic Ising
model on the periodic $L \times L$ square lattice at inverse temperature $\beta$. There exist a
function $F : \mathbb{R} \to \mathbb{R}$ and a real number $\beta_c > 0$ such that, for every real
$\beta$, $\log Z_{n+1}(\beta) / (n+1)^2$ converges to $F(\beta)$ as $n \to \infty$, and $F$ is not
real analytic at $\beta_c$.

Source: L. Onsager, *Crystal statistics I*, Phys. Rev. 65 (1944). Knill, §158. Via leanprover/lean-eval@38361be, problem `ising_2d_phase_transition`. -/
public theorem_wanted ising_2d_phase_transition :
    ∃ (F : ℝ → ℝ) (βc : ℝ),
      0 < βc ∧
        (∀ β : ℝ,
          Tendsto (fun n : ℕ => finiteIsingFreeEnergySeq n β) atTop (𝓝 (F β))) ∧
        ¬ AnalyticAt ℝ F βc

end Analysis.IsingPhaseTransition

end MathlibExt.Analysis.IsingPhaseTransitionWanted
