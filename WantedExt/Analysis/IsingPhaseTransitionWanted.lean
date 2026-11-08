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

/-- Sites in the `L × L` periodic square lattice. -/
abbrev IsingSite (L : ℕ) [NeZero L] : Type := ZMod L × ZMod L

/-- Ising spins encoded as `±1`. -/
def spinValue (b : Bool) : ℝ := if b then 1 else -1

/-- Right neighbour in the periodic lattice. -/
def rightNeighbour {L : ℕ} [NeZero L] (p : IsingSite L) : IsingSite L :=
  ((p.1 + 1 : ZMod L), p.2)

/-- Upward neighbour in the periodic lattice. -/
def upNeighbour {L : ℕ} [NeZero L] (p : IsingSite L) : IsingSite L :=
  (p.1, (p.2 + 1 : ZMod L))

/-- Zero-field ferromagnetic Ising Hamiltonian on the periodic box. -/
noncomputable def isingEnergy (L : ℕ) [NeZero L] (σ : IsingSite L → Bool) : ℝ :=
  -((∑ p : IsingSite L, spinValue (σ p) * spinValue (σ (rightNeighbour p))) +
      ∑ p : IsingSite L, spinValue (σ p) * spinValue (σ (upNeighbour p)))

/-- Finite-volume partition function at inverse temperature `β`. -/
noncomputable def isingPartitionFunction (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  ∑ σ : IsingSite L → Bool, Real.exp (-β * isingEnergy L σ)

/-- Finite-volume free energy density. -/
noncomputable def finiteIsingFreeEnergy (L : ℕ) [NeZero L] (β : ℝ) : ℝ :=
  Real.log (isingPartitionFunction L β) / (L : ℝ) ^ 2

/-- Free energy along positive side lengths `n+1`. -/
noncomputable def finiteIsingFreeEnergySeq (n : ℕ) (β : ℝ) : ℝ :=
  finiteIsingFreeEnergy (n + 1) β

/- **Onsager's 2D Ising phase transition.** The thermodynamic-limit free
energy exists for all `β` and is non-analytic at some positive `βc`. -/
/-- Source: L. Onsager, *Crystal statistics I*, Phys. Rev. 65 (1944). Knill, §158. Via leanprover/lean-eval@38361be, problem `ising_2d_phase_transition`. -/
public theorem_wanted ising_2d_phase_transition :
    ∃ (F : ℝ → ℝ) (βc : ℝ),
      0 < βc ∧
        (∀ β : ℝ,
          Tendsto (fun n : ℕ => finiteIsingFreeEnergySeq n β) atTop (𝓝 (F β))) ∧
        ¬ AnalyticAt ℝ F βc

end Analysis.IsingPhaseTransition

end MathlibExt.Analysis.IsingPhaseTransitionWanted
