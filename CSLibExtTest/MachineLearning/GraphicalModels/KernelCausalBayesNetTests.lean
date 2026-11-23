/-
Copyright (c) 2026 Adam Kiezun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Kiezun
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.KernelCausalBayesNet

/-!
# Tests for kernel causal Bayesian networks

The discrete embedding and intervention theorems instantiated on concrete
networks: a two-node `Bool` chain, and a network on `ℝ` showing the
definitions apply off the discrete case.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open MeasureTheory ProbabilityTheory Finset Convexity

/-- Parents of the two-node chain `0 → 1`. -/
def chainPa2 : (k : Fin 2) → Finset (Fin k)
  | ⟨0, _⟩ => ∅
  | ⟨1, _⟩ => {0}

variable (cpt2 : (k : Fin 2) → (chainPa2 k → Bool) → StdSimplex ℝ Bool)

/-- On the two-node chain, singleton masses under the kernel joint are the
finite joint probabilities. -/
example (x : Fin 2 → Bool) :
    (BayesNet.mk chainPa2 cpt2).toKernelCBN.joint {x} =
      ENNReal.ofReal ((BayesNet.mk chainPa2 cpt2).joint x) :=
  BayesNet.toKernelCBN_joint_singleton _ _

/-- The embedding of the chain commutes with intervening on node `1`. -/
example (a : Bool) :
    ((BayesNet.mk chainPa2 cpt2).intervene 1 a).toKernelCBN =
      (BayesNet.mk chainPa2 cpt2).toKernelCBN.intervene 1 a :=
  BayesNet.toKernelCBN_intervene _ _ _

/-- The joint of every kernel network is a probability measure, here on
`ℝ`-valued nodes. -/
example (c : KernelCBN 2 (fun _ => ℝ)) : IsProbabilityMeasure c.joint :=
  inferInstance

/-- After `do(X_0 = a)` on an `ℝ`-valued network, the law of `X_0` is
`δ_a`, and node `0` has no parents. -/
example (c : KernelCBN 2 (fun _ => ℝ)) (a : ℝ) :
    (c.intervene 0 a).joint.map (fun x => x 0) = Measure.dirac a ∧
      (c.intervene 0 a).pa 0 = ∅ :=
  ⟨c.map_joint_intervene_apply_eq_dirac 0 a, c.intervene_pa_self 0 a⟩

/-- The degenerate chain that always outputs `true`. -/
noncomputable def trueChain : BayesNet Bool 2 :=
  BayesNet.mk chainPa2 (fun _ _ => StdSimplex.single true)

/-- Concrete joint mass: the embedded degenerate chain puts mass `1` on
`![true, true]` and mass `0` on `![true, false]`. -/
example : trueChain.toKernelCBN.joint {![true, true]} = 1 ∧
    trueChain.toKernelCBN.joint {![true, false]} = 0 := by
  constructor
  · rw [BayesNet.toKernelCBN_joint_singleton]
    simp [trueChain, BayesNet.joint_eq_prod]
  · rw [BayesNet.toKernelCBN_joint_singleton]
    simp [trueChain, BayesNet.joint_eq_prod]

/-- Concrete intervention: after `do(X_1 = false)` the embedded chain puts
mass `1` on `![true, false]`. -/
example : (trueChain.intervene 1 false).toKernelCBN.joint {![true, false]} = 1 := by
  rw [BayesNet.toKernelCBN_joint_singleton]
  simp [trueChain, BayesNet.joint_eq_prod, BayesNet.intervene]

/-- The zero-node network: its joint is a probability measure on the
one-point type of empty assignments. -/
example (c : KernelCBN 0 (fun _ => ℝ)) : c.joint Set.univ = 1 :=
  measure_univ

end Cslib.MachineLearning.GraphicalModels
