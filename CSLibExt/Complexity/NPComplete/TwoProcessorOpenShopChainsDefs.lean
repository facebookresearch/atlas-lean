/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN SHOP O2|chains|Cmax: definitions

Source:
V. S. Tanaev, Y. N. Sotskov and V. A. Strusevich, *Scheduling Theory. Multi-Stage Systems*,
Mathematics and its Applications 285, Kluwer Academic Publishers, Dordrecht (1994),
doi:10.1007/978-94-011-1192-8 (not available here); recorded as strongly NP-hard (a minimal
NP-hard problem) in P. Brucker and S. Knust, *Complexity results for scheduling problems*, class
"Open-shop problems without preemption" (University of Osnabrück,
http://www.mathematik.uni-osnabrueck.de/research/OR/class/), problem `O2|chains|C_max`,
credited to Tanaev et al. (1994).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.F3UnitChainsLateJobsDefs
public import CSLibExt.Complexity.NPComplete.OpenShopSchedulingDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopChains

open MetaMathlibExt.Complexity.NPComplete.OpenShopScheduling (OpenShopSchedulingInstance)
open MetaMathlibExt.Complexity.NPComplete.NoWaitFlowShopScheduling
  (IsOpenShopSchedule taskLength)
open MetaMathlibExt.Complexity.NPComplete.F3UnitChainsLateJobs (ChainsWellFormed)

/-- An instance: an OPEN-SHOP SCHEDULING instance (the number `m` of machines, the jobs as lists
of task lengths, the bound `K`) and the chain arcs `(i, j)`. -/
abbrev TwoProcessorOpenShopChainsInstance := OpenShopSchedulingInstance × List (ℕ × ℕ)

/-- Well-formedness of an instance: a well-formed OPEN-SHOP SCHEDULING instance with two
machines, whose arcs form chains on the jobs. -/
def WellFormed (i : TwoProcessorOpenShopChainsInstance) : Prop :=
  NoWaitFlowShopScheduling.WellFormed i.1 ∧ i.1.1 = 2 ∧ ChainsWellFormed i.1.2.1.length i.2

/-- Some open-shop schedule meeting the makespan bound `K` respects the chains: if job `a`
immediately precedes job `b`, every task of `b` starts after every task of `a` is completed. -/
def TwoProcessorOpenShopChainsFeasible (i : TwoProcessorOpenShopChainsInstance) : Prop :=
  ∃ σ : Fin i.1.1 → Fin i.1.2.1.length → ℕ, IsOpenShopSchedule i.1 σ ∧
    ∀ a b : Fin i.1.2.1.length, ((a : ℕ), (b : ℕ)) ∈ i.2 →
      ∀ p q, σ p a + taskLength i.1 p a ≤ σ q b

open Classical in
/-- OPEN SHOP `O2|chains|C_max` as a decision problem over bitstrings. -/
noncomputable def twoProcessorOpenShopChainsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TwoProcessorOpenShopChainsInstance) x with
  | some i => decide (WellFormed i ∧ TwoProcessorOpenShopChainsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorOpenShopChains
