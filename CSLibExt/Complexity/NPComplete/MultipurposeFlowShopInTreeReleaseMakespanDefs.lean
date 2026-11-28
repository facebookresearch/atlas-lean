/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MPM FLOW SHOP, IN-TREE, RELEASE DATES (FMPM|intree; r_i; p_ij = 1|C_max): definitions

Source:
P. Brucker, *Scheduling Algorithms*, 5th ed., Springer (2007): Sections 1.2, 1.3 and 5.2
(release dates, precedence relations, in-trees), Chapter 10 (the MPM flow-shop model) and Table 5.3
(`P|p_i = 1; intree; r_i|C_max` is NP-hard, Brucker, Garey and Johnson);
P. Brucker, M. R. Garey and D. S. Johnson, "Scheduling equal-length tasks under treelike
precedence constraints to minimize maximum lateness", Mathematics of Operations Research 2
(1977), 275-284, doi:10.1287/moor.2.3.275;
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class "Shop problems with multipurpose
machines", which lists `FMPM|intree; r_i; p_ij = 1|C_max` as strongly NP-hard with the
attribution to Brucker, Garey and Johnson (1977).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultipurposeFlowShopPrecedenceMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopInTreeReleaseMakespan

open MultipurposeFlowShopPrecedenceMakespan (StagesWellFormed Prec PrecedenceWellFormed
  IsPrecedenceSchedule completionTime)

/-- An instance: the number of machines `m`, the stage machine sets `[μ_1, …, μ_r]`, the
release dates `[r_1, …, r_n]` (one per job), the pairs `(i, k)` with `i → k`, and the bound
`K`. -/
abbrev MultipurposeFlowShopInTreeReleaseMakespanInstance :=
  ℕ × List (List ℕ) × List ℕ × List (ℕ × ℕ) × ℕ

/-- The jobs of the instance, `Fin n` for `n` release dates. -/
abbrev Job (i : MultipurposeFlowShopInTreeReleaseMakespanInstance) : Type := Fin i.2.2.1.length

/-- The stages of the instance, `Fin r` for `r` machine sets. -/
abbrev Stage (i : MultipurposeFlowShopInTreeReleaseMakespanInstance) : Type := Fin i.2.1.length

/-- The release date `r_j` of job `j`. -/
def releaseDate (i : MultipurposeFlowShopInTreeReleaseMakespanInstance) (j : Job i) : ℕ :=
  i.2.2.1.get j

/-- `k` is an immediate successor of `j` (and `j` an immediate predecessor of `k`): `j → k`, and
no job `c` has `j → c → k`. -/
def ImmediateSuccessor (i : MultipurposeFlowShopInTreeReleaseMakespanInstance) (j k : Job i) :
    Prop :=
  Prec i.2.2.2.1 j k ∧ ∀ c, ¬ (Prec i.2.2.2.1 j c ∧ Prec i.2.2.2.1 c k)

/-- Well-formedness of an instance: the machine environment is well formed and every stage
machine set is nonempty (each operation is processed by one machine of its set), the listed
pairs describe a precedence relation on the jobs, and it is an in-tree (every job has at most
one immediate successor). -/
def WellFormed (i : MultipurposeFlowShopInTreeReleaseMakespanInstance) : Prop :=
  StagesWellFormed i.1 i.2.1 ∧ (∀ M ∈ i.2.1, M ≠ []) ∧
    PrecedenceWellFormed i.2.2.1.length i.2.2.2.1 ∧
    ∀ j a b, ImmediateSuccessor i j a → ImmediateSuccessor i j b → a = b

/-- Some MPM flow-shop schedule of the unit-time jobs obeys the precedence constraints, starts
no operation of a job before its release date, and has makespan at most `K`. -/
def MultipurposeFlowShopInTreeReleaseMakespanFeasible
    (i : MultipurposeFlowShopInTreeReleaseMakespanInstance) : Prop :=
  ∃ σ : Job i → Stage i → ℕ, ∃ a : Job i → Stage i → Fin i.1,
    IsPrecedenceSchedule i.1 i.2.1 i.2.2.2.1 σ a ∧ (∀ j s, releaseDate i j ≤ σ j s) ∧
      ∀ j, completionTime (fun _ _ => 1) σ j ≤ i.2.2.2.2

open Classical in
/-- `FMPM|intree; r_i; p_ij = 1|C_max` as a decision problem over bitstrings. -/
noncomputable def multipurposeFlowShopInTreeReleaseMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultipurposeFlowShopInTreeReleaseMakespanInstance) x with
  | some i => decide (WellFormed i ∧ MultipurposeFlowShopInTreeReleaseMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MultipurposeFlowShopInTreeReleaseMakespan
