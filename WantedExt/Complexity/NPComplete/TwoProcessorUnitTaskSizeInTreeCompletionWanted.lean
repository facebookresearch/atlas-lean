/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIPROCESSOR TASKS `P2|intree;p_i=1;size_i|ΣC_i` is NP-complete

Source:
Y. Zinder and V. H. Do, "Scheduling unit execution time tasks on two parallel machines with the
criteria of makespan and total completion time", in G. Kendall, E. Burke, S. Petrovic and
M. Gendreau (eds.), *Multidisciplinary Scheduling: Theory and Applications*, Springer (2005),
83-112, doi:10.1007/0-387-27744-7_5 (only the abstract was available);
P. Brucker and S. Knust, *Complexity results for scheduling problems*,
http://www2.informatik.uni-osnabrueck.de/knust/class/, class `pmpt_nop` (multiprocessor tasks on
parallel processors, without preemption), entry `P2|intree;p_i=1;size_i|ΣC_i` (minimal NP-hard
in the strong sense, citing Zinder and Do 2005).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.TwoProcessorUnitTaskSizeInTreeCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitTaskSizeInTreeCompletion

open UnitFlowShopPrecedenceMakespan (Prec PrecWellFormed)

/-!
# MULTIPROCESSOR TASKS `P2|intree;p_i=1;size_i|ΣC_i` is NP-complete

INSTANCE: two identical processors, each executing at most one task at a time; `n` tasks, each
with unit processing time (`p_i = 1`) and a size `size_i ∈ {1, 2}` (the task uses `size_i`
processors, any of them, simultaneously); an in-tree precedence relation on the tasks (in-forest:
each task has at most one immediate successor), where `i` preceding `j` means that `j` cannot
start before `i` is completed; and a bound `K`. QUESTION: is there a schedule whose total
completion time `ΣC_i` is at most `K`, where `C_i` is the completion time of task `i`?

Zinder and Do's abstract states that for unit execution time multiprocessor tasks on two parallel
machines "the problem with the criterion of total completion time turns out to be NP-hard in the
strong sense even for in-trees".

Tasks are listed one per entry by their sizes; tasks are `Fin n`. Precedence arcs `(i, j)` (task
`i` precedes task `j`) name tasks and generate an acyclic relation, as in
`UnitFlowShopPrecedenceMakespanWanted` (`Prec`, `PrecWellFormed`), and every task has at most one
immediate successor in the generated order. A schedule gives each task an integer start time
`σ j` (with unit lengths and integer data, rounding start times down keeps every constraint and
increases no completion time). Processors are not named: the tasks starting at time `t` can be
given processors exactly when their sizes sum to at most `2`. Deleting a time unit in which no
task runs, and moving everything after it one unit earlier, keeps a schedule feasible and lowers
the total completion time, so some optimal schedule has all start times below `n`; membership in
NP is therefore the certificate argument. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIPROCESSOR TASKS `P2|intree;p_i=1;size_i|ΣC_i` is NP-complete.** Source: Zinder and Do
(2005), as recorded in the Brucker-Knust classification. -/
public theorem_wanted twoProcessorUnitTaskSizeInTreeCompletion_npComplete :
    twoProcessorUnitTaskSizeInTreeCompletionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L twoProcessorUnitTaskSizeInTreeCompletionDec

end MetaMathlibExt.Complexity.NPComplete.TwoProcessorUnitTaskSizeInTreeCompletion
