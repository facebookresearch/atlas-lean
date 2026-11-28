/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TWO PARALLEL MACHINES WITH A SINGLE SERVER, unit setups, makespan (`P2;S1|s_i=1|Cmax`): definitions
is NP-complete

Source:
S. A. Kravchenko and F. Werner, "Parallel machine scheduling problems with a single server",
Mathematical and Computer Modelling 26 (1997), 1-11, doi:10.1016/S0895-7177(97)00236-7;
N. G. Hall, C. N. Potts and C. Sriskandarajah, "Parallel machine scheduling with a common
server", Discrete Applied Mathematics 102 (2000), 223-243,
doi:10.1016/S0166-218X(99)00206-1;
P. Brucker and S. Knust, *Complexity results for scheduling problems*, Universität Osnabrück,
class "Parallel machine problems with a single server" (`P2;S1|s_i=1|C_max`, NP-hard and
maximal pseudo-polynomially solvable, citing Hall et al. 2000 and Kravchenko and Werner 1997).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesUnitSetupMakespan

open MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesEqualSetupMakespan
  (SingleServerTwoMachinesEqualSetupMakespanInstance
    SingleServerTwoMachinesEqualSetupMakespanFeasible)

/-- Well-formedness of an instance: it is a well-formed `P2;S1|s_i=s|C_max` instance whose
common setup time is `s = 1`. -/
def WellFormed (i : SingleServerTwoMachinesEqualSetupMakespanInstance) : Prop :=
  SingleServerTwoMachinesEqualSetupMakespan.WellFormed i ∧ i.1 = 1

open Classical in
/-- `P2;S1|s_i=1|Cmax` as a decision problem over bitstrings. -/
noncomputable def singleServerTwoMachinesUnitSetupMakespanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := SingleServerTwoMachinesEqualSetupMakespanInstance) x with
  | some i => decide (WellFormed i ∧ SingleServerTwoMachinesEqualSetupMakespanFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.SingleServerTwoMachinesUnitSetupMakespan
