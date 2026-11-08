/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.BusyBeaver

@[expose] public section

namespace Cslib.BusyBeaverWanted

open Cslib.BusyBeaver

/-!
# Catalogue bounds for the first ZFC-undecidable Busy Beaver value

The frozen catalogue bounds for constant 14a: the smallest number of
states `n` for which the Busy Beaver value `BB(n)` is undecidable in
ZFC.

ZFC is not formalized in this repository. The provider models the
constant relative to an abstract formal theory whose provability
predicate acts on syntactic sentence codes in `ℕ` (`haltsSentence`,
`notHaltsSentence`, `falseSentence`, `boundSentence`), so provability
does not collapse under `propext`. Lower and upper catalogue rows are
treated differently:

* Lower rows (`6 ≤ C₁₄`): the provider proves that any
  `ZFCPresentation`, a theory presented by an explicit proof checker
  satisfying the recorded verification properties, decides halting
  through five states (`ZFCPresentation.decidesHalting_le_five`), and
  hence that decidability through five states forces
  `6 ≤ firstUndecidable T` when some size is undecidable
  (`six_le_firstUndecidable_of_decides_le_five`). What is not supplied
  is an instance of that bundle for actual ZFC: no ZFC syntax, proof
  checker, or transfer of the `BB(5)` computation into ZFC proofs is
  formalized. The finite content behind the lower rows, the computed
  values `S(n)` and `Σ(n)` for `n = 3, 4, 5`, is registered below.

* Upper rows (`C₁₄ ≤ 7910, 1919, 748, 745, 432`): not registered. Those
  counts are state counts of concrete machines implementing specific
  ZFC proof checkers. They are not consequences of the abstract
  verification properties in `ZFCPresentation`, which fix neither an
  effective proof enumeration for ZFC nor the implementation whose
  size is counted, and no concrete encoded ZFC proof predicate or
  Gödel second-incompleteness formalization is supplied. The provider
  instead proves the model-level step with machine existence and
  unprovability as explicit hypotheses
  (`not_decides_of_consistency_machine`): a machine halting exactly
  when the false sentence is provable, whose non-halting sentence the
  theory does not prove, blocks decidability at its size, for any
  consistent theory sound for that machine's halting sentence.
-/

/-- Source: Lin--Radó (1965), determination of `S(3) = 21`. -/
theorem_wanted busyBeaverSteps_three_wanted :
    busyBeaverSteps 3 = 21

/-- Source: Lin--Radó (1965), determination of `Σ(3) = 6`. -/
theorem_wanted busyBeaverOnes_three_wanted :
    busyBeaverOnes 3 = 6

/-- Source: Brady (1983), determination of `S(4) = 107`. -/
theorem_wanted busyBeaverSteps_four_wanted :
    busyBeaverSteps 4 = 107

/-- Source: Brady (1983), determination of `Σ(4) = 13`. -/
theorem_wanted busyBeaverOnes_four_wanted :
    busyBeaverOnes 4 = 13

/-- Source: Busy Beaver Challenge (2025), determination of
`S(5) = 47176870`. -/
theorem_wanted busyBeaverSteps_five_wanted :
    busyBeaverSteps 5 = 47176870

/-- Source: Busy Beaver Challenge (2025), determination of
`Σ(5) = 4098`. -/
theorem_wanted busyBeaverOnes_five_wanted :
    busyBeaverOnes 5 = 4098

end Cslib.BusyBeaverWanted
