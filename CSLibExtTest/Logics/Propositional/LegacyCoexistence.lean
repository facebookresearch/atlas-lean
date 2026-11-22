/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Logics.Propositional.Defs
public import Cslib.Logics.Propositional.NaturalDeduction.Basic
public import Cslib.Logics.Propositional.NaturalDeduction.Lemmas
public import CSLibExt.Algorithms.Lean.Approximation.MaxSatRounding
public import CSLibExt.Algorithms.SAT.CDCL.Basic
public import CSLibExt.Algorithms.SAT.CDCL.Termination
public import CSLibExt.Algorithms.SAT.DavisPutnam.Basic
public import CSLibExt.Algorithms.SAT.DPLL.Correctness
public import CSLibExt.Algorithms.SAT.DPLL.Solver
public import CSLibExt.Algorithms.SAT.Horn.Basic
public import CSLibExt.Algorithms.SAT.MaxSAT.Basic
public import CSLibExt.Algorithms.SAT.Tseitin.Basic
public import CSLibExt.Algorithms.SAT.TwoSAT.Basic
public import CSLibExt.Algorithms.SAT.UnitPropagation.Basic
public import CSLibExt.AutomatedReasoning.Certificates.LRAT
public import CSLibExt.AutomatedReasoning.CNF.Restriction
public import CSLibExt.AutomatedReasoning.CNF.Semantics
public import CSLibExt.AutomatedReasoning.StringConstraints.BitBlast
public import CSLibExt.AutomatedReasoning.StringConstraints.Complexity
public import CSLibExt.Combinatorics.RandomThreeSat
public import CSLibExt.Computability.Complexity.Karp.Clique
public import CSLibExt.Computability.Complexity.Karp.CliqueComplete
public import CSLibExt.Computability.Complexity.Karp.CliqueCorrect
public import CSLibExt.Computability.Complexity.Karp.CliqueEmit
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.Complexity.Karp.ColorComplete
public import CSLibExt.Computability.Complexity.Karp.ColorCorrect
public import CSLibExt.Computability.Complexity.Karp.ColorEmit
public import CSLibExt.Computability.Complexity.Karp.HamPath
public import CSLibExt.Computability.Complexity.Karp.HamPathComplete
public import CSLibExt.Computability.Complexity.Karp.HamPathCorrect
public import CSLibExt.Computability.Complexity.Karp.HamPathDetours
public import CSLibExt.Computability.Complexity.Karp.HamPathEmit
public import CSLibExt.Computability.Complexity.Karp.HamPathEmitMachine
public import CSLibExt.Computability.Complexity.Karp.HamPathEmitSpec
public import CSLibExt.Computability.Complexity.Karp.HamPathForward
public import CSLibExt.Computability.Complexity.Karp.HamPathNormal
public import CSLibExt.Computability.Complexity.Karp.ThreeSat
public import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete
public import CSLibExt.Computability.Complexity.Karp.ThreeSatCorrect
public import CSLibExt.Computability.Complexity.Karp.ThreeSatEmit
public import CSLibExt.Computability.Complexity.Karp.ThreeSatFilter
public import CSLibExt.Computability.Complexity.Karp.TokThen
public import CSLibExt.Computability.Complexity.Preimage
public import CSLibExt.Computability.Complexity.SatCheck
public import CSLibExt.Computability.Complexity.SatTokenizer
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import CSLibExt.Computability.Complexity.SatVerifierTM
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.SatTimeM
public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.CurryHoward
public import CSLibExt.Logics.FirstOrder.PropositionalBridge
public import CSLibExt.Logics.LinearLogic.CLL.GirardTranslation
public import CSLibExt.Logics.Propositional.BDD.Basic
public import CSLibExt.Logics.Propositional.BDD.Count
public import CSLibExt.Logics.Propositional.BDD.Quantify
public import CSLibExt.Logics.Propositional.CNF.Basic
public import CSLibExt.Logics.Propositional.CNF.Compaction
public import CSLibExt.Logics.Propositional.CNF.NormalForm
public import CSLibExt.Logics.Propositional.CNF.ParsimoniousThree
public import CSLibExt.Logics.Propositional.CNF.Resolution
public import CSLibExt.Logics.Propositional.CNF.ResolutionSize
public import CSLibExt.Logics.Propositional.CNF.ResolutionWidth
public import CSLibExt.Logics.Propositional.CNF.Restriction
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import CSLibExt.Logics.Propositional.Legacy.Defs
public import CSLibExt.Logics.Propositional.Legacy.NaturalDeduction.Basic
public import CSLibExt.Logics.Propositional.Legacy.NaturalDeduction.Theory
public import CSLibExt.Logics.Propositional.NaturalDeduction.Completeness
public import CSLibExt.Logics.Propositional.NaturalDeduction.FunctionalCompleteness
public import CSLibExt.Logics.Propositional.NaturalDeduction.Interpolation
public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics

@[expose] public section

/-!
# CSLib's propositional logic and ATLAS's restored v4.35 copy build together

CSLib v4.36 declares its `falsum`-based propositions as `Cslib.Logic.PL.Proposition`. ATLAS keeps
CSLib v4.35's propositions, which have no `falsum`, in `CSLibExt/Logics/Propositional/Legacy/`
under the namespace `Cslib.Logic.LegacyPL`, and every ATLAS declaration once in `Cslib.Logic.PL`
moved there too; other developments refer to them in that namespace. This module imports CSLib's
propositional logic together with every `CSLibExt` module that declares or uses `LegacyPL`
names, so a declaration of one that takes a name of the other makes it fail to build.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.LegacyCoexistence

/-- CSLib's propositions have a `falsum` constructor. -/
example : Cslib.Logic.PL.Proposition Nat := .falsum

/-- The restored propositions have none: their bottom is an atom. -/
example : Cslib.Logic.LegacyPL.Proposition (WithBot Nat) := ⊥

end CSLibExtTest.Logics.Propositional.LegacyCoexistence
