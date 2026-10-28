/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.AssociatedPrimes.MinimalPrimesAtCM
import Appendix_FixedPoint.BezoutChain.Regularity.CohenMacaulayLink.LocalizedQuotientDimEq

/-!
# Finite-dimensional discharge

The `GapBase` finite-dim fence is discharged
by the proved `gapBaseFin` (MinimalPrimesAtCM), and `C3aGapAll` follows via the
proved linkage chain (`c3aGapAll_of_gapBase`: MaximalRegularSequenceExists + LocQuotDimEq
both closed). After this, no remaining hypothesis named `GapBase`/`C3aGapAll`
is unproved at finite dimension; infinite-dim stays open and uninstantiated.
This removes the permanent residual but unlocks no downstream results
while the FirstReg apex stands.
-/

namespace EvolutionAlgebras.Appendix_FixedPoint.AssociatedPrimes.FiniteDimDischarge

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain

/-- `GapBase` (finite-dim) from the proved `gapBaseFin` (MinimalPrimesAtCM). -/
theorem gapBase_of_gapBaseFin : LocalizationOfCMGap.GapBase.{u} := by
  intro S _ _ _ p _ hfin hCM hall
  exact AssociatedPrimes.MinimalPrimesAtCM.gapBaseFin (S := S) p hfin hCM hall

/-- `C3aGapAll` (finite-dim) via the linkage chain. The GapBase residual is closed. -/
theorem c3aGapAll_of_gapBaseFin :
    CMQuotientFull.C3aGapAll.{u} :=
  LocalizationOfCMGap.c3aGapAll_of_gapBase gapBase_of_gapBaseFin

#print axioms gapBase_of_gapBaseFin
#print axioms c3aGapAll_of_gapBaseFin

end EvolutionAlgebras.Appendix_FixedPoint.AssociatedPrimes.FiniteDimDischarge
