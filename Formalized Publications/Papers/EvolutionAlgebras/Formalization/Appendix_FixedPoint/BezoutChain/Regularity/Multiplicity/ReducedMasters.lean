/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.LeadingTermMaps
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.IntertwiningAssembly

/-!
# Reduced R2 masters: exactness + dimension equation on `[hker]` only

Mechanical assembly (no new math): feeds the two proved discharge masters —

* (P3) `koszulIntertwine_assemble`
  (`IntertwiningAssembly.lean`): full `GrLiftIntertwining` on
  `[hker]` only;
* (N2) `filtr_grlift_conseq_unconditional` (`LeadingTermMaps.lean`):
  `GrLiftFiltrationConseq` from `hgen` alone —

into the file-6 masters `grlift_r2_exact` (`GradedLift.lean`) and
`grlift_master` (`GradedLift.lean`).

`FRL P` is a reducible abbrev for `Localization.AtPrime P`
(`FiltrationLift.lean`), so the `hgen` binders match by defeq with no
bridge (per the placement note at `GradedLift.lean`). This file
sits downstream of all three inputs, so there is no import cycle.

## References

Project (all read-only):
* `Regularity/Koszul/GradedLift.lean`: `grlift_r2_exact_of_equiv` (:543),
  `grlift_r2_exact` (:559), `grlift_master` (:574).
* `Regularity/Koszul/LeadingTermMaps.lean`: `filtr_grlift_conseq_unconditional`
  (:2061).
* `Regularity/Koszul/IntertwiningAssembly.lean`: `koszulIntertwine_assemble`
  (:210).

## Status

* `grlift_r2_exact_reduced`: conditional-exact on `[hker]`.
* `grlift_r2_exact_reduced_full`: conditional-exact on `[hker]`.

## Residual register

* `hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥` closes via the
  `hwit`-chain (`ker_assemble_ker_eq_bot`, parallel lane).

## Resource knobs (inventoried, permitted class)

`set_option maxSynthPendingDepth 4 in` (scoped, minimal bump over the repo
default 3) on both masters: the nested TC for submodule quotients over a
`ker`-of-`koszulContract` ambient exceeds depth 3 (same knob as file 6).
Not a linter suppression: without it the declarations do not elaborate
at all.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace ReducedMasters

open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedLift
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.LeadingTermMaps
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.IntertwiningAssembly
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.KoszulComplex
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.AugmentedConeStep
open EvolutionAlgebras.Appendix_FixedPoint.BezoutChain.GradedSurjection

variable {K : Type*} [Field K] {m : ℕ} (P : Ideal (MvPolynomial (Fin m) K))
  [P.IsPrime]

set_option maxSynthPendingDepth 4 in
/-- R2 exactness on `[hker]` only: `K(sop)` exact over `R_P`, with the
intertwining half discharged by `koszulIntertwine_assemble` and the
filtration half by `filtr_grlift_conseq_unconditional`.
conditional-exact on `[hker]`. -/
theorem grlift_r2_exact_reduced (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    ∀ j, contractExactAt (koszulContractOfSequence g) j :=
  grlift_r2_exact P d g hgen hker
    (koszulIntertwine_assemble P d g hgen hker)
    (filtr_grlift_conseq_unconditional P d g hgen)

set_option maxSynthPendingDepth 4 in
/-- The reduced file-6 master: dimension equation + R2 exactness from the
sop data on `[hker]` only.
conditional-exact on `[hker]`. -/
theorem grlift_r2_exact_reduced_full (d : ℕ) (g : Fin d → Localization.AtPrime P)
    (hgen : Ideal.span (Set.range g) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P))
    (hd : d = (IsLocalRing.maximalIdeal (Localization.AtPrime P)).spanFinrank)
    (hker : RingHom.ker (polySurjResidue P d g hgen) = ⊥) :
    ringKrullDim (Localization.AtPrime P) = d ∧
      ∀ j, contractExactAt (koszulContractOfSequence g) j :=
  grlift_master P d g hgen hd hker
    (koszulIntertwine_assemble P d g hgen hker)
    (filtr_grlift_conseq_unconditional P d g hgen)

#print axioms grlift_r2_exact_reduced
#print axioms grlift_r2_exact_reduced_full

end ReducedMasters
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
