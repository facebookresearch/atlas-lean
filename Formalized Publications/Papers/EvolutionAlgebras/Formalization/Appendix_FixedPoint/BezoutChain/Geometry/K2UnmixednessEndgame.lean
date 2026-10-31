/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeDepthFragment
import Appendix_FixedPoint.BezoutChain.Regularity.Grade.GradeUnmixedBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Unmixed.HeightDrop
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AssHeightBound
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MacaulayScoped
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.MacaulayTwo
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Appendix_FixedPoint.BezoutChain.Regularity.Rees.ReesAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedLift
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.GradedSurjection
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.GradedSurjectionInjective
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.KernelAssembly
import Appendix_FixedPoint.BezoutChain.Regularity.Koszul.KernelChain
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.NewtonDifferences
import Appendix_FixedPoint.BezoutChain.Regularity.Multiplicity.SingleDropRegularity

/-!
# `k = 2` unmixedness endgame, conditional on `DepthEqDimAt` (proof)

For `R = MvPolynomial (Fin m) K` (`[Field K]`), `q : Fin 2 → R` carrying
successive SMul-regularity data, and `J = Ideal.span (Set.range q)`, this
module closes the `k = 2` endgame conditional-exact on `[hdepth]`, where

`hdepth : ∀ Q [Q.IsPrime], Q ∈ associatedPrimes _ (_ ⧸ J) → DepthEqDimAt m K Q`

is taken as an explicit hypothesis in the exact T2-master shape
(`ReesAssembly.depthEqDimAt_of_koszul_bridge` proves `DepthEqDimAt` in
parallel, so it is not imported here — wiring is one-line
application).

Inputs (all proved, read-only):
* `GradeUnmixedBridge.heightDrop_of_chain_depth` /
  `GradeUnmixedBridge.unmixed_of_chain_depth`
  (`Regularity/Grade/GradeUnmixedBridge.lean`): the hbaby-closed
  one-line corollaries (hbaby discharged by `babyAB_of_babyAB_quot`); the `k = 2` masters below
  are one-line applications at
  `k := 2`, replacing the former manual pair-bridge + chain +
  wiring.
* `GradeDepthFragment.gradeDropChain_of_successive` (`Regularity/Grade/GradeDepthFragment.lean`):
  `GradeDropChain` closed unconditionally from successive data.
* `AssHeightBound.le_height_of_mem_associatedPrimes_of_successive`
  (`Regularity/Avoid/AssHeightBound.lean`): `(k : ℕ∞) ≤ P.height` lower bound.
* `MacaulayScoped.scoped_iff_heightDrop` (`Regularity/Avoid/MacaulayScoped.lean`):
  scoped Macaulay iff height-drop at lengths `≥ 2`.

Masters (all conditional-exact on `[hdepth]`, T2 shape):
* `heightDrop_pair_of_depthEq` — `HeightDropResidualAt` at `k = 2`.
* `heightDropPair_of_depthEq` — same content as `HeightDropResidualPair`.
* `height_eq_pair_of_depthEq` — `P.height = 2` (upper + Krull lower bound).
* `unmixed_pair_of_depthEq` — `P ∈ J.minimalPrimes` per `Ass` prime.
* `scoped_pair_of_depthEq` — `ScopedMacaulayAt 2`.

Residual (out of scope): general-`k` baby-AB (length-`k` AB equation
`pd + grade(M) = grade(R)` for `k ≠ 2`) is not attempted here; only the
`k = 2` endgame is closed.

## Standing context (routine binders)

Named once here; per-decl docstrings below repeat GRADE verdicts and name only
substantive non-routine premises.

* `hsucc : RegularityBridge.SuccessiveSMulRegular q` — successive SMul-regularity
  data on the pair `q : Fin 2 → R`.
* `hJ : J = Ideal.span (Set.range q)` — the spanned-ideal identification.
* `hQ : Q ∈ associatedPrimes _ (_ ⧸ J)` — Ass-membership of the prime.
* `hdepth : ∀ Q [Q.IsPrime], Q ∈ Ass → GradeDepthFragment.DepthEqDimAt m K Q` — the
  routine conditional input of every master (GRADE stays per-decl).
* Instances: `[Field K]` throughout; `[Q.IsPrime]`/`[P.IsPrime]` on primes;
  `[IsDomain R]` in the §hne chain.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace BabyABPair

/-- `k = 2` height-drop from `DepthEqDimAt`: one-line application of the
hbaby-closed `GradeUnmixedBridge.heightDrop_of_chain_depth`  at
`k := 2`, fed with the closed chain
(`GradeDepthFragment.gradeDropChain_of_successive`) and the explicit `hdepth`
hypothesis (exact T2-master shape).

Conditional on exactly `[hdepth]`. -/
theorem heightDrop_pair_of_depthEq (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ :=
  GradeUnmixedBridge.heightDrop_of_chain_depth m K q hsucc J hJ
    (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc) hdepth

/-- `k = 2` height-drop in `HeightDropResidualPair` form (defeq alias). -/
theorem heightDropPair_of_depthEq (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    HeightDrop.HeightDropResidualPair m K q hsucc J hJ :=
  heightDrop_pair_of_depthEq m K q hsucc J hJ hdepth

/-- Height equality at an `Ass` prime from `DepthEqDimAt`: the bridge upper
bound plus the Krull lower bound
(`AssHeightBound.le_height_of_mem_associatedPrimes_of_successive`).

Conditional on exactly `[hdepth]`. -/
theorem height_eq_pair_of_depthEq (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    P.height = ((2 : ℕ) : ℕ∞) := by
  have hle : P.height ≤ ((2 : ℕ) : ℕ∞) :=
    heightDrop_pair_of_depthEq m K q hsucc J hJ hdepth P hP
  have hge : (((2 : ℕ)) : ℕ∞) ≤ P.height :=
    AssHeightBound.le_height_of_mem_associatedPrimes_of_successive q hsucc J hJ
      P hP
  exact le_antisymm hle hge

/-- Per-prime minimality over `J` from `DepthEqDimAt`: one-line application
of the hbaby-closed `GradeUnmixedBridge.unmixed_of_chain_depth`
at `k := 2`.

Conditional on exactly `[hdepth]`. -/
theorem unmixed_pair_of_depthEq (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    P ∈ J.minimalPrimes :=
  GradeUnmixedBridge.unmixed_of_chain_depth m K q hsucc J hJ P hP
    (GradeDepthFragment.gradeDropChain_of_successive m K q hsucc)
    hdepth

/-- Scoped Macaulay unmixedness at `j = 2` from `DepthEqDimAt`: the
height-drop residual implies the scoped residual at lengths `≥ 2`
(`MacaulayScoped.scoped_iff_heightDrop`).

Conditional on exactly `[hdepth]`. -/
theorem scoped_pair_of_depthEq (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hdepth : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) → GradeDepthFragment.DepthEqDimAt m K Q) :
    MacaulayScoped.ScopedMacaulayAt 2 K q hsucc J hJ :=
  (MacaulayScoped.scoped_iff_heightDrop 2 m K q hsucc J hJ).mpr
    (fun _ => heightDrop_pair_of_depthEq m K q hsucc J hJ hdepth)

#print axioms heightDrop_pair_of_depthEq
#print axioms heightDropPair_of_depthEq
#print axioms height_eq_pair_of_depthEq
#print axioms unmixed_pair_of_depthEq
#print axioms scoped_pair_of_depthEq

end BabyABPair
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# `k = 2` endgame on `[hker]`: per-prime `hdepth` discharge (proof)

The five `hdepth`-conditional masters above are restated conditional-exact on
`[hker]`, discharging `hdepth : ∀ Q ∈ Ass(R ⧸ J), DepthEqDimAt m K Q` prime by
prime:

* sop data `(d, g, hgen, hd)` per prime from the proved
  `GradedLift.grlift_sop_exists` (`Regularity/Koszul/GradedLift.lean`,
  SystemOfParameters Finset + `Finset.equivFin`, unconditional);
* the Ext-comparison basis `b` as `extBasisULift` below (`Pi.basisFun`
  reindexed along `Equiv.ulift`, keeping `Ix := ULift (Fin d)` at the formalization
  universe with the `LinearOrder (ULift _)` instance from
  `Mathlib/Order/Lattice.lean`);
* `d = 0` via `ReesAssembly.depthEqDimAt_zero_of_sop`
  (`Regularity/Rees/ReesAssembly.lean`, unconditional given sop data),
  `d ≥ 1` via `ReesAssembly.depthEqDimAt_of_r2Reduced`
  (`Regularity/Rees/ReesAssembly.lean` — `1 ≤ d` from the case split, not
  assumed).

`HkerAtAss` is the universal `hker` over `Ass(R ⧸ J)` and all sop-shaped
families. Its discharge is by `d`-split (`hkerAtAss_of_hmin_hdimEq`,
appended below): `d = 0` is closed unconditionally
(`GradedSurjectionInjective.hsAssemble_ker_eq_bot_zero`,
`Regularity/Multiplicity/GradedSurjectionInjective.lean`); `d = 1` is closed on `[hmin]`
(`KernelChain.ker_chain_ker_eq_bot_one`,
`Regularity/Koszul/KernelChain.lean`); `d ≥ 2` goes through the
`hwit`-chain master (`KernelAssembly.ker_assemble_ker_eq_bot`,
`Regularity/Multiplicity/KernelAssembly.lean`) conditional on `hdimEq` in exact
M3-conclusion shape (`SingleDropRegularity.singleDrop_hdimEq_of_hle_gr`,
`Regularity/Multiplicity/SingleDropRegularity.lean`). `hdimEq` itself is the residual
crux and is not attempted here.

Residual (out of scope): `HkerAtAss` itself (kernel triviality per
prime); general-`k` baby-AB (inherited from above).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace BabyABPair

/-- Universal `hker` over `Ass(R ⧸ J)`: for every associated prime `Q` and
every sop-shaped generating family `(d, g, hgen)`, the poly-surjection kernel
is trivial. The exact conditional shape the `hwit`-chain discharges.

Specification (Prop address for the universal kernel hypothesis). -/
def HkerAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
      RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen) = ⊥

/-- The Ext-comparison basis at the formalization universe: `Pi.basisFun` reindexed
from `Fin d` to `ULift (Fin d)` along `Equiv.ulift`. The `ReesAssemble` sop
master needs `Ix : Type u` at `K`'s universe (`Type u`, not `Type 0`), so the
`Type`-valued `Fin d` index does not fit; the `ULift` reindexing keeps full
`K : Type*` generality (`LinearOrder (ULift _)` is the Mathlib instance).
-/
noncomputable def extBasisULift (R : Type*) [CommRing R] (d : ℕ) :
    Module.Basis (ULift (Fin d)) R (Fin d → R) :=
  (Pi.basisFun R (Fin d)).reindex Equiv.ulift.symm

/-- Per-prime `DepthEqDimAt` from local `hker`: sop data from
`grlift_sop_exists`, then `d = 0` via `depthEqDimAt_zero_of_sop` and `d ≥ 1`
via `depthEqDimAt_of_r2Reduced` with `extBasisULift` (`1 ≤ d` by `omega` from
the case split).

Conditional on exactly `[hkerQ]`. -/
theorem depthEqDimAt_of_hker_atPrime (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hkerQ : ∀ {d : ℕ} (g : Fin d → Localization.AtPrime Q)
      (hgen : Ideal.span (Set.range g) =
        IsLocalRing.maximalIdeal (Localization.AtPrime Q)),
      RingHom.ker (GradedSurjection.polySurjResidue Q d g hgen) = ⊥) :
    GradeDepthFragment.DepthEqDimAt m K Q := by
  obtain ⟨d, g, hgen, hd⟩ := GradedLift.grlift_sop_exists Q
  by_cases hd0 : d = 0
  · subst hd0
    exact ReesAssembly.depthEqDimAt_zero_of_sop m K Q g hgen
  · have hd1 : 1 ≤ d := by omega
    exact ReesAssembly.depthEqDimAt_of_r2Reduced m K Q
      (extBasisULift (Localization.AtPrime Q) d) g hgen hd
      (hkerQ g hgen) hd1

/-- Universal `hdepth` from `HkerAtAss`: specialization of the per-prime
discharge to each `Q ∈ Ass(R ⧸ J)`.

Conditional on exactly `[hker]`. -/
theorem hdepth_of_hker (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hker : HkerAtAss m K J)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    GradeDepthFragment.DepthEqDimAt m K Q :=
  depthEqDimAt_of_hker_atPrime m K Q (hker Q hQ)

/-- `k = 2` height-drop on `[hker]`: `hdepth` discharged per prime.

Conditional on exactly `[hker]`. -/
theorem heightDrop_pair_of_hker (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hker : HkerAtAss m K J) :
    HeightDrop.HeightDropResidualAt m K q hsucc J hJ :=
  heightDrop_pair_of_depthEq m K q hsucc J hJ (hdepth_of_hker m K J hker)

/-- `k = 2` height-drop in `HeightDropResidualPair` form, on `[hker]`.

Conditional on exactly `[hker]`. -/
theorem heightDropPair_of_hker (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hker : HkerAtAss m K J) :
    HeightDrop.HeightDropResidualPair m K q hsucc J hJ :=
  heightDropPair_of_depthEq m K q hsucc J hJ (hdepth_of_hker m K J hker)

/-- Height equality `P.height = 2` at an `Ass` prime, on `[hker]`.

Conditional on exactly `[hker]`. -/
theorem height_eq_pair_of_hker (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hker : HkerAtAss m K J) :
    P.height = ((2 : ℕ) : ℕ∞) :=
  height_eq_pair_of_depthEq m K q hsucc J hJ P hP (hdepth_of_hker m K J hker)

/-- Per-prime minimality over `J`, on `[hker]`.

Conditional on exactly `[hker]`. -/
theorem unmixed_pair_of_hker (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hker : HkerAtAss m K J) :
    P ∈ J.minimalPrimes :=
  unmixed_pair_of_depthEq m K q hsucc J hJ P hP (hdepth_of_hker m K J hker)

/-- Scoped Macaulay unmixedness at `j = 2`, on `[hker]`.

Conditional on exactly `[hker]`. -/
theorem scoped_pair_of_hker (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q))
    (hker : HkerAtAss m K J) :
    MacaulayScoped.ScopedMacaulayAt 2 K q hsucc J hJ :=
  scoped_pair_of_depthEq m K q hsucc J hJ (hdepth_of_hker m K J hker)

#print axioms HkerAtAss
#print axioms extBasisULift
#print axioms depthEqDimAt_of_hker_atPrime
#print axioms hdepth_of_hker
#print axioms heightDrop_pair_of_hker
#print axioms heightDropPair_of_hker
#print axioms height_eq_pair_of_hker
#print axioms unmixed_pair_of_hker
#print axioms scoped_pair_of_hker

end BabyABPair
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# `HkerAtAss` by `d`-split: `d = 0` / `d = 1` closed, `d ≥ 2` on `[hdimEq]` (proof)

`hkerAtAss_of_hmin_hdimEq` discharges the universal kernel hypothesis
`HkerAtAss` (above) prime by prime and dimension by dimension:

* `d = 0` via `GradedSurjectionInjective.hsAssemble_ker_eq_bot_zero`
  (`Regularity/Multiplicity/GradedSurjectionInjective.lean`, unconditional);
* `d = 1` via `KernelChain.ker_chain_ker_eq_bot_one`
  (`Regularity/Koszul/KernelChain.lean`), conditional-exact on `[hmin]`
  (`1 ≤ spanFinrank 𝔪`), universalized as `HminOneAtAss`;
* `d ≥ 2` via `KernelAssembly.ker_assemble_ker_eq_bot`
  (`Regularity/Multiplicity/KernelAssembly.lean`), conditional-exact on
  `[hdimEq]`, universalized as `HdimEqAtAss` in exact M3-conclusion shape
  (`SingleDropRegularity.singleDrop_hdimEq_of_hle_gr`,
  `Regularity/Multiplicity/SingleDropRegularity.lean`).

Status: `hkerAtAss_of_hmin_hdimEq` is conditional-exact on
`[hmin1, hdimEq]`.

Residual (out of scope): `HdimEqAtAss` itself (the `hdimEq` crux:
exact degree `d - 1` for the `gr` Hilbert function per prime).
`HminOneAtAss` (minimality `1 ≤ spanFinrank 𝔪` per prime) is closed below
(`hminOneAtAss_of_span_ne_bot`:591, `hminOneAtAss_of_pair`:601).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace BabyABPair

/-- Universal `d = 1` minimality over `Ass(R ⧸ J)`: the exact `hmin` shape
`ker_chain_ker_eq_bot_one` (`Regularity/Koszul/KernelChain.lean`)
consumes.

Specification (Prop address for the universal `d = 1` minimality hypothesis). -/
def HminOneAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    1 ≤ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).spanFinrank

/-- Universal `hdimEq` over `Ass(R ⧸ J)` for `d ≥ 2`, in exact M3-conclusion
shape: the `singleDrop_hdimEq_of_hle_gr` conclusion
(`Regularity/Multiplicity/SingleDropRegularity.lean`), which is the
`ker_assemble_ker_eq_bot` hyp (`Regularity/Multiplicity/KernelAssembly.lean`).

Specification (Prop address for the universal dim-equality hypothesis). -/
def HdimEqAtAss (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) : Prop :=
  ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
    Q ∈ associatedPrimes _ (_ ⧸ J) →
    ∀ {d : ℕ}, 2 ≤ d →
      ∀ Qw : Polynomial ℚ, Qw.natDegree ≤ d - 1 →
        (fun n => ((SingleDropRegularity.singleDrop_grHilbert
          (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) n : ℕ) : ℚ))
          =ᶠ[Filter.atTop] NewtonDifferences.evalFun Qw →
        Qw.natDegree = d - 1

/-- `d`-split discharge of `HkerAtAss`: `d = 0` closed via
`hsAssemble_ker_eq_bot_zero` , `d = 1` closed on `[hmin1]` via
`ker_chain_ker_eq_bot_one` , `d ≥ 2` via `ker_assemble_ker_eq_bot`
 on `[hdimEq]` in exact M3-conclusion shape. `hdimEq` itself is
not attempted (residual crux).

Conditional on exactly `[hmin1, hdimEq]`. -/
theorem hkerAtAss_of_hmin_hdimEq (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hmin1 : HminOneAtAss m K J)
    (hdimEq : HdimEqAtAss m K J) :
    HkerAtAss m K J := by
  intro Q _ hQ d g hgen
  cases d with
  | zero =>
    exact GradedSurjectionInjective.hsAssemble_ker_eq_bot_zero Q g hgen
  | succ n =>
    cases n with
    | zero =>
      exact KernelChain.ker_chain_ker_eq_bot_one Q g hgen (hmin1 Q hQ)
    | succ k =>
      have hd2 : 2 ≤ k + 2 := by omega
      exact KernelAssembly.ker_assemble_ker_eq_bot Q (k + 2) g hgen
        hd2 (hdimEq Q hQ hd2)

#print axioms HminOneAtAss
#print axioms HdimEqAtAss
#print axioms hkerAtAss_of_hmin_hdimEq

end BabyABPair
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# Universal `d = 1` minimality from per-prime nonvanishing (proof)

`hminOneAtAss_of_ne_bot` discharges the universal `HminOneAtAss` hypothesis
(consumed by `hkerAtAss_of_hmin_hdimEq` above, hence by `hdepth_of_hker` and
the universal depth hypothesis) prime by prime, applying the `hmin`-one gate
`KernelChain.ker_chain_one_le_spanFinrank_of_ne_bot`
(`Regularity/Koszul/KernelChain.lean`) to each `Q ∈ Ass(R ⧸ J)`.

Status: `hminOneAtAss_of_ne_bot` is conditional-exact on `[hne]`.

Residual: `hne` itself (`𝔪(R_Q) ≠ ⊥` per `Q ∈ Ass(R ⧸ J)`: `J ≤ Q` +
`J ≠ ⊥` + `(Q ≠ ⊥ → 𝔪(R_Q) ≠ ⊥)`) is closed in the next section
(:524-608; register at `Regularity/Koszul/KernelChain.lean` discharged).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace BabyABPair

/-- Universal `d = 1` minimality over `Ass(R ⧸ J)` from per-prime
maximal-ideal nonvanishing: the `hmin`-one gate
(`KernelChain.ker_chain_one_le_spanFinrank_of_ne_bot`) applied to each
associated prime. Discharges the `hmin1` hypothesis of
`hkerAtAss_of_hmin_hdimEq` (above), hence the `d = 1` branch of the universal
depth hypothesis consumed via `hdepth_of_hker`.

Conditional on exactly `[hne]`. -/
theorem hminOneAtAss_of_ne_bot (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (hne : ∀ (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime],
      Q ∈ associatedPrimes _ (_ ⧸ J) →
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≠ ⊥) :
    HminOneAtAss m K J :=
  fun Q _ hQ =>
    KernelChain.ker_chain_one_le_spanFinrank_of_ne_bot Q (hne Q hQ)

#print axioms hminOneAtAss_of_ne_bot

end BabyABPair
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# `hne` chain closed: `HminOneAtAss` from pair data (proof)

This section discharges the `hne` residual of `hminOneAtAss_of_ne_bot`
(above) — `𝔪(R_Q) ≠ ⊥` per `Q ∈ Ass(R ⧸ J)` — through the three links
anticipated in the residual register at
`Regularity/Koszul/KernelChain.lean`:

* `J ≤ Q` for `Q ∈ Ass(R ⧸ J)` is the proved
  `LocalUnmixed.assPrime_contains_span`
  (`Dimension/LocalUnmixed.lean`; annihilator containment);
* `J ≠ ⊥` from successive pair data via
  `MacaulayTwo.pair_fst_ne_zero`
  (`Regularity/Avoid/MacaulayTwo.lean`): the first generator is nonzero and
  lies in `J` (`pair_span_ne_bot_of_successive`);
* `Q ≠ ⊥ → 𝔪(R_Q) ≠ ⊥`
  (`maximalIdeal_atPrime_ne_bot_of_ne_bot`): a nonzero `x ∈ Q` maps into
  `𝔪` (`IsLocalization.AtPrime.to_map_mem_maximal_iff`) and stays nonzero
  (`IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors` over
  `Q.primeCompl_le_nonZeroDivisors`) — the same pair as
  `IsLocalization.AtPrime.isDomain_of_local_atPrime`
  (`Mathlib/RingTheory/Localization/AtPrime/Basic.lean`).

`hne_of_span_ne_bot` joins the first and third links into the exact `hne`
shape `hminOneAtAss_of_ne_bot` consumes, closing `HminOneAtAss` given
`J ≠ ⊥` (`hminOneAtAss_of_span_ne_bot`); `hminOneAtAss_of_pair` feeds the
second link, closing `HminOneAtAss` on the ambient BabyAuslanderBuchsbaum pair data
`[hsucc, hJ]` with no `hne` hypothesis.

Status: all six lemmas unconditional (conditional-form on the stated
`[J ≠ ⊥]` / `[hsucc, hJ]` gates).

Residual: closed in the pair context — the `d = 1` branch of
`hkerAtAss_of_hmin_hdimEq` now needs only `[hdimEq]` alongside ambient
pair data. (`J ≠ ⊥` is the natural gate: for `J = ⊥`, `Q = ⊥` localizes
to a field with `𝔪 = ⊥`.)
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace BabyABPair

/-- The maximal ideal of `R_Q` is nonzero when `Q` is: a nonzero `x ∈ Q`
maps into `𝔪` (`to_map_mem_maximal_iff`) and stays nonzero
(`to_map_ne_zero_of_mem_nonZeroDivisors` over
`primeCompl_le_nonZeroDivisors`).
-/
theorem maximalIdeal_atPrime_ne_bot_of_ne_bot {R : Type*} [CommRing R]
    [IsDomain R] (Q : Ideal R) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≠ ⊥ := by
  rw [Submodule.ne_bot_iff] at hQ ⊢
  obtain ⟨x, x_mem, x_ne⟩ := hQ
  exact ⟨algebraMap R (Localization.AtPrime Q) x,
    (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime Q) Q x).mpr x_mem,
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _
      Q.primeCompl_le_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero x_ne)⟩

/-- An associated prime over a nonzero ideal is nonzero: `J ≤ Q`
(`LocalUnmixed.assPrime_contains_span`), so `Q = ⊥` would force
`J = ⊥`.
-/
theorem assPrime_ne_bot_of_span_ne_bot (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (hJne : J ≠ ⊥)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    Q ≠ ⊥ := by
  intro hcon
  apply hJne
  have hle := LocalUnmixed.assPrime_contains_span J Q hQ
  rw [hcon] at hle
  exact le_bot_iff.mp hle

/-- The pair ideal is nonzero from successive data: the first generator is
nonzero (`MacaulayTwo.pair_fst_ne_zero`) and lies in `J`.
-/
theorem pair_span_ne_bot_of_successive (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) :
    J ≠ ⊥ := by
  have hf0 := MacaulayTwo.pair_fst_ne_zero hsucc
  intro hcon
  have hmem : q ⟨0, by omega⟩ ∈ J := by
    rw [hJ]
    exact Ideal.subset_span (Set.mem_range_self _)
  rw [hcon] at hmem
  exact hf0 (Ideal.mem_bot.mp hmem)

/-- The exact `hne` shape `hminOneAtAss_of_ne_bot` consumes, from
`J ≠ ⊥`: annihilator containment plus the localization nonvanishing link.
-/
theorem hne_of_span_ne_bot (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (hJne : J ≠ ⊥)
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≠ ⊥ :=
  maximalIdeal_atPrime_ne_bot_of_ne_bot Q
    (assPrime_ne_bot_of_span_ne_bot m K J hJne Q hQ)

/-- Universal `d = 1` minimality over `Ass(R ⧸ J)` from `J ≠ ⊥`: the
`hne` chain above fed into `hminOneAtAss_of_ne_bot`.
-/
theorem hminOneAtAss_of_span_ne_bot (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K)) (hJne : J ≠ ⊥) :
    HminOneAtAss m K J :=
  hminOneAtAss_of_ne_bot m K J (hne_of_span_ne_bot m K J hJne)

/-- Universal `d = 1` minimality over `Ass(R ⧸ J)` from ambient BabyAuslanderBuchsbaum
pair data: `J ≠ ⊥` via `pair_span_ne_bot_of_successive`, no `hne`
hypothesis.
-/
theorem hminOneAtAss_of_pair (m : ℕ) (K : Type*) [Field K]
    (q : Fin 2 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K))
    (hJ : J = Ideal.span (Set.range q)) :
    HminOneAtAss m K J :=
  hminOneAtAss_of_span_ne_bot m K J
    (pair_span_ne_bot_of_successive m K q hsucc J hJ)

#print axioms maximalIdeal_atPrime_ne_bot_of_ne_bot
#print axioms assPrime_ne_bot_of_span_ne_bot
#print axioms pair_span_ne_bot_of_successive
#print axioms hne_of_span_ne_bot
#print axioms hminOneAtAss_of_span_ne_bot
#print axioms hminOneAtAss_of_pair

end BabyABPair
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
