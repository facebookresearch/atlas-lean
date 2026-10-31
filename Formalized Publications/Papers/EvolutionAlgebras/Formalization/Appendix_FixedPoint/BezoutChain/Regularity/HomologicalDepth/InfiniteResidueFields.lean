/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.SimpleRing.DivisionRing
/-!
# Per-`Q` infinite residue fields — T4 discharge (Sup tower)

Closes the T4 per-`Q` infinite-residue input (`hInf`) of
`hChiReduceAtAss_of_quotExact` (QuotientTowerFire:242): at every
prime `Q` of `MvPolynomial (Fin m) K`, the residue field `R_Q ⧸ 𝔪_Q`
is infinite whenever `K` is infinite.

## What this file proves

* `perQResidueMap`: the structure map `K →+* R_Q ⧸ 𝔪_Q`
  (`C` into the polynomial ring, localized, then quotiented).
* `perQResidueMap_injective`: it is injective — a ring hom out of a
  field (a simple ring) into a nontrivial ring, via Mathlib's
  `RingHom.injective`; nontriviality is the residue `Field`
  instance (`ResidueField.field`).
* `atPrime_residue_infinite`: `Infinite K → Infinite (R_Q ⧸ 𝔪_Q)`
  via `Infinite.of_injective`.
* `atPrime_residue_infinite_atAss`: the Ass-gated form — verbatim the
  `hInf` conjunct of `hquot` in `hChiReduceAtAss_of_quotExact`
  (membership is recorded, not needed).
* `atPrime_residue_infinite_of_algClosed`: the formalization corollary —
  `IsAlgClosed K` gives `Infinite K` (Mathlib instance), hence
  infinite residues.

## Status

All theorems: unconditional (the general ones take ambient
`Infinite K`; the corollary takes the formalization-standard
`IsAlgClosed K`).

## References

Project (read-only): `InfiniteResidueFields.lean` (same proof in the
R23 graded-exact shape), `QuotientTowerFire.lean`
(`hChiReduceAtAss_of_quotExact`:250, consumer of `hInf`).

Mathlib (`lean-toolchain` pins `v4.34.0`): `RingHom.injective`,
`Infinite.of_injective`, `MvPolynomial.C`, `algebraMap` into
`Localization.AtPrime`, `IsLocalRing.ResidueField.field`,
`IsAlgClosed → Infinite` instance.
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace InfiniteResidueFields

open IsLocalRing MvPolynomial

/-- The structure map `K →+* R_Q ⧸ 𝔪_Q`: constants into the polynomial
ring, localized at `Q`, then quotiented by the maximal ideal.
-/
noncomputable def perQResidueMap (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    K →+* (Localization.AtPrime Q ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  (Ideal.Quotient.mk _).comp
    ((algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q)).comp
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K))

#print axioms perQResidueMap

/-- The structure map is injective: a ring hom out of the field `K`
(a simple ring) into the nontrivial residue field.
-/
theorem perQResidueMap_injective (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Function.Injective (perQResidueMap m K Q) := by
  have : Field (Localization.AtPrime Q
      ⧸ maximalIdeal (Localization.AtPrime Q)) :=
    IsLocalRing.ResidueField.field _
  exact RingHom.injective _

#print axioms perQResidueMap_injective

/-- T4 at general prime `Q`: infinite `K` gives infinite residue field.
-/
theorem atPrime_residue_infinite (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Infinite (Localization.AtPrime Q
      ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  Infinite.of_injective _ (perQResidueMap_injective m K Q)

#print axioms atPrime_residue_infinite

/-- T4 at `Q ∈ Ass(R ⧸ J)`: the Ass-gated form discharging the `hInf`
conjunct of `hquot` in `hChiReduceAtAss_of_quotExact` (QuotTowerFire
:250). Membership is recorded for shape match; the proof needs only
primality.
-/
theorem atPrime_residue_infinite_atAss (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    Infinite (Localization.AtPrime Q
      ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  atPrime_residue_infinite m K Q

#print axioms atPrime_residue_infinite_atAss

/-- T4 under the formalization's top-level hypothesis: `IsAlgClosed K`
gives `Infinite K` (Mathlib instance), hence infinite residues.
-/
theorem atPrime_residue_infinite_of_algClosed (m : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K] (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Infinite (Localization.AtPrime Q
      ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  atPrime_residue_infinite m K Q

#print axioms atPrime_residue_infinite_of_algClosed

end InfiniteResidueFields
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras

/-!
# Infinite residue fields at `R_Q` — T2 discharge
Closes the T2 infinite-residue input of the R23 masters
(`hChiReduceAtAss_of_gradedExact`, SupColonDimDrop:560): at every prime
`Q` of `MvPolynomial (Fin m) K`, the residue field
`R_Q ⧸ 𝔪_Q` is infinite whenever `K` is infinite.

## What this file proves

* `residueFieldMap`: the structure map `K →+* R_Q ⧸ 𝔪_Q`
  (`C` into the polynomial ring, localized, then quotiented).
* `residueFieldMap_injective`: it is injective — a ring hom out of a
  field (a simple ring) into a nontrivial ring, via Mathlib's
  `RingHom.injective` (`SimpleRing/Basic.lean`); nontriviality is the
  residue `Field` instance (`ResidueField.field`).
* `infinite_residue_of_infinite`: `Infinite K → Infinite (R_Q ⧸ 𝔪_Q)`
  via `Infinite.of_injective`.
* `infinite_residue_atAss_of_infinite`: the Ass-gated form consumed by
  the R23 plugs (membership is recorded, not needed).
* `infinite_residue_of_algClosed`: the top-level corollary — the
  ambient `IsAlgClosed K` gives `Infinite K` (Mathlib instance,
  `IsAlgClosed/Basic.lean`), hence infinite residues.

## Status

All theorems: unconditional (the general ones take ambient `Infinite K`;
the corollary takes the formalization-standard `IsAlgClosed K`).

## References

Mathlib (`lean-toolchain` pins `v4.34.0`), all read-only, all verified
by elaboration in the probe (`RingHom.injective`,
`Infinite.of_injective`, `MvPolynomial.C`, `algebraMap` into
`Localization.AtPrime`, `IsLocalRing.ResidueField.field`,
`IsAlgClosed → Infinite` instance).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace KoszulResidueInfinite

open IsLocalRing MvPolynomial

/-- The structure map `K →+* R_Q ⧸ 𝔪_Q`: constants into the polynomial
ring, localized at `Q`, then quotiented by the maximal ideal.
-/
noncomputable def residueFieldMap (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    K →+* (Localization.AtPrime Q ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  (Ideal.Quotient.mk _).comp
    ((algebraMap (MvPolynomial (Fin m) K) (Localization.AtPrime Q)).comp
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K))

#print axioms residueFieldMap

/-- The structure map is injective: a ring hom out of the field `K`
(a simple ring) into the nontrivial residue field.
-/
theorem residueFieldMap_injective (m : ℕ) (K : Type*) [Field K]
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Function.Injective (residueFieldMap m K Q) := by
  have : Field (Localization.AtPrime Q
      ⧸ maximalIdeal (Localization.AtPrime Q)) :=
    IsLocalRing.ResidueField.field _
  exact RingHom.injective _

#print axioms residueFieldMap_injective

/-- T2 at general prime `Q`: infinite `K` gives infinite residue field.
-/
theorem infinite_residue_of_infinite (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Infinite (Localization.AtPrime Q
      ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  Infinite.of_injective _ (residueFieldMap_injective m K Q)

#print axioms infinite_residue_of_infinite

/-- T2 at `Q ∈ Ass(R ⧸ J)`: the Ass-gated form consumed verbatim by the
R23 masters (`hChiReduceAtAss_of_gradedExact`:560). Membership is
recorded for shape match; the proof needs only primality.
-/
theorem infinite_residue_atAss_of_infinite (m : ℕ) (K : Type*) [Field K]
    [Infinite K] (J : Ideal (MvPolynomial (Fin m) K))
    (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime]
    (_hQ : Q ∈ associatedPrimes _ (_ ⧸ J)) :
    Infinite (Localization.AtPrime Q
      ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  infinite_residue_of_infinite m K Q

#print axioms infinite_residue_atAss_of_infinite

/-- T2 under the formalization's top-level hypothesis: `IsAlgClosed K`
gives `Infinite K` (Mathlib instance), hence infinite residues.
-/
theorem infinite_residue_of_algClosed (m : ℕ) (K : Type*) [Field K]
    [IsAlgClosed K] (Q : Ideal (MvPolynomial (Fin m) K)) [Q.IsPrime] :
    Infinite (Localization.AtPrime Q
      ⧸ maximalIdeal (Localization.AtPrime Q)) :=
  infinite_residue_of_infinite m K Q

#print axioms infinite_residue_of_algClosed

end KoszulResidueInfinite
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
