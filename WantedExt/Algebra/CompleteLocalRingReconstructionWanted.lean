/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-1453-004: Reconstructing complete local rings from finite quotients.
If complete local Noetherian rings `A`, `B` satisfy `A/𝔪^r ≅ B/𝔫^r`
for every natural number `r`, must `A ≅ B`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

@[expose] public section

namespace MathlibExt.Algebra.CompleteLocalRingReconstructionWanted

/-! Source record `OWR-1453-004__30000671`. -/

/-- **Complete local ring reconstruction conjecture.** The statement that any two commutative
Noetherian local rings $A$ and $B$, with maximal ideals $\mathfrak m_A$ and $\mathfrak m_B$, that
are complete and Hausdorff for the $\mathfrak m_A$-adic and $\mathfrak m_B$-adic topologies are
isomorphic as rings whenever $A/\mathfrak m_A^r$ and $B/\mathfrak m_B^r$ are isomorphic as rings
for every natural number $r$.

Source: OWR-1453-004. -/
def conjecture : Prop :=
  ∀ (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B],
    (∀ r : ℕ, Nonempty (A ⧸ (IsLocalRing.maximalIdeal A) ^ r ≃+*
      B ⧸ (IsLocalRing.maximalIdeal B) ^ r)) →
    Nonempty (A ≃+* B)

/--
**The complete local ring reconstruction conjecture is false.** There exist commutative
Noetherian local rings $A$ and $B$, with maximal ideals $\mathfrak m_A$ and $\mathfrak m_B$, that
are complete and Hausdorff for the $\mathfrak m_A$-adic and $\mathfrak m_B$-adic topologies, such
that $A/\mathfrak m_A^r$ and $B/\mathfrak m_B^r$ are isomorphic as rings for every natural number
$r$, but $A$ and $B$ are not isomorphic as rings.

Van den Dries proves that such rings are isomorphic when the residue field is algebraic over its
prime field, and reports examples by Gabber showing that the answer is no in general.

Source: Lou van den Dries, Isomorphism of complete local noetherian rings and strong
approximation, Proc. Amer. Math. Soc. 136 (2008), 3435-3448,
https://doi.org/10.1090/S0002-9939-08-09401-X. Moved from
`OpenConjectures/Algebra/CompleteLocalRingReconstruction`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.CompleteLocalRingReconstructionWanted
