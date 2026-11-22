/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Character
public import Mathlib.SetTheory.Cardinal.Basic

open CategoryTheory

namespace MetaMathlibExt

@[expose] public section

/-- The irreducible complex characters of `G` of `p'`-degree, as a set of
functions: the characters of simple finite-dimensional complex representations
whose dimension is not divisible by `p`. Two simple representations have equal
characters exactly when they are isomorphic, so this set is in canonical
bijection with the set `Irr_{p'}(G)` counted by the McKay conjecture. -/
def pPrimeCharacters (G : Type*) [Group G] (p : ℕ) : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ ∧ ¬p ∣ Module.finrank ℂ V}

/-- The **McKay conjecture**, now the theorem of Cabanes and Späth: for every
finite group `G`, every prime `p`, and every Sylow `p`-subgroup `P` of `G`, the
irreducible complex characters of `G` of degree not divisible by `p` are
equinumerous with those of the normalizer of `P` in `G`.

Source: M. Cabanes and B. Späth, *The McKay conjecture*,
Ann. of Math. 203(3) (2026), arXiv:2410.20392, doi:10.4007/annals.2026.203.3.5. -/
theorem_wanted mckay_irr_equicardinal (G : Type*) [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    Cardinal.mk (pPrimeCharacters G p) =
      Cardinal.mk (pPrimeCharacters (Subgroup.normalizer (P : Set G)) p)

/-! ## AnnalsChallenge statement of the McKay theorem

The formalization above (pPrimeCharacters / mckay_irr_equicardinal) predates the
AnnalsChallenge port. The declarations below reproduce Thomas Browning's
expert-written AnnalsChallenge formalization of the same theorem
(ImperialCollegeLondon/AnnalsChallenge v1.0.0, e32eb14,
AnnalsChallenge/AnnalsOfMathematics/2026-203-3-McKayConjecture.lean,
Apache License 2.0; dataset paper arXiv:2610.18301) verbatim, with only the
WantedExt conversion of the sorried theorem to theorem_wanted. It counts
Irr' by Set.ncard and coprimality, where the formalization above uses
Cardinal.mk and non-divisibility. -/

namespace McKayConjecture

open CategoryTheory Module Subgroup

variable (ℓ : ℕ) (X : Type*) [Group X] [Finite X]

/-- `Irr'(X)` is the set of complex irreducible characters of `X` whose degree is prime to `ℓ`. -/
def Irr' : Set (X → ℂ) :=
  {χ | ∃ V : FDRep ℂ X, Simple V ∧ V.character = χ ∧ ℓ.Coprime (finrank ℂ V)}

/--
Statement of Theorem 1.1:

Let `X` be a finite group, `ℓ` a prime and `S` a Sylow `ℓ`-subgroup of `X`. Let `Irr_ℓ'(X)` denote
the set of complex irreducible characters of `X` whose degree is prime to `ℓ`. Then
`|Irr_ℓ'(X)| = |Irr_ℓ'(N_X(S))|`.

Source: M. Cabanes and B. Spaeth, The McKay Conjecture on character degrees, Annals of Math, 203 (3) 2026. Statement taken verbatim from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2026-203-3-McKayConjecture.lean (author: Thomas Browning; Apache License 2.0); dataset paper arXiv:2610.18301.
-/
public theorem_wanted theorem_1_1 (hℓ : ℓ.Prime) (S : Sylow ℓ X) :
    (Irr' ℓ X).ncard = (Irr' ℓ (normalizer S : Subgroup X)).ncard

end McKayConjecture

end

end MetaMathlibExt
