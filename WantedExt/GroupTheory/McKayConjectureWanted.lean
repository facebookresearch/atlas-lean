/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Complex.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Character
public import Mathlib.SetTheory.Cardinal.Basic

open CategoryTheory

namespace MetaMathlibExt

@[expose] public section

/-- **Irreducible characters of $p'$-degree.** For a group $G$ and a natural number $p$,
$\mathrm{Irr}_{p'}(G)$ is the set of functions $G \to \mathbb{C}$ that are characters of simple
finite-dimensional complex representations of $G$ whose dimension is not divisible by $p$.

Two simple representations have equal characters exactly when they are isomorphic, so these
characters correspond bijectively to the isomorphism classes of such representations, which is
what the McKay conjecture counts. -/
def pPrimeCharacters (G : Type*) [Group G] (p : ℕ) : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ ∧ ¬p ∣ Module.finrank ℂ V}

/-- **McKay conjecture (Cabanes–Späth theorem).** For every finite group $G$, every prime $p$ and
every Sylow $p$-subgroup $P$ of $G$, with normalizer $N_G(P)$ in $G$, the sets
$\mathrm{Irr}_{p'}(G)$ and $\mathrm{Irr}_{p'}(N_G(P))$ of irreducible complex characters of
degree not divisible by $p$ have the same cardinality.

Source: M. Cabanes and B. Späth, *The McKay conjecture*,
Ann. of Math. 203(3) (2026), arXiv:2410.20392, doi:10.4007/annals.2026.203.3.5. -/
theorem_wanted mckay_irr_equicardinal (G : Type*) [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    Cardinal.mk (pPrimeCharacters G p) =
      Cardinal.mk (pPrimeCharacters (Subgroup.normalizer (P : Set G)) p)

end

end MetaMathlibExt
