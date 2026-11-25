/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.FiniteRamificationConductors

@[expose] public noncomputable section

/-!
# Higher-rank finite-image Artin and Swan integrality

Authors: Jean-Pierre Serre.
Source: Corps Locaux, Chapter VI, §2, Artin characters and conductors;
https://doi.org/10.1007/978-1-4757-5673-9.

The local fields, valuation ring, decomposition group, lower groups,
representation and invariant subspaces are actual Mathlib objects.
The conductors are computed from a certified bound N with G_N=1. The
existence of such a bound, i.e. the termination of the lower filtration of a
finite Galois extension of nonarchimedean local fields (Serre, Corps Locaux,
Chapter IV, §1), is requested first; the completed bound-independence laws
then make the conductors intrinsic.
The integrality request is arbitrary finite-dimensional Q_ell representation
integrality, beyond the verified one-dimensional abelian formula. It needs no
condition relating ell to the residue characteristic: the Artin conductor of a
representation over any field of characteristic zero is the inner product of
its character with the Artin character, hence a natural number.
-/

namespace WantedExt.AlgebraicGeometry.RamificationConductors

open ValuativeRel
open MathlibExt.NumberTheory.FiniteRamificationConductors

universe u v w

/-- The lower ramification filtration of a finite Galois extension of
nonarchimedean local fields terminates: some `G_N` is trivial. -/
public theorem_wanted exists_lowerGroup_eq_bot
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Module.Finite K L] [IsGalois K L] :
    ∃ N : ℕ, lowerGroup K L N = ⊥

/-- Integrality of Artin and Swan conductors (Serre, *Corps locaux*, VI §2): let $L/K$ be a finite
Galois extension of nonarchimedean local fields, $ℓ$ a prime, $V$ a finite-dimensional
$ℚ_ℓ$-vector space with a representation $ρ$ of the decomposition group of the valuation ring of
$L$ over $K$, and $N$ a natural number with $G_N = 1$ for the lower ramification groups. Then the
Artin conductor and the Swan conductor of $ρ$, computed from the bound $N$ (the Swan term
omitting $i = 0$), are natural numbers. -/
public theorem_wanted finiteImage_artin_swan_integral
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (L : Type v) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Module.Finite K L] [IsGalois K L]
    (ell : ℕ) [Fact ell.Prime]
    (V : Type w) [AddCommGroup V] [Module ℚ_[ell] V] [Module.Finite ℚ_[ell] V]
    (ρ : Representation ℚ_[ell] (DecompositionGroup K L) V)
    (N : ℕ) (finiteRamification : lowerGroup K L N = ⊥) :
    (∃ a : ℕ, artinConductor K L ell V ρ ⟨N, finiteRamification⟩ = a) ∧
      ∃ s : ℕ, swanConductor K L ell V ρ ⟨N, finiteRamification⟩ = s

end WantedExt.AlgebraicGeometry.RamificationConductors
