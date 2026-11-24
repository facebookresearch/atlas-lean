/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Valuation.SimpleRootLifting

@[expose] public section

open Polynomial

universe u

example {K : Type*} [Field K] (A : ValuationSubring K) (g : Polynomial A)
    (hsplit : (g.map (algebraMap A K)).Splits)
    (b : IsLocalRing.ResidueField A)
    (hb : (g.map (IsLocalRing.residue A)).rootMultiplicity b = 1) :
    ∃! r : K, (g.map (algebraMap A K)).IsRoot r ∧
      ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b :=
  ValuationSubring.existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one
    A g hsplit b hb

example {K : Type u} [Field K] (A : ValuationSubring K) (g : Polynomial A)
    (hsplit : (g.map (algebraMap A K)).Splits)
    (b : IsLocalRing.ResidueField A)
    (hb : (g.map (IsLocalRing.residue A)).rootMultiplicity b = 1) :
    ∃ r : K, (g.map (algebraMap A K)).IsRoot r ∧
      ∃ h : r ∈ A, IsLocalRing.residue A ⟨r, h⟩ = b :=
  (ValuationSubring.existsUnique_isRoot_residue_eq_of_rootMultiplicity_map_residue_eq_one
    A g hsplit b hb).exists
