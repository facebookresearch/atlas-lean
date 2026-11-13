/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Varieties with commutative relative multiplication (Kourovka Notebook Problem 2.44)

Kourovka Notebook, Archive of Solved Problems, Problem 2.44 (A. I. Mal'cev): let `𝔄` and `𝔅` be
subvarieties of a variety of groups `𝔐`; then `(𝔄𝔅) ∩ 𝔐` is the `𝔐`-product of `𝔄` by `𝔅`. Does
there exist a non-abelian variety `𝔐` with an infinite lattice of subvarieties and commutative
`𝔐`-multiplication?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import WantedExt.Algebra.VarietyIdentitiesShared

@[expose] public section

namespace MathlibExt.GroupTheory.CommutativeVarietyProductKourovka2Problem44Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.44 (A. I.
Mal'cev). UnsolvedMath record UM-00700117 (`KOU-2.44`), dataset ulamai/UnsolvedMath v1.8.0.

Varieties are given by sets of laws `L ⊆ FreeGroup ℕ` and compared as classes of groups in `Type`
(`InVariety`, shared in `WantedExt.Algebra.VarietyIdentitiesShared`); the product `𝔄𝔅` is the class
of groups with a normal subgroup in `𝔄` and quotient in `𝔅`. An infinite lattice of subvarieties
means `n` pairwise distinct subvarieties for every `n`; commutativity means `(𝔄𝔅) ∩ 𝔐 = (𝔅𝔄) ∩ 𝔐`
for all subvarieties `𝔄`, `𝔅`.
-/

open MathlibExt.Algebra.VarietyIdentitiesShared

/-- `G` lies in the product `𝔄𝔅` of the varieties defined by `LA` and `LB`: it has a normal
subgroup in `𝔄` with quotient in `𝔅`. -/
def InProduct (LA LB : Set (FreeGroup ℕ)) (G : Type) [Group G] : Prop :=
  ∃ (N : Subgroup G) (_ : N.Normal), InVariety LA N ∧ InVariety LB (G ⧸ N)

/-- The variety defined by `LA` is contained in the one defined by `LM`. -/
def IsSubvariety (LA LM : Set (FreeGroup ℕ)) : Prop :=
  ∀ (G : Type) [Group G], InVariety LA G → InVariety LM G

/-- The law sets `L` and `L'` define the same variety. -/
def SameVariety (L L' : Set (FreeGroup ℕ)) : Prop :=
  ∀ (G : Type) [Group G], InVariety L G ↔ InVariety L' G

/-- Kourovka 2.44 (A. I. Mal'cev): there is a non-abelian variety of groups `𝔐` with an infinite
lattice of subvarieties (for every `n`, `n` pairwise distinct subvarieties) in which the
`𝔐`-product `(𝔄𝔅) ∩ 𝔐` of subvarieties is commutative. -/
def nonabelianVarietyWithCommutativeProductExists : Prop :=
  ∃ LM : Set (FreeGroup ℕ),
    (∃ (G : Type) (_ : Group G), InVariety LM G ∧ ∃ x y : G, x * y ≠ y * x) ∧
    (∀ n : ℕ, ∃ Ls : Fin n → Set (FreeGroup ℕ), (∀ i, IsSubvariety (Ls i) LM) ∧
      ∀ i j, i ≠ j → ¬ SameVariety (Ls i) (Ls j)) ∧
    ∀ LA LB : Set (FreeGroup ℕ), IsSubvariety LA LM → IsSubvariety LB LM →
      ∀ (G : Type) [Group G], InVariety LM G → (InProduct LA LB G ↔ InProduct LB LA G)

/--
Resolved true: the Kourovka Archive answers 2.44 "Yes, there does", with the example `𝔐 = 𝔄_p𝔄_p`
for a prime `p`, where `𝔄_p` is the variety of abelian groups of exponent `p` (Yu. M. Gorchakov,
1967). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.44
(A. I. Mal'cev); resolution: Yu. M. Gorchakov, talk of 21 June 1967, Krasnoyarsk, Kourovka Archive,
Problem 2.44: Yes, for example 𝔐 = 𝔄_p𝔄_p, where 𝔄_p is the variety of abelian groups of prime
exponent p (Gorchakov), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted nonabelianVarietyWithCommutativeProductExists_holds :
    nonabelianVarietyWithCommutativeProductExists

end MathlibExt.GroupTheory.CommutativeVarietyProductKourovka2Problem44Wanted
