/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Embedding finite lattices in subgroup lattices of finite groups (Kourovka Notebook Problem 5.3)

Kourovka Notebook, Archive of Solved Problems, Problem 5.3 (G. M. Bergman): (well-known problem) can
every finite lattice L be embedded in the lattice of subgroups of a finite group?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.Lattice

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteLatticeSubgroupLatticeEmbeddingKourovka5Problem3Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.3 (G. M.
Bergman). UnsolvedMath record UM-00700287 (`KOU-5.3`), dataset ulamai/UnsolvedMath v1.8.0.

An embedding is an injective lattice homomorphism (preserving `⊔` and `⊓`, not necessarily the
bounds) into `Subgroup G`; this is the sublattice question, not the open Pálfy-Pudlák question about
intervals.
-/

/-- Kourovka 5.3 (G. M. Bergman): every finite lattice embeds in the subgroup lattice of a finite
group: there is an injective lattice homomorphism into `Subgroup G`. -/
def finiteLatticeEmbedsInSubgroupLattice : Prop :=
  ∀ (L : Type) [Lattice L] [Finite L], ∃ (G : Type) (_ : Group G) (_ : Finite G)
    (f : LatticeHom L (Subgroup G)), Function.Injective f

/--
Resolved true: the Kourovka Archive answers 5.3 "Yes, it can", citing Pudlák and Tůma, Every finite
lattice can be embedded in a finite partition lattice (Algebra Universalis 10 (1980), 74-95).
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.3 (G. M.
Bergman); resolution: P. Pudlák and J. Tůma, Every finite lattice can be embedded in a finite
partition lattice, Algebra Universalis 10 (1980), 74-95, Kourovka Archive, Problem 5.3: Yes, it can
(Pudlák-Tůma); the paper's title and main theorem: every finite lattice embeds in the partition
lattice of a finite set, https://doi.org/10.1007/BF02482893.
-/
public theorem_wanted finiteLatticeEmbedsInSubgroupLattice_holds :
    finiteLatticeEmbedsInSubgroupLattice

end MathlibExt.GroupTheory.FiniteLatticeSubgroupLatticeEmbeddingKourovka5Problem3Wanted
