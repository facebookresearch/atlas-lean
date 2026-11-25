/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Surjections that are injective on no nontrivial subgroup (Kourovka Notebook Problem 17.50)

Kourovka Notebook, Archive of Solved Problems, Problem 17.50 (E. G. Zelenyuk): is it true that for
every finite group `G`, there is a finite group `F` and a surjective homomorphism `f : F → G` such
that for each nontrivial subgroup `H` of `F`, the restriction `f|_H` is not injective?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Basic.Finite.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.SurjectionNoninjectiveOnSubgroupsKourovka17Problem50Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.50 (E. G.
Zelenyuk). UnsolvedMath record UM-00701352 (`KOU-17.50`), dataset ulamai/UnsolvedMath v1.8.0.

The restriction of `f` to `H` is `f.comp H.subtype`; groups are taken in `Type`.
-/

/-- **Kourovka Problem 17.50: surjections injective on no nontrivial subgroup.** The statement
that for every finite group $G$ there are a finite group $F$ and a surjective homomorphism
$f \colon F \to G$ such that for every nontrivial subgroup $H$ of $F$ the restriction of $f$ to
$H$ is not injective. -/
def surjectionNoninjectiveOnSubgroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G], ∃ (F : Type) (_ : Group F) (_ : Finite F) (f : F →* G),
    Function.Surjective f ∧ ∀ H : Subgroup F, H ≠ ⊥ → ¬ Function.Injective (f.comp H.subtype)

/--
**Burichenko's theorem on surjections injective on no nontrivial subgroup.** For every finite
group $G$ there are a finite group $F$ and a surjective homomorphism $f \colon F \to G$ such that
for every nontrivial subgroup $H$ of $F$ the restriction of $f$ to $H$ is not injective.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 17.50 (E. G. Zelenyuk); resolution: V. P. Burichenko, Math.
Notes 92 (2012), 327-332, Kourovka Archive, Problem 17.50 (Yes, it is).
-/
public theorem_wanted surjectionNoninjectiveOnSubgroups_holds : surjectionNoninjectiveOnSubgroups

end MathlibExt.GroupTheory.SurjectionNoninjectiveOnSubgroupsKourovka17Problem50Wanted
