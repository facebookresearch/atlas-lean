/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_groupCohomology_natCard_H1_eq_natCard_H2_of_finite.lean`
and
`P2M/Sol/S_groupCohomology_natCard_H1_eq_natCard_H2_of_finite.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

@[expose] public section

universe u v

open CategoryTheory groupCohomology

namespace GroupCohomologyFiniteCyclicCardAux

variable {R : Type u} [Ring R]

private theorem natCard_ker_eq_natCard_homology_mul (S : ShortComplex (ModuleCat R))
    [Finite S.X₂] :
    Nat.card (LinearMap.ker S.g.hom) =
      Nat.card S.homology * Nat.card (LinearMap.range S.f.hom) := by
  rw [Nat.card_congr S.moduleCatHomologyIso.toLinearEquiv.toEquiv]
  have h1 : Nat.card (LinearMap.ker S.g.hom)
      = Nat.card (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
        * Nat.card (LinearMap.range S.moduleCatToCycles) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (LinearMap.range S.moduleCatToCycles).toAddSubgroup
  have h2 : Nat.card (LinearMap.range S.moduleCatToCycles) =
      Nat.card (LinearMap.range S.f.hom) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun x => ⟨(x.1 : S.X₂), ?_⟩) ⟨?_, ?_⟩)
    · obtain ⟨y, hy⟩ := x.2
      exact ⟨y, by rw [← hy]; rfl⟩
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
      have h' := congrArg (fun z : LinearMap.range S.f.hom => (z : S.X₂)) h
      exact Subtype.ext (Subtype.ext h')
    · rintro ⟨x, y, rfl⟩
      exact ⟨⟨S.moduleCatToCycles y, y, rfl⟩, rfl⟩
  rw [h1, h2]
  rfl

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] (A : Rep k G) (g : G)

private theorem natCard_eq_natCard_ker_mul_natCard_range {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) :
    Nat.card M = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [← Nat.card_congr f.quotKerEquivRange.toEquiv, mul_comm]
  exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (LinearMap.ker f).toAddSubgroup

private theorem finite_homology_of_finite (S : ShortComplex (ModuleCat k))
    [Finite S.X₂] :
    Finite S.homology := by
  haveI : Finite (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  haveI : Finite S.moduleCatLeftHomologyData.H :=
    inferInstanceAs (Finite (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles))
  exact Finite.of_equiv _ S.moduleCatHomologyIso.toLinearEquiv.toEquiv.symm

private theorem natCard_homology_normHomCompSub_eq [Finite A] :
    Nat.card (Rep.FiniteCyclicGroup.normHomCompSub A g).homology =
      Nat.card (Rep.FiniteCyclicGroup.subCompNormHom A g).homology := by
  haveI : Finite (Rep.FiniteCyclicGroup.normHomCompSub A g).X₂ :=
    inferInstanceAs (Finite A)
  haveI : Finite (Rep.FiniteCyclicGroup.subCompNormHom A g).X₂ :=
    inferInstanceAs (Finite A)
  have hS0 : Nat.card (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) =
      Nat.card (Rep.FiniteCyclicGroup.normHomCompSub A g).homology *
        Nat.card (LinearMap.range A.norm.asHom.hom.toLinearMap) :=
    natCard_ker_eq_natCard_homology_mul (Rep.FiniteCyclicGroup.normHomCompSub A g)
  have hS1 : Nat.card (LinearMap.ker A.norm.asHom.hom.toLinearMap) =
      Nat.card (Rep.FiniteCyclicGroup.subCompNormHom A g).homology *
        Nat.card (LinearMap.range (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :=
    natCard_ker_eq_natCard_homology_mul (Rep.FiniteCyclicGroup.subCompNormHom A g)
  have hD := natCard_eq_natCard_ker_mul_natCard_range
    (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap
  have hN := natCard_eq_natCard_ker_mul_natCard_range A.norm.asHom.hom.toLinearMap
  have hpos : 0 < Nat.card (LinearMap.range A.norm.asHom.hom.toLinearMap) *
      Nat.card (LinearMap.range (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have key : Nat.card (Rep.FiniteCyclicGroup.normHomCompSub A g).homology *
        (Nat.card (LinearMap.range A.norm.asHom.hom.toLinearMap) *
          Nat.card (LinearMap.range (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap))
      = Nat.card (Rep.FiniteCyclicGroup.subCompNormHom A g).homology *
        (Nat.card (LinearMap.range A.norm.asHom.hom.toLinearMap) *
          Nat.card (LinearMap.range (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)) := by
    calc _ = Nat.card (LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) *
            Nat.card (LinearMap.range (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap) := by
            rw [hS0]; ring
      _ = Nat.card A := hD.symm
      _ = Nat.card (LinearMap.ker A.norm.asHom.hom.toLinearMap) *
          Nat.card (LinearMap.range A.norm.asHom.hom.toLinearMap) := hN
      _ = _ := by rw [hS1]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

end GroupCohomologyFiniteCyclicCardAux

/-- For a finite cyclic group `G` and a finite `G`-module `A` over a
commutative ring in the same universe, the first and second group
cohomology groups are finite of equal cardinality. -/
public theorem groupCohomology.natCard_H1_eq_natCard_H2_of_finite
    {k : Type u} [CommRing k] {G : Type u} [Group G] [Finite G] [IsCyclic G]
    (A : Rep k G) [Finite A] :
    Finite (H1 A) ∧ Finite (H2 A) ∧ Nat.card (H1 A) = Nat.card (H2 A) := by
  classical
  letI : CommGroup G := IsCyclic.commGroup
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  haveI : Finite (Rep.FiniteCyclicGroup.normHomCompSub A g).X₂ :=
    inferInstanceAs (Finite A)
  haveI : Finite (Rep.FiniteCyclicGroup.subCompNormHom A g).X₂ :=
    inferInstanceAs (Finite A)
  have e1 := (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1
    (by decide)).toLinearEquiv.toEquiv
  have e2 := (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2
    (by decide)).toLinearEquiv.toEquiv
  haveI := GroupCohomologyFiniteCyclicCardAux.finite_homology_of_finite
    (Rep.FiniteCyclicGroup.normHomCompSub A g)
  haveI := GroupCohomologyFiniteCyclicCardAux.finite_homology_of_finite
    (Rep.FiniteCyclicGroup.subCompNormHom A g)
  refine ⟨Finite.of_equiv _ e1.symm, Finite.of_equiv _ e2.symm, ?_⟩
  rw [Nat.card_congr e1, Nat.card_congr e2]
  exact (GroupCohomologyFiniteCyclicCardAux.natCard_homology_normHomCompSub_eq A g).symm
