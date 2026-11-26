/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Deformations_LiftFunctor.lean`
and
`Definitions/Def_Deformations_Deformations_Lemmas.lean`
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

The cited upstream files are adapted from files of the Imperial College London FLT
project (https://github.com/ImperialCollegeLondon/FLT, branch `main` as of 2026-05-21, as
the upstream `ATTRIBUTION.md` records; headers checked at commit
`a7dbce8494c29858093974a612a72b6454fc5cba`). The portions of this file that come from them
are adapted from:

`FLT/Deformations/LiftFunctor.lean` (FLT):
Copyright (c) 2025 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde

`FLT/Deformations/Lemmas.lean` (FLT):
Copyright (c) 2025 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/

module

public import Mathlib.Topology.Instances.Matrix
public import MathlibExt.RingTheory.Deformations.ProartinianCat

/-!
# The functor of continuous representations

Let `G` be a topological group, `𝓞` a local ring and `n` a finite type. For a local proartinian
`𝓞`-algebra `R` we consider continuous homomorphisms `ρ : G →ₜ* GL n R`. These form a functor
`repnFunctor n G 𝓞` on `ProartinianCat 𝓞`. Two representations are *strictly equivalent* if they
are conjugate by a matrix reducing to the identity modulo the maximal ideal; the quotient by this
relation is the functor `repnQuotFunctor n G 𝓞`.

## Main definitions

* `Units.mapₜ`, `ContinuousAlgHom.mapMatrix`: continuous versions of the corresponding maps.
* The pointwise action of a monoid acting distributively on `G` on `M →* G` and `M →ₜ* G`.
* `Deformation.repnFunctor n G 𝓞`: `R ↦ (G →ₜ* GL n R)`.
* `Deformation.repnQuotFunctor n G 𝓞`: representations up to strict equivalence.
* `Deformation.toRepnQuot n G 𝓞`: the quotient map `repnFunctor ⟶ repnQuotFunctor`.
-/

@[expose] public section

/-- **Continuous maps of unit groups.** The continuous homomorphism of unit groups induced by a
continuous monoid homomorphism. -/
@[simps!]
def Units.mapₜ {M N : Type*} [Monoid M] [Monoid N] [TopologicalSpace M] [TopologicalSpace N]
    (f : M →ₜ* N) : Mˣ →ₜ* Nˣ :=
  ⟨Units.map f, Continuous.units_map _ f.continuous⟩

/-- **Continuous maps of matrix algebras.** The continuous algebra map of matrix rings induced by
a continuous algebra map. -/
@[simps!]
def ContinuousAlgHom.mapMatrix
    {R A B n : Type*} [CommSemiring R] [Semiring A] [Semiring B] [TopologicalSpace A]
    [TopologicalSpace B] [Algebra R A] [Algebra R B] (f : A →A[R] B)
    [Fintype n] [DecidableEq n] :
    Matrix n n A →A[R] Matrix n n B :=
  ⟨f.1.mapMatrix, Continuous.matrix_map continuous_id' f.2⟩

/-- A monoid acting distributively on `G` acts pointwise on monoid homomorphisms into `G`. -/
instance MonoidHom.instMulActionOfMulDistribMulAction
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G] :
    MulAction α (M →* G) where
  smul a f := ⟨⟨a • f, by simp⟩, by simp⟩
  one_smul _ := by ext; exact one_smul _ _
  mul_smul a b f := by ext x; change (a * b) • (f x) = a • b • (f x); simp [mul_smul]

@[simp]
theorem MonoidHom.coe_smul
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    (a : α) (f : M →* G) :
    ⇑(a • f) = a • ⇑f := rfl

/-- A monoid acting distributively and continuously on `G` acts pointwise on continuous monoid
homomorphisms into `G`. -/
instance ContinuousMonoidHom.instMulActionOfMulDistribMulAction
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G] :
    MulAction α (M →ₜ* G) where
  smul a f := ⟨a • f, .const_smul f.2 _⟩
  one_smul _ := by ext; exact one_smul _ _
  mul_smul a b f := by ext x; change (a * b) • (f x) = a • b • (f x); simp [mul_smul]

@[simp]
theorem ContinuousMonoidHom.coe_smul
    {α M G : Type*} [Monoid M] [Monoid G] [Monoid α] [MulDistribMulAction α G]
    [TopologicalSpace M] [TopologicalSpace G] [ContinuousConstSMul α G]
    (a : α) (f : M →ₜ* G) :
    ⇑(a • f) = a • ⇑f := rfl

open CategoryTheory IsLocalRing

namespace Deformation

universe u v w

variable {n : Type v} [Fintype n] [DecidableEq n] (G : Type w) [Group G] [TopologicalSpace G]
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]

variable (n) in
/-- **The functor of continuous representations.** The functor sending a local proartinian
`𝓞`-algebra `R` to the continuous representations `G →ₜ* GL n R`. -/
def repnFunctor : ProartinianCat 𝓞 ⥤ Type (max u v w) where
  obj R := G →ₜ* GL n R
  map {R S} f := TypeCat.ofHom
    (fun ρ ↦ .comp (Units.mapₜ (f.hom.mapMatrix (n := n) : Matrix n n R →ₜ* Matrix n n S)) ρ)

omit [IsLocalRing 𝓞] in
@[simp]
theorem repnFunctor_map {R S : ProartinianCat 𝓞} (f : R ⟶ S) (ρ : G →ₜ* GL n R) (x : G) :
    DFunLike.coe (F := G →ₜ* GL n S) ((repnFunctor n G 𝓞).map f ρ) x =
      Matrix.GeneralLinearGroup.map (n := n) f.hom.toRingHom (ρ x) := rfl

variable (n)

set_option backward.isDefEq.respectTransparency false in
/-- **Representations up to strict equivalence.** For a local ring `𝓞`, the functor of continuous
representations up to strict equivalence: conjugation by matrices reducing to the identity
modulo the maximal ideal. -/
noncomputable def repnQuotFunctor : ProartinianCat 𝓞 ⥤ Type (max u v w) where
  obj R := MulAction.orbitRel.Quotient ((Matrix.GeneralLinearGroup.map (n := n)
    (ProartinianCat.toResidueField R).hom.toRingHom).ker.comap (ConjAct.ofConjAct.toMonoidHom))
    (G →ₜ* GL n R)
  map {R S} f := TypeCat.ofHom <| Quotient.map ((repnFunctor n G 𝓞).map f) (by
    rintro _ ρ ⟨⟨g, hg⟩, rfl⟩
    refine ⟨⟨.toConjAct (Matrix.GeneralLinearGroup.map f.hom.toRingHom g.ofConjAct), ?_⟩, ?_⟩
    · simpa [← Matrix.GeneralLinearGroup.map_comp_apply, ← Matrix.GeneralLinearGroup.map_comp,
        ← RingHom.coe_comp, ← ContinuousAlgHom.coe_comp,
        ← AlgHom.comp_toRingHom, ← ProartinianCat.hom_comp,
        Subsingleton.elim _ R.toResidueField]
    · obtain ⟨g, rfl⟩ := ConjAct.toConjAct.surjective g
      ext1 γ
      simp [ConjAct.toConjAct_smul, ← map_inv, -ConjAct.ofConjAct_inv, ← map_mul])
  map_id _ := by ext ⟨_⟩; rfl
  map_comp _ _ := by ext ⟨_⟩; rfl

/-- **Strict equivalence classes.** The quotient map from representations to strict equivalence
classes. -/
noncomputable def toRepnQuot : repnFunctor n G 𝓞 ⟶ repnQuotFunctor n G 𝓞 where
  app _ := TypeCat.ofHom Quotient.mk''
  naturality _ _ _ := rfl

end Deformation
