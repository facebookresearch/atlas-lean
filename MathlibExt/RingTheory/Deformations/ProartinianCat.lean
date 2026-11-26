/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_Deformations_ProartinianCat.lean`
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

`FLT/Deformations/Categories.lean` (FLT):
Copyright (c) 2025 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang, Kevin Buzzard, Pietro Monticone

`FLT/Deformations/Lemmas.lean` (FLT):
Copyright (c) 2025 Andrew Yang. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.Topology.Algebra.Algebra
public import MathlibExt.RingTheory.Deformations.IsProartinian
public import MathlibExt.RingTheory.Deformations.IsResidueAlgebra

/-!
# The category of local proartinian `𝓞`-algebras

Fix a commutative ring `𝓞`. A *local proartinian `𝓞`-algebra* is a proartinian topological local
`𝓞`-algebra `R` whose structure map is local and which is a residue algebra over `𝓞`. These
algebras with continuous `𝓞`-algebra maps form the category `ProartinianCat 𝓞` on which Galois
deformation functors are defined. When `𝓞` is local, the residue field of `𝓞` with the discrete
topology is a terminal object.

## Main definitions

* `Deformation.IsLocalProartinianAlgebra 𝓞 R`: the conditions above.
* `Deformation.ProartinianCat 𝓞`: the category of local proartinian `𝓞`-algebras.
* `Deformation.ProartinianCat.residueField`: the residue field of `𝓞`, as an object.
* `Deformation.ProartinianCat.toResidueField R`: the reduction map `R ⟶ residueField`.
* `Deformation.ProartinianCat.isTerminalResidueField`: `residueField` is terminal.
-/

@[expose] public section

/-- **Continuity of homomorphisms to a discrete target.** A monoid homomorphism from a topological
group to a discrete target is continuous if and only if its kernel is open. -/
@[to_additive /-- An additive monoid homomorphism from an additive topological group to a
discrete target is continuous if and only if its kernel is open. -/]
theorem MonoidHom.continuous_iff_isOpen_ker {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [Group α] [MulOneClass β] {f : α →* β} [DiscreteTopology β]
    [IsTopologicalGroup α] :
    Continuous f ↔ IsOpen (X := α) f.ker := by
  refine ⟨fun H ↦ H.1 {1} (isOpen_discrete _), fun H ↦ continuous_of_continuousAt_one _ ?_⟩
  simpa [ContinuousAt] using Filter.eventually_of_mem (H.mem_nhds (by simp)) (by simp)

/-- **Continuity of ring homomorphisms to a discrete target.** A ring homomorphism from a ring
whose additive group is a topological group to a discrete semiring is continuous if and only if
its kernel is open. -/
theorem RingHom.continuous_iff_isOpen_ker {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [Ring α] [Semiring β] {f : α →+* β} [DiscreteTopology β]
    [IsTopologicalAddGroup α] :
    Continuous f ↔ IsOpen (X := α) (RingHom.ker f) :=
  AddMonoidHom.continuous_iff_isOpen_ker (f := f.toAddMonoidHom)

theorem ContinuousAlgHom.isLocalHom_toRingHom {R A B : Type*}
    [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    [TopologicalSpace A] [TopologicalSpace B] {f : A →A[R] B} :
    IsLocalHom f.toRingHom ↔ IsLocalHom f :=
  ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

instance {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
    [Algebra R A] [Algebra R B] [TopologicalSpace A] [TopologicalSpace B]
    (f : A →A[R] B) [IsLocalHom f] : IsLocalHom f.toRingHom := by
  rwa [ContinuousAlgHom.isLocalHom_toRingHom]

instance IsLocalRing.isLocalHom_algebraMap_residueField {R : Type*} [CommRing R]
    [IsLocalRing R] : IsLocalHom (algebraMap R (IsLocalRing.ResidueField R)) := by
  rw [IsLocalRing.ResidueField.algebraMap_eq]
  infer_instance

universe u

open CategoryTheory Function Limits IsLocalRing

namespace Deformation

variable (𝓞 : Type u) [CommRing 𝓞]

/-- **Local proartinian algebras.** A *local proartinian `𝓞`-algebra*: a proartinian topological
local ring with a local structure map from `𝓞` that surjects onto its residue field. -/
class IsLocalProartinianAlgebra
    (R : Type u) [CommRing R] [TopologicalSpace R] [Algebra 𝓞 R] : Prop extends
  IsTopologicalRing R, IsLocalRing R, IsProartinian R,
  IsLocalHom (algebraMap 𝓞 R), IsResidueAlgebra 𝓞 R

/-- **The category of local proartinian algebras.** The category of local proartinian
`𝓞`-algebras, with continuous `𝓞`-algebra maps as morphisms. -/
structure ProartinianCat where
  /-- The underlying ring. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [algebra : Algebra 𝓞 carrier]
  [isLocalProartinianAlgebra : IsLocalProartinianAlgebra 𝓞 carrier]

namespace ProartinianCat

attribute [instance] commRing algebra topologicalSpace isLocalProartinianAlgebra

initialize_simps_projections ProartinianCat (-commRing, -algebra, -topologicalSpace)

instance : CoeSort (ProartinianCat 𝓞) (Type u) := ⟨carrier⟩

attribute [coe] ProartinianCat.carrier

/-- **Local proartinian algebras as objects.** The object of `ProartinianCat 𝓞` with carrier
`X`. -/
abbrev of (X : Type u) [CommRing X] [Algebra 𝓞 X]
    [TopologicalSpace X] [IsLocalProartinianAlgebra 𝓞 X] :
    ProartinianCat 𝓞 :=
  ⟨X⟩

theorem coe_of (X : Type u) [CommRing X] [Algebra 𝓞 X] [TopologicalSpace X]
    [IsLocalProartinianAlgebra 𝓞 X] :
    of 𝓞 X = X := rfl

variable {𝓞} in
/-- **Morphisms of local proartinian algebras.** Morphisms in `ProartinianCat 𝓞` are continuous
`𝓞`-algebra maps. -/
@[ext]
structure Hom (A B : ProartinianCat 𝓞) where
  /-- The underlying continuous algebra map. -/
  hom : A →A[𝓞] B

instance : Category (ProartinianCat 𝓞) where
  Hom A B := Hom A B
  id A := ⟨ContinuousAlgHom.id 𝓞 A⟩
  comp f g := ⟨g.hom.comp f.hom⟩

instance (A B : ProartinianCat 𝓞) (f : A ⟶ B) : IsLocalHom f.hom := by
  convert isLocalHom_of_isContinuous_of_isProartinian f.hom.toRingHom f.hom.cont
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

variable {𝓞} in
/-- **Continuous algebra maps as morphisms.** The morphism of `ProartinianCat 𝓞` given by a
continuous algebra map. -/
abbrev ofHom {A B : Type u}
    [CommRing A] [Algebra 𝓞 A] [TopologicalSpace A] [IsLocalProartinianAlgebra 𝓞 A]
    [CommRing B] [Algebra 𝓞 B] [TopologicalSpace B] [IsLocalProartinianAlgebra 𝓞 B]
    (f : A →A[𝓞] B) :
    of 𝓞 A ⟶ of 𝓞 B := ⟨f⟩

variable {𝓞}

variable {X Y Z : Type u}
  [CommRing X] [Algebra 𝓞 X] [TopologicalSpace X] [IsLocalProartinianAlgebra 𝓞 X]
  [CommRing Y] [Algebra 𝓞 Y] [TopologicalSpace Y] [IsLocalProartinianAlgebra 𝓞 Y]
  [CommRing Z] [Algebra 𝓞 Z] [TopologicalSpace Z] [IsLocalProartinianAlgebra 𝓞 Z]

variable {A B C : ProartinianCat 𝓞}

@[simp]
theorem hom_id : (𝟙 A :).hom = ContinuousAlgHom.id 𝓞 A := rfl

theorem id_apply (x) : (𝟙 A :).hom x = x := rfl

@[simp]
theorem hom_comp (f : A ⟶ B) (g : B ⟶ C) : (f ≫ g).hom = g.hom.comp f.hom := rfl

theorem comp_apply (f : A ⟶ B) (g : B ⟶ C) (x) : (f ≫ g).hom x = g.hom (f.hom x) := rfl

@[ext]
theorem hom_ext {f g : A ⟶ B} (hf : f.hom = g.hom) : f = g :=
  Hom.ext hf

theorem hom_ofHom (f : X →A[𝓞] Y) : (ofHom f).hom = f := rfl

@[simp]
theorem ofHom_hom (f : A ⟶ B) : ofHom (Hom.hom f) = f := rfl

@[simp]
theorem ofHom_id : ofHom (ContinuousAlgHom.id 𝓞 X) = 𝟙 (of 𝓞 X) := rfl

@[simp]
theorem ofHom_comp (f : X →A[𝓞] Y) (g : Y →A[𝓞] Z) :
    ofHom (g.comp f) = ofHom f ≫ ofHom g :=
  rfl

section residueField

variable [IsLocalRing 𝓞]

set_option backward.isDefEq.respectTransparency false in
/-- **The residue field as a local proartinian algebra.** For a local ring `𝓞`, the residue field
of `𝓞` with the discrete topology, as an object of `ProartinianCat 𝓞`. -/
def residueField : ProartinianCat 𝓞 where
  carrier := ResidueField 𝓞
  topologicalSpace := ⊥
  isLocalProartinianAlgebra :=
    letI : TopologicalSpace (ResidueField 𝓞) := ⊥
    letI : DiscreteTopology (ResidueField 𝓞) := ⟨rfl⟩
    ⟨⟩

instance : DiscreteTopology (residueField (𝓞 := 𝓞)) := ⟨rfl⟩

noncomputable instance : Field (residueField (𝓞 := 𝓞)) :=
  inferInstanceAs (Field (ResidueField 𝓞))

set_option backward.isDefEq.respectTransparency false in
/-- **Reduction to the residue field.** For a local ring `𝓞`, the reduction map from a local
proartinian `𝓞`-algebra to the residue field of `𝓞`. -/
noncomputable def toResidueField (R : ProartinianCat 𝓞) : R ⟶ residueField where
  hom := ⟨(IsResidueAlgebra.algEquiv 𝓞 R).symm.toAlgHom.comp (IsScalarTower.toAlgHom 𝓞 R _), by
    refine (RingHom.continuous_iff_isOpen_ker (β := residueField) (f := AlgHom.toRingHom _)).mpr ?_
    dsimp [residueField]
    rw [AlgHom.comp_toRingHom, RingHom.ker_comp_of_injective]
    · simp only [IsScalarTower.coe_toAlgHom, ResidueField.algebraMap_eq, residue]
      rw [Ideal.mk_ker]
      exact isOpen_maximalIdeal_of_isProartinian
    · exact (IsResidueAlgebra.algEquiv 𝓞 R).symm.injective⟩

theorem toResidueField_surjective (R : ProartinianCat 𝓞) :
    Function.Surjective (toResidueField R).hom :=
  (IsResidueAlgebra.algEquiv 𝓞 R).symm.surjective.comp Ideal.Quotient.mk_surjective

theorem ker_toResidueField (R : ProartinianCat 𝓞) :
    RingHom.ker (toResidueField R).hom = maximalIdeal R :=
  (RingHom.ker_comp_of_injective _ (f := (IsResidueAlgebra.algEquiv 𝓞 R).symm.toRingHom)
    (IsResidueAlgebra.algEquiv 𝓞 R).symm.injective).trans Ideal.mk_ker

/-- **Morphisms to the residue field.** Every morphism to the residue field sends `r` to the
residue of its chosen preimage. -/
theorem hom_apply_eq_residue_preimage {R : ProartinianCat 𝓞} (f : R ⟶ residueField)
    (r : R.carrier) :
    f.hom r = residue _ (IsResidueAlgebra.preimage 𝓞 r) := by
  trans f.hom (algebraMap _ _ (IsResidueAlgebra.preimage 𝓞 r))
  · rw [← sub_eq_zero, ← map_sub, ← not_ne_iff,
      ← @isUnit_iff_ne_zero _ _ (f.hom (r - (algebraMap 𝓞 ↑R) (IsResidueAlgebra.preimage 𝓞 r)))]
    change ¬IsUnit (f.hom.toRingHom _)
    rw [isUnit_map_iff f.hom.toRingHom, ← mem_nonunits_iff, ← mem_maximalIdeal]
    exact IsResidueAlgebra.preimage_spec _ _
  · erw [AlgHom.commutes]; rfl

noncomputable instance (R : ProartinianCat 𝓞) : Unique (R ⟶ residueField) := by
  refine ⟨⟨toResidueField R⟩, fun f ↦ ?_⟩
  ext x
  rw [hom_apply_eq_residue_preimage, hom_apply_eq_residue_preimage]

/-- **The residue field is terminal.** For a local ring `𝓞`, the residue field of `𝓞` is a
terminal object of `ProartinianCat 𝓞`. -/
noncomputable def isTerminalResidueField : IsTerminal (residueField (𝓞 := 𝓞)) := .ofUnique _

end residueField

end ProartinianCat

end Deformation
