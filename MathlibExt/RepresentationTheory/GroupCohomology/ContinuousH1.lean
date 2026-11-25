/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GroupCohomology_ContinuousH1.lean`
and
`Definitions/Def_GroupCohomology_ContinuousH2.lean`
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

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Continuous first Galois cohomology

For a homomorphism `r : G →* Gal(ℚ̄/ℚ)`, a cochain is *level constant* when
it is invariant under right multiplication by the fixing subgroup of some
finite intermediate field. The level-constant 1-cocycles span a submodule
of `H¹(G, M)`, the continuous first cohomology in this encoding.
-/

@[expose] public section

open CategoryTheory

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
  (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

/-- A 1-cochain is level constant when it factors through a finite level. -/
def IsLevelConstant₁ {X : Type*} (f : G → X) : Prop :=
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g

variable {r} in
/-- Level-constant 1-cochains are closed under addition. -/
lemma IsLevelConstant₁.add {X : Type*} [Add X] {f f' : G → X}
    (hf : IsLevelConstant₁ r f) (hf' : IsLevelConstant₁ r f') :
    IsLevelConstant₁ r (f + f') := by
  obtain ⟨F, hF, h⟩ := hf
  obtain ⟨F', hF', h'⟩ := hf'
  haveI := hF; haveI := hF'
  refine ⟨F ⊔ F', inferInstance, fun g s hs => ?_⟩
  simp only [Pi.add_apply]
  rw [h g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs),
    h' g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]

/-- Constant 1-cochains are level constant. -/
lemma isLevelConstant₁_const {X : Type*} (x : X) :
    IsLevelConstant₁ r (fun _ : G => x) :=
  ⟨⊥, inferInstance, fun _ _ _ => rfl⟩

variable {r} in
/-- Level constancy is preserved by postcomposition. -/
lemma IsLevelConstant₁.comp {X Y : Type*} {f : G → X}
    (hf : IsLevelConstant₁ r f) (φ : X → Y) :
    IsLevelConstant₁ r (φ ∘ f) := by
  obtain ⟨F, hF, h⟩ := hf
  exact ⟨F, hF, fun g s hs => by simp only [Function.comp_apply, h g s hs]⟩

variable (M : Rep k G)

/-- The submodule of level-constant 1-cochains. -/
def levelCochains₁ : Submodule k (G → M) where
  carrier := {f | IsLevelConstant₁ r f}
  add_mem' hf hf' := hf.add hf'
  zero_mem' := isLevelConstant₁_const r (0 : M)
  smul_mem' c _ hf := hf.comp (c • ·)

/-- Membership in the level-constant 1-cochains. -/
lemma mem_levelCochains₁_iff (f : G → M) :
    f ∈ levelCochains₁ r M ↔ IsLevelConstant₁ r f :=
  Iff.rfl

/-- The level-constant 1-cocycles, as a submodule of all 1-cocycles. -/
def levelCocycles₁ : Submodule k (cocycles₁ M) :=
  (levelCochains₁ r M).comap (cocycles₁ M).subtype

/-- Membership in the level-constant 1-cocycles. -/
lemma mem_levelCocycles₁_iff (c : cocycles₁ M) :
    c ∈ levelCocycles₁ r M ↔ IsLevelConstant₁ r c :=
  Iff.rfl

/-- The continuous first cohomology, as a submodule of `H¹(G, M)`. -/
noncomputable def continuousH1 : Submodule k (H1 M) :=
  (levelCocycles₁ r M).map (H1π M).hom

/-- A class lies in continuous `H¹` exactly when a level-constant
1-cocycle represents it. -/
lemma mem_continuousH1_iff (x : H1 M) :
    x ∈ continuousH1 r M ↔ ∃ c : cocycles₁ M, IsLevelConstant₁ r c ∧
      (H1π M).hom c = x := by
  simp only [continuousH1, Submodule.mem_map, mem_levelCocycles₁_iff]

/-- The class of a level-constant 1-cocycle lies in continuous `H¹`. -/
lemma H1π_mem_continuousH1 {c : cocycles₁ M} (hc : IsLevelConstant₁ r c) :
    (H1π M).hom c ∈ continuousH1 r M :=
  (mem_continuousH1_iff r M _).2 ⟨c, hc, rfl⟩

/-- A submodule of `H¹` with the same membership criterion as
`continuousH1` equals it. -/
lemma eq_continuousH1_of_forall_mem_iff (adm₁ : Submodule k (H1 M))
    (hadm₁ : ∀ x, x ∈ adm₁ ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : G), r s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (H1π M).hom c = x) :
    adm₁ = continuousH1 r M := by
  ext x
  rw [hadm₁, mem_continuousH1_iff]
  rfl

end groupCohomology
