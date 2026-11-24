/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.Stabilization

/-! Ordinary explicit and simp-normal-form use of stable GL generators. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory AlgebraicKTheory

namespace MathlibExtTest.AlgebraicKTheory.StableGL.GeneratorNormalForms

universe u

private theorem explicit_map {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.functor.map (SemiRingCat.ofHom f) (StableGL.of g) =
      StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f g) :=
  StableGL.map_of f g

private theorem default_map {R S : Type u} [Semiring R] [Semiring S]
    (f : R →+* S) {n : ℕ} (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.functor.map (SemiRingCat.ofHom f) (StableGL.of g) =
      StableGL.of (Matrix.GeneralLinearGroup.mapRingHom f g) := by
  simp only [StableGL.of_eq_G_mk, StableGL.map_G_mk]
  rfl

private theorem explicit_one (R : Type u) [Semiring R] (n : ℕ) :
    (StableGL.of (1 : Matrix.GeneralLinearGroup (Fin n) R) : StableGL R) = 1 :=
  StableGL.of_one

private theorem default_one (R : Type u) [Semiring R] (n : ℕ) :
    (StableGL.of (1 : Matrix.GeneralLinearGroup (Fin n) R) : StableGL R) = 1 := by
  simp only [StableGL.of_eq_G_mk, StableGL.G_mk_one]
  rfl

/-- The historical stage-application equation remains an explicit rewrite rule. -/
private theorem explicit_inclusion (R : Type u) [Semiring R] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (StableGL.inclusion n).app (SemiRingCat.of R) g = StableGL.of g := by
  rw [StableGL.inclusion_apply]

/-- Bare simp still handles the public stage inclusion after normalizing its natural transform. -/
private theorem default_inclusion (R : Type u) [Semiring R] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (StableGL.inclusion n).app (SemiRingCat.of R) g = StableGL.of g := by
  simp
  rfl

/-- Bare simp also handles the actual cocone application occurring in simp normal forms. -/
private theorem default_colimit_generator (R : Type u) [Semiring R] (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    (GrpCat.FilteredColimits.colimitCocone
      (F := finiteGLDiagram.obj (SemiRingCat.of R))).ι.app n g =
      GrpCat.FilteredColimits.G.mk
        (F := finiteGLDiagram.obj (SemiRingCat.of R)) ⟨n, g⟩ := by
  simp
  rfl

/-- The original successor law remains usable by explicit rewriting. -/
private theorem explicit_stabilization (R : Type u) [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of (Matrix.GeneralLinearGroup.stabilization R g) = StableGL.of g := by
  rw [StableGL.of_stabilization]

/-- Bare simp still identifies a successor-stabilized representative with its original class. -/
private theorem default_stabilization (R : Type u) [Semiring R] {n : ℕ}
    (g : Matrix.GeneralLinearGroup (Fin n) R) :
    StableGL.of (Matrix.GeneralLinearGroup.stabilization R g) = StableGL.of g := by
  simp
  rfl

/-- Rank zero is a genuine finite stage; its identity stays the stable identity after padding. -/
private theorem rank_zero_stabilization (R : Type u) [Semiring R] :
    (StableGL.of (Matrix.GeneralLinearGroup.stabilization R
      (1 : Matrix.GeneralLinearGroup (Fin 0) R)) : StableGL R) = 1 := by
  simp
  rfl

#print axioms StableGL.colimitCocone_ι_app_apply
#print axioms StableGL.G_mk_stabilization
#print axioms explicit_inclusion
#print axioms default_inclusion
#print axioms default_colimit_generator
#print axioms explicit_stabilization
#print axioms default_stabilization
#print axioms rank_zero_stabilization

#print axioms StableGL.map_G_mk
#print axioms StableGL.G_mk_one
#print axioms explicit_map
#print axioms default_map
#print axioms explicit_one
#print axioms default_one

end MathlibExtTest.AlgebraicKTheory.StableGL.GeneratorNormalForms
