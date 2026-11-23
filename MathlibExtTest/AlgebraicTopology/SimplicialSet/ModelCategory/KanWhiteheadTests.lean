/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead

/-!
# Simplicial Whitehead tests

These tests pin the literal homotopy-inverse endpoint for Kan complexes in
all universes. They also verify both standard-cylinder endpoint directions
and retain the boundaries against ordinary isomorphisms, non-Kan objects,
other weak notions, private cylinder helpers and leaked model instances.
-/

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead

section Generic

variable {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
variable {f : X ⟶ Y}

/-- Exact symbolic-universe result type. -/
example (hf : SSet.KanComplex.W f) :
    ∃ g : Y ⟶ X,
      Nonempty (SSet.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SSet.Homotopy (g ≫ f) (𝟙 Y)) :=
  hf.exists_homotopy_inverse

/-- Realization weakness is converted through the exact Kan comparison. -/
example (hf : SSet.realizationWeakEquivalences f) :
    ∃ g : Y ⟶ X,
      Nonempty (SSet.Homotopy (f ≫ g) (𝟙 X)) ∧
      Nonempty (SSet.Homotopy (g ≫ f) (𝟙 Y)) :=
  SSet.KanComplex.W.exists_homotopy_inverse
    ((SSet.KanComplex.W_iff_realizationWeakEquivalence f).mpr hf)

/-- Both returned homotopies have composite at endpoint zero and the literal
identity at endpoint one. -/
example (hf : SSet.KanComplex.W f) :
    ∃ (g : Y ⟶ X)
      (Hfg : SSet.Homotopy (f ≫ g) (𝟙 X))
      (Hgf : SSet.Homotopy (g ≫ f) (𝟙 Y)),
      SSet.ι₀ ≫ Hfg.h = f ≫ g ∧
      SSet.ι₁ ≫ Hfg.h = 𝟙 X ∧
      SSet.ι₀ ≫ Hgf.h = g ≫ f ∧
      SSet.ι₁ ≫ Hgf.h = 𝟙 Y := by
  obtain ⟨g, ⟨Hfg⟩, ⟨Hgf⟩⟩ := hf.exists_homotopy_inverse
  exact ⟨g, Hfg, Hgf, Hfg.h₀, Hfg.h₁, Hgf.h₀, Hgf.h₁⟩

/-- Identity weak equivalences. -/
example (X : SSet.{u}) [SSet.KanComplex X] :
    ∃ g : X ⟶ X,
      Nonempty (SSet.Homotopy ((𝟙 X) ≫ g) (𝟙 X)) ∧
      Nonempty (SSet.Homotopy (g ≫ 𝟙 X) (𝟙 X)) :=
  SSet.KanComplex.W.exists_homotopy_inverse SSet.KanComplex.W.id

/-- Isomorphisms of Kan complexes. -/
example (e : X ≅ Y) :
    ∃ g : Y ⟶ X,
      Nonempty (SSet.Homotopy (e.hom ≫ g) (𝟙 X)) ∧
      Nonempty (SSet.Homotopy (g ≫ e.hom) (𝟙 Y)) :=
  SSet.KanComplex.W.exists_homotopy_inverse
    (SSet.KanComplex.W.ofIso e)

end Generic

section DeltaZero

open scoped SSet.modelCategoryQuillen in
/-- The terminal standard zero-simplex is Kan. -/
example :
    ∃ g : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}),
      Nonempty (SSet.Homotopy ((𝟙 _) ≫ g) (𝟙 _)) ∧
      Nonempty (SSet.Homotopy (g ≫ 𝟙 _) (𝟙 _)) := by
  let _ : SSet.KanComplex (Δ[0] : SSet.{u}) :=
    (isFibrant_iff_of_isTerminal (𝟙 _)
      SSet.stdSimplex.isTerminalObj₀).2 (by infer_instance)
  exact SSet.KanComplex.W.exists_homotopy_inverse SSet.KanComplex.W.id

end DeltaZero

section ConcreteUniverses

example (X : SSet.{1}) [SSet.KanComplex X] :
    ∃ g : X ⟶ X,
      Nonempty (SSet.Homotopy ((𝟙 X) ≫ g) (𝟙 X)) ∧
      Nonempty (SSet.Homotopy (g ≫ 𝟙 X) (𝟙 X)) :=
  SSet.KanComplex.W.exists_homotopy_inverse SSet.KanComplex.W.id

example (X : SSet.{0}) [SSet.KanComplex X] :
    ∃ g : X ⟶ X,
      Nonempty (SSet.Homotopy ((𝟙 X) ≫ g) (𝟙 X)) ∧
      Nonempty (SSet.Homotopy (g ≫ 𝟙 X) (𝟙 X)) :=
  SSet.KanComplex.W.exists_homotopy_inverse SSet.KanComplex.W.id

end ConcreteUniverses

section NegativeBoundaries

example {X Y : SSet.{u}} [SSet.KanComplex X] [SSet.KanComplex Y]
    {f : X ⟶ Y} (_hf : SSet.KanComplex.W f) : True := by
  fail_if_success
    let _ : IsIso f := inferInstance
  trivial

example : True := by
  fail_if_success
    let _ : SSet.KanComplex (Δ[1] : SSet.{u}) := inferInstance
  trivial

example (_X : SSet.{u}) : True := by
  fail_if_success
    let _ : ModelCategory SSet.{u} := inferInstance
  fail_if_success
    let _ : IsCofibrant _X := inferInstance
  trivial

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.KanComplex.standardCylinder

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.KanComplex.leftHomotopyRelToHomotopy

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.KanComplex.W.exists_joyal_homotopy_inverse

/-- error: Unknown constant -/
#guard_msgs (error, substring := true) in
#check SSet.KanComplex.W.exists_rezk_homotopy_inverse

end NegativeBoundaries

#print axioms SSet.KanComplex.W.exists_homotopy_inverse

end MathlibExtTest.AlgebraicTopology.SimplicialSet.ModelCategory.KanWhitehead
