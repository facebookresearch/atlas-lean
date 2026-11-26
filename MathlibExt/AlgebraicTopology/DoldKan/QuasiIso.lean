/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Quasi-isomorphisms and projective objects under Moore normalization

Let C be abelian, N the normalized Moore complex and A the alternating face-map complex. Their
natural inclusion N(X) → A(X) is a chain homotopy equivalence. Its naturality shows that N(f)
is a quasi-isomorphism exactly when A(f) is, for each simplicial morphism f.

The normalization projection makes N(X) a retract of A(X). At degree n, A(X)_n = X_n, so
projectivity of X_n implies projectivity of N(X)_n. The category's object and morphism
universes are independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicTopology Opposite
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Normalized quasi-isomorphism from an alternating-chain quasi-isomorphism.

For a simplicial morphism f : X → Y in an abelian category, if the alternating face-map chain
map A(f) is a quasi-isomorphism, then the normalized Moore map N(f) is one. The natural Moore
inclusions are themselves quasi-isomorphisms. -/
theorem quasiIso_normalizedMap_of_alternatingMap
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    (hf : QuasiIso ((alternatingFaceMapComplex C).map f)) :
    QuasiIso ((normalizedMooreComplex C).map f) := by
  letI : QuasiIso ((alternatingFaceMapComplex C).map f) := hf
  letI : QuasiIso (inclusionOfMooreComplexMap X) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X)).quasiIso_hom
  letI : QuasiIso (inclusionOfMooreComplexMap Y) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y)).quasiIso_hom
  have hComp : QuasiIso
      ((normalizedMooreComplex C).map f ≫ inclusionOfMooreComplexMap Y) := by
    have h := (inclusionOfMooreComplex C).naturality f
    dsimp only [inclusionOfMooreComplex] at h
    rw [h]
    infer_instance
  letI := hComp
  exact quasiIso_of_comp_right ((normalizedMooreComplex C).map f)
    (inclusionOfMooreComplexMap Y)

/-- Alternating-chain quasi-isomorphism from a normalized quasi-isomorphism.

For a simplicial morphism f in an abelian category, if N(f) is a quasi-isomorphism, then A(f)
is a quasi-isomorphism. Naturality of the Moore inclusions compares the two chain maps. -/
theorem quasiIso_alternatingMap_of_normalizedMap
    {X Y : SimplicialObject C} (f : X ⟶ Y)
    (hf : QuasiIso ((normalizedMooreComplex C).map f)) :
    QuasiIso ((alternatingFaceMapComplex C).map f) := by
  let _ : QuasiIso ((normalizedMooreComplex C).map f) := hf
  let _ : QuasiIso (inclusionOfMooreComplexMap X) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := X)).quasiIso_hom
  let _ : QuasiIso (inclusionOfMooreComplexMap Y) :=
    (DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex (Y := Y)).quasiIso_hom
  have h := (inclusionOfMooreComplex C).naturality f
  dsimp only [inclusionOfMooreComplex] at h
  have hComp : QuasiIso
      (inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex C).map f) := by
    rw [← h]
    infer_instance
  let _ := hComp
  exact quasiIso_of_comp_left (inclusionOfMooreComplexMap X) ((alternatingFaceMapComplex C).map f)

/-- Equivalence of quasi-isomorphism criteria for two simplicial chain models.

For a simplicial morphism f : X → Y in an abelian category, N(f) is a quasi-isomorphism if and
only if A(f) is a quasi-isomorphism. Here N is the normalized Moore complex and A the
alternating face-map complex. -/
theorem quasiIso_normalizedMap_iff_alternatingMap {X Y : SimplicialObject C} (f : X ⟶ Y) :
    QuasiIso ((normalizedMooreComplex C).map f) ↔ QuasiIso ((alternatingFaceMapComplex C).map f) :=
  ⟨quasiIso_alternatingMap_of_normalizedMap f, quasiIso_normalizedMap_of_alternatingMap f⟩

/-- Projectivity of a normalized Moore term from its ambient term.

For a simplicial object X in an abelian category and n : ℕ, if X_n is a projective object,
then N(X)_n is projective. Moore inclusion and normalization projection exhibit N(X)_n as a
retract of X_n. -/
theorem normalizedDegree_projective (X : SimplicialObject C) (n : ℕ)
    [Projective (X.obj (op ⦋n⦌))] :
    Projective (((normalizedMooreComplex C).obj X).X n) := by
  let R : Retract ((normalizedMooreComplex C).obj X)
      ((alternatingFaceMapComplex C).obj X) :=
    { i := inclusionOfMooreComplexMap X
      r := DoldKan.PInftyToNormalizedMooreComplex X
      retract := (DoldKan.splitMonoInclusionOfMooreComplexMap X).id }
  letI : Projective
      ((HomologicalComplex.eval C (ComplexShape.down ℕ) n).obj
        ((alternatingFaceMapComplex C).obj X)) := by
    change Projective (X.obj (op ⦋n⦌))
    infer_instance
  exact (R.map (HomologicalComplex.eval C (ComplexShape.down ℕ) n)).projective

end CategoryTheory.SimplicialObject

end
