/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/DG/Twisted/Pretriangulated.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import MathlibExt.CategoryTheory.DGSourceMore.DGTwistedTriangle

/-!
# The homotopy category of twisted objects is pretriangulated

Let `C` be a differential graded category and let `H⁰` be the homotopy category of the twisted
objects of the additive closure of the shift closure of `C`, with the shift of
`MathlibExt/CategoryTheory/DGSourceMore/DGTwistedHomotopyShift.lean` and the cone triangles
`P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` of `MathlibExt/CategoryTheory/DGSourceMore/DGTwistedTriangle.lean` as distinguished
triangles.  This file proves the remaining axiom, the converse half of the rotation axiom, and so
makes `H⁰` a pretriangulated category.

The converse rotation follows, as for the homotopy category of cochain complexes, from the
stability of distinguished triangles under the shift functors of the category of triangles: the
inverse rotation of a triangle is isomorphic to the shift by `-1` of its double rotation.  The
shift by `n` of the cone triangle of `u : P ⟶ Q` is the triangle
`P⟦n⟧ ⟶ Q⟦n⟧ ⟶ (cone u)⟦n⟧ ⟶ P⟦n⟧⟦1⟧` whose morphisms are `(-1)^n` times the shifts of those of
the cone triangle, the last one followed by the isomorphism `P⟦1⟧⟦n⟧ ≅ P⟦n⟧⟦1⟧`.  It is
isomorphic to the cone triangle of `u⟦n⟧` by the identity of `P⟦n⟧`, `(-1)^n` times the identity
of `Q⟦n⟧`, and the isomorphism `(cone u)⟦n⟧ ≅ cone (u⟦n⟧)`
(`MathlibExt.DGSource.DGTwistedObject.shiftConeIso`) of `MathlibExt/CategoryTheory/DGSourceMore/DGTwistedCone.lean`.

## Main definitions

* `MathlibExt.DGSource.DGTwistedObject.coneTriangleShiftIso`: the isomorphism between the shift by `n` of the
  cone triangle of `u` and the cone triangle of `u⟦n⟧`.
* `MathlibExt.DGSource.DGTwistedObject.pretriangulated`: the pretriangulated structure on `H⁰`.

## Main results

* `MathlibExt.DGSource.DGTwistedObject.shift_mem_distinguishedTriangles` and
  `MathlibExt.DGSource.DGTwistedObject.invRotate_mem_distinguishedTriangles`: the shift and the inverse
  rotation of a distinguished triangle are distinguished.
* `MathlibExt.DGSource.DGTwistedObject.rotate_mem_distinguishedTriangles_iff`: a triangle is distinguished
  exactly when its rotation is.

## References

* A. I. Bondal and M. M. Kapranov, *Enhanced triangulated categories*, Section 1.
* V. Drinfeld, *DG quotients of DG categories*, Section 2.4.
* `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`, whose isomorphism
  `CochainComplex.mappingCone.shiftTriangleIso` between shifted mapping cone triangles and mapping
  cone triangles of shifted morphisms, and whose deduction of the converse rotation from it, are
  followed here.
-/

public section

open CategoryTheory Limits Pretriangulated

namespace MathlibExt.DGSource

universe v u

namespace DGTwistedObject

open DGHomotopyCategory

variable {R : Type v} [CommRing R] {C : Type u} [DGCategory R C]

/-! ### Shifts of cone triangles -/

section shiftCone

variable {P Q : DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))}
  {u : DGHom R 0 P Q} (hu : dgDifferential R 0 u = 0) (n : ℤ)

/-- **The shift of a cone triangle is a cone triangle**: the shift by `n` of the cone triangle of
`u`, whose morphisms are `(-1)^n` times the shifts of those of the cone triangle, is isomorphic to
the cone triangle of `u⟦n⟧`, by the identity of `P⟦n⟧`, `(-1)^n` times the identity of `Q⟦n⟧`, and
the isomorphism `(cone u)⟦n⟧ ≅ cone (u⟦n⟧)`. -/
noncomputable def coneTriangleShiftIso :
    (Triangle.shiftFunctor _ n).obj (coneTriangle u hu) ≅
      coneTriangle ((shiftFunctor R n).dgMap 0 u)
        ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu) :=
  -- The squares are first proved for general morphisms of the homotopy category; the objects of
  -- the shifted triangle agree with those of the DG shifts by `rfl`, but cannot be rewritten
  -- inside the implicit objects of the composites.
  Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (shiftConeIso hu n)
    (by
      have key : ∀ {X Y : DGHomotopyCategory R
          (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))} {a : X ⟶ Y}
          {b : X⟦n⟧ ⟶ Y⟦n⟧}, a⟦n⟧' = b →
          (n.negOnePow • a⟦n⟧') ≫ (n.negOnePow • 𝟙 (Y⟦n⟧)) = 𝟙 (X⟦n⟧) ≫ b := by
        rintro X Y a b rfl
        simp only [Linear.comp_units_smul, Category.comp_id, Category.id_comp, smul_smul,
          Int.units_mul_self, one_smul]
      exact key (shiftFunctor_map_homOf n u _))
    (by
      have key : ∀ {X Y W : DGHomotopyCategory R
          (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))} {a : X ⟶ Y}
          {c : Y⟦n⟧ ⟶ W} {b : X⟦n⟧ ⟶ W}, a⟦n⟧' ≫ c = b →
          (n.negOnePow • a⟦n⟧') ≫ c = (n.negOnePow • 𝟙 (X⟦n⟧)) ≫ b := by
        rintro X Y W a c b rfl
        simp only [Linear.units_smul_comp, Category.id_comp]
      have h : (homOf R (extensionInl R (dgDifferential_coneMorphism hu))
            ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)))⟦n⟧' ≫
          (shiftConeIso hu n).hom =
          homOf R (extensionInl R (dgDifferential_coneMorphism
            ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
            ((mem_dgCycles R).mpr (dgDifferential_extensionInl R _)) := by
        simp only [shiftFunctor_map_homOf, shiftConeIso_hom]
        exact homOf_comp_eq_homOf_of_dgComp_eq R _ _ _ (dgComp_dgMap_extensionInl_shiftConeHom hu n)
      exact key h)
    (by
      have key : ∀ {X Y : DGHomotopyCategory R
          (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))} {m m' : X ⟶ Y⟦n⟧⟦(1 : ℤ)⟧},
          m = m' → m ≫ (𝟙 (Y⟦n⟧))⟦(1 : ℤ)⟧' = m' := by
        rintro X Y m m' rfl
        simp only [CategoryTheory.Functor.map_id, Category.comp_id]
      have h₀ : n.negOnePow • (homOf R
          ((shiftFunctor R n).dgMap 0 (extensionSnd R (dgDifferential_coneMorphism hu)))
          ((shiftFunctor R n).dgMap_mem_dgCycles
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _))) ≫
          homOf R (shiftCommHom P 1 n) ((mem_dgCycles R).mpr (dgDifferential_shiftCommHom P 1 n))) =
          homOf R (shiftConeHom hu n) ((mem_dgCycles R).mpr (dgDifferential_shiftConeHom hu n)) ≫
            homOf R (extensionSnd R (dgDifferential_coneMorphism
              ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
              ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) := by
        simp only [homOf_comp, dgCompZero_def, dgComp_shiftConeHom_extensionSnd]
        exact (homOf_units_smul R _ _ _).symm
      have h : n.negOnePow • ((homOf R (extensionSnd R (dgDifferential_coneMorphism hu))
            ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)))⟦n⟧' ≫
          (shiftFunctorComm _ 1 n).hom.app (DGHomotopyCategory.of R P)) =
          (shiftConeIso hu n).hom ≫
            homOf R (extensionSnd R (dgDifferential_coneMorphism
              ((shiftFunctor R n).dgDifferential_dgMap_eq_zero hu)))
              ((mem_dgCycles R).mpr (dgDifferential_extensionSnd R _)) := by
        simp only [shiftFunctor_map_homOf, shiftFunctorComm_hom_app_of, shiftConeIso_hom]
        exact h₀
      exact key h)

@[simp]
theorem coneTriangleShiftIso_hom_hom₁ : (coneTriangleShiftIso hu n).hom.hom₁ = 𝟙 _ :=
  (rfl)

@[simp]
theorem coneTriangleShiftIso_hom_hom₂ :
    (coneTriangleShiftIso hu n).hom.hom₂ = n.negOnePow • 𝟙 _ :=
  (rfl)

@[simp]
theorem coneTriangleShiftIso_hom_hom₃ :
    (coneTriangleShiftIso hu n).hom.hom₃ = (shiftConeIso hu n).hom :=
  (rfl)

@[simp]
theorem coneTriangleShiftIso_inv_hom₁ : (coneTriangleShiftIso hu n).inv.hom₁ = 𝟙 _ :=
  (rfl)

@[simp]
theorem coneTriangleShiftIso_inv_hom₂ :
    (coneTriangleShiftIso hu n).inv.hom₂ = n.negOnePow • 𝟙 _ := by
  rw [← Int.units_inv_eq_self n.negOnePow]
  rfl

@[simp]
theorem coneTriangleShiftIso_inv_hom₃ :
    (coneTriangleShiftIso hu n).inv.hom₃ = (shiftConeIso hu n).inv :=
  (rfl)

end shiftCone

/-! ### The pretriangulated structure -/

section pretriangulated

/-- **The shift of a distinguished triangle is distinguished**: the shift by `n` of a cone triangle
is isomorphic to the cone triangle of the shifted morphism. -/
theorem shift_mem_distinguishedTriangles
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (hT : T ∈ distinguishedTriangles R C) (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj T ∈ distinguishedTriangles R C := by
  obtain ⟨P, Q, u, hu, ⟨e⟩⟩ := mem_distinguishedTriangles_iff.mp hT
  exact mem_distinguishedTriangles_iff.mpr
    ⟨_, _, _, _, ⟨(Triangle.shiftFunctor _ n).mapIso e ≪≫ coneTriangleShiftIso hu n⟩⟩

/-- **The inverse rotation of a distinguished triangle is distinguished**: it is isomorphic to the
shift by `-1` of the double rotation. -/
theorem invRotate_mem_distinguishedTriangles
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))))
    (hT : T ∈ distinguishedTriangles R C) : T.invRotate ∈ distinguishedTriangles R C :=
  isomorphic_distinguished _
    (shift_mem_distinguishedTriangles _
      (rotate_mem_distinguishedTriangles _ (rotate_mem_distinguishedTriangles _ hT)) _) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

/-- **The rotation axiom**: a triangle of the homotopy category of twisted objects is
distinguished exactly when its rotation is. -/
theorem rotate_mem_distinguishedTriangles_iff
    (T : Triangle
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C))))) :
    T ∈ distinguishedTriangles R C ↔ T.rotate ∈ distinguishedTriangles R C :=
  ⟨rotate_mem_distinguishedTriangles T, fun hT ↦ isomorphic_distinguished _
    (invRotate_mem_distinguishedTriangles _ hT) _ ((triangleRotation _).unitIso.app T)⟩

/-- **The homotopy category of twisted objects is pretriangulated**, with the triangles isomorphic
to cone triangles `P ⟶ Q ⟶ cone u ⟶ P⟦1⟧` as distinguished triangles.  Since `distTriang _`
unfolds to `MathlibExt.DGSource.DGTwistedObject.distinguishedTriangles`, the lemmas
`MathlibExt.DGSource.DGTwistedObject.mem_distinguishedTriangles_iff` and
`MathlibExt.DGSource.DGTwistedObject.coneTriangle_mem_distinguishedTriangles` describe its distinguished
triangles. -/
noncomputable instance pretriangulated :
    Pretriangulated
      (DGHomotopyCategory R (DGTwistedObject R (DGAdditiveClosure (DGShiftClosure C)))) where
  distinguishedTriangles := distinguishedTriangles R C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_mem_distinguishedTriangles_iff
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

end pretriangulated

end DGTwistedObject

end MathlibExt.DGSource
