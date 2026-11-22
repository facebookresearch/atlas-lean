/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderNerveDiagonal
import MathlibExt.AlgebraicTopology.SimplicialCategory.StrictCategory
import MathlibExt.CategoryTheory.Comma.UnderConstantProjectionChains

/-!
# The actual original scalar under-nerve projection and whole Hom fibre map

The SAME canonical original undercategory forgetful functors give the
actual full scalar under-nerve diagonal projection. Each full original
Hom simplex is its constant native undercategory word at the actual
original source and target. Every scalar operator and base projection
is retained. The strict fibre geometry uses all original chain arities,
not an assumed homotopy-fibre or completion weak equivalence.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.ScalarUnderCategory

variable (C : CategoryTheory.SimplicialEnrichment.Carrier.{u})

private theorem const_post {J A B : Type*} [Category J] [Category A] [Category B]
    (x : A) (F : A ⥤ B) : (Functor.const J).obj x ⋙ F = (Functor.const J).obj (F.obj x) :=
  Functor.hext (F := (Functor.const J).obj x ⋙ F) (G := (Functor.const J).obj (F.obj x))
    (fun _ => rfl) (fun _ _ _ => heq_of_eq (F.map_id x))

/-- The SAME whole canonical scalar base nerve diagram of the original enrichment. -/
def baseNerveDiagram : SimplicialObject SSet.{u} := scalarCategoryDiagramUniverse C ⋙ nerveFunctor

/-- The actual whole original scalar base-nerve diagonal. -/
def baseTotal : SSet.{u} := simplicialDiagonalFunctor.obj (baseNerveDiagram C)

/-- Every SAME full original canonical undercategory forgetful functor is an entire original scalar diagram map. -/
def forgetDiagram (z : C) : diagram C z ⟶ scalarCategoryDiagramUniverse C where
  app q := (forget C z q).toCatHom
  naturality q r f := by
    apply Cat.ext
    exact operator_forget C z f

/-- The actual original full nerve diagram projection keeps all whole original chains and coefficients. -/
def nerveProjection (z : C) : nerveDiagram C z ⟶ baseNerveDiagram C :=
  Functor.whiskerRight (forgetDiagram C z) nerveFunctor

/-- The SAME entire actual original under-nerve diagonal projection. -/
def projection (z : C) : total C z ⟶ baseTotal C := simplicialDiagonalFunctor.map (nerveProjection C z)

/-- Each original full projection simplex is exactly its whole native undercategory chain with the SAME original
forgetful functor. -/
theorem projection_apply (z : C) (q : SimplexCategoryᵒᵖ) (a : (total C z).obj q) :
    (projection C z).app q a = a ⋙ forget C z q := rfl

/-- The SAME original individual base vertex, as an entire native zero chain. -/
def baseVertex (y : C) : (baseTotal C) _⦋0⦌ :=
  (Functor.const (Fin 1)).obj (ScalarObject.mk (Δ := op ⦋0⦌) y)

/-- The original point map keeps the SAME entire constant scalar base word. -/
def point (y : C) : (Δ[0] : SSet.{u}) ⟶ baseTotal C := SSet.const (baseVertex C y)

/-- The SAME full original Hom simplex gives its entire constant native undercategory word in the matching original
degree. -/
def homInclusion (z y : C) : (z ⟶[SSet.{u}] y) ⟶ total C z where
  app q := ↾fun a => (Functor.const (Fin (q.unop.len + 1))).obj
    (Under.mk (X := sourceObject C z q) (Y := sourceObject C y q) a)
  naturality q r f := by
    ext a
    exact (const_post (Under.mk (X := sourceObject C z q) (Y := sourceObject C y q) a) (operator C z f)).symm

/-- Every original full Hom coefficient reads back as its SAME complete native constant undercategory chain. -/
theorem homInclusion_apply (z y : C) (q : SimplexCategoryᵒᵖ) (a : (z ⟶[SSet.{u}] y).obj q) :
    (homInclusion C z y).app q a = (Functor.const (Fin (q.unop.len + 1))).obj
      (Under.mk (X := sourceObject C z q) (Y := sourceObject C y q) a) := rfl

/-- The SAME full original Hom simplex has the literal constant original base word as its full projection. -/
theorem projection_homInclusion_apply (z y : C) (q : SimplexCategoryᵒᵖ) (a : (z ⟶[SSet.{u}] y).obj q) :
    (projection C z).app q ((homInclusion C z y).app q a) =
      (Functor.const (Fin (q.unop.len + 1))).obj (sourceObject C y q) :=
  const_post (Under.mk (X := sourceObject C z q) (Y := sourceObject C y q) a) (forget C z q)

/-- At every original scalar degree the full strict fibre consists exactly of the SAME complete original Hom
coefficients. -/
theorem projection_eq_const_iff (z y : C) (q : SimplexCategoryᵒᵖ) (a : (total C z).obj q) :
    (projection C z).app q a = (Functor.const (Fin (q.unop.len + 1))).obj (sourceObject C y q) ↔
      ∃ b : (z ⟶[SSet.{u}] y).obj q, (homInclusion C z y).app q b = a := by
  constructor
  · intro h
    exact ⟨Under.constantProjectionArrow a h, (Under.constantProjection_chain a h).symm⟩
  · rintro ⟨b, rfl⟩
    exact projection_homInclusion_apply C z y q b

end SSet.ScalarUnderCategory
