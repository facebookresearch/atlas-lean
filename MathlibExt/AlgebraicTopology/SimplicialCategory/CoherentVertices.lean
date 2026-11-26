/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentSimplex

/-!
# Individual vertices of the actual coherent nerve

The zero-simplex is the terminal coherent simplex. Its enriched functors
are identified with individual original objects, without a component
quotient. The comparison is natural for the actual enriched maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment

/-- The unique original vertex of the zero-dimensional coherent simplex. -/
def zeroPoint : coherentSimplex.{u} ⦋0⦌ := .mk (.up 0)

/-- Every individual object of the zero coherent simplex is its actual unique vertex. -/
theorem zeroPoint_unique (i : coherentSimplex.{u} ⦋0⦌) : i = zeroPoint := by
  cases i
  congr 1
  apply ULift.ext
  exact Subsingleton.elim (α := Fin 1) _ _

private instance zeroPath_subsingleton (i j : coherentSimplex.{u} ⦋0⦌) :
    Subsingleton (SimplicialThickening.Path i.as j.as) := by
  apply SimplicialThickening.Path.subsingleton_of_forall_not_lt
  intro k hik _
  have h : i.as = k := by
    apply ULift.ext
    exact Subsingleton.elim (α := Fin 1) _ _
  exact (ne_of_lt hik) h

private instance zeroPath_hom_subsingleton (i j : coherentSimplex.{u} ⦋0⦌)
    (a b : SimplicialThickening.Path i.as j.as) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The canonical map to the actual simplicial tensor unit. -/
def toUnit (X : SSet.{u}) : X ⟶ 𝟙_ SSet.{u} where
  app q := ↾fun _ => PUnit.unit
  naturality q r f := by ext a; rfl

/-- The actual constant coherent simplex at one supplied original object. -/
def constantSimplex (C : Carrier.{u}) (n : SimplexCategory) (c : C) : CoherentSimplexIn C n where
  obj _ := c
  map i j := toUnit (i ⟶[SSet.{u}] j) ≫ eId SSet.{u} c
  map_id i := by ext q a; rfl
  map_comp i j k := by
    ext q a
    exact congr($(e_id_comp SSet.{u} c c).app q ((eId SSet.{u} c).app q PUnit.unit)).symm

/-- Read the original object represented by one actual coherent-nerve vertex. -/
def vertexOf (C : Carrier.{u}) (σ : CoherentSimplexIn C ⦋0⦌) : C := σ.obj zeroPoint

/-- Every zero coherent simplex is exactly the constant simplex at its individual original
object. -/
theorem constant_vertexOf (C : Carrier.{u}) (σ : CoherentSimplexIn C ⦋0⦌) :
    constantSimplex C ⦋0⦌ (vertexOf C σ) = σ := by
  apply (SimplicialNerve.vertexEquiv (ForgetEnrichment SSet.{u} C)).injective
  rfl

/-- The actual coherent-nerve vertex equivalence retains individual original objects. -/
abbrev verticesEquiv (C : Carrier.{u}) : CoherentSimplexIn C ⦋0⦌ ≃ C :=
  SimplicialNerve.vertexEquiv (ForgetEnrichment SSet.{u} C)

/-- Original object readback is natural for every actual enriched functor. -/
theorem verticesEquiv_map (C D : Carrier.{u}) (F : C ⟶ D) (σ : CoherentSimplexIn C ⦋0⦌) :
    verticesEquiv D ((coherentNerveFunctor.map F).app (op ⦋0⦌) σ) =
      F.obj (verticesEquiv C σ) := rfl

end CategoryTheory.SimplicialEnrichment
