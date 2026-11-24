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
    Subsingleton (SimplicialThickening.Path i.as j.as) where
  allEq a b := by
    apply SimplicialThickening.Path.ext
    ext k
    constructor
    · intro _
      have h : k = i.as := by
        apply ULift.ext
        exact Subsingleton.elim (α := Fin 1) _ _
      simpa only [h] using b.left
    · intro _
      have h : k = i.as := by
        apply ULift.ext
        exact Subsingleton.elim (α := Fin 1) _ _
      simpa only [h] using a.left

private instance zeroPath_hom_subsingleton (i j : coherentSimplex.{u} ⦋0⦌)
    (a b : SimplicialThickening.Path i.as j.as) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

private theorem zeroHom_unique (i j : coherentSimplex.{u} ⦋0⦌) (q : SimplexCategoryᵒᵖ)
    (a b : (i ⟶[SSet.{u}] j).obj q) : a = b := by
  exact @CategoryTheory.Functor.ext (Fin (q.unop.len + 1)) inferInstance
    (SimplicialThickening.Path i.as j.as) inferInstance a b
      (fun _ => Subsingleton.elim _ _) (fun _ _ _ => Subsingleton.elim _ _)

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
  refine EnrichedFunctor.ext SSet.{u}
    (F := constantSimplex C ⦋0⦌ (vertexOf C σ)) (G := σ)
    (fun i => congrArg σ.obj (zeroPoint_unique i).symm) ?_
  intro i j
  obtain rfl := zeroPoint_unique i
  obtain rfl := zeroPoint_unique j
  change (toUnit _ ≫ eId SSet.{u} (σ.obj zeroPoint)) ≫ 𝟙 _ = σ.map zeroPoint zeroPoint
  rw [Category.comp_id]
  ext q a
  have h : a = (eId SSet.{u} zeroPoint).app q PUnit.unit := zeroHom_unique _ _ q a _
  subst a
  exact congr($(σ.map_id zeroPoint).app q PUnit.unit).symm

/-- The actual coherent-nerve vertex equivalence retains individual original objects. -/
def verticesEquiv (C : Carrier.{u}) : CoherentSimplexIn C ⦋0⦌ ≃ C where
  toFun := vertexOf C
  invFun := constantSimplex C ⦋0⦌
  left_inv := constant_vertexOf C
  right_inv _ := rfl

/-- Original object readback is natural for every actual enriched functor. -/
theorem verticesEquiv_map (C D : Carrier.{u}) (F : C ⟶ D) (σ : CoherentSimplexIn C ⦋0⦌) :
    verticesEquiv D ((coherentNerveFunctor.map F).app (op ⦋0⦌) σ) =
      F.obj (verticesEquiv C σ) := rfl

end CategoryTheory.SimplicialEnrichment
