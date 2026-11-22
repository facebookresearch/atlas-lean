/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCofaceMaxima
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products
import Mathlib.AlgebraicTopology.SimplicialNerve

/-!
# Original root-coordinate insertion and whole scalar prisms

At the original zero interval vertex the complete coface subset is
retained. At the other interval vertex the single omitted original
coordinate is inserted. The actual whole simplicial map keeps every
scalar operator. Its marked carrier inherits exactly the original
maximum-preserving marking by comap along this same map.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- Insert the actual original coordinate into the entire original root subset. -/
def coneRootInsert {n : ℕ} (k : Vertex.{u} n) (a : ConeSubset (⊥ : Vertex.{u} n)) :
    ConeSubset (⊥ : Vertex.{u} n) where
  vertices := insert k a.vertices
  mem := Finset.mem_insert_of_mem a.mem
  lower _ _ := bot_le

/-- The original coordinate insertion retains exactly the original whole finite subset with that one coordinate
inserted. -/
theorem coneRootInsert_vertices {n : ℕ} (k : Vertex.{u} n) (a : ConeSubset (⊥ : Vertex.{u} n)) :
    (coneRootInsert k a).vertices = insert k a.vertices := rfl

/-- The entire original coordinate insertion is monotone on the same whole root subsets. -/
theorem coneRootInsert_mono {n : ℕ} (k : Vertex.{u} n) : Monotone (coneRootInsert k) :=
  fun _ _ h => Finset.insert_subset_insert k h

/-- Its actual maximum is the maximum of the original coordinate and the unchanged whole subset maximum. -/
theorem coneRootInsert_maximum {n : ℕ} (k : Vertex.{u} n) (a : ConeSubset (⊥ : Vertex.{u} n)) :
    (coneRootInsert k a).maximum = Max.max k a.maximum := by
  change (insert k a.vertices).max' _ = Max.max k (a.vertices.max' _)
  exact Finset.max'_insert k a.vertices ⟨⊥, a.mem⟩

/-- Read the original interval coordinate and retain or insert that single coordinate in the whole original subset. -/
def coneRootCoordinateLevel {n : ℕ} (k : Vertex.{u} n)
    (z : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n)) : ConeSubset (⊥ : Vertex.{u} n) :=
  if z.1 = ⊥ then z.2 else coneRootInsert k z.2

/-- The same original whole coordinate reconstruction is monotone on the entire interval/subset product. -/
theorem coneRootCoordinateLevel_mono {n : ℕ} (k : Vertex.{u} n) :
    Monotone (coneRootCoordinateLevel k) := by
  intro a b h
  by_cases ha : a.1 = ⊥
  · by_cases hb : b.1 = ⊥
    · simp only [coneRootCoordinateLevel, ite_eq_left ha, ite_eq_left hb]
      exact h.2
    · simp only [coneRootCoordinateLevel, ite_eq_left ha, ite_eq_right hb]
      exact fun j hj => Finset.mem_insert_of_mem (h.2 hj)
  · have hb : b.1 ≠ ⊥ := by
      intro hb
      have hh : a.1 ≤ ⊥ := hb ▸ h.1
      exact ha (le_antisymm hh bot_le)
    simp only [coneRootCoordinateLevel, ite_eq_right ha, ite_eq_right hb]
    exact coneRootInsert_mono k h.2

/-- The original coordinate maximum reads the exact interval choice and the unchanged original subset maximum. -/
theorem coneRootCoordinateLevel_maximum {n : ℕ} (k : Vertex.{u} n)
    (z : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n)) :
    (coneRootCoordinateLevel k z).maximum =
      if z.1 = ⊥ then z.2.maximum else Max.max k z.2.maximum := by
  dsimp only [coneRootCoordinateLevel]
  split_ifs
  · rfl
  · exact coneRootInsert_maximum k z.2

/-- Every original coordinate value retains the same whole maximum when that original maximum is at least the
inserted coordinate. -/
theorem coneRootCoordinateLevel_maximum_of_le {n : ℕ} (k : Vertex.{u} n)
    (z : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n)) (hk : k ≤ z.2.maximum) :
    (coneRootCoordinateLevel k z).maximum = z.2.maximum := by
  rw [coneRootCoordinateLevel_maximum]
  split_ifs
  · rfl
  · exact max_eq_right hk

/-- Its actual whole maximum remains bounded by the original inserted coordinate whenever the unchanged subset
maximum is bounded by that coordinate. -/
theorem coneRootCoordinateLevel_maximum_le {n : ℕ} (k : Vertex.{u} n)
    (z : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n)) (hk : z.2.maximum ≤ k) :
    (coneRootCoordinateLevel k z).maximum ≤ k := by
  rw [coneRootCoordinateLevel_maximum]
  split_ifs
  · exact hk
  · exact max_le le_rfl hk

/-- The actual original subset reconstruction is a functor on the full original interval/subset product. -/
def coneRootCoordinateLevelFunctor {n : ℕ} (k : Vertex.{u} n) :
    Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n) ⥤ ConeSubset (⊥ : Vertex.{u} n) where
  obj := coneRootCoordinateLevel k
  map f := homOfLE (coneRootCoordinateLevel_mono k ⟨leOfHom f.1, leOfHom f.2⟩)

/-- The genuine original whole interval prism inserts the original coordinate at every whole original scalar word. -/
def coneRootCoordinatePrism {n : ℕ} (k : Vertex.{u} n) :
    (Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet ⟶
      (coneWeight (⊥ : Vertex.{u} n)).toSSet where
  app q := ↾fun a => ((stdSimplex.isoNerve 1).hom.app q a.1).prod' a.2 ⋙
    coneRootCoordinateLevelFunctor k
  naturality q r f := by
    ext a
    refine CategoryTheory.Functor.ext (fun t => rfl) (fun _ _ _ => Subsingleton.elim _ _)

/-- The same entire original coface scalar simplex supplies the original root-coordinate insertion prism. -/
def coneRootCoordinateScalarMap {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) :
    (Δ[1] : SSet.{u}) ⊗ Δ[d] ⟶ (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet :=
  (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ (yonedaEquiv.symm a ≫ (coneRootCofaceImage j hj).hom)) ≫
    coneRootCoordinatePrism (ULift.up j)

/-- Every original scalar vertex of the complete original coordinate prism reads exactly its interval vertex and
whole original root-coface subset. -/
theorem coneRootCoordinateScalarMap_vertex {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) (q : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ Δ[d]).obj q) (t : Fin (q.unop.len + 1)) :
    ((coneRootCoordinateScalarMap j hj a).app q z).obj t =
      coneRootCoordinateLevel (ULift.up j)
        (((stdSimplex.isoNerve 1).hom.app q z.1).obj t,
          (((coneRootCofaceImage j hj).hom.app q ((yonedaEquiv.symm a).app q z.2)).obj t)) := rfl

/-- The actual original coordinate/scalar cell inherits precisely the marking of the same original larger root
coefficient. -/
def coneRootCoordinateScalarAmbient {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) : Marked.{u} :=
  comap (coneWeight (⊥ : Vertex.{u} (n + 1))) (coneRootCoordinateScalarMap j hj a)

end SSet.Marked.CoherentWeight
