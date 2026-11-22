/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateHornMarking
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# The same original root-horn coefficient and its complete marked prism source

Restrict the actual whole original coordinate prism and its entire
original inverse to the exact horn preimage. Both original source maps
retain the unchanged horn inclusion and full inherited maximum marking.
Their actual marked arrow isomorphism has precisely the original horn
attaching map as its target arrow.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The SAME original upper-endpoint/scalar-boundary horn prism source has the unchanged original ambient marking by
comap. -/
def coneRootCoordinateHornPrismMarked {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) : Marked.{u} :=
  comap (coneRootCoordinateWholeAmbient j hj)
    (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n))).ι

/-- The complete original marked horn-prism inclusion retains its SAME original source and original ambient carrier. -/
def coneRootCoordinateHornPrismMap {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateHornPrismMarked.{u} j hj ⟶ coneRootCoordinateWholeAmbient.{u} j hj :=
  comapHom (coneRootCoordinateWholeAmbient j hj)
    (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n))).ι

/-- The actual whole original prism restricts to its SAME exact original horn preimage. -/
def coneRootCoordinateHornPrismSourceMap {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n)) : SSet.{u}) ⟶
      (coneRootCoordinateHorn j : SSet.{u}) :=
  Subcomplex.lift
    ((Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n))).ι ≫
      coneRootCoordinateWholeMap j hj) (by
    rintro q z ⟨a, rfl⟩
    exact (congrArg (fun A => a.val ∈ A.obj q) (coneRootCoordinateHorn_preimage j hj)).to_iff.mpr a.property)

/-- The SAME entire original coordinate inverse restricts to the full original horn-prism source. -/
def coneRootCoordinateHornPrismSourceInverse {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (coneRootCoordinateHorn j : SSet.{u}) ⟶
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n)) : SSet.{u}) :=
  Subcomplex.lift ((coneRootCoordinateHorn j).ι ≫ coneRootCoordinateWholeInverse j hj) (by
    rintro q z ⟨a, rfl⟩
    have h : (coneRootCoordinateWholeMap j hj).app q
        ((coneRootCoordinateWholeInverse j hj).app q a.val) = a.val :=
      congrArg (fun f : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet ⟶
        (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet => f.app q a.val)
          (coneRootCoordinateWholeInverse_map j hj)
    have hh : (coneRootCoordinateWholeInverse j hj).app q a.val ∈
        ((coneRootCoordinateHorn j).preimage (coneRootCoordinateWholeMap j hj)).obj q := by
      change (coneRootCoordinateWholeMap j hj).app q
        ((coneRootCoordinateWholeInverse j hj).app q a.val) ∈ (coneRootCoordinateHorn j).obj q
      exact (congrArg (fun b : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet.obj q =>
        b ∈ (coneRootCoordinateHorn j).obj q) h).to_iff.mpr a.property
    exact (congrArg (fun A => (coneRootCoordinateWholeInverse j hj).app q a.val ∈ A.obj q)
      (coneRootCoordinateHorn_preimage j hj)).to_iff.mp hh)

/-- The entire original restricted source map keeps the literal full original horn attaching map. -/
theorem coneRootCoordinateHornPrismSourceMap_inclusion {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateHornPrismSourceMap j hj ≫ (coneRootCoordinateHorn j).ι =
      (Subcomplex.unionProd (horn.{u} 1 (Fin.last 1)) (coneCoordinateBoundary (⊥ : Vertex.{u} n))).ι ≫
        coneRootCoordinateWholeMap j hj := Subcomplex.lift_ι _ _

/-- Both actual original restricted source maps retain the entire original horn-prism identity. -/
theorem coneRootCoordinateHornPrismSourceMap_inverse {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateHornPrismSourceMap.{u} j hj ≫ coneRootCoordinateHornPrismSourceInverse.{u} j hj = 𝟙 _ := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  exact congrArg (fun f : (Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet ⟶
      (Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet => f.app q a.val)
    (coneRootCoordinateWholeMap_inverse j hj)

/-- The SAME whole original restricted inverse retains the original full horn identity. -/
theorem coneRootCoordinateHornPrismSourceInverse_map {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateHornPrismSourceInverse.{u} j hj ≫ coneRootCoordinateHornPrismSourceMap.{u} j hj = 𝟙 _ := by
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  exact congrArg (fun f : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet ⟶
      (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet => f.app q a.val)
    (coneRootCoordinateWholeInverse_map j hj)

/-- The original entire restricted coordinate prism preserves exactly its SAME source and target inherited marking. -/
def coneRootCoordinateHornPrismMarkedSourceMap {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateHornPrismMarked.{u} j hj ⟶ coneRootCoordinateHornMarked.{u} j where
  hom := coneRootCoordinateHornPrismSourceMap j hj
  preserve he := he

/-- The SAME original restricted whole inverse preserves all original horn marks through its actual original whole
identity. -/
def coneRootCoordinateHornPrismMarkedSourceInverse {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateHornMarked.{u} j ⟶ coneRootCoordinateHornPrismMarked.{u} j hj where
  hom := coneRootCoordinateHornPrismSourceInverse j hj
  preserve {e} he := by
    have h : (coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
        ((coneRootCoordinateWholeInverse j hj).app (op ⦋1⦌) e.val) = e.val :=
      congrArg (fun f : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet ⟶
        (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet => f.app (op ⦋1⦌) e.val)
          (coneRootCoordinateWholeInverse_map j hj)
    change (((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
      ((coneRootCoordinateHornPrismSourceInverse j hj).app (op ⦋1⦌) e).val).obj 0).maximum =
        (((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
          ((coneRootCoordinateHornPrismSourceInverse j hj).app (op ⦋1⦌) e).val).obj 1).maximum
    change (e.val.obj 0).maximum = (e.val.obj 1).maximum at he
    exact (congrArg (fun a : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet _⦋1⦌ => (a.obj 0).maximum) h).trans
      (he.trans (congrArg (fun a : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet _⦋1⦌ => (a.obj 1).maximum) h).symm)

/-- The complete original marked horn-prism source and the SAME original root-horn coefficient are genuinely
isomorphic through the actual original restricted prism and whole inverse. -/
def coneRootCoordinateHornPrismSourceIso {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateHornPrismMarked.{u} j hj ≅ coneRootCoordinateHornMarked.{u} j where
  hom := coneRootCoordinateHornPrismMarkedSourceMap j hj
  inv := coneRootCoordinateHornPrismMarkedSourceInverse j hj
  hom_inv_id := Hom.ext (coneRootCoordinateHornPrismSourceMap_inverse j hj)
  inv_hom_id := Hom.ext (coneRootCoordinateHornPrismSourceInverse_map j hj)

/-- The SAME full original marked horn attaching arrow is isomorphic to its original whole marked prism-source
inclusion, retaining both entire original carriers and both original attaching maps. -/
def coneRootCoordinateHornPrismArrowIso {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    Arrow.mk (coneRootCoordinateHornPrismMap.{u} j hj) ≅ Arrow.mk (coneRootCoordinateHornMap.{u} j) :=
  Arrow.isoMk (coneRootCoordinateHornPrismSourceIso j hj) (coneRootCoordinateWholeMarkedIso j hj)
    (Hom.ext (coneRootCoordinateHornPrismSourceMap_inclusion j hj))

end SSet.Marked.CoherentWeight
