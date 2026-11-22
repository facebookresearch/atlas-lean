/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeRootCoordinateOrder
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso

/-!
# The whole original coordinate prism with its original inherited marking

The entire original coface image and coordinate insertion map has the
same whole original interval/cube inverse. Both simplex inverses retain
the original scalar operators and full original subset words. The marked
prism inherits precisely the larger-root marking by comap along this SAME
original map. Its restrictions are the original marked scalar cells.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The actual whole original membership coordinate is a functor on every original larger-root subset inclusion. -/
def coneRootCoordinateMembershipFunctor {n : ℕ} (j : Fin (n + 2)) :
    ConeSubset (⊥ : Vertex.{u} (n + 1)) ⥤ Vertex.{u} 1 :=
  (coneRootCoordinateMembership_mono j).functor

/-- The complete original coface preimage is a functor on the same whole original larger-root inclusion category. -/
def coneRootCoordinatePreimageFunctor {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    ConeSubset (⊥ : Vertex.{u} (n + 1)) ⥤ ConeSubset (⊥ : Vertex.{u} n) :=
  (coneRootCofacePreimage_mono j hj).functor

/-- The SAME original whole coface map and coordinate insertion construct the complete original root prism map. -/
def coneRootCoordinateWholeMap {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet ⟶
      (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet :=
  (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ (coneRootCofaceImage j hj).hom) ≫ coneRootCoordinatePrism (ULift.up j)

/-- Every scalar vertex of the complete original coordinate prism reconstructs its same actual interval vertex and
entire original smaller-root subset. -/
theorem coneRootCoordinateWholeMap_obj {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (q : SimplexCategoryᵒᵖ)
    (z : ((Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet).obj q)
    (t : Fin (q.unop.len + 1)) :
    ((coneRootCoordinateWholeMap j hj).app q z).obj t =
      coneRootCoordinateRebuild j hj (((stdSimplex.isoNerve 1).hom.app q z.1).obj t, z.2.obj t) :=
  congrArg (fun a => coneRootCoordinateLevel (ULift.up j)
    (((stdSimplex.isoNerve 1).hom.app q z.1).obj t, a)) (coneRootCofaceImage_obj j hj q z.2 t)

/-- Each whole original scalar cell is the exact restriction of the SAME complete original coordinate prism,
retaining its unchanged original scalar map. -/
theorem coneRootCoordinateWholeMap_scalar {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) :
    (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ yonedaEquiv.symm a) ≫ coneRootCoordinateWholeMap j hj =
      coneRootCoordinateScalarMap j hj a := rfl

/-- Read every whole original larger-root simplex as its same original membership interval simplex and complete
original coface-preimage simplex. -/
def coneRootCoordinateWholeInverse {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet ⟶
      (Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet where
  app q := ↾fun a => ((stdSimplex.isoNerve 1).inv.app q (a ⋙ coneRootCoordinateMembershipFunctor j),
    a ⋙ coneRootCoordinatePreimageFunctor j hj)
  naturality q r f := by
    ext a
    apply Prod.ext
    · exact congr($((stdSimplex.isoNerve 1).inv.naturality f) (a ⋙ coneRootCoordinateMembershipFunctor j)).symm
    · rfl

/-- The complete original coordinate prism has both original full simplex inverses, retaining every subset and
scalar operator in both directions. -/
def coneRootCoordinateWholeIso {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (Δ[1] : SSet.{u}) ⊗ (coneWeight (⊥ : Vertex.{u} n)).toSSet ≅
      (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet where
  hom := coneRootCoordinateWholeMap j hj
  inv := coneRootCoordinateWholeInverse j hj
  hom_inv_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro z
    change (coneRootCoordinateWholeInverse j hj).app q ((coneRootCoordinateWholeMap j hj).app q z) = z
    apply Prod.ext
    · apply stdSimplex.ext
      intro t
      change (coneRootCoordinateMembership j (((coneRootCoordinateWholeMap j hj).app q z).obj t)).down =
        stdSimplex.asOrderHom z.1 t
      rw [coneRootCoordinateWholeMap_obj]
      exact congrArg (fun a : Vertex.{u} 1 × ConeSubset (⊥ : Vertex.{u} n) => a.1.down)
        (coneRootCoordinateSplit_rebuild j hj (((stdSimplex.isoNerve 1).hom.app q z.1).obj t, z.2.obj t))
    · refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
      change coneRootCofacePreimage j hj (((coneRootCoordinateWholeMap j hj).app q z).obj t) = z.2.obj t
      rw [coneRootCoordinateWholeMap_obj]
      exact congrArg Prod.snd
        (coneRootCoordinateSplit_rebuild j hj (((stdSimplex.isoNerve 1).hom.app q z.1).obj t, z.2.obj t))
  inv_hom_id := by
    apply SSet.hom_ext
    intro q
    apply ConcreteCategory.hom_ext
    intro a
    change (coneRootCoordinateWholeMap j hj).app q ((coneRootCoordinateWholeInverse j hj).app q a) = a
    refine CategoryTheory.Functor.ext (fun t => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    rw [coneRootCoordinateWholeMap_obj]
    change coneRootCoordinateRebuild j hj
      (coneRootCoordinateMembership j (a.obj t), coneRootCofacePreimage j hj (a.obj t)) = a.obj t
    exact coneRootCoordinateRebuild_split j hj (a.obj t)

/-- The whole original coordinate prism keeps precisely the marking pulled back from the SAME actual larger-root
cone along its unchanged original full prism map. -/
def coneRootCoordinateWholeAmbient {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) : Marked.{u} :=
  comap (coneWeight (⊥ : Vertex.{u} (n + 1))) (coneRootCoordinateWholeMap j hj)

/-- The SAME complete original prism map followed by its whole original inverse is the actual original product
identity. -/
theorem coneRootCoordinateWholeMap_inverse {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateWholeMap j hj ≫ coneRootCoordinateWholeInverse j hj = 𝟙 _ :=
  (coneRootCoordinateWholeIso j hj).hom_inv_id

/-- The SAME whole original inverse followed by the actual original prism map is the unchanged larger-root identity. -/
theorem coneRootCoordinateWholeInverse_map {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateWholeInverse j hj ≫ coneRootCoordinateWholeMap j hj = 𝟙 _ :=
  (coneRootCoordinateWholeIso j hj).inv_hom_id

/-- The SAME original complete prism map retains its full original inherited marking. -/
def coneRootCoordinateWholeMarkedMap {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateWholeAmbient j hj ⟶ coneWeight (⊥ : Vertex.{u} (n + 1)) :=
  comapHom (coneWeight (⊥ : Vertex.{u} (n + 1))) (coneRootCoordinateWholeMap j hj)

/-- The SAME whole original prism inverse preserves the actual original larger-root marking by its proved full
original identity. -/
def coneRootCoordinateWholeMarkedInverse {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneWeight (⊥ : Vertex.{u} (n + 1)) ⟶ coneRootCoordinateWholeAmbient j hj where
  hom := coneRootCoordinateWholeInverse j hj
  preserve {e} he := by
    change (((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
      ((coneRootCoordinateWholeInverse j hj).app (op ⦋1⦌) e)).obj 0).maximum =
        (((coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
          ((coneRootCoordinateWholeInverse j hj).app (op ⦋1⦌) e)).obj 1).maximum
    change (e.obj 0).maximum = (e.obj 1).maximum at he
    have h : (coneRootCoordinateWholeMap j hj).app (op ⦋1⦌)
        ((coneRootCoordinateWholeInverse j hj).app (op ⦋1⦌) e) = e := by
      have h := congrArg (fun f : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet ⟶
          (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet => f.app (op ⦋1⦌) e)
        (coneRootCoordinateWholeInverse_map j hj)
      exact h
    have h₀ := congrArg (fun a : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet _⦋1⦌ => (a.obj 0).maximum) h
    have h₁ := congrArg (fun a : (coneWeight (⊥ : Vertex.{u} (n + 1))).toSSet _⦋1⦌ => (a.obj 1).maximum) h
    exact h₀.trans (he.trans h₁.symm)

/-- Both actual original marked prism maps retain their complete original marked product identity. -/
theorem coneRootCoordinateWholeMarkedMap_inverse {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateWholeMarkedMap j hj ≫ coneRootCoordinateWholeMarkedInverse j hj = 𝟙 _ := by
  apply Hom.ext
  change coneRootCoordinateWholeMap j hj ≫ coneRootCoordinateWholeInverse j hj = 𝟙 _
  exact coneRootCoordinateWholeMap_inverse j hj

/-- The SAME actual original marked inverse and prism maps retain the complete original larger-root identity. -/
theorem coneRootCoordinateWholeMarkedInverse_map {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateWholeMarkedInverse j hj ≫ coneRootCoordinateWholeMarkedMap j hj = 𝟙 _ := by
  apply Hom.ext
  change coneRootCoordinateWholeInverse j hj ≫ coneRootCoordinateWholeMap j hj = 𝟙 _
  exact coneRootCoordinateWholeInverse_map j hj

/-- The SAME original coordinate prism with its inherited original marking is the entire original marked larger-root
cone. -/
def coneRootCoordinateWholeMarkedIso {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    coneRootCoordinateWholeAmbient j hj ≅ coneWeight (⊥ : Vertex.{u} (n + 1)) where
  hom := coneRootCoordinateWholeMarkedMap j hj
  inv := coneRootCoordinateWholeMarkedInverse j hj
  hom_inv_id := coneRootCoordinateWholeMarkedMap_inverse j hj
  inv_hom_id := coneRootCoordinateWholeMarkedInverse_map j hj

/-- The actual full marked coordinate prism isomorphism retains precisely the SAME original coface/insertion map and
its original comap marking. -/
theorem coneRootCoordinateWholeMarkedIso_hom {n : ℕ} (j : Fin (n + 2)) (hj : 0 < j) :
    (coneRootCoordinateWholeMarkedIso j hj).hom =
      comapHom (coneWeight (⊥ : Vertex.{u} (n + 1))) (coneRootCoordinateWholeMap j hj) := Hom.ext rfl

/-- The original scalar-cell marking is exactly the restriction of the SAME whole marked root-coordinate prism along
its unchanged original scalar parameter map. -/
theorem coneRootCoordinateScalarAmbient_whole_comap {n d : ℕ} (j : Fin (n + 2)) (hj : 0 < j)
    (a : (coneWeight (⊥ : Vertex.{u} n)).toSSet _⦋d⦌) :
    comap (coneRootCoordinateWholeAmbient j hj) (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ yonedaEquiv.symm a) =
      coneRootCoordinateScalarAmbient j hj a :=
  (comap_comp (coneWeight (⊥ : Vertex.{u} (n + 1)))
    (𝟙 (Δ[1] : SSet.{u}) ⊗ₘ yonedaEquiv.symm a) (coneRootCoordinateWholeMap j hj)).symm.trans
      (congrArg (comap (coneWeight (⊥ : Vertex.{u} (n + 1)))) (coneRootCoordinateWholeMap_scalar j hj a))

end SSet.Marked.CoherentWeight
