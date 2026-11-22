/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalInitialIntervalCover

/-!
# The original Segal initial interval cover as its leading edge and full tail face

The full tail face and original initial edge meet at exactly their
original shared vertex. Their actual subcomplex union is the existing
initial-interval cover. This gives the genuine whole pushout used to
compare fixed-object path rows to original mapping fibres and tail simplices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.Rezk.InitialEdgeTail

/-- The original entire tail face of the same simplex. -/
abbrev tail (n : ℕ) : (Δ[n + 1] : SSet.{u}).Subcomplex :=
  stdSimplex.face {(0 : Fin (n + 2))}ᶜ

/-- The original whole leading edge of the same simplex. -/
abbrev edge (n : ℕ) : (Δ[n + 1] : SSet.{u}).Subcomplex :=
  stdSimplex.face {(0 : Fin (n + 2)), (1 : Fin (n + 2))}

/-- The original shared vertex between the complete tail and the initial edge. -/
abbrev vertex (n : ℕ) : (Δ[n + 1] : SSet.{u}).Subcomplex :=
  stdSimplex.face {(1 : Fin (n + 2))}

/-- The actual whole union is the existing original initial interval cover. -/
theorem union_cover (n : ℕ) : tail.{u} n ⊔ edge n = initialIntervalCover (n + 1) := rfl

/-- The original two subcomplexes meet at their exact same original vertex. -/
theorem intersection_vertex (n : ℕ) : tail.{u} n ⊓ edge n = vertex n := by
  rw [stdSimplex.face_inter_face]
  congr 1
  ext i
  simp

/-- The whole original tail and edge form the actual pushout over their unchanged shared vertex. -/
theorem isPushout (n : ℕ) :
    IsPushout
      (Subcomplex.homOfLE (show vertex.{u} n ≤ tail n from by
        rw [← intersection_vertex]; exact inf_le_left))
      (Subcomplex.homOfLE (show vertex.{u} n ≤ edge n from by
        rw [← intersection_vertex]; exact inf_le_right))
      (Subcomplex.homOfLE (show tail.{u} n ≤ initialIntervalCover (n + 1) from by
        rw [← union_cover]; exact le_sup_left))
      (Subcomplex.homOfLE (show edge.{u} n ≤ initialIntervalCover (n + 1) from by
        rw [← union_cover]; exact le_sup_right)) :=
  (show Subcomplex.BicartSq (vertex.{u} n) (tail n) (edge n) (initialIntervalCover (n + 1)) from
    { sup_eq := union_cover n
      inf_eq := intersection_vertex n }).isPushout

/-- The actual whole original tail face is the original right-face simplex. -/
def tailIso (n : ℕ) : (Δ[n] : SSet.{u}) ≅ (tail n : SSet.{u}) :=
  stdSimplex.faceSingletonComplIso (0 : Fin (n + 2))

/-- The actual original leading edge is the whole original interval. -/
def edgeIso (n : ℕ) : (Δ[1] : SSet.{u}) ≅ (edge n : SSet.{u}) :=
  stdSimplex.facePairIso (0 : Fin (n + 2)) 1 (by change (0 : ℕ) < 1; omega)

/-- The actual original shared vertex is the same original zero simplex. -/
def vertexIso (n : ℕ) : (Δ[0] : SSet.{u}) ≅ (vertex n : SSet.{u}) :=
  stdSimplex.faceSingletonIso (1 : Fin (n + 2))

/-- The whole tail comparison retains its exact original first coface. -/
theorem tailIso_inclusion (n : ℕ) :
    (tailIso.{u} n).hom ≫ (tail n).ι = SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (n + 2))) :=
  stdSimplex.faceSingletonComplIso_hom_ι _

/-- The whole initial-edge comparison retains the actual original adjacent first edge. -/
theorem edgeIso_inclusion (n : ℕ) :
    (edgeIso.{u} n).hom ≫ (edge n).ι =
      SSet.stdSimplex.map (SimplexCategory.mkOfSucc (0 : Fin (n + 1))) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply stdSimplex.objEquiv.injective
  ext i
  change ((Fin.orderIsoPair (0 : Fin (n + 2)) 1
    (show (0 : Fin (n + 2)) < 1 from by change (0 : ℕ) < 1; omega))
      (stdSimplex.asOrderHom x i)).val.val =
    ((SimplexCategory.mkOfSucc (0 : Fin (n + 1))).toOrderHom (stdSimplex.asOrderHom x i)).val
  generalize stdSimplex.asOrderHom x i = a
  fin_cases a <;> rfl

/-- The whole shared-vertex comparison retains the original vertex one of the same simplex. -/
theorem vertexIso_inclusion (n : ℕ) :
    (vertexIso.{u} n).hom ≫ (vertex n).ι =
      SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk (n + 1)) 1) := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro x
  apply stdSimplex.objEquiv.injective
  ext i
  rfl

end SSet.Rezk.InitialEdgeTail
