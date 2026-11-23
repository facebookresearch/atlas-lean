/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import Mathlib.CategoryTheory.ComposableArrows.Basic

/-!
# Signed realization-grid algebra

This file packages the finite category algebra used after a relative square
approximation has produced compatible target data. A signed edge may traverse
an actual simplicial edge forward or backward, or may be a transported
identity. A rectangular certificate assumes two triangle relations with one
literally shared diagonal in every square and transported-identity vertical
boundary maps. Those relations telescope to equality of the normalized bottom
and top horizontal composites.

The certificate deliberately carries only the resulting groupoid relations.
It does not assert that target `2`-simplices exist or certify them; actual
simplex/permutation/face data and existence of a relative grid belong to the
later approximation provider. No approximation, fullness, faithfulness, unit,
Kan, weak-equivalence, or model-category claim is made here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet

/-- An oriented traversal from `x` to `y`: an actual forward edge, the formal
inverse traversal of an actual edge from `y` to `x`, or a transported
identity when `x = y`. The reverse case does not assert an opposite simplicial
edge. -/
structure SignedEdge (X : SSet.{u}) (x y : X _⦋0⦌) where
  data : X.Edge x y ⊕ X.Edge y x ⊕ PLift (x = y)

namespace SignedEdge

/-- A forward traversal of an actual simplicial edge. -/
def forward {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    SignedEdge X x y :=
  ⟨Sum.inl e⟩

/-- A reverse traversal of an actual simplicial edge. -/
def reverse {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge y x) :
    SignedEdge X x y :=
  ⟨Sum.inr (Sum.inl e)⟩

/-- The transported identity traversal associated to an endpoint equality. -/
def ofEq {X : SSet.{u}} {x y : X _⦋0⦌} (h : x = y) :
    SignedEdge X x y :=
  ⟨Sum.inr (Sum.inr ⟨h⟩)⟩

/-- The constant signed edge at a vertex. -/
def identity {X : SSet.{u}} (x : X _⦋0⦌) : SignedEdge X x x :=
  ofEq rfl

/-- The fundamental-groupoid morphism represented by a signed edge. -/
noncomputable def toHom {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SignedEdge X x y) :
    SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk y := by
  rcases e.data with e | e
  · exact SSet.FundamentalGroupoid.homMk e
  · rcases e with e | h
    · exact inv (SSet.FundamentalGroupoid.homMk e)
    · exact eqToHom (congrArg SSet.FundamentalGroupoid.mk h.down)

@[simp]
theorem toHom_forward {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y) :
    (forward e).toHom = SSet.FundamentalGroupoid.homMk e :=
  rfl

@[simp]
theorem toHom_reverse {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge y x) :
    (reverse e).toHom = inv (SSet.FundamentalGroupoid.homMk e) :=
  rfl

@[simp]
theorem toHom_ofEq {X : SSet.{u}} {x y : X _⦋0⦌} (h : x = y) :
    (ofEq h).toHom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk h) :=
  rfl

@[simp]
theorem toHom_identity {X : SSet.{u}} (x : X _⦋0⦌) :
    (identity x).toHom = 𝟙 (SSet.FundamentalGroupoid.mk x) := by
  simp [identity]

/-- Reverse the traversal direction, toggling forward and reverse data and
reversing an endpoint equality. -/
def reverseTraversal {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SignedEdge X x y) : SignedEdge X y x := by
  rcases e.data with e | e
  · exact reverse e
  · rcases e with e | h
    · exact forward e
    · exact ofEq h.down.symm

@[simp]
theorem reverseTraversal_reverseTraversal {X : SSet.{u}}
    {x y : X _⦋0⦌} (e : SignedEdge X x y) :
    e.reverseTraversal.reverseTraversal = e := by
  rcases e with ⟨e | e⟩
  · rfl
  · rcases e with e | h
    · rfl
    · cases h.down
      rfl

@[simp]
theorem toHom_reverseTraversal {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SignedEdge X x y) :
    e.reverseTraversal.toHom = inv e.toHom := by
  rcases e with ⟨e | e⟩
  · rfl
  · rcases e with e | h
    · change SSet.FundamentalGroupoid.homMk e =
        inv (inv (SSet.FundamentalGroupoid.homMk e))
      simp
    · cases h.down
      change 𝟙 _ = inv (𝟙 _)
      simp

end SignedEdge

/-- The algebraic relation contributed by one oriented target triangle.
Actual target simplex, permutation, and face certification are intentionally
not part of this relation-only provider. -/
structure SignedTriangleRelation {X : SSet.{u}}
    {x₀ x₁ x₂ : X _⦋0⦌}
    (e₀₁ : SignedEdge X x₀ x₁)
    (e₁₂ : SignedEdge X x₁ x₂)
    (e₀₂ : SignedEdge X x₀ x₂) : Prop where
  relation : e₀₁.toHom ≫ e₁₂.toHom = e₀₂.toHom

/-- A relation-only finite rectangular grid. Each square has one literally
shared signed diagonal. The lower and upper fields are the two assumed
triangle relations. Boundary vertices are identified with common endpoints,
and boundary vertical morphisms are the corresponding transported identities.

This structure does not certify the relations by actual `X` 2-simplices and
does not assert that such a grid exists. -/
structure RelativeGridCertificate (X : SSet.{u}) (rows cols : ℕ) where
  vertex : Fin (rows + 1) → Fin (cols + 1) → X _⦋0⦌
  horizontal : ∀ r : Fin (rows + 1), ∀ c : Fin cols,
    SignedEdge X (vertex r c.castSucc) (vertex r c.succ)
  vertical : ∀ r : Fin rows, ∀ c : Fin (cols + 1),
    SignedEdge X (vertex r.castSucc c) (vertex r.succ c)
  diagonal : ∀ r : Fin rows, ∀ c : Fin cols,
    SignedEdge X (vertex r.castSucc c.castSucc) (vertex r.succ c.succ)
  lower : ∀ r : Fin rows, ∀ c : Fin cols,
    SignedTriangleRelation (horizontal r.castSucc c) (vertical r c.succ)
      (diagonal r c)
  upper : ∀ r : Fin rows, ∀ c : Fin cols,
    SignedTriangleRelation (vertical r c.castSucc) (horizontal r.succ c)
      (diagonal r c)
  leftVertex : X _⦋0⦌
  rightVertex : X _⦋0⦌
  left_vertex : ∀ r : Fin (rows + 1), vertex r 0 = leftVertex
  right_vertex : ∀ r : Fin (rows + 1),
    vertex r (Fin.last cols) = rightVertex
  left_constant : ∀ r : Fin rows,
    (vertical r 0).toHom = eqToHom (congrArg SSet.FundamentalGroupoid.mk
      ((left_vertex r.castSucc).trans (left_vertex r.succ).symm))
  right_constant : ∀ r : Fin rows,
    (vertical r (Fin.last cols)).toHom =
      eqToHom (congrArg SSet.FundamentalGroupoid.mk
        ((right_vertex r.castSucc).trans (right_vertex r.succ).symm))

namespace RelativeGridCertificate

variable {X : SSet.{u}} {rows cols : ℕ}

/-- The two triangle relations with their shared diagonal give the square
relation. -/
theorem square (G : RelativeGridCertificate X rows cols)
    (r : Fin rows) (c : Fin cols) :
    (G.horizontal r.castSucc c).toHom ≫ (G.vertical r c.succ).toHom =
      (G.vertical r c.castSucc).toHom ≫
        (G.horizontal r.succ c).toHom :=
  (G.lower r c).relation.trans (G.upper r c).relation.symm

/-- The horizontal composite of one row. When `cols = 0`, this is the
identity supplied by `ComposableArrows.hom`. -/
noncomputable def rowComposite (G : RelativeGridCertificate X rows cols)
    (r : Fin (rows + 1)) :
    SSet.FundamentalGroupoid.mk (G.vertex r 0) ⟶
      SSet.FundamentalGroupoid.mk (G.vertex r (Fin.last cols)) :=
  (ComposableArrows.mkOfObjOfMapSucc
    (fun c => SSet.FundamentalGroupoid.mk (G.vertex r c))
    (fun c => (G.horizontal r c).toHom)).hom

@[simp]
theorem rowComposite_zero (G : RelativeGridCertificate X rows 0)
    (r : Fin (rows + 1)) : G.rowComposite r = 𝟙 _ := by
  change (ComposableArrows.mkOfObjOfMapSucc
    (fun c => SSet.FundamentalGroupoid.mk (G.vertex r c))
    (fun c => (G.horizontal r c).toHom)).map' 0 0 = 𝟙 _
  exact ComposableArrows.map'_self _ 0

@[simp]
theorem rowComposite_one (G : RelativeGridCertificate X rows 1)
    (r : Fin (rows + 1)) :
    G.rowComposite r = (G.horizontal r 0).toHom := by
  change (ComposableArrows.mkOfObjOfMapSucc
    (fun c => SSet.FundamentalGroupoid.mk (G.vertex r c))
    (fun c => (G.horizontal r c).toHom)).map' 0 1 =
      (G.horizontal r 0).toHom
  exact ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ 0 (by omega)

/-- Telescope the square relation across all columns of one strip. -/
theorem strip (G : RelativeGridCertificate X rows cols) (r : Fin rows) :
    G.rowComposite r.castSucc ≫ (G.vertical r (Fin.last cols)).toHom =
      (G.vertical r 0).toHom ≫ G.rowComposite r.succ := by
  let F₀ := ComposableArrows.mkOfObjOfMapSucc
    (fun c => SSet.FundamentalGroupoid.mk (G.vertex r.castSucc c))
    (fun c => (G.horizontal r.castSucc c).toHom)
  let F₁ := ComposableArrows.mkOfObjOfMapSucc
    (fun c => SSet.FundamentalGroupoid.mk (G.vertex r.succ c))
    (fun c => (G.horizontal r.succ c).toHom)
  let φ : F₀ ⟶ F₁ := ComposableArrows.homMk
    (fun c => (G.vertical r c).toHom) (by
      intro i hi
      rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi,
        ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ i hi]
      exact G.square r ⟨i, hi⟩)
  have h := ComposableArrows.naturality' φ 0 cols
  change G.rowComposite r.castSucc ≫
      (G.vertical r (Fin.last cols)).toHom =
    (G.vertical r 0).toHom ≫ G.rowComposite r.succ at h
  exact h

/-- A row composite transported to the certificate's common left and right
boundary vertices. -/
noncomputable def normalizedRow (G : RelativeGridCertificate X rows cols)
    (r : Fin (rows + 1)) :
    SSet.FundamentalGroupoid.mk G.leftVertex ⟶
      SSet.FundamentalGroupoid.mk G.rightVertex :=
  eqToHom (congrArg SSet.FundamentalGroupoid.mk (G.left_vertex r).symm) ≫
    G.rowComposite r ≫
      eqToHom (congrArg SSet.FundamentalGroupoid.mk (G.right_vertex r))

/-- After cancelling the transported-identity vertical boundary maps, two
adjacent normalized rows have the same composite. -/
theorem normalizedRow_castSucc_eq_succ
    (G : RelativeGridCertificate X rows cols) (r : Fin rows) :
    G.normalizedRow r.castSucc = G.normalizedRow r.succ := by
  have h := G.strip r
  rw [G.left_constant r, G.right_constant r] at h
  calc
    G.normalizedRow r.castSucc =
        eqToHom (congrArg SSet.FundamentalGroupoid.mk
            (G.left_vertex r.castSucc).symm) ≫
          (G.rowComposite r.castSucc ≫
            eqToHom (congrArg SSet.FundamentalGroupoid.mk
              ((G.right_vertex r.castSucc).trans
                (G.right_vertex r.succ).symm))) ≫
          eqToHom (congrArg SSet.FundamentalGroupoid.mk
            (G.right_vertex r.succ)) := by
      simp [normalizedRow, Category.assoc]
    _ = eqToHom (congrArg SSet.FundamentalGroupoid.mk
            (G.left_vertex r.castSucc).symm) ≫
          (eqToHom (congrArg SSet.FundamentalGroupoid.mk
              ((G.left_vertex r.castSucc).trans
                (G.left_vertex r.succ).symm)) ≫
            G.rowComposite r.succ) ≫
          eqToHom (congrArg SSet.FundamentalGroupoid.mk
            (G.right_vertex r.succ)) := by rw [h]
    _ = G.normalizedRow r.succ := by
      simp [normalizedRow, Category.assoc]

/-- Every normalized row has the same composite as the bottom row. -/
theorem normalizedRow_eq_bottom
    (G : RelativeGridCertificate X rows cols) (r : Fin (rows + 1)) :
    G.normalizedRow r = G.normalizedRow 0 := by
  induction r using Fin.induction with
  | zero => rfl
  | succ r ih =>
      exact (G.normalizedRow_castSucc_eq_succ r).symm.trans ih

/-- Full bottom-to-top telescope. This includes `rows = 0`; both sides are
then the same normalized row. -/
theorem bottomRow_eq_topRow (G : RelativeGridCertificate X rows cols) :
    G.normalizedRow 0 = G.normalizedRow (Fin.last rows) :=
  (G.normalizedRow_eq_bottom (Fin.last rows)).symm

end RelativeGridCertificate

end SSet

end
