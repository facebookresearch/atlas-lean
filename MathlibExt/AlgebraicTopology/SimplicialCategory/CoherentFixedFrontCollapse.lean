/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentPathMaximumOperators
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentAdjunction

/-!
# The actual fixed-front collapse for coherent right resolutions

The original last-face simplices of the standard successor simplex are
collapsed to one structural source vertex, while every simplex meeting
the original last vertex is retained individually. This is a quotient
of the finite resolving simplex, not a quotient of any target's original
object type. Its whole operators are defined on the actual quotient.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontCollapse
variable {n : ℕ}

/-- A resolving simplex is in the original front when none of its actual vertices is the
last vertex. -/
def InFront {q : SimplexCategoryᵒᵖ} (a : (Δ[n + 1] : SSet.{u}).obj q) : Prop :=
  ∀ i : Fin (q.unop.len + 1), a.down.toOrderHom i ≠ Fin.last (n + 1)

/-- The actual degreewise fixed-front relation, retaining every nonfront original simplex
individually. -/
def relation (q : SimplexCategoryᵒᵖ) : Setoid ((Δ[n + 1] : SSet.{u}).obj q) where
  r a b := a = b ∨ InFront a ∧ InFront b
  iseqv := {
    refl a := Or.inl rfl
    symm := by rintro a b (h | h); exacts [Or.inl h.symm, Or.inr h.symm]
    trans := by
      rintro a b c (rfl | hab) (rfl | hbc)
      · exact Or.inl rfl
      · exact Or.inr hbc
      · exact Or.inr hab
      · exact Or.inr ⟨hab.1, hbc.2⟩ }

/-- Original simplex restriction retains the actual front property. -/
theorem inFront_map {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r)
    (a : (Δ[n + 1] : SSet.{u}).obj q) (ha : InFront a) : InFront ((Δ[n + 1] :
      SSet.{u}).map θ a) := by
  intro i
  exact ha (θ.unop.toOrderHom i)

/-- The actual fixed-front resolving simplicial set. -/
def object (n : ℕ) : SSet.{u} where
  obj q := _root_.Quotient (relation (n := n) q)
  map θ := ↾fun a => _root_.Quotient.map ((Δ[n + 1] : SSet.{u}).map θ) (by
    rintro a b (rfl | hab)
    · exact Or.inl rfl
    · exact Or.inr ⟨inFront_map θ a hab.1, inFront_map θ b hab.2⟩) a
  map_id q := by
    apply ConcreteCategory.hom_ext
    intro a
    induction a using _root_.Quotient.inductionOn with
    | _ a =>
      change _root_.Quotient.mk _ ((Δ[n + 1] : SSet.{u}).map (𝟙 q) a) = _
      exact congrArg (fun a => _root_.Quotient.mk _ a) (congr($((Δ[n + 1] : SSet.{u}).map_id q) a))
  map_comp θ ψ := by
    apply ConcreteCategory.hom_ext
    intro a
    induction a using _root_.Quotient.inductionOn with
    | _ a =>
      change _root_.Quotient.mk _ ((Δ[n + 1] : SSet.{u}).map (θ ≫ ψ) a) = _
      exact congrArg (fun a => _root_.Quotient.mk _ a) (congr($((Δ[n + 1] :
        SSet.{u}).map_comp θ ψ) a))

/-- The entire original successor simplex maps to its actual structural fixed-front quotient. -/
def projection (n : ℕ) : (Δ[n + 1] : SSet.{u}) ⟶ object.{u} n where
  app q := ↾fun a => _root_.Quotient.mk _ a
  naturality q r θ := by ext a; rfl

/-- Two original front simplices have precisely the same structural quotient image in their
original scalar degree. -/
theorem projection_front_eq {q : SimplexCategoryᵒᵖ} (a b : (Δ[n + 1] : SSet.{u}).obj q)
    (ha : InFront a) (hb : InFront b) : (projection n).app q a = (projection n).app q b :=
  _root_.Quotient.sound (Or.inr ⟨ha, hb⟩)

/-- The original structural source vertex is the projected first original vertex. -/
def source (n : ℕ) : (object.{u} n) _⦋0⦌ :=
  (projection n).app (op ⦋0⦌) (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0))

/-- The original structural target vertex is the projected last original vertex. -/
def target (n : ℕ) : (object.{u} n) _⦋0⦌ :=
  (projection n).app (op ⦋0⦌) (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const
    ⦋0⦌ ⦋n + 1⦌ (Fin.last (n + 1))))

/-- The actual coherent right-resolution Hom of this constructed fixed-front simplicial quotient. -/
def rightHom (n : ℕ) : SSet.{u} := CoherentRealization.hom (object.{u} n) (source n) (target n)

end CategoryTheory.CoherentRealization.FixedFrontCollapse
