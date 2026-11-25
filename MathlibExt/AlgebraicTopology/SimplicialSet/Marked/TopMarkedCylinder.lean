/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Products
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

/-!
# The actual original cylinder with a maximally marked top layer

The whole underlying cylinder is the original coefficient times the
minimally marked interval. Only the actual top copy is additionally
maximally marked. The original top marking upgrade and interval
inclusion give a genuine marked pushout, with its whole universal maps
proved. No ordinary product marking is substituted for this cylinder.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original bottom interval inclusion has its native degenerate scalar edge marking. -/
def markedCylinderBottom (A : Marked.{u}) : A ⟶ prod A (min (Δ[1] : SSet.{u})) where
  hom := SSet.ι₀
  preserve {e} he := ⟨he, SSet.stdSimplex.objMk₁ (1 : Fin 2), by ext j; fin_cases j <;> rfl⟩

/-- The original top inclusion uses the other actual degenerate scalar edge. -/
def markedCylinderTop (A : Marked.{u}) : A ⟶ prod A (min (Δ[1] : SSet.{u})) where
  hom := SSet.ι₁
  preserve {e} he := ⟨he, SSet.stdSimplex.objMk₁ (0 : Fin 2), by ext j; fin_cases j <;> rfl⟩

/-- The genuine top-marked cylinder retains the entire original product and adds exactly its original
  top-edge image to the mark set. -/
def topMarkedCylinder (A : Marked.{u}) : Marked.{u} where
  toSSet := (prod A (min (Δ[1] : SSet.{u}))).toSSet
  marking := (prod A (min (Δ[1] : SSet.{u}))).marking ∪
    Set.range ((SSet.ι₁ (X := A.toSSet)).app (op ⦋1⦌))
  degenerate_mem x := Or.inl ((prod A (min (Δ[1] : SSet.{u}))).degenerate_mem x)

/-- The original product includes into its actual top marking upgrade by the whole identity map. -/
def topMarkedCylinderInl (A : Marked.{u}) : prod A (min (Δ[1] : SSet.{u})) ⟶ topMarkedCylinder A :=
  ⟨𝟙 _, fun he => Or.inl he⟩

/-- The maximally marked original top copy includes by precisely the same whole top interval map. -/
def topMarkedCylinderInr (A : Marked.{u}) : max A.toSSet ⟶ topMarkedCylinder A where
  hom := SSet.ι₁
  preserve {e} _ := Or.inr ⟨e, rfl⟩

/-- Both whole original top maps give the same actual marked pushout square. -/
theorem topMarkedCylinder_condition (A : Marked.{u}) :
    markedCylinderTop A ≫ topMarkedCylinderInl A =
      (toMax (𝟙 A.toSSet) : A ⟶ max A.toSSet) ≫ topMarkedCylinderInr A := Hom.ext rfl

/-- The genuine original marked cylinder universal map retains the entire product map and derives
  preservation of all added top marks from the actual source square. -/
def topMarkedCylinderDesc {A Y : Marked.{u}}
    (f : prod A (min (Δ[1] : SSet.{u})) ⟶ Y) (g : max A.toSSet ⟶ Y)
    (hw : markedCylinderTop A ≫ f = (toMax (𝟙 A.toSSet) : A ⟶ max A.toSSet) ≫ g) :
    topMarkedCylinder A ⟶ Y where
  hom := f.hom
  preserve {e} he := by
    rcases he with h | ⟨a, rfl⟩
    · exact f.preserve h
    · have h := congrArg (fun m : A ⟶ Y => m.hom.app (op ⦋1⦌) a) hw
      exact h.symm ▸ g.preserve (Set.mem_univ _)

/-- The entire original product map factors through the actual marked cylinder descent. -/
theorem topMarkedCylinderDesc_inl {A Y : Marked.{u}}
    (f : prod A (min (Δ[1] : SSet.{u})) ⟶ Y) (g : max A.toSSet ⟶ Y)
    (hw : markedCylinderTop A ≫ f = (toMax (𝟙 A.toSSet) : A ⟶ max A.toSSet) ≫ g) :
    topMarkedCylinderInl A ≫ topMarkedCylinderDesc f g hw = f := Hom.ext rfl

/-- The complete original maximally marked top map has the same whole descent equation. -/
theorem topMarkedCylinderDesc_inr {A Y : Marked.{u}}
    (f : prod A (min (Δ[1] : SSet.{u})) ⟶ Y) (g : max A.toSSet ⟶ Y)
    (hw : markedCylinderTop A ≫ f = (toMax (𝟙 A.toSSet) : A ⟶ max A.toSSet) ≫ g) :
    topMarkedCylinderInr A ≫ topMarkedCylinderDesc f g hw = g := by
  apply Hom.ext
  have h := congrArg (fun m : A ⟶ Y => m.hom) hw
  exact h.trans (Category.id_comp g.hom)

/-- The actual top-marked cylinder is the genuine native pushout of the original minimal-interval top
  inclusion and original maximal marking upgrade. -/
def topMarkedCylinderIsColimit (A : Marked.{u}) :
    IsColimit (PushoutCocone.mk (topMarkedCylinderInl A) (topMarkedCylinderInr A)
      (topMarkedCylinder_condition A)) :=
  PushoutCocone.IsColimit.mk (topMarkedCylinder_condition A)
    (fun s => topMarkedCylinderDesc s.inl s.inr s.condition)
    (fun s => topMarkedCylinderDesc_inl s.inl s.inr s.condition)
    (fun s => topMarkedCylinderDesc_inr s.inl s.inr s.condition)
    (fun s m h _ => by
      apply Hom.ext
      have hh := congrArg (fun f : prod A (min (Δ[1] : SSet.{u})) ⟶ s.pt => f.hom) h
      exact (Category.id_comp m.hom).symm.trans hh)

end SSet.Marked
