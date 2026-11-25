/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Basic

/-!
# Strict isomorphisms of the actual marked carriers

An original simplicial isomorphism lifts to a marked isomorphism precisely
when it preserves and reflects the specified edge set. The inverse is the
same original simplicial inverse, and no replacement or model certificate
is used. Comap along an isomorphism is the corresponding literal transport.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Lift the original isomorphism when its actual one-simplex map identifies both markings. -/
def isoMk {X Y : Marked.{u}} (e : X.toSSet ≅ Y.toSSet)
    (h : ∀ a : X.toSSet _⦋1⦌, a ∈ X.marking ↔ e.hom.app (op ⦋1⦌) a ∈ Y.marking) :
    X ≅ Y where
  hom := ⟨e.hom, fun ha => (h _).mp ha⟩
  inv :=
    { hom := e.inv
      preserve {a} ha := by
        apply (h _).mpr
        have he := congrArg (fun f => f.app (op ⦋1⦌) a) e.inv_hom_id
        change e.hom.app _ (e.inv.app _ a) = a at he
        exact he.symm ▸ ha }
  hom_inv_id := Hom.ext e.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id

/-- The forward map is the original simplicial isomorphism. -/
@[simp] theorem isoMk_hom {X Y : Marked.{u}} (e : X.toSSet ≅ Y.toSSet)
    (h : ∀ a : X.toSSet _⦋1⦌, a ∈ X.marking ↔ e.hom.app (op ⦋1⦌) a ∈ Y.marking) :
    (isoMk e h).hom.hom = e.hom := rfl

/-- The inverse map is its original simplicial inverse. -/
@[simp] theorem isoMk_inv {X Y : Marked.{u}} (e : X.toSSet ≅ Y.toSSet)
    (h : ∀ a : X.toSSet _⦋1⦌, a ∈ X.marking ↔ e.hom.app (op ⦋1⦌) a ∈ Y.marking) :
    (isoMk e h).inv.hom = e.inv := rfl

/-- Literal comap by a simplicial isomorphism is an isomorphism of the marked carriers. -/
def comapIso (Y : Marked.{u}) {X : SSet.{u}} (e : X ≅ Y.toSSet) : comap Y e.hom ≅ Y :=
  isoMk e (fun _ => Iff.rfl)

/-- An existing marked isomorphism reflects its entire marking by its actual inverse. -/
theorem mem_marking_iff_of_iso {X Y : Marked.{u}} (e : X ≅ Y) (a : X.toSSet _⦋1⦌) :
    a ∈ X.marking ↔ e.hom.hom.app (op ⦋1⦌) a ∈ Y.marking := by
  constructor
  · exact e.hom.preserve
  · intro ha
    have h := e.inv.preserve ha
    have he := congrArg (fun f : X ⟶ X => f.hom.app (op ⦋1⦌) a) e.hom_inv_id
    change e.inv.hom.app _ (e.hom.hom.app _ a) = a at he
    exact he ▸ h

end SSet.Marked
