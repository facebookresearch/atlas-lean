/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Connectedness of the Quillen nerve via zero-to-object edges

For one exact category `C`, the admissible zero-to-object span with apex `0`,
left leg `𝟙 0`, and right leg `0 ⟶ X` induces `QuillenQ.zeroToObjectHom`
and the nerve edge `NQ.zeroToVertexEdge` from `NQ.zeroVertex C` to
`ComposableArrows.mk₀ ⟨X⟩`. Every vertex is so connected, hence `(NQ C)`
is connected (`NQ.isConnected`).

Orientation: `δ 1` source is zero (`NQ.zeroVertex C`), `δ 0` target is `X`
(`ComposableArrows.mk₀ ⟨X⟩`).

Nonclaims: no initial or zero object in `QuillenQ`, no contractibility,
no `π₀ (NQ C) = K₀`, no loops or higher K-groups, no weak equivalence, no Q/S
comparison or spectra.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial ZeroObject
open CategoryTheory.ExactCategory

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Zero-to-object span with apex `0`, left leg `𝟙 0`, right leg `0 ⟶ X`. -/
noncomputable def QuillenQ.zeroToObjectSpan (X : C) : QuillenSpan (0 : C) X where
  apex := (0 : C)
  l := 𝟙 (0 : C)
  r := (0 : (0 : C) ⟶ X)
  wl := IsAdmissibleEpi.id (0 : C)
  wr := IsAdmissibleMono.fromZero (0 : (0 : C) ⟶ X)

/-- Zero-to-object morphism in `QuillenQ` from `⟨0⟩` to `⟨X⟩`. -/
noncomputable def QuillenQ.zeroToObjectHom (X : C) :
    (⟨0⟩ : QuillenQ C) ⟶ (⟨X⟩ : QuillenQ C) :=
  QuillenQ.mkHom (QuillenQ.zeroToObjectSpan X)

/-- Representative formula for the zero-to-object morphism. -/
@[simp]
theorem QuillenQ.zeroToObjectHom_mk (X : C) :
    QuillenQ.zeroToObjectHom X =
      QuillenQ.mkHom (QuillenQ.zeroToObjectSpan X) :=
  rfl

/-- Nerve edge from the zero vertex to `mk₀ ⟨X⟩`, via `nerve.edgeMk`. -/
noncomputable def NQ.zeroToVertexEdge (X : C) :
    (NQ C).Edge (NQ.zeroVertex C) (ComposableArrows.mk₀ (⟨X⟩ : QuillenQ C)) :=
  SSet.Edge.ofEq (CategoryTheory.nerve.edgeMk (QuillenQ.zeroToObjectHom X))
    (by simp [NQ.zeroVertex]; rfl)
    (by rfl)

/-- Edge formula for the zero-to-vertex edge. -/
@[simp]
theorem NQ.zeroToVertexEdge_edge (X : C) :
    (NQ.zeroToVertexEdge X).edge =
      ComposableArrows.mk₁ (QuillenQ.zeroToObjectHom X) :=
  rfl

/-- Source face of the zero-to-vertex edge is the zero vertex. -/
@[simp]
theorem NQ.zeroToVertexEdge_src (X : C) :
    (NQ C).δ 1 (NQ.zeroToVertexEdge X).edge = NQ.zeroVertex C :=
  SSet.Edge.src_eq _

/-- Target face of the zero-to-vertex edge is `mk₀ ⟨X⟩`. -/
@[simp]
theorem NQ.zeroToVertexEdge_tgt (X : C) :
    (NQ C).δ 0 (NQ.zeroToVertexEdge X).edge =
      ComposableArrows.mk₀ (⟨X⟩ : QuillenQ C) :=
  SSet.Edge.tgt_eq _

/-- The Quillen nerve is connected, as a theorem (not a global instance). -/
theorem NQ.isConnected (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C] :
    (NQ C).IsConnected := by
  have key : ∀ v : (NQ C).obj (op ⦋0⦌),
      SSet.π₀.mk (NQ.zeroVertex C) = SSet.π₀.mk v := by
    intro v
    let Q : QuillenQ C := CategoryTheory.nerveEquiv v
    have hQ : (⟨QuillenQ.get Q⟩ : QuillenQ C) = Q := QuillenQ.mk_get Q
    have hv : ComposableArrows.mk₀ (⟨QuillenQ.get Q⟩ : QuillenQ C) = v :=
      (congrArg ComposableArrows.mk₀ hQ).trans
        (CategoryTheory.nerveEquiv.left_inv v)
    have e : (NQ C).Edge (NQ.zeroVertex C) v :=
      SSet.Edge.ofEq (NQ.zeroToVertexEdge (QuillenQ.get Q)) rfl hv
    exact SSet.π₀.sound e
  rw [SSet.isConnected_iff]
  constructor
  · refine ⟨fun a b => ?_⟩
    obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
    obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective b
    exact (key x).symm.trans (key y)
  · exact ⟨NQ.zeroVertex C⟩

end AlgebraicKTheory
