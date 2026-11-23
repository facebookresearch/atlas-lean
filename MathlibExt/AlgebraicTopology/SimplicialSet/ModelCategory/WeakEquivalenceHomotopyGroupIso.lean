/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.KanComplexW
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FundamentalGroupoidAction

/-!
# Homotopy-group equivalences from weak equivalences

Pointed homotopy-group equivalence `KanComplex.W.homotopyGroupEquiv` /
multiplicative isomorphism `KanComplex.W.homotopyGroupIso` induced by
`KanComplex.W`, with identity (`homotopyGroupEquiv_id` /
`homotopyGroupIso_id`), composition (`homotopyGroupEquiv_comp` /
`homotopyGroupIso_comp`), and basepoint-change naturality
(`homotopyGroupEquiv_naturality` / `homotopyGroupIso_naturality`) laws.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace KanComplex

namespace W

/-- Equivalence on homotopy groups induced by a weak equivalence,
for every `n`. Built from `W.bijective_piMap` via `Equiv.ofBijective`. -/
noncomputable def homotopyGroupEquiv {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : W f) (n : ℕ) (x : X _⦋0⦌) :
    π n X x ≃ π n Y (f.app _ x) :=
  Equiv.ofBijective (π.map f rfl n) (W.bijective_piMap hf n x)

@[simp]
lemma homotopyGroupEquiv_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : W f) (n : ℕ) (x : X _⦋0⦌) (q : π n X x) :
    homotopyGroupEquiv f hf n x q = π.map f rfl n q :=
  rfl

@[simp]
lemma homotopyGroupEquiv_id {X : SSet.{u}} [KanComplex X]
    (n : ℕ) (x : X _⦋0⦌) :
    homotopyGroupEquiv (𝟙 X) W.id n x = Equiv.refl _ := by
  ext q
  exact π.map_id_apply q

lemma homotopyGroupEquiv_comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (n : ℕ) (x : X _⦋0⦌) :
    homotopyGroupEquiv (f ≫ g) (W.comp hf hg) n x =
      (homotopyGroupEquiv f hf n x).trans
        (homotopyGroupEquiv g hg n (f.app _ x)) := by
  ext q
  exact π.map_comp_apply f g rfl rfl rfl q

/-- Multiplicative isomorphism `π_{n+1}` induced by a weak equivalence.
Requires only `hf : W f`; Kan instances are recovered from `hf` via
`W.kanComplex_source` and `W.kanComplex_target`. -/
noncomputable def homotopyGroupIso {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : W f) (n : ℕ) (x : X _⦋0⦌) :
    letI : KanComplex X := W.kanComplex_source hf
    letI : KanComplex Y := W.kanComplex_target hf
    π (n + 1) X x ≃* π (n + 1) Y (f.app _ x) :=
  letI : KanComplex X := W.kanComplex_source hf
  letI : KanComplex Y := W.kanComplex_target hf
  MulEquiv.ofBijective (π.mapHom f rfl n)
    (W.bijective_piMap hf (n + 1) x)

@[simp]
lemma homotopyGroupIso_apply {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : W f) (n : ℕ) (x : X _⦋0⦌) (q : π (n + 1) X x) :
    homotopyGroupIso f hf n x q = π.map f rfl (n + 1) q :=
  rfl

lemma homotopyGroupIso_toEquiv {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : W f) (n : ℕ) (x : X _⦋0⦌) :
    letI : KanComplex X := W.kanComplex_source hf
    letI : KanComplex Y := W.kanComplex_target hf
    (homotopyGroupIso f hf n x).toEquiv =
      homotopyGroupEquiv f hf (n + 1) x := by
  have : KanComplex X := W.kanComplex_source hf
  have : KanComplex Y := W.kanComplex_target hf
  ext q
  rfl

@[simp]
lemma homotopyGroupIso_id {X : SSet.{u}} [KanComplex X]
    (n : ℕ) (x : X _⦋0⦌) :
    homotopyGroupIso (𝟙 X) W.id n x = MulEquiv.refl _ := by
  ext q
  exact π.map_id_apply q

lemma homotopyGroupIso_comp {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : W f) (hg : W g) (n : ℕ) (x : X _⦋0⦌) :
    letI : KanComplex X := W.kanComplex_source hf
    letI : KanComplex Y := W.kanComplex_target hf
    letI : KanComplex Z := W.kanComplex_target hg
    homotopyGroupIso (f ≫ g) (W.comp hf hg) n x =
      (homotopyGroupIso f hf n x).trans
        (homotopyGroupIso g hg n (f.app _ x)) := by
  have : KanComplex X := W.kanComplex_source hf
  have : KanComplex Y := W.kanComplex_target hf
  have : KanComplex Z := W.kanComplex_target hg
  ext q
  exact π.map_comp_apply f g rfl rfl rfl (n := n + 1) q

theorem homotopyGroupEquiv_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : W f) {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶
      SSet.FundamentalGroupoid.mk y) (n : ℕ) (q : π n X x) :
    letI : KanComplex X := W.kanComplex_source hf
    letI : KanComplex Y := W.kanComplex_target hf
    π.map f rfl n (π.action (n := n) p q) =
      π.action (n := n) ((SSet.mapFundamentalGroupoid f).map p)
        (homotopyGroupEquiv f hf n x q) := by
  have : KanComplex X := W.kanComplex_source hf
  have : KanComplex Y := W.kanComplex_target hf
  simp only [homotopyGroupEquiv_apply]
  exact π.action_naturality f p q

theorem homotopyGroupIso_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (hf : W f) {x y : X _⦋0⦌}
    (p : SSet.FundamentalGroupoid.mk (X := X) x ⟶
      SSet.FundamentalGroupoid.mk y) (n : ℕ) (q : π (n + 1) X x) :
    letI : KanComplex X := W.kanComplex_source hf
    letI : KanComplex Y := W.kanComplex_target hf
    π.map f rfl (n + 1) (π.action (n := n + 1) p q) =
      π.action (n := n + 1) ((SSet.mapFundamentalGroupoid f).map p)
        (homotopyGroupIso f hf n x q) := by
  have : KanComplex X := W.kanComplex_source hf
  have : KanComplex Y := W.kanComplex_target hf
  simp only [homotopyGroupIso_apply]
  exact π.action_naturality (n := n + 1) f p q

end W

end KanComplex

end SSet
