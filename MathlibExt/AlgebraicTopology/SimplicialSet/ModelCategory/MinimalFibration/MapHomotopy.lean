/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Basic

@[expose] public section

/-!
# Map-level fiberwise homotopy and the simplex over-relation

This module provides the smallest reusable pure-simplicial foundation needed by
the next minimal-fibration comparison/rigidity packets.

* Goerss–Jardine, *Simplicial Homotopy Theory*, Chapter I §10.
* Hovey, *Model Categories*, §3.5.

## Map-level fiberwise homotopy

For maps `p : E ⟶ B` and `p' : E' ⟶ B`, a witness
`H : SSet.FiberwiseHomotopy p p' f g` between `f g : E ⟶ E'` extends an
ordinary `SSet.Homotopy f g` (cylinder `E ⊗ Δ[1] ⟶ E'`) with the exact
over-base equation `H.hom.h ≫ p' = fst ≫ p`: the cylinder is constant over
`p` in the interval direction. The name is unambiguous beside the existing
simplex-level `SSet.MinimalFibration.FiberwiseHomotopy`, which relates
`n`-simplices relative to `SSet.boundary n` over a constant base. Only the
documented endpoint consequences `fac₀`/`fac₁` and the reflexive constructor
from `f ≫ p' = p` are exposed.

## Simplex over-relation

`SSet.MinimalFibration.OverRelation p x y` is a simplex-level witness
carrying a boundary-stationary cylinder homotopy between the `n`-simplices
`x y : X _⦋n⦌`, an arbitrary base simplex `base : Δ[n] ⟶ S`, a common
boundary map `bd : ∂Δ[n] ⟶ X`, and the two compatibility equations `over`
and `boundary`. Only the derived base/boundary equalities, the over-base
square, extensionality, the reflexive constructor, and the conversion into
the existing constant-base `FiberwiseHomotopy` (hence an `IsMinimal p`
equality) are exposed.

## Nonclaims

* Does not prove symmetry, transitivity, or any equivalence-relation
  structure for either relation.
* Does not introduce `SSet.FiberwiseHomotopyEquiv`: the pinned/local audit
  shows no immediately following rigidity statement needs it, so it is
  explicitly deferred rather than exposed as a redundant wrapper.
* Does not prove rigidity, `IsIso`, weak equivalences, or any
  model-categorical consequence.
* Does not introduce internal-hom, fundamental-groupoid, quotient, or
  selection machinery, and does not generalize or duplicate the accepted
  simplex-level relation.
-/

open CategoryTheory Simplicial SSet
open MonoidalCategory CartesianMonoidalCategory

namespace SSet

universe u

variable {E E' B : SSet.{u}}

/-- Map-level fiberwise homotopy between `f g : E ⟶ E'` over `p : E ⟶ B`
and `p' : E' ⟶ B`.

* `hom` is an ordinary simplicial homotopy with cylinder `E ⊗ Δ[1] ⟶ E'`.
* `over` requires the cylinder to lie over `p`: `hom.h ≫ p' = fst ≫ p`,
  constant in the interval direction. Consequently `f ≫ p' = p`
  (`fac₀`) and `g ≫ p' = p` (`fac₁`). -/
structure FiberwiseHomotopy (p : E ⟶ B) (p' : E' ⟶ B) (f g : E ⟶ E') where
  /-- Underlying ordinary simplicial homotopy. -/
  hom : Homotopy f g
  /-- The cylinder lies over `p`: `hom.h ≫ p' = fst ≫ p`. -/
  over : hom.h ≫ p' = fst _ _ ≫ p

namespace FiberwiseHomotopy

variable {p : E ⟶ B} {p' : E' ⟶ B} {f g : E ⟶ E'}

/-- Source endpoint lies over the base: `f ≫ p' = p`.

Follows `hom.h₀` along `SSet.ι₀`: both composites agree with the constant
over-base value `p`. -/
lemma fac₀ (H : FiberwiseHomotopy (p := p) (p' := p') (f := f) (g := g)) :
    f ≫ p' = p := by
  have h₀ : (SSet.ι₀ ≫ H.hom.h) ≫ p' = f ≫ p' := by rw [H.hom.h₀]
  have hbase : (SSet.ι₀ ≫ H.hom.h) ≫ p' = p := by
    calc (SSet.ι₀ ≫ H.hom.h) ≫ p'
        = SSet.ι₀ ≫ (H.hom.h ≫ p') := by rw [Category.assoc]
      _ = SSet.ι₀ ≫ (fst _ _ ≫ p) := by rw [H.over]
      _ = (SSet.ι₀ ≫ fst _ _) ≫ p := by rw [Category.assoc]
      _ = p := by rw [SSet.ι₀_fst, Category.id_comp]
  exact h₀.symm.trans hbase

/-- Target endpoint lies over the base: `g ≫ p' = p`.

Follows `hom.h₁` along `SSet.ι₁`: both composites agree with the constant
over-base value `p`. -/
lemma fac₁ (H : FiberwiseHomotopy (p := p) (p' := p') (f := f) (g := g)) :
    g ≫ p' = p := by
  have h₁ : (SSet.ι₁ ≫ H.hom.h) ≫ p' = g ≫ p' := by rw [H.hom.h₁]
  have hbase : (SSet.ι₁ ≫ H.hom.h) ≫ p' = p := by
    calc (SSet.ι₁ ≫ H.hom.h) ≫ p'
        = SSet.ι₁ ≫ (H.hom.h ≫ p') := by rw [Category.assoc]
      _ = SSet.ι₁ ≫ (fst _ _ ≫ p) := by rw [H.over]
      _ = (SSet.ι₁ ≫ fst _ _) ≫ p := by rw [Category.assoc]
      _ = p := by rw [SSet.ι₁_fst, Category.id_comp]
  exact h₁.symm.trans hbase

/-- Reflexive map-level fiberwise homotopy from a map lying over the base.

Given `hfac : f ≫ p' = p`, the constant cylinder `fst ≫ f` is an ordinary
homotopy from `f` to `f` and lies over `p` by associativity. Needs no
fibration hypothesis. -/
def refl (f : E ⟶ E') (hfac : f ≫ p' = p) :
    FiberwiseHomotopy (p := p) (p' := p') (f := f) (g := f) where
  hom :=
    { h := fst _ _ ≫ f
      h₀ := by simp
      h₁ := by simp
      rel := by ext n ⟨⟨x, hx⟩, t⟩; cases hx }
  over := by
    change (fst _ _ ≫ f) ≫ p' = fst _ _ ≫ p
    rw [Category.assoc, hfac]

end FiberwiseHomotopy

namespace MinimalFibration

variable {X S : SSet.{u}}

/-- Simplex-level over-relation witness between `n`-simplices `x y : X _⦋n⦌`
over `p : X ⟶ S`.

* `hom` is a cylinder homotopy stationary on `SSet.boundary n`.
* `base` is an arbitrary base simplex `Δ[n] ⟶ S` (not assumed constant).
* `bd` is the common boundary value `∂Δ[n] ⟶ X`.
* `over` requires the cylinder to lie over `base`.
* `boundary` requires the source simplex to restrict to `bd` on `∂Δ[n]`;
  the target restriction is derived from stationarity (`boundary_right`). -/
@[ext]
structure OverRelation {n : ℕ} (p : X ⟶ S) (x y : X _⦋n⦌) where
  /-- Cylinder homotopy stationary on `SSet.boundary n`. -/
  hom : HomotopyRel (yonedaEquiv.symm x) (yonedaEquiv.symm y) (SSet.boundary n)
  /-- Arbitrary base simplex. -/
  base : Δ[n] ⟶ S
  /-- Common boundary value. -/
  bd : (SSet.boundary n : SSet.{u}) ⟶ X
  /-- The cylinder lies over `base`. -/
  over : hom.h ≫ p = fst _ _ ≫ base
  /-- The source simplex restricts to `bd` on the boundary. -/
  boundary : (SSet.boundary n).ι ≫ yonedaEquiv.symm x = bd

namespace OverRelation

variable {p : X ⟶ S} {n : ℕ} {x y : X _⦋n⦌}

/-- The source simplex lies over `base`: `yonedaEquiv.symm x ≫ p = base`.

Follows `hom.h₀` along `SSet.ι₀`. -/
lemma base_left (W : OverRelation (n := n) p x y) :
    yonedaEquiv.symm x ≫ p = W.base := by
  have h₀ : (SSet.ι₀ ≫ W.hom.h) ≫ p = yonedaEquiv.symm x ≫ p := by
    rw [W.hom.h₀]
  have hbase : (SSet.ι₀ ≫ W.hom.h) ≫ p = W.base := by
    calc (SSet.ι₀ ≫ W.hom.h) ≫ p
        = SSet.ι₀ ≫ (W.hom.h ≫ p) := by rw [Category.assoc]
      _ = SSet.ι₀ ≫ (fst _ _ ≫ W.base) := by rw [W.over]
      _ = (SSet.ι₀ ≫ fst _ _) ≫ W.base := by rw [Category.assoc]
      _ = W.base := by rw [SSet.ι₀_fst, Category.id_comp]
  exact h₀.symm.trans hbase

/-- The target simplex lies over `base`: `yonedaEquiv.symm y ≫ p = base`.

Follows `hom.h₁` along `SSet.ι₁`. -/
lemma base_right (W : OverRelation (n := n) p x y) :
    yonedaEquiv.symm y ≫ p = W.base := by
  have h₁ : (SSet.ι₁ ≫ W.hom.h) ≫ p = yonedaEquiv.symm y ≫ p := by
    rw [W.hom.h₁]
  have hbase : (SSet.ι₁ ≫ W.hom.h) ≫ p = W.base := by
    calc (SSet.ι₁ ≫ W.hom.h) ≫ p
        = SSet.ι₁ ≫ (W.hom.h ≫ p) := by rw [Category.assoc]
      _ = SSet.ι₁ ≫ (fst _ _ ≫ W.base) := by rw [W.over]
      _ = (SSet.ι₁ ≫ fst _ _) ≫ W.base := by rw [Category.assoc]
      _ = W.base := by rw [SSet.ι₁_fst, Category.id_comp]
  exact h₁.symm.trans hbase

/-- Both simplices agree on the boundary.

Derived from stationarity of `hom` on `SSet.boundary n` at the `ι₁` endpoint;
the boundary map `bd` is not needed. -/
lemma boundary_eq (W : OverRelation (n := n) p x y) :
    (SSet.boundary n).ι ≫ yonedaEquiv.symm x =
      (SSet.boundary n).ι ≫ yonedaEquiv.symm y := by
  ext m ⟨a, ha⟩
  change (yonedaEquiv.symm x).app m a = (yonedaEquiv.symm y).app m a
  have h_app_y : W.hom.h.app m (SSet.ι₁.app m a) =
      (yonedaEquiv.symm y).app m a := by
    calc W.hom.h.app m (SSet.ι₁.app m a)
        = (SSet.ι₁ ≫ W.hom.h).app m a := rfl
      _ = (yonedaEquiv.symm y).app m a := by rw [W.hom.h₁]
  have h_fst : (SSet.ι₁.app m a).1 = a := by simp
  have h_pair : SSet.ι₁.app m a = ⟨a, (SSet.ι₁.app m a).2⟩ := by
    apply Prod.ext
    · exact h_fst
    · rfl
  have h_stat : W.hom.h.app m (SSet.ι₁.app m a) =
      (yonedaEquiv.symm x).app m a := by
    calc W.hom.h.app m (SSet.ι₁.app m a)
        = W.hom.h.app m ⟨a, (SSet.ι₁.app m a).2⟩ := by rw [h_pair]
      _ = (yonedaEquiv.symm x).app m a := W.hom.stationary a ha _
  exact h_stat.symm.trans h_app_y

/-- The target simplex restricts to `bd` on the boundary.

Combines `boundary` with `boundary_eq`. -/
lemma boundary_right (W : OverRelation (n := n) p x y) :
    (SSet.boundary n).ι ≫ yonedaEquiv.symm y = W.bd := by
  rw [← W.boundary_eq, W.boundary]

/-- The over-base commuting square: `hom.h ≫ p = fst ≫ base`. -/
theorem overSquare (W : OverRelation (n := n) p x y) :
    CommSq W.hom.h (fst _ _) p W.base :=
  CommSq.mk W.over

/-- Unconditional reflexive witness over the constant base.

Uses `HomotopyRel.refl`; the `over` condition holds by associativity and
the boundary condition holds by reflexivity. Needs no fibration
hypothesis. -/
noncomputable def refl (x : X _⦋n⦌) :
    OverRelation (n := n) (p := p) (x := x) (y := x) where
  hom := HomotopyRel.refl (yonedaEquiv.symm x) (SSet.boundary n)
  base := yonedaEquiv.symm x ≫ p
  bd := (SSet.boundary n).ι ≫ yonedaEquiv.symm x
  over := by
    calc (HomotopyRel.refl (yonedaEquiv.symm x) (SSet.boundary n)).h ≫ p
        _ = (fst _ _ ≫ yonedaEquiv.symm x) ≫ p := rfl
        _ = fst _ _ ≫ (yonedaEquiv.symm x ≫ p) := Category.assoc _ _ _
  boundary := rfl

/-- Convert into the existing constant-base simplex-level
`FiberwiseHomotopy`.

The cylinder is reused unchanged; `base_left` rewrites the arbitrary base
to the constant base `yonedaEquiv.symm x ≫ p`. -/
def toFiberwiseHomotopy (W : OverRelation (n := n) p x y) :
    FiberwiseHomotopy (n := n) p x y where
  homotopyRel := W.hom
  over := by
    calc W.hom.h ≫ p
        = fst _ _ ≫ W.base := W.over
      _ = fst _ _ ≫ (yonedaEquiv.symm x ≫ p) := by rw [W.base_left]

/-- An over-relation witness forces equality under `IsMinimal p`.

The base images agree by `base_left`/`base_right`, the boundary
restrictions agree by `boundary`/`boundary_right`, and
`toFiberwiseHomotopy` supplies the constant-base witness. -/
theorem eq (hmin : IsMinimal p) (W : OverRelation (n := n) p x y) : x = y := by
  apply hmin
  · exact W.toFiberwiseHomotopy.base_app_eq
  · exact W.boundary.trans W.boundary_right.symm
  · exact ⟨W.toFiberwiseHomotopy⟩

end OverRelation

end MinimalFibration

end SSet
