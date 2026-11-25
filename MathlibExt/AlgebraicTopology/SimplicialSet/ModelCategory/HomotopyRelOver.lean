/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetDeformationRetract

/-!
This module defines `HomotopyRelOver p f g A`: a homotopy relative to `A`
with source endpoint `f`, target endpoint `g`, stationary on `A`, and lying
over `f ≫ p`.

* `refl` is unconditional and constant from `f` to `f`.
* `symm` requires `[Fibration p]` and uses outer horn `Λ[2,2]`.
* `trans` requires `[Fibration p]` and uses inner horn `Λ[2,1]`.

This module provides no associativity/unit/coherence laws and no
minimal-fibration wrapper.
-/

@[expose] public section

open CategoryTheory Simplicial SSet Limits MonoidalCategory CartesianMonoidalCategory

universe u

namespace SSet

/-- A homotopy relative to `A : X.Subcomplex` that lies over a fixed `p : Y ⟶ S`.

For `f g : X ⟶ Y`, a witness `H : HomotopyRelOver p f g A` consists of an
underlying relative homotopy `H.toHomotopyRel : HomotopyRel f g A` with homotopy
`h : X ⊗ Δ[1] ⟶ Y` satisfying `h ≫ p = fst ≫ (f ≫ p)`. Stationarity on `A`
is inherited from `HomotopyRel`. The equation implies `f ≫ p = g ≫ p`. This is
the simplicial analogue of a homotopy over a base, used for fiberwise homotopy
in the minimal-fibration development. -/
structure HomotopyRelOver {X Y S : SSet.{u}} (p : Y ⟶ S) (f g : X ⟶ Y)
    (A : X.Subcomplex) where
  /-- Underlying relative homotopy stationary on `A`. -/
  toHomotopyRel : HomotopyRel f g A
  /-- The homotopy lies over `p`: `h ≫ p = fst ≫ (f ≫ p)`. -/
  over : toHomotopyRel.h ≫ p = fst _ _ ≫ (f ≫ p)

namespace HomotopyRelOver

variable {X Y S : SSet.{u}} {p : Y ⟶ S} {f g : X ⟶ Y} {A : X.Subcomplex}

/-- The underlying homotopy `X ⊗ Δ[1] ⟶ Y`. -/
def h (H : HomotopyRelOver p f g A) : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  H.toHomotopyRel.h

@[reassoc (attr := simp)]
lemma h₀ (H : HomotopyRelOver p f g A) : SSet.ι₀ ≫ H.h = f :=
  H.toHomotopyRel.h₀

@[reassoc (attr := simp)]
lemma h₁ (H : HomotopyRelOver p f g A) : SSet.ι₁ ≫ H.h = g :=
  H.toHomotopyRel.h₁

/-- Stationarity on `A`: `h` coincides with `f` on `A` in the interval direction. -/
lemma stationary (H : HomotopyRelOver p f g A) {n : SimplexCategoryᵒᵖ}
    {x : X.obj n} (hx : x ∈ A.obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    H.h.app n ⟨x, t⟩ = f.app n x :=
  H.toHomotopyRel.stationary x hx t

@[reassoc]
lemma over_eq (H : HomotopyRelOver p f g A) :
    H.h ≫ p = fst _ _ ≫ (f ≫ p) :=
  H.over

/-- Derived equality `f ≫ p = g ≫ p` from lying over `p`. -/
lemma map_eq (H : HomotopyRelOver p f g A) : f ≫ p = g ≫ p := by
  have hg1 : (SSet.ι₁ ≫ H.toHomotopyRel.h) ≫ p = g ≫ p := by
    rw [H.toHomotopyRel.h₁]
  have hg2 : (SSet.ι₁ ≫ H.toHomotopyRel.h) ≫ p = f ≫ p := by
    calc (SSet.ι₁ ≫ H.toHomotopyRel.h) ≫ p
        = SSet.ι₁ ≫ (H.toHomotopyRel.h ≫ p) := by rw [Category.assoc]
      _ = SSet.ι₁ ≫ (fst _ _ ≫ (f ≫ p)) := by rw [H.over]
      _ = (SSet.ι₁ ≫ fst _ _) ≫ (f ≫ p) := by rw [Category.assoc]
      _ = f ≫ p := by rw [SSet.ι₁_fst, Category.id_comp]
  exact hg2.symm.trans hg1

/-- Unconditional reflexivity: the constant homotopy from `f` to `f`.

`HomotopyRelOver.refl f A p` is the unconditional constant homotopy from `f`
to `f`; both endpoints are `f` (`ι₀ = f`, `ι₁ = f`); it is stationary at `f`
on `A`; its underlying homotopy satisfies
`(HomotopyRelOver.refl f A p).h ≫ p = fst _ _ ≫ (f ≫ p)`; it needs no
`[Fibration p]`. -/
noncomputable def refl (f : X ⟶ Y) (A : X.Subcomplex) (p : Y ⟶ S) :
    HomotopyRelOver p f f A where
  toHomotopyRel := HomotopyRel.refl f A
  over := by
    calc (HomotopyRel.refl f A).h ≫ p
        = (fst _ _ ≫ f) ≫ p := rfl
      _ = fst _ _ ≫ (f ≫ p) := by rw [Category.assoc]

end HomotopyRelOver

end SSet

end

public section

open CategoryTheory Simplicial SSet Limits MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet

namespace HomotopyRelOver

variable {X Y S : SSet.{u}} {p : Y ⟶ S} {f g : X ⟶ Y} {A : X.Subcomplex}

/-! ## Symmetry horn scaffolding (outer horn `Λ[2,2]`)

For `H : HomotopyRelOver p f g A` we build symmetry `g ~ f` by filling
outer horn `Λ[2,2]`. First step tensors `horn₂₂.isPushout` left by `X`
and glues constant homotopy `fst ≫ g` on `ι₀₂` with `H.h` on `ι₁₂`.
Shared vertex is final endpoint `g` via `δ 0`. Glued map
`X ⊗ Λ[2,2] ⟶ Y` is outer-horn part of future `symm`. No union-product,
fibration lift, missing edge, or public `symm` here. -/

/-- `Λ[2,2]` as pushout tensored left by `X`. -/
private theorem horn₂₂TensorLeftIsPushout (X : SSet.{u}) :
    IsPushout
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (X ◁ SSet.horn₂₂.ι₀₂)
      (X ◁ SSet.horn₂₂.ι₁₂) := by
  have : PreservesColimit
      (span (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])
        (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (MonoidalCategory.tensorLeft (X : SSet.{u})) :=
    inferInstance
  exact (MonoidalCategory.tensorLeft (X : SSet.{u})).map_isPushout
    SSet.horn₂₂.isPushout

/-- Constant homotopy at `g`, placed on face `ι₀₂`. -/
private noncomputable def symmHornConst {X Y : SSet.{u}} (g : X ⟶ Y) :
    X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  fst _ _ ≫ g

/-- Face: constant homotopy restricts to `g` at final vertex `ι₁`. -/
@[reassoc (attr := simp)]
private lemma symmHornConst_ι₁ {X Y : SSet.{u}} (g : X ⟶ Y) :
    SSet.ι₁ ≫ (symmHornConst g : X ⊗ Δ[1] ⟶ Y) = g := by
  simp [symmHornConst]

/-- Face: `H.h` restricts to `g` at final vertex `ι₁`. -/
@[reassoc (attr := simp)]
private lemma symmHornH_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    SSet.ι₁ ≫ H.h = g :=
  H.h₁

/-- Shared-vertex: constant face equals `g` after `X ⊗ Δ[0]`. -/
private lemma symmHornConst_δ₀ {X Y : SSet.{u}} (g : X ⟶ Y) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫
        (symmHornConst g : X ⊗ Δ[1] ⟶ Y) =
      fst _ _ ≫ g := by
  ext n ⟨x, _t₀⟩
  rfl

/-- Shared-vertex: `H.h` equals `g` after `X ⊗ Δ[0]`, keeping final
endpoint `g` as common vertex. -/
private lemma symmHornH_δ₀ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H.h =
      fst _ _ ≫ g := by
  ext n ⟨x, t₀⟩
  have hδ : stdSimplex.δ (0 : Fin 2) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
    stdSimplex.δ_zero_eq_const
  have h_pair :
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])).app n ⟨x, t₀⟩ =
        SSet.ι₁.app n x := by
    have h₁ : (X ◁ (stdSimplex.δ (0 : Fin 2))).app n ⟨x, t₀⟩ =
        ⟨x, (stdSimplex.δ (0 : Fin 2)).app n t₀⟩ := rfl
    have h₂ : (stdSimplex.δ (0 : Fin 2)).app n t₀ =
        (SSet.const (stdSimplex.obj₀Equiv.symm 1) : X ⟶ Δ[1]).app n x := by
      rw [hδ]
      rfl
    have h₃ : SSet.ι₁.app n x =
        ⟨x, (SSet.const (stdSimplex.obj₀Equiv.symm 1) : X ⟶ Δ[1]).app n x⟩ := rfl
    rw [h₁, h₂, ← h₃]
  calc H.h.app n ((X ◁ (stdSimplex.δ (0 : Fin 2))).app n ⟨x, t₀⟩)
      = H.h.app n (SSet.ι₁.app n x) := by rw [h_pair]
    _ = (SSet.ι₁ ≫ H.h).app n x := rfl
    _ = g.app n x := by rw [H.h₁]
    _ = (fst _ _ ≫ g).app n ⟨x, t₀⟩ := rfl

/-- Agreement of two outer faces at shared vertex `g`. -/
private lemma symmHornFaces_agree {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫
        (symmHornConst g : X ⊗ Δ[1] ⟶ Y) =
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H.h := by
  rw [symmHornConst_δ₀, symmHornH_δ₀]

/-- Glued map `X ⊗ Λ[2,2] ⟶ Y` from const on `ι₀₂` and `H.h` on `ι₁₂`. -/
private noncomputable def symmHornMap {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    X ⊗ (SSet.horn 2 (2 : Fin 3) : SSet.{u}) ⟶ Y :=
  (horn₂₂TensorLeftIsPushout X).desc
    (symmHornConst g) H.h (symmHornFaces_agree H)

/-- Face `ι₀₂` of glued horn map is constant at `g`. -/
@[reassoc]
private lemma symmHornMap_ι₀₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H = symmHornConst g :=
  (horn₂₂TensorLeftIsPushout X).inl_desc _ _ _

/-- Face `ι₁₂` of glued horn map is `H.h`. -/
@[reassoc]
private lemma symmHornMap_ι₁₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H = H.h :=
  (horn₂₂TensorLeftIsPushout X).inr_desc _ _ _

/-! ## Stationary `A`-face

For future symmetry, the union-product square has a stationary face
`A ⊗ Δ[2] ⟶ Y` obtained by projecting to `A`, including into `X`, and then
`f`. Its postcomposition with `p` is the restriction of the base map
`X ⊗ Δ[2] ⟶ S`, `fst ≫ (f ≫ p)`, along `A.ι ▷ Δ[2]`. This is the only
result proved in this checkpoint. -/

/-- Base map `X ⊗ Δ[2] ⟶ S` projecting to `X` then `f ≫ p`. -/
private noncomputable def symmBaseMap {X Y S : SSet.{u}} (p : Y ⟶ S) (f : X ⟶ Y) :
    X ⊗ (Δ[2] : SSet.{u}) ⟶ S :=
  fst X _ ≫ f ≫ p

/-- Stationary face `A ⊗ Δ[2] ⟶ Y` projecting to `A` then `A.ι ≫ f`. -/
private noncomputable def symmStationaryFace {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) :
    (A : SSet.{u}) ⊗ (Δ[2] : SSet.{u}) ⟶ Y :=
  fst (A : SSet.{u}) _ ≫ A.ι ≫ f

/-- Projection equality: the stationary face over `p` is the restriction of the
base map along `A.ι ▷ Δ[2]`. -/
private lemma symmStationaryFace_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f : X ⟶ Y} {A : X.Subcomplex} :
    symmStationaryFace f A ≫ p = (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmBaseMap p f := by
  calc symmStationaryFace f A ≫ p
      = (fst (A : SSet.{u}) (Δ[2] : SSet.{u}) ≫ A.ι) ≫ f ≫ p := by
        simp only [symmStationaryFace, Category.assoc]
    _ = (A.ι ▷ (Δ[2] : SSet.{u}) ≫ fst X (Δ[2] : SSet.{u})) ≫ f ≫ p := by
        rw [← whiskerRight_fst (f := A.ι) (Z := (Δ[2] : SSet.{u}))]
    _ = (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmBaseMap p f := by
        simp only [symmBaseMap, Category.assoc]

/-- A relative homotopy stationary on `A` has equal restrictions to `A` at both endpoints:
`A.ι ≫ f = A.ι ≫ g`. Derived from the pointwise stationarity `H.stationary` and the
endpoint law `H.h₁` (and symmetrically `H.h₀`). -/
private lemma stationary_ends {X Y S : SSet.{u}} {p : Y ⟶ S} {f g : X ⟶ Y}
    {A : X.Subcomplex} (H : HomotopyRelOver p f g A) :
    A.ι ≫ f = A.ι ≫ g := by
  ext n ⟨x, hx⟩
  have h_app_g : H.h.app n (SSet.ι₁.app n x) = g.app n x := by
    calc H.h.app n (SSet.ι₁.app n x)
        = (SSet.ι₁ ≫ H.h).app n x := rfl
      _ = g.app n x := by rw [H.h₁]
  have h_fst : (SSet.ι₁.app n x).1 = x := by
    simp
  have h_pair : SSet.ι₁.app n x = ⟨x, (SSet.ι₁.app n x).2⟩ := by
    apply Prod.ext
    · exact h_fst
    · rfl
  have h_stat : H.h.app n (SSet.ι₁.app n x) = f.app n x := by
    calc H.h.app n (SSet.ι₁.app n x)
        = H.h.app n ⟨x, (SSet.ι₁.app n x).2⟩ := by rw [h_pair]
      _ = f.app n x := H.stationary (x := x) hx (t := (SSet.ι₁.app n x).2)
  calc (A.ι ≫ f).app n ⟨x, hx⟩
      = f.app n x := rfl
    _ = H.h.app n (SSet.ι₁.app n x) := h_stat.symm
    _ = g.app n x := h_app_g
    _ = (A.ι ≫ g).app n ⟨x, hx⟩ := rfl

/-- Stationary face restricts to `ι₀₂` as `fst ≫ A.ι ≫ f`. -/
private lemma symmStationaryFace_ι₀₂ {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) :
    (A : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 3) ≫ symmStationaryFace f A
      = (A : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 3) ≫
          (fst (A : SSet.{u}) (Δ[2] : SSet.{u}) ≫ A.ι ≫ f) := rfl
    _ = ((A : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 3) ≫
          fst (A : SSet.{u}) (Δ[2] : SSet.{u})) ≫ A.ι ≫ f := by
        simp only [Category.assoc]
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
        rw [whiskerLeft_fst]

/-- Horn side `ι₀₂` restricts to `fst ≫ A.ι ≫ g`. -/
private lemma symmHornMap_ι₀₂_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
        (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
      fst _ _ ≫ A.ι ≫ g := by
  calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
      = ((A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
            A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H := by
        simp only [Category.assoc]
    _ = ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H := by
        rw [whisker_exchange]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (X ◁ SSet.horn₂₂.ι₀₂ ≫ symmHornMap H) := by
        simp only [Category.assoc]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ symmHornConst g := by
        rw [symmHornMap_ι₀₂]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (fst X (Δ[1] : SSet.{u}) ≫ g) := rfl
    _ = (A.ι ▷ (Δ[1] : SSet.{u}) ≫ fst X (Δ[1] : SSet.{u})) ≫ g := by
        simp only [Category.assoc]
    _ = (fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι) ≫ g := by
        rw [whiskerRight_fst]
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ g := by
        simp only [Category.assoc]

/-- Common-intersection on face `ι₀₂`: horn-side and stationary `A ⊗ Δ[2]`
restrictions agree. This is the `ι₀₂` face compatibility needed for symmetry. -/
private lemma symmHornMap_ι₀₂_stationaryAgree {X Y S : SSet.{u}}
    {p : Y ⟶ S} {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
        (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
      (A : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A := by
  have hHorn := symmHornMap_ι₀₂_restrict H
  have hStat := symmStationaryFace_ι₀₂ (X := X) (Y := Y) f A
  have hg : A.ι ≫ g = A.ι ≫ f := (stationary_ends H).symm
  calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
      = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ g := hHorn
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
        rw [hg]
    _ = (A : SSet.{u}) ◁ stdSimplex.δ (1 : Fin 3) ≫ symmStationaryFace f A := by
        rw [← hStat]

/-- Stationary face restricts to `ι₁₂` as `fst ≫ A.ι ≫ f`. -/
private lemma symmStationaryFace_ι₁₂ {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) :
    (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 3) ≫ symmStationaryFace f A
      = (A : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 3) ≫
          (fst (A : SSet.{u}) (Δ[2] : SSet.{u}) ≫ A.ι ≫ f) := rfl
    _ = ((A : SSet.{u}) ◁ stdSimplex.δ (0 : Fin 3) ≫
          fst (A : SSet.{u}) (Δ[2] : SSet.{u})) ≫ A.ι ≫ f := by
        simp only [Category.assoc]
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
        rw [whiskerLeft_fst]

/-- `H.h` is stationary on `A`: `(A.ι ▷ Δ[1]) ≫ H.h = fst ≫ A.ι ≫ f`. -/
private lemma symmHornH_stationary {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst _ _ ≫ A.ι ≫ f := by
  ext n ⟨⟨x, hx⟩, t⟩
  calc (A.ι ▷ (Δ[1] : SSet.{u}) ≫ H.h).app n ⟨⟨x, hx⟩, t⟩
      = H.h.app n ⟨x, t⟩ := rfl
    _ = f.app n x := H.stationary hx t
    _ = (fst _ _ ≫ A.ι ≫ f).app n ⟨⟨x, hx⟩, t⟩ := rfl

/-- Horn side `ι₁₂` restricts to `fst ≫ A.ι ≫ f` via stationarity. -/
private lemma symmHornMap_ι₁₂_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
        (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
      = ((A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
            A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H := by
        simp only [Category.assoc]
    _ = ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H := by
        rw [whisker_exchange]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (X ◁ SSet.horn₂₂.ι₁₂ ≫ symmHornMap H) := by
        simp only [Category.assoc]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ H.h := by
        rw [symmHornMap_ι₁₂]
    _ = fst _ _ ≫ A.ι ≫ f := symmHornH_stationary H

/-- Common-intersection on face `ι₁₂`: horn-side and stationary `A ⊗ Δ[2]`
restrictions agree. This is the `ι₁₂` face compatibility needed for symmetry. -/
private lemma symmHornMap_ι₁₂_stationaryAgree {X Y S : SSet.{u}}
    {p : Y ⟶ S} {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
        (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
      (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A := by
  rw [symmHornMap_ι₁₂_restrict H, symmStationaryFace_ι₁₂]

/-- Full common-intersection equality on `A ⊗ Λ[2,2]`:
the horn-side `(A.ι ▷ horn) ≫ symmHornMap H` equals stationary side
`(A ◁ horn.ι) ≫ symmStationaryFace f A`, via `horn₂₂TensorLeftIsPushout A`
hom-ext and the two accepted face agreements together with
`SSet.horn.ι_ι` and `MonoidalCategory.whiskerLeft_comp`. -/
private lemma symmHornMap_commonIntersection {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H =
    (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι ≫
      symmStationaryFace f A := by
  apply (horn₂₂TensorLeftIsPushout (A : SSet.{u})).hom_ext
  · calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
        = (A : SSet.{u}) ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
            symmStationaryFace f A :=
          symmHornMap_ι₀₂_stationaryAgree H
      _ = (A : SSet.{u}) ◁ (SSet.horn₂₂.ι₀₂ ≫
            (SSet.horn 2 (2 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [← SSet.horn.ι_ι (2 : Fin 3) (1 : Fin 3) (by decide)]
      _ = ((A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [MonoidalCategory.whiskerLeft_comp]
      _ = (A : SSet.{u}) ◁ SSet.horn₂₂.ι₀₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι ≫
              symmStationaryFace f A := by
          rw [Category.assoc]
  · calc (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
          (A.ι ▷ (SSet.horn 2 (2 : Fin 3) : SSet.{u})) ≫ symmHornMap H
        = (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
            symmStationaryFace f A :=
          symmHornMap_ι₁₂_stationaryAgree H
      _ = (A : SSet.{u}) ◁ (SSet.horn₂₂.ι₁₂ ≫
            (SSet.horn 2 (2 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [← SSet.horn.ι_ι (2 : Fin 3) (0 : Fin 3) (by decide)]
      _ = ((A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [MonoidalCategory.whiskerLeft_comp]
      _ = (A : SSet.{u}) ◁ SSet.horn₂₂.ι₁₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (2 : Fin 3)).ι ≫
              symmStationaryFace f A := by
          rw [Category.assoc]

/-! ## Union-product gluing

Glued map `(A.unionProd Λ[2,2]).toSSet ⟶ Y` from `symmHornMap H : X ⊗ Λ[2,2] ⟶ Y`
and `symmStationaryFace f A : A ⊗ Δ[2] ⟶ Y`, via the pinned
`Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))` and the accepted
`symmHornMap_commonIntersection H`. Two private restriction equations. -/

/-- Union-product glued map
`(A.unionProd (SSet.horn 2 (2 : Fin 3))).toSSet ⟶ Y`, from
`symmHornMap H` and `symmStationaryFace f A` via
`Subcomplex.unionProd.isPushout`. -/
private noncomputable def symmUnionMap {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    (A.unionProd (SSet.horn 2 (2 : Fin 3)) : SSet.{u}) ⟶ Y :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))).desc
    (symmHornMap H) (symmStationaryFace f A)
    (symmHornMap_commonIntersection H)

/-- Restriction to `ι₁` recovers `symmHornMap H`. -/
private lemma symmUnionMap_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H =
      symmHornMap H :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))).inl_desc _ _ _

/-- Restriction to `ι₂` recovers `symmStationaryFace f A`. -/
private lemma symmUnionMap_ι₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H =
      symmStationaryFace f A :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))).inr_desc _ _ _

/-- Constant horn face lies over `f ≫ p` via `H.map_eq`. -/
private lemma symmHornConst_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    symmHornConst g ≫ p = fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
  calc symmHornConst g ≫ p
      = (fst _ _ ≫ g) ≫ p := rfl
    _ = fst _ _ ≫ (g ≫ p) := by rw [Category.assoc]
    _ = fst _ _ ≫ (f ≫ p) := by rw [← H.map_eq]

/-- Glued outer-horn map lies over the base map
`fst ≫ (f ≫ p)` after whiskering by `horn.ι`. -/
private lemma symmHornMap_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    symmHornMap H ≫ p =
      (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f := by
  apply (horn₂₂TensorLeftIsPushout X).hom_ext
  · have hL : (X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H ≫ p =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H ≫ p
          = ((X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H) ≫ p := by
            rw [Category.assoc]
        _ = symmHornConst g ≫ p := by rw [symmHornMap_ι₀₂]
        _ = fst _ _ ≫ (f ≫ p) := symmHornConst_over H
    have hR : (X ◁ SSet.horn₂₂.ι₀₂) ≫
          (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₂.ι₀₂) ≫
              (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f
          = ((X ◁ SSet.horn₂₂.ι₀₂) ≫
                X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [Category.assoc]
        _ = (X ◁ (SSet.horn₂₂.ι₀₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι)) ≫
              symmBaseMap p f := by
            rw [← MonoidalCategory.whiskerLeft_comp]
        _ = (X ◁ stdSimplex.δ (1 : Fin 3)) ≫ symmBaseMap p f := by
            rw [SSet.horn.ι_ι (2 : Fin 3) (1 : Fin 3) (by decide)]
        _ = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              (fst _ _ ≫ (f ≫ p)) := by
            simp only [symmBaseMap]
        _ = ((X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              fst _ _) ≫ (f ≫ p) := by rw [← Category.assoc]
        _ = fst _ _ ≫ (f ≫ p) := by rw [whiskerLeft_fst]
    exact hL.trans hR.symm
  · have hL : (X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H ≫ p =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H ≫ p
          = ((X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H) ≫ p := by
            rw [Category.assoc]
        _ = H.h ≫ p := by rw [symmHornMap_ι₁₂]
        _ = fst _ _ ≫ (f ≫ p) := H.over
    have hR : (X ◁ SSet.horn₂₂.ι₁₂) ≫
          (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₂.ι₁₂) ≫
              (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f
          = ((X ◁ SSet.horn₂₂.ι₁₂) ≫
                X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [Category.assoc]
        _ = (X ◁ (SSet.horn₂₂.ι₁₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι)) ≫
              symmBaseMap p f := by
            rw [← MonoidalCategory.whiskerLeft_comp]
        _ = (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ symmBaseMap p f := by
            rw [SSet.horn.ι_ι (2 : Fin 3) (0 : Fin 3) (by decide)]
        _ = (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              (fst _ _ ≫ (f ≫ p)) := by
            simp only [symmBaseMap]
        _ = ((X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              fst _ _) ≫ (f ≫ p) := by rw [← Category.assoc]
        _ = fst _ _ ≫ (f ≫ p) := by rw [whiskerLeft_fst]
    exact hL.trans hR.symm

/-- The union-product gluing lies over the base `X ⊗ Δ[2] ⟶ S`. -/
private lemma symmUnionMap_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    symmUnionMap H ≫ p =
      (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmBaseMap p f := by
  apply (Subcomplex.unionProd.isPushout A (SSet.horn 2 (2 : Fin 3))).hom_ext
  · calc Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
              symmUnionMap H ≫ p
          = (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
              symmUnionMap H) ≫ p := by rw [Category.assoc]
        _ = symmHornMap H ≫ p := by rw [symmUnionMap_ι₁]
        _ = (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [symmHornMap_over H]
        _ = Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
              (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫
                symmBaseMap p f := by
            rw [Subcomplex.unionProd.ι₁_ι_assoc]
  · calc Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
              symmUnionMap H ≫ p
          = (Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
              symmUnionMap H) ≫ p := by rw [Category.assoc]
        _ = symmStationaryFace f A ≫ p := by rw [symmUnionMap_ι₂]
        _ = (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmBaseMap p f := by
            rw [symmStationaryFace_over]
        _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
              (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫
                symmBaseMap p f := by
            rw [Subcomplex.unionProd.ι₂_ι_assoc]

/-! ## Symmetry `CommSq` and anodyne lift setup

Packaging `symmUnionMap_over H` into a `CommSq` whose left inclusion
`(A.unionProd Λ[2,2]).ι` is anodyne; the fibration lift will supply the
future symmetry filler `X ⊗ Δ[2] ⟶ Y`. No `HasLiftingProperty`,
`lift`, filler, or endpoint law is chosen here. -/

/-- The symmetry square packaging `symmUnionMap_over H`:
top `symmUnionMap H`, left `(A.unionProd Λ[2,2]).ι`, right `p`,
bottom `symmBaseMap p f`. Orientation matches `CommSq f g h i`
with `f ≫ h = g ≫ i` and the fibration lifting API. -/
private theorem symmUnionCommSq {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H : HomotopyRelOver p f g A) :
    CommSq (symmUnionMap H)
      (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι
      p (symmBaseMap p f) :=
  CommSq.mk (symmUnionMap_over H)

/-- The union-product inclusion of `A` with outer horn `Λ[2,2]`
belongs to `SSet.anodyneExtensions`, via `anodyneExtensions_unionProd_ι`
and `anodyneExtensions.horn_ι (2 : Fin 3)`. -/
private lemma symmUnionProd_horn_ι_mem_anodyneExtensions
    {X : SSet.{u}} (A : X.Subcomplex) :
    SSet.anodyneExtensions
      (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι := by
  have hHorn : SSet.anodyneExtensions (SSet.horn 2 (2 : Fin 3)).ι :=
    SSet.anodyneExtensions.horn_ι (2 : Fin 3)
  exact SSet.anodyneExtensions_unionProd_ι A (SSet.horn 2 (2 : Fin 3)) hHorn

/-! ## Symmetry filler via fibration lifting (r6l)

From `symmUnionProd_horn_ι_mem_anodyneExtensions A` and the pinned
`HomotopicalAlgebra.fibration_iff` API we obtain
`HasLiftingProperty (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι p`
for `[Fibration p]`. The chosen filler `X ⊗ Δ[2] ⟶ Y` is
`(symmUnionCommSq H).lift`, with the two exact lift equations. -/

private lemma symmUnionProd_horn_ι_hasLiftingProperty
    {X : SSet.{u}} (A : X.Subcomplex)
    {Y S : SSet.{u}} {p : Y ⟶ S} [Fibration p] :
    HasLiftingProperty (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι p :=
  (symmUnionProd_horn_ι_mem_anodyneExtensions A) p
    (by rwa [← HomotopicalAlgebra.fibration_iff])

private instance symmUnionProd_horn_hasLiftingPropertyInst
    {X : SSet.{u}} {A : X.Subcomplex}
    {Y S : SSet.{u}} {p : Y ⟶ S} [Fibration p] :
    HasLiftingProperty (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι p :=
  symmUnionProd_horn_ι_hasLiftingProperty A

/-- Chosen symmetry filler `X ⊗ Δ[2] ⟶ Y` obtained from `symmUnionCommSq H`. -/
private noncomputable def symmFiller {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    X ⊗ (Δ[2] : SSet.{u}) ⟶ Y :=
  (symmUnionCommSq H).lift

/-- Filler postcomposes with `p` to `symmBaseMap p f`. -/
private lemma symmFiller_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    symmFiller H ≫ p = symmBaseMap p f :=
  (symmUnionCommSq H).fac_right

/-- Filler precomposed with union-product inclusion is `symmUnionMap H`. -/
private lemma symmFiller_union {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmFiller H = symmUnionMap H :=
  (symmUnionCommSq H).fac_left

/-- Reversed edge `X ⊗ Δ[1] ⟶ Y` obtained by restricting `symmFiller H` along
the missing outer-horn face `δ₂ : Δ[1] ⟶ Δ[2]` (Goerss–Jardine, *Simplicial
Homotopy Theory*, Chapter I, §6). -/
private noncomputable def symmHomotopy {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H

/-! ## Initial endpoint: `ι₀ ≫ symmHomotopy H = g`

The missing edge `δ₂ : Δ[1] ⟶ Δ[2]` has `δ₂ 0 = 0`. Its initial vertex is
`0 : Fin 3`, which lies on the constant horn face `ι₀₂ = δ₁ : Δ[1] ⟶ Δ[2]` that
carries `g`. Hence `ι₀ ≫ (X ◁ δ₂) = ι₀ ≫ (X ◁ δ₁)`. The latter factors as
`(ι₀ ≫ X ◁ horn₂₂.ι₀₂) ≫ X ◁ horn.ι = (ι₀ ≫ X ◁ horn₂₂.ι₀₂) ≫ unionProd.ι₁ ≫
union.ι`, so `filler` restricts via `symmFiller_union`, `symmUnionMap_ι₁`,
and `symmHornMap_ι₀₂` to the constant map `fst ≫ g`, whose `ι₀` restriction
is `g`. -/

/-- `δ₁` is `horn₂₂.ι₀₂ ≫ horn.ι` from `horn.ι_ι`. -/
private lemma symm_delta₁_eq :
    (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.horn₂₂.ι₀₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι := by
  rw [← SSet.horn.ι_ι (2 : Fin 3) (1 : Fin 3) (by decide)]

/-- Whisker factorisation for `δ₁`. -/
private lemma symm_whisker_δ₁ {X : SSet.{u}} :
    (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      (X ◁ SSet.horn₂₂.ι₀₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) := by
  calc (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = X ◁ (SSet.horn₂₂.ι₀₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι) := by
        rw [symm_delta₁_eq]
    _ = (X ◁ SSet.horn₂₂.ι₀₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) := by
        rw [MonoidalCategory.whiskerLeft_comp]

/-- Constant map at `g` has `ι₀` endpoint `g`. -/
private lemma symmHornConst_ι₀ {X Y : SSet.{u}} (g : X ⟶ Y) :
    SSet.ι₀ ≫ (symmHornConst g : X ⊗ Δ[1] ⟶ Y) = g := by
  calc SSet.ι₀ ≫ (symmHornConst g : X ⊗ Δ[1] ⟶ Y)
      = SSet.ι₀ ≫ (fst _ _ ≫ g) := rfl
    _ = (SSet.ι₀ ≫ fst _ _) ≫ g := by rw [Category.assoc]
    _ = g := by rw [SSet.ι₀_fst, Category.id_comp]

/-- Vertex `0 : Δ[1]` maps to `0 : Δ[2]` under both `δ₁` and `δ₂`. -/
private lemma symm_δ₁_zero :
    (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (0 : Fin 3) := rfl

private lemma symm_δ₂_zero :
    (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (0 : Fin 3) := rfl

/-- Both `δ₁` and `δ₂` send vertex `0` to `0`. Hence
`ι₀ ≫ X ◁ δ₁ = ι₀ ≫ X ◁ δ₂` as maps `X ⟶ X ⊗ Δ[2]`. -/
private lemma symm_iota₀_δ₁_eq_δ₂ {X : SSet.{u}} :
    SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
  -- `ι₀ = lift (𝟙 X) (const 0)` and `lift _ _ ≫ X ◁ δ = lift _ (const 0 ≫ δ)`
  calc SSet.ι₀ (X := X) ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
            (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) := by
        rw [SSet.const_comp]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3) : (Δ[2] : SSet.{u}) _⦋0⦌)) := by
        rw [symm_δ₁_zero]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) := by
        rw [symm_δ₂_zero]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
            (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [SSet.const_comp]
    _ = SSet.ι₀ (X := X) ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl

/-- `X ◁ horn.ι` is `unionProd.ι₁ ≫ union.ι` by `ι₁_ι` (rfl). -/
private lemma symm_horn_whisker_eq_unionProd {X : SSet.{u}}
    (A : X.Subcomplex) :
    (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) =
      Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
        (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι := by
  rw [← Subcomplex.unionProd.ι₁_ι]

private lemma symmHomotopy_ι₀ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    SSet.ι₀ ≫ symmHomotopy H = g := by
  calc SSet.ι₀ ≫ symmHomotopy H
      = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H := rfl
    _ = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H := by
        rw [← Category.assoc, ← Category.assoc, symm_iota₀_δ₁_eq_δ₂]
    _ = (SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ symmFiller H := by
        rw [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι)) ≫
        symmFiller H := by
        rw [symm_whisker_δ₁]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmFiller H := by
        simp only [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι) ≫ symmFiller H := by
        rw [symm_horn_whisker_eq_unionProd A]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmFiller H) := by
        simp only [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          symmUnionMap H := by
        rw [symmFiller_union H]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H) := by
        rw [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₀₂)) ≫ symmHornMap H := by
        rw [symmUnionMap_ι₁]
    _ = SSet.ι₀ ≫ ((X ◁ SSet.horn₂₂.ι₀₂) ≫ symmHornMap H) := by
        rw [Category.assoc]
    _ = SSet.ι₀ ≫ (symmHornConst g : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y) := by
        rw [symmHornMap_ι₀₂]
    _ = g := by
        rw [symmHornConst_ι₀]

/-! ## Final endpoint: `ι₁ ≫ symmHomotopy H = f`

The missing edge `δ₂ : Δ[1] ⟶ Δ[2]` has `δ₂ 1 = 1`. The horn face
`δ₀ = horn₂₂.ι₁₂ ≫ horn.ι` has `δ₀ 0 = 1`. Hence
`ι₁ ≫ (X ◁ δ₂) = ι₀ ≫ (X ◁ δ₀)` as maps `X ⟶ X ⊗ Δ[2]`, both equal to
`lift (𝟙 X) (const 1 : X ⟶ Δ[2])`. The latter factors as
`(ι₀ ≫ X ◁ horn₂₂.ι₁₂) ≫ X ◁ horn.ι = (ι₀ ≫ X ◁ horn₂₂.ι₁₂) ≫ unionProd.ι₁ ≫
union.ι`, so `filler` restricts via `symmFiller_union`, `symmUnionMap_ι₁`,
and `symmHornMap_ι₁₂` to `H.h`, whose `ι₀` restriction is `f` via `H.h₀`.
-/

/-- `δ₀` is `horn₂₂.ι₁₂ ≫ horn.ι` from `horn.ι_ι`. -/
private lemma symm_delta₀_eq :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.horn₂₂.ι₁₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι := by
  rw [← SSet.horn.ι_ι (2 : Fin 3) (0 : Fin 3) (by decide)]

/-- Whisker factorisation for `δ₀`. -/
private lemma symm_whisker_δ₀ {X : SSet.{u}} :
    (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      (X ◁ SSet.horn₂₂.ι₁₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) := by
  calc (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = X ◁ (SSet.horn₂₂.ι₁₂ ≫ (SSet.horn 2 (2 : Fin 3)).ι) := by
        rw [symm_delta₀_eq]
    _ = (X ◁ SSet.horn₂₂.ι₁₂) ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) := by
        rw [MonoidalCategory.whiskerLeft_comp]

/-- Vertex `0 : Δ[1]` maps to `1 : Δ[2]` under `δ₀`. -/
private lemma symm_δ₀_zero :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 3) := rfl

/-- Vertex `1 : Δ[1]` maps to `1 : Δ[2]` under missing `δ₂`. -/
private lemma symm_δ₂_one :
    (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (1 : Fin 3) := rfl

/-- `ι₁` on missing `δ₂` and `ι₀` on `δ₀ = horn₂₂.ι₁₂ ≫ horn.ι` reach the same
vertex `1 : Δ[2]`, hence
`ι₁ ≫ X ◁ δ₂ = ι₀ ≫ X ◁ δ₀` as maps `X ⟶ X ⊗ Δ[2]`. -/
private lemma symm_iota₁_δ₂_eq_ι₀_δ₀ {X : SSet.{u}} :
    SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
  calc SSet.ι₁ (X := X) ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
            (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) := by
        rw [SSet.const_comp]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 3) : (Δ[2] : SSet.{u}) _⦋0⦌)) := by
        rw [symm_δ₂_one]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) := by
        rw [symm_δ₀_zero]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
            (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [SSet.const_comp]
    _ = SSet.ι₀ (X := X) ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl

private lemma symmHomotopy_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    SSet.ι₁ ≫ symmHomotopy H = f := by
  calc SSet.ι₁ ≫ symmHomotopy H
      = SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H := rfl
    _ = (SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ symmFiller H := by
        rw [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ symmFiller H := by
        rw [symm_iota₁_δ₂_eq_ι₀_δ₀]
    _ = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H := by
        rw [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂ ≫ (X ◁ (SSet.horn 2 (2 : Fin 3)).ι)) ≫
        symmFiller H := by
        rw [symm_whisker_δ₀]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        (X ◁ (SSet.horn 2 (2 : Fin 3)).ι) ≫ symmFiller H := by
        simp only [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι) ≫ symmFiller H := by
        rw [symm_horn_whisker_eq_unionProd A]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmFiller H) := by
        simp only [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫
          symmUnionMap H := by
        rw [symmFiller_union H]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H) := rfl
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H := by
        rw [symmUnionMap_ι₁]
    _ = SSet.ι₀ ≫ ((X ◁ SSet.horn₂₂.ι₁₂) ≫ symmHornMap H) := rfl
    _ = SSet.ι₀ ≫ H.h := by
        rw [symmHornMap_ι₁₂]
    _ = f := by
        rw [H.h₀]

/-! ## Reversed-edge stationarity: `symmHomotopy H | A = g`

`symmFiller H : X ⊗ Δ[2] ⟶ Y` restricts along
`A.ι ▷ Δ[2] = ι₂ ≫ ι` to `symmStationaryFace f A` via `symmFiller_union`
and `symmUnionMap_ι₂`. Hence it is stationary on `A` at `f`. The missing
edge `δ₂ : Δ[1] ⟶ Δ[2]` whiskered left gives `symmHomotopy H`, whose
pointwise value on `A` is therefore `f`, hence `g` after `stationary_ends`.
-/

/-- Filler restricted to `A ⊗ Δ[2]` equals the stationary face at `f`. -/
private lemma symmFiller_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmFiller H = symmStationaryFace f A := by
  calc (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmFiller H
      = (Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (2 : Fin 3))).ι) ≫ symmFiller H := by
        rw [← Subcomplex.unionProd.ι₂_ι]
    _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (2 : Fin 3))).ι ≫ symmFiller H) := by
        rw [Category.assoc]
    _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (2 : Fin 3)) ≫ symmUnionMap H := by
        rw [symmFiller_union H]
    _ = symmStationaryFace f A := by
        rw [symmUnionMap_ι₂ H]

/-- `symmHomotopy H` is stationary on `A` at `g`:
`(symmHomotopy H).app n ⟨x,t⟩ = g.app n x` for `x ∈ A`. -/
private lemma symmHomotopy_stationary {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) {n : SimplexCategoryᵒᵖ}
    {x : X.obj n} (hx : x ∈ A.obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    (symmHomotopy H).app n ⟨x, t⟩ = g.app n x := by
  have h_whisker_δ₂ : (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])).app n ⟨x, t⟩ =
      ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
  have h_filler : (symmFiller H).app n
      ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ = f.app n x := by
    have hA : (A.ι ▷ (Δ[2] : SSet.{u})).app n
        ⟨⟨x, hx⟩, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ =
        ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
    calc (symmFiller H).app n
          ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩
        = (symmFiller H).app n
            ((A.ι ▷ (Δ[2] : SSet.{u})).app n
              ⟨⟨x, hx⟩, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩) := by
          rw [hA]
      _ = ((A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmFiller H).app n
            ⟨⟨x, hx⟩, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
      _ = (symmStationaryFace f A).app n
            ⟨⟨x, hx⟩, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := by
          rw [symmFiller_restrict H]
      _ = f.app n x := rfl
  have h_eq_f : (symmHomotopy H).app n ⟨x, t⟩ = f.app n x := by
    calc (symmHomotopy H).app n ⟨x, t⟩
        = ((X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmFiller H).app n ⟨x, t⟩ := rfl
      _ = (symmFiller H).app n
            ((X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])).app n ⟨x, t⟩) := rfl
      _ = (symmFiller H).app n
            ⟨x, (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := by
          rw [h_whisker_δ₂]
      _ = f.app n x := h_filler
  have h_fg : f.app n x = g.app n x := by
    calc f.app n x
        = (A.ι ≫ f).app n ⟨x, hx⟩ := rfl
      _ = (A.ι ≫ g).app n ⟨x, hx⟩ := by
          rw [stationary_ends H]
      _ = g.app n x := rfl
  exact h_eq_f.trans h_fg

/-- Reversed homotopy lies over the base at `g`: `symmHomotopy H ≫ p = fst ≫ (g ≫ p)`. -/
private lemma symmHomotopy_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H : HomotopyRelOver p f g A) :
    symmHomotopy H ≫ p = fst _ _ ≫ (g ≫ p) := by
  calc symmHomotopy H ≫ p
      = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫ symmFiller H) ≫ p := rfl
    _ = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ (symmFiller H ≫ p) := by
        rw [Category.assoc]
    _ = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmBaseMap p f := by
        rw [symmFiller_over H]
    _ = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
          (fst X _ ≫ (f ≫ p)) := by
        simp only [symmBaseMap]
    _ = ((X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ fst X _) ≫ (f ≫ p) := by
        rw [Category.assoc]
    _ = fst _ _ ≫ (f ≫ p) := by
        rw [whiskerLeft_fst]
    _ = fst _ _ ≫ (g ≫ p) := by
        rw [← H.map_eq]

/-- Symmetry for relative homotopies over a base.

For `H : HomotopyRelOver p f g A`, the result has start `g` and end `f`
(`ι₀` is `g`, `ι₁` is `f`), is stationary at `g` on `A`, and
`(symmHomotopy H) ≫ p = fst _ _ ≫ (g ≫ p)`. The `[Fibration p]` hypothesis is
required for this construction and the declaration does not assert transitivity. -/
noncomputable def symm [Fibration p] (H : HomotopyRelOver p f g A) :
    HomotopyRelOver p g f A where
  toHomotopyRel :=
    { h := symmHomotopy H
      h₀ := symmHomotopy_ι₀ H
      h₁ := symmHomotopy_ι₁ H
      stationary := fun _ hx t => symmHomotopy_stationary H hx t }
  over := symmHomotopy_over H

/-! ## Transitivity via inner horn `Λ[2,1]`

For transitivity we will use inner horn `Λ[2,1]`. This checkpoint
tensors `horn₂₁.isPushout` left by `X`, exactly as in
`horn₂₂TensorLeftIsPushout` (Goerss–Jardine, *Simplicial Homotopy Theory*,
Chapter I, §6). No horn map, union-product, lift, or public `trans` here. -/

/-- `Λ[2,1]` as pushout tensored left by `X`. -/
private theorem horn₂₁TensorLeftIsPushout (X : SSet.{u}) :
    IsPushout
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (X ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (X ◁ SSet.horn₂₁.ι₀₁)
      (X ◁ SSet.horn₂₁.ι₁₂) := by
  have : PreservesColimit
      (span (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])
        (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1]))
      (MonoidalCategory.tensorLeft (X : SSet.{u})) :=
    inferInstance
  exact (MonoidalCategory.tensorLeft (X : SSet.{u})).map_isPushout
    SSet.horn₂₁.isPushout

/-- Shared-vertex: `H₀₁.h` equals `g` after `X ⊗ Δ[0]`, keeping final
endpoint `g` as common vertex. -/
private lemma transHornH₀₁_δ₀ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H₀₁.h =
      fst _ _ ≫ g := by
  ext n ⟨x, t₀⟩
  have hδ : stdSimplex.δ (0 : Fin 2) =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
    stdSimplex.δ_zero_eq_const
  have h_pair :
      (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])).app n ⟨x, t₀⟩ =
        SSet.ι₁.app n x := by
    have h₁ : (X ◁ (stdSimplex.δ (0 : Fin 2))).app n ⟨x, t₀⟩ =
        ⟨x, (stdSimplex.δ (0 : Fin 2)).app n t₀⟩ := rfl
    have h₂ : (stdSimplex.δ (0 : Fin 2)).app n t₀ =
        (SSet.const (stdSimplex.obj₀Equiv.symm 1) : X ⟶ Δ[1]).app n x := by
      rw [hδ]
      rfl
    have h₃ : SSet.ι₁.app n x =
        ⟨x, (SSet.const (stdSimplex.obj₀Equiv.symm 1) : X ⟶ Δ[1]).app n x⟩ := rfl
    rw [h₁, h₂, ← h₃]
  calc H₀₁.h.app n ((X ◁ (stdSimplex.δ (0 : Fin 2))).app n ⟨x, t₀⟩)
      = H₀₁.h.app n (SSet.ι₁.app n x) := by rw [h_pair]
    _ = (SSet.ι₁ ≫ H₀₁.h).app n x := rfl
    _ = g.app n x := by rw [H₀₁.h₁]
    _ = (fst _ _ ≫ g).app n ⟨x, t₀⟩ := rfl

/-- Shared-vertex: `H₁₂.h` equals `g` after `X ⊗ Δ[0]`, keeping initial
endpoint `g` as common vertex via `δ_one_eq_const`. -/
private lemma transHornH₁₂_δ₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {g h : X ⟶ Y} {A : X.Subcomplex}
    (H₁₂ : HomotopyRelOver p g h A) :
    (X ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H₁₂.h =
      fst _ _ ≫ g := by
  ext n ⟨x, t₀⟩
  have hδ : stdSimplex.δ (1 : Fin 2) =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) :=
    stdSimplex.δ_one_eq_const
  have h_pair :
      (X ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1])).app n ⟨x, t₀⟩ =
        SSet.ι₀.app n x := by
    have h₁ : (X ◁ (stdSimplex.δ (1 : Fin 2))).app n ⟨x, t₀⟩ =
        ⟨x, (stdSimplex.δ (1 : Fin 2)).app n t₀⟩ := rfl
    have h₂ : (stdSimplex.δ (1 : Fin 2)).app n t₀ =
        (SSet.const (stdSimplex.obj₀Equiv.symm 0) : X ⟶ Δ[1]).app n x := by
      rw [hδ]
      rfl
    have h₃ : SSet.ι₀.app n x =
        ⟨x, (SSet.const (stdSimplex.obj₀Equiv.symm 0) : X ⟶ Δ[1]).app n x⟩ := rfl
    rw [h₁, h₂, ← h₃]
  calc H₁₂.h.app n ((X ◁ (stdSimplex.δ (1 : Fin 2))).app n ⟨x, t₀⟩)
      = H₁₂.h.app n (SSet.ι₀.app n x) := by rw [h_pair]
    _ = (SSet.ι₀ ≫ H₁₂.h).app n x := rfl
    _ = g.app n x := by rw [H₁₂.h₀]
    _ = (fst _ _ ≫ g).app n ⟨x, t₀⟩ := rfl

/-- Agreement of two inner faces at shared vertex `g`. -/
private lemma transHornFaces_agree {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (X ◁ (stdSimplex.δ (0 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H₀₁.h =
      (X ◁ (stdSimplex.δ (1 : Fin 2) : Δ[0] ⟶ Δ[1])) ≫ H₁₂.h := by
  rw [transHornH₀₁_δ₀ H₀₁, transHornH₁₂_δ₁ H₁₂]

/-- Glued map `X ⊗ Λ[2,1] ⟶ Y` from `H₀₁.h` on `ι₀₁` and `H₁₂.h` on `ι₁₂`. -/
private noncomputable def transHornMap {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    X ⊗ (SSet.horn 2 (1 : Fin 3) : SSet.{u}) ⟶ Y :=
  (horn₂₁TensorLeftIsPushout X).desc
    H₀₁.h H₁₂.h (transHornFaces_agree H₀₁ H₁₂)

/-- Face `ι₀₁` of glued transitivity horn map is `H₀₁.h`. -/
@[reassoc]
private lemma transHornMap_ι₀₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ = H₀₁.h :=
  (horn₂₁TensorLeftIsPushout X).inl_desc _ _ _

/-- Face `ι₁₂` of glued transitivity horn map is `H₁₂.h`. -/
@[reassoc]
private lemma transHornMap_ι₁₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ = H₁₂.h :=
  (horn₂₁TensorLeftIsPushout X).inr_desc _ _ _

/-- Stationary face restricts to `ι₀₁` as `fst ≫ A.ι ≫ f`. -/
private lemma transStationaryFace_ι₀₁ {X Y : SSet.{u}} (f : X ⟶ Y)
    (A : X.Subcomplex) :
    (A : SSet.{u}) ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3) ≫ symmStationaryFace f A
      = (A : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3) ≫
          (fst (A : SSet.{u}) (Δ[2] : SSet.{u}) ≫ A.ι ≫ f) := rfl
    _ = ((A : SSet.{u}) ◁ stdSimplex.δ (2 : Fin 3) ≫
          fst (A : SSet.{u}) (Δ[2] : SSet.{u})) ≫ A.ι ≫ f := by
        simp only [Category.assoc]
    _ = fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ f := by
        rw [whiskerLeft_fst]

/-- Horn side `ι₀₁` restricts to `fst ≫ A.ι ≫ f` via stationarity of `H₀₁`. -/
private lemma transHornMap_ι₀₁_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
        (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
          (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂
      = ((A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
            A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ := by
        simp only [Category.assoc]
    _ = ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ := by
        rw [whisker_exchange]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (X ◁ SSet.horn₂₁.ι₀₁ ≫ transHornMap H₀₁ H₁₂) := by
        simp only [Category.assoc]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ H₀₁.h := by
        rw [transHornMap_ι₀₁]
    _ = fst _ _ ≫ A.ι ≫ f := symmHornH_stationary H₀₁

/-- Horn side `ι₁₂` restricts to `fst ≫ A.ι ≫ f` via stationarity of `H₁₂` at `g`
then `stationary_ends H₀₁`. -/
private lemma transHornMap_ι₁₂_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
        (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      fst _ _ ≫ A.ι ≫ f := by
  calc (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
          (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂
      = ((A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
            A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ := by
        simp only [Category.assoc]
    _ = ((A.ι ▷ (Δ[1] : SSet.{u})) ≫ X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ := by
        rw [whisker_exchange]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ (X ◁ SSet.horn₂₁.ι₁₂ ≫ transHornMap H₀₁ H₁₂) := by
        simp only [Category.assoc]
    _ = A.ι ▷ (Δ[1] : SSet.{u}) ≫ H₁₂.h := by
        rw [transHornMap_ι₁₂]
    _ = fst _ _ ≫ A.ι ≫ g := symmHornH_stationary H₁₂
    _ = fst _ _ ≫ A.ι ≫ f := by
        have hg : A.ι ≫ g = A.ι ≫ f := (stationary_ends H₀₁).symm
        calc fst _ _ ≫ A.ι ≫ g
            = fst _ _ ≫ (A.ι ≫ g) := rfl
          _ = fst _ _ ≫ (A.ι ≫ f) := by rw [hg]
          _ = fst _ _ ≫ A.ι ≫ f := rfl

/-- Common-intersection on face `ι₀₁`: horn-side and stationary `A ⊗ Δ[2]`
restrictions agree. This is the `ι₀₁` face compatibility needed for
transitivity via inner horn `Λ[2,1]`. -/
private lemma transHornMap_ι₀₁_stationaryAgree {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
        (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      (A : SSet.{u}) ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A := by
  rw [transHornMap_ι₀₁_restrict H₀₁ H₁₂, transStationaryFace_ι₀₁]

/-- Common-intersection on face `ι₁₂`: horn-side and stationary `A ⊗ Δ[2]`
restrictions agree. This is the `ι₁₂` face compatibility needed for
transitivity; it uses the `δ₀` face `symmStationaryFace_ι₁₂`, not `ι₀₂`. -/
private lemma transHornMap_ι₁₂_stationaryAgree {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
        (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
        symmStationaryFace f A := by
  rw [transHornMap_ι₁₂_restrict H₀₁ H₁₂, symmStationaryFace_ι₁₂]

/-- Full common-intersection equality on `A ⊗ Λ[2,1]`:
the horn-side `(A.ι ▷ horn) ≫ transHornMap H₀₁ H₁₂` equals stationary side
`(A ◁ horn.ι) ≫ symmStationaryFace f A`, via `horn₂₁TensorLeftIsPushout A`
hom-ext and the two accepted face agreements together with
`SSet.horn.ι_ι` and `MonoidalCategory.whiskerLeft_comp`. -/
private lemma transHornMap_commonIntersection {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂ =
      (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι ≫ symmStationaryFace f A := by
  apply (horn₂₁TensorLeftIsPushout (A : SSet.{u})).hom_ext
  · calc (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
          (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂
        = (A : SSet.{u}) ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
            symmStationaryFace f A :=
          transHornMap_ι₀₁_stationaryAgree H₀₁ H₁₂
      _ = (A : SSet.{u}) ◁ (SSet.horn₂₁.ι₀₁ ≫
            (SSet.horn 2 (1 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [← SSet.horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide)]
      _ = ((A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [MonoidalCategory.whiskerLeft_comp]
      _ = (A : SSet.{u}) ◁ SSet.horn₂₁.ι₀₁ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι ≫
              symmStationaryFace f A := by
          rw [Category.assoc]
  · calc (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
          (A.ι ▷ (SSet.horn 2 (1 : Fin 3) : SSet.{u})) ≫ transHornMap H₀₁ H₁₂
        = (A : SSet.{u}) ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫
            symmStationaryFace f A :=
          transHornMap_ι₁₂_stationaryAgree H₀₁ H₁₂
      _ = (A : SSet.{u}) ◁ (SSet.horn₂₁.ι₁₂ ≫
            (SSet.horn 2 (1 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [← SSet.horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide)]
      _ = ((A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫
            symmStationaryFace f A := by
          rw [MonoidalCategory.whiskerLeft_comp]
      _ = (A : SSet.{u}) ◁ SSet.horn₂₁.ι₁₂ ≫
            (A : SSet.{u}) ◁ (SSet.horn 2 (1 : Fin 3)).ι ≫
              symmStationaryFace f A := by
          rw [Category.assoc]

/-- Union-product glued map
`(A.unionProd (SSet.horn 2 (1 : Fin 3))).toSSet ⟶ Y`, from
`transHornMap H₀₁ H₁₂` and `symmStationaryFace f A` via
`Subcomplex.unionProd.isPushout`. -/
private noncomputable def transUnionMap {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A.unionProd (SSet.horn 2 (1 : Fin 3)) : SSet.{u}) ⟶ Y :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (1 : Fin 3))).desc
    (transHornMap H₀₁ H₁₂) (symmStationaryFace f A)
    (transHornMap_commonIntersection H₀₁ H₁₂)

/-- Restriction to `ι₁` recovers `transHornMap H₀₁ H₁₂`. -/
private lemma transUnionMap_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂ =
      transHornMap H₀₁ H₁₂ :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (1 : Fin 3))).inl_desc _ _ _

/-- Restriction to `ι₂` recovers `symmStationaryFace f A`. -/
private lemma transUnionMap_ι₂ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂ =
      symmStationaryFace f A :=
  (Subcomplex.unionProd.isPushout A (SSet.horn 2 (1 : Fin 3))).inr_desc _ _ _

/-- Glued inner-horn map lies over the base map
`fst ≫ (f ≫ p)` after whiskering by `horn.ι`. -/
private lemma transHornMap_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    transHornMap H₀₁ H₁₂ ≫ p =
      (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f := by
  apply (horn₂₁TensorLeftIsPushout X).hom_ext
  · have hL : (X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ ≫ p =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ ≫ p
          = ((X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂) ≫ p := by
            rw [Category.assoc]
        _ = H₀₁.h ≫ p := by
            rw [transHornMap_ι₀₁]
        _ = fst _ _ ≫ (f ≫ p) := H₀₁.over
    have hR : (X ◁ SSet.horn₂₁.ι₀₁) ≫
          (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₁.ι₀₁) ≫
              (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f
          = ((X ◁ SSet.horn₂₁.ι₀₁) ≫
                X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [Category.assoc]
        _ = (X ◁ (SSet.horn₂₁.ι₀₁ ≫ (SSet.horn 2 (1 : Fin 3)).ι)) ≫
              symmBaseMap p f := by
            rw [← MonoidalCategory.whiskerLeft_comp]
        _ = (X ◁ stdSimplex.δ (2 : Fin 3)) ≫ symmBaseMap p f := by
            rw [SSet.horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide)]
        _ = (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              (fst _ _ ≫ (f ≫ p)) := by
            simp only [symmBaseMap]
        _ = ((X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              fst _ _) ≫ (f ≫ p) := by
            rw [← Category.assoc]
        _ = fst _ _ ≫ (f ≫ p) := by
            rw [whiskerLeft_fst]
    exact hL.trans hR.symm
  · have hL : (X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ ≫ p =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ ≫ p
          = ((X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂) ≫ p := by
            rw [Category.assoc]
        _ = H₁₂.h ≫ p := by
            rw [transHornMap_ι₁₂]
        _ = fst _ _ ≫ (g ≫ p) := H₁₂.over
        _ = fst _ _ ≫ (f ≫ p) := by
            rw [← H₀₁.map_eq]
    have hR : (X ◁ SSet.horn₂₁.ι₁₂) ≫
          (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f =
        fst (X : SSet.{u}) (Δ[1] : SSet.{u}) ≫ (f ≫ p) := by
      calc (X ◁ SSet.horn₂₁.ι₁₂) ≫
              (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f
          = ((X ◁ SSet.horn₂₁.ι₁₂) ≫
                X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [Category.assoc]
        _ = (X ◁ (SSet.horn₂₁.ι₁₂ ≫ (SSet.horn 2 (1 : Fin 3)).ι)) ≫
              symmBaseMap p f := by
            rw [← MonoidalCategory.whiskerLeft_comp]
        _ = (X ◁ stdSimplex.δ (0 : Fin 3)) ≫ symmBaseMap p f := by
            rw [SSet.horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide)]
        _ = (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              (fst _ _ ≫ (f ≫ p)) := by
            simp only [symmBaseMap]
        _ = ((X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
              fst _ _) ≫ (f ≫ p) := by
            rw [← Category.assoc]
        _ = fst _ _ ≫ (f ≫ p) := by
            rw [whiskerLeft_fst]
    exact hL.trans hR.symm

/-- The union-product gluing for transitivity lies over the base
`X ⊗ Δ[2] ⟶ S`. -/
private lemma transUnionMap_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    transUnionMap H₀₁ H₁₂ ≫ p =
      (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ symmBaseMap p f := by
  apply (Subcomplex.unionProd.isPushout A (SSet.horn 2 (1 : Fin 3))).hom_ext
  · calc Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
              transUnionMap H₀₁ H₁₂ ≫ p
          = (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
              transUnionMap H₀₁ H₁₂) ≫ p := by
            rw [Category.assoc]
        _ = transHornMap H₀₁ H₁₂ ≫ p := by
            rw [transUnionMap_ι₁]
        _ = (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ symmBaseMap p f := by
            rw [transHornMap_over H₀₁ H₁₂]
        _ = Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
              (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫
                symmBaseMap p f := by
            rw [Subcomplex.unionProd.ι₁_ι_assoc]
  · calc Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
              transUnionMap H₀₁ H₁₂ ≫ p
          = (Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
              transUnionMap H₀₁ H₁₂) ≫ p := by
            rw [Category.assoc]
        _ = symmStationaryFace f A ≫ p := by
            rw [transUnionMap_ι₂]
        _ = (A.ι ▷ (Δ[2] : SSet.{u})) ≫ symmBaseMap p f := by
            rw [symmStationaryFace_over]
        _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
              (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫
                symmBaseMap p f := by
            rw [Subcomplex.unionProd.ι₂_ι_assoc]

/-- The transitivity square packaging `transUnionMap_over H₀₁ H₁₂`:
top `transUnionMap H₀₁ H₁₂`, left `(A.unionProd Λ[2,1]).ι`, right `p`,
bottom `symmBaseMap p f`. Orientation matches `CommSq f g h i`
with `f ≫ h = g ≫ i` and the fibration lifting API. -/
private theorem transUnionCommSq {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex}
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    CommSq (transUnionMap H₀₁ H₁₂)
      (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι
      p (symmBaseMap p f) :=
  CommSq.mk (transUnionMap_over H₀₁ H₁₂)

/-- The union-product inclusion of `A` with inner horn `Λ[2,1]`
belongs to `SSet.anodyneExtensions`, via `anodyneExtensions_unionProd_ι`
and `anodyneExtensions.horn_ι (1 : Fin 3)`. -/
private lemma transUnionProd_horn_ι_mem_anodyneExtensions
    {X : SSet.{u}} (A : X.Subcomplex) :
    SSet.anodyneExtensions
      (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι := by
  have hHorn : SSet.anodyneExtensions (SSet.horn 2 (1 : Fin 3)).ι :=
    SSet.anodyneExtensions.horn_ι (1 : Fin 3)
  exact SSet.anodyneExtensions_unionProd_ι A (SSet.horn 2 (1 : Fin 3)) hHorn

/-! ## Transitivity filler via fibration lifting (r7j)

From `transUnionProd_horn_ι_mem_anodyneExtensions A` and the pinned
`HomotopicalAlgebra.fibration_iff` API we obtain
`HasLiftingProperty (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι p`
for `[Fibration p]`. The chosen filler `X ⊗ Δ[2] ⟶ Y` is
`(transUnionCommSq H₀₁ H₁₂).lift`, with the two exact lift equations. -/

private lemma transUnionProd_horn_ι_hasLiftingProperty
    {X : SSet.{u}} (A : X.Subcomplex)
    {Y S : SSet.{u}} {p : Y ⟶ S} [Fibration p] :
    HasLiftingProperty (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι p :=
  (transUnionProd_horn_ι_mem_anodyneExtensions A) p
    (by rwa [← HomotopicalAlgebra.fibration_iff])

private instance transUnionProd_horn_hasLiftingPropertyInst
    {X : SSet.{u}} {A : X.Subcomplex}
    {Y S : SSet.{u}} {p : Y ⟶ S} [Fibration p] :
    HasLiftingProperty (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι p :=
  transUnionProd_horn_ι_hasLiftingProperty A

/-- Chosen transitivity filler `X ⊗ Δ[2] ⟶ Y` obtained from `transUnionCommSq H₀₁ H₁₂`. -/
private noncomputable def transFiller {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    X ⊗ (Δ[2] : SSet.{u}) ⟶ Y :=
  (transUnionCommSq H₀₁ H₁₂).lift

/-- Filler postcomposes with `p` to `symmBaseMap p f`. -/
private lemma transFiller_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    transFiller H₀₁ H₁₂ ≫ p = symmBaseMap p f :=
  (transUnionCommSq H₀₁ H₁₂).fac_right

/-- Filler precomposed with union-product inclusion is `transUnionMap H₀₁ H₁₂`. -/
private lemma transFiller_union {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ transFiller H₀₁ H₁₂ =
      transUnionMap H₀₁ H₁₂ :=
  (transUnionCommSq H₀₁ H₁₂).fac_left

/-- Composite edge `X ⊗ Δ[1] ⟶ Y` obtained by restricting `transFiller H₀₁ H₁₂` along
the missing inner-horn face `δ₁ : Δ[1] ⟶ Δ[2]` (Goerss–Jardine, *Simplicial
Homotopy Theory*, Chapter I, §6). This is the composite homotopy edge from `f` to `h`. -/
private noncomputable def transHomotopy {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    X ⊗ (Δ[1] : SSet.{u}) ⟶ Y :=
  (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂

/-- `δ₂` is `horn₂₁.ι₀₁ ≫ horn.ι` from `horn.ι_ι`. -/
private lemma trans_delta₂_eq :
    (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.horn₂₁.ι₀₁ ≫ (SSet.horn 2 (1 : Fin 3)).ι := by
  rw [← SSet.horn.ι_ι (1 : Fin 3) (2 : Fin 3) (by decide)]

/-- Whisker factorisation for `δ₂`. -/
private lemma trans_whisker_δ₂ {X : SSet.{u}} :
    (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      (X ◁ SSet.horn₂₁.ι₀₁) ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) := by
  calc (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = X ◁ (SSet.horn₂₁.ι₀₁ ≫ (SSet.horn 2 (1 : Fin 3)).ι) := by
        rw [trans_delta₂_eq]
    _ = (X ◁ SSet.horn₂₁.ι₀₁) ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) := by
        rw [MonoidalCategory.whiskerLeft_comp]

/-- `X ◁ horn.ι` is `unionProd.ι₁ ≫ union.ι` by `ι₁_ι` (rfl). -/
private lemma trans_horn_whisker_eq_unionProd {X : SSet.{u}}
    (A : X.Subcomplex) :
    (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) =
      Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
        (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι := by
  rw [← Subcomplex.unionProd.ι₁_ι]

private lemma transHomotopy_ι₀ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    SSet.ι₀ ≫ transHomotopy H₀₁ H₁₂ = f := by
  calc SSet.ι₀ ≫ transHomotopy H₀₁ H₁₂
      = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂ := rfl
    _ = (SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ transFiller H₀₁ H₁₂ := by
        rw [Category.assoc]
    _ = (SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ transFiller H₀₁ H₁₂ := by
        rw [symm_iota₀_δ₁_eq_δ₂]
    _ = SSet.ι₀ ≫ (X ◁ (stdSimplex.δ (2 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂ := by
        rw [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁ ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι)) ≫
        transFiller H₀₁ H₁₂ := by
        rw [trans_whisker_δ₂]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ transFiller H₀₁ H₁₂ := by
        simp only [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι) ≫ transFiller H₀₁ H₁₂ := by
        rw [trans_horn_whisker_eq_unionProd A]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ transFiller H₀₁ H₁₂) := by
        simp only [Category.assoc]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          transUnionMap H₀₁ H₁₂ := by
        rw [transFiller_union H₀₁ H₁₂]
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂) := rfl
    _ = SSet.ι₀ ≫ (X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂ := by
        rw [transUnionMap_ι₁]
    _ = SSet.ι₀ ≫ ((X ◁ SSet.horn₂₁.ι₀₁) ≫ transHornMap H₀₁ H₁₂) := rfl
    _ = SSet.ι₀ ≫ H₀₁.h := by
        rw [transHornMap_ι₀₁]
    _ = f := by
        rw [H₀₁.h₀]

/-- `δ₀` is `horn₂₁.ι₁₂ ≫ horn.ι` from `horn.ι_ι`. -/
private lemma trans_delta₀_eq :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) =
      SSet.horn₂₁.ι₁₂ ≫ (SSet.horn 2 (1 : Fin 3)).ι := by
  rw [← SSet.horn.ι_ι (1 : Fin 3) (0 : Fin 3) (by decide)]

/-- Whisker factorisation for `δ₀`. -/
private lemma trans_whisker_δ₀ {X : SSet.{u}} :
    (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      (X ◁ SSet.horn₂₁.ι₁₂) ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) := by
  calc (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = X ◁ (SSet.horn₂₁.ι₁₂ ≫ (SSet.horn 2 (1 : Fin 3)).ι) := by
        rw [trans_delta₀_eq]
    _ = (X ◁ SSet.horn₂₁.ι₁₂) ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) := by
        rw [MonoidalCategory.whiskerLeft_comp]

/-- Vertex `1 : Δ[1]` maps to `2 : Δ[2]` under missing `δ₁`. -/
private lemma trans_δ₁_one :
    (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (2 : Fin 3) := rfl

/-- Vertex `1 : Δ[1]` maps to `2 : Δ[2]` under horn face `δ₀`. -/
private lemma trans_δ₀_one :
    (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u}) ⟶ Δ[2]).app _
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌) =
      stdSimplex.obj₀Equiv.symm (2 : Fin 3) := rfl

/-- Both `δ₁` and `δ₀` send vertex `1` to `2`. Hence
`ι₁ ≫ X ◁ δ₁ = ι₁ ≫ X ◁ δ₀` as maps `X ⟶ X ⊗ Δ[2]`. -/
private lemma trans_iota₁_δ₁_eq_δ₀ {X : SSet.{u}} :
    SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) =
      SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
  calc SSet.ι₁ (X := X) ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))
      = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
            (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) := by
        rw [SSet.const_comp]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (2 : Fin 3) : (Δ[2] : SSet.{u}) _⦋0⦌)) := by
        rw [trans_δ₁_one]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const
            ((stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]).app _
              (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))) := by
        rw [trans_δ₀_one]
    _ = CartesianMonoidalCategory.lift (𝟙 X)
          (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) ≫
            (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [SSet.const_comp]
    _ = SSet.ι₁ (X := X) ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) := by
        rw [← CartesianMonoidalCategory.lift_whiskerLeft]
        rfl

private lemma transHomotopy_ι₁ {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    SSet.ι₁ ≫ transHomotopy H₀₁ H₁₂ = h := by
  calc SSet.ι₁ ≫ transHomotopy H₀₁ H₁₂
      = SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂ := rfl
    _ = (SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ transFiller H₀₁ H₁₂ := by
        rw [Category.assoc]
    _ = (SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2]))) ≫ transFiller H₀₁ H₁₂ := by
        rw [trans_iota₁_δ₁_eq_δ₀]
    _ = SSet.ι₁ ≫ (X ◁ (stdSimplex.δ (0 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂ := by
        rw [Category.assoc]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂ ≫ (X ◁ (SSet.horn 2 (1 : Fin 3)).ι)) ≫
        transFiller H₀₁ H₁₂ := by
        rw [trans_whisker_δ₀]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        (X ◁ (SSet.horn 2 (1 : Fin 3)).ι) ≫ transFiller H₀₁ H₁₂ := by
        simp only [Category.assoc]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι) ≫ transFiller H₀₁ H₁₂ := by
        rw [trans_horn_whisker_eq_unionProd A]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ transFiller H₀₁ H₁₂) := by
        simp only [Category.assoc]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫
          transUnionMap H₀₁ H₁₂ := by
        rw [transFiller_union H₀₁ H₁₂]
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫
        (Subcomplex.unionProd.ι₁ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂) := rfl
    _ = SSet.ι₁ ≫ (X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂ := by
        rw [transUnionMap_ι₁]
    _ = SSet.ι₁ ≫ ((X ◁ SSet.horn₂₁.ι₁₂) ≫ transHornMap H₀₁ H₁₂) := rfl
    _ = SSet.ι₁ ≫ H₁₂.h := by
        rw [transHornMap_ι₁₂]
    _ = h := by
        rw [H₁₂.h₁]

/-! ## Composite-edge stationarity: `transHomotopy H₀₁ H₁₂ | A = f`

`transFiller H₀₁ H₁₂ : X ⊗ Δ[2] ⟶ Y` restricts along
`A.ι ▷ Δ[2] = ι₂ ≫ ι` to `symmStationaryFace f A` via `transFiller_union`
and `transUnionMap_ι₂`. Hence it is stationary on `A` at `f`. The missing
edge `δ₁ : Δ[1] ⟶ Δ[2]` whiskered left gives `transHomotopy H₀₁ H₁₂`, whose
pointwise value on `A` is therefore `f` directly. -/

/-- Filler restricted to `A ⊗ Δ[2]` equals the stationary face at `f`. -/
private lemma transFiller_restrict {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    (A.ι ▷ (Δ[2] : SSet.{u})) ≫ transFiller H₀₁ H₁₂ = symmStationaryFace f A := by
  calc (A.ι ▷ (Δ[2] : SSet.{u})) ≫ transFiller H₀₁ H₁₂
      = (Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
          (A.unionProd (SSet.horn 2 (1 : Fin 3))).ι) ≫ transFiller H₀₁ H₁₂ := by
        rw [← Subcomplex.unionProd.ι₂_ι]
    _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫
          ((A.unionProd (SSet.horn 2 (1 : Fin 3))).ι ≫ transFiller H₀₁ H₁₂) := by
        rw [Category.assoc]
    _ = Subcomplex.unionProd.ι₂ A (SSet.horn 2 (1 : Fin 3)) ≫ transUnionMap H₀₁ H₁₂ := by
        rw [transFiller_union H₀₁ H₁₂]
    _ = symmStationaryFace f A := by
        rw [transUnionMap_ι₂ H₀₁ H₁₂]

/-- `transHomotopy H₀₁ H₁₂` is stationary on `A` at `f`:
`(transHomotopy H₀₁ H₁₂).app n ⟨x,t⟩ = f.app n x` for `x ∈ A`. -/
private lemma transHomotopy_stationary {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A)
    {n : SimplexCategoryᵒᵖ} {x : X.obj n} (hx : x ∈ A.obj n)
    (t : (Δ[1] : SSet.{u}).obj n) :
    (transHomotopy H₀₁ H₁₂).app n ⟨x, t⟩ = f.app n x := by
  have h_whisker_δ₁ : (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])).app n ⟨x, t⟩ =
      ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
  have h_filler : (transFiller H₀₁ H₁₂).app n
      ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ = f.app n x := by
    have hA : (A.ι ▷ (Δ[2] : SSet.{u})).app n
        ⟨⟨x, hx⟩, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ =
        ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
    calc (transFiller H₀₁ H₁₂).app n
          ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩
        = (transFiller H₀₁ H₁₂).app n
            ((A.ι ▷ (Δ[2] : SSet.{u})).app n
              ⟨⟨x, hx⟩, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩) := by
          rw [hA]
      _ = ((A.ι ▷ (Δ[2] : SSet.{u})) ≫ transFiller H₀₁ H₁₂).app n
            ⟨⟨x, hx⟩, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := rfl
      _ = (symmStationaryFace f A).app n
            ⟨⟨x, hx⟩, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := by
          rw [transFiller_restrict H₀₁ H₁₂]
      _ = f.app n x := rfl
  calc (transHomotopy H₀₁ H₁₂).app n ⟨x, t⟩
      = ((X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ transFiller H₀₁ H₁₂).app n
          ⟨x, t⟩ := rfl
    _ = (transFiller H₀₁ H₁₂).app n
          ((X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])).app n ⟨x, t⟩) := rfl
    _ = (transFiller H₀₁ H₁₂).app n
          ⟨x, (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]).app n t⟩ := by
        rw [h_whisker_δ₁]
    _ = f.app n x := h_filler

private lemma transHomotopy_over {X Y S : SSet.{u}} {p : Y ⟶ S}
    {f g h : X ⟶ Y} {A : X.Subcomplex} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    transHomotopy H₀₁ H₁₂ ≫ p = fst _ _ ≫ (f ≫ p) := by
  calc transHomotopy H₀₁ H₁₂ ≫ p
      = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2]) ≫ transFiller H₀₁ H₁₂) ≫ p := rfl
    _ = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ (transFiller H₀₁ H₁₂ ≫ p) := by
        rw [Category.assoc]
    _ = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ symmBaseMap p f := by
        rw [transFiller_over H₀₁ H₁₂]
    _ = (X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫
          (fst X _ ≫ (f ≫ p)) := by
        simp only [symmBaseMap]
    _ = ((X ◁ (stdSimplex.δ (1 : Fin 3) : Δ[1] ⟶ Δ[2])) ≫ fst X _) ≫ (f ≫ p) := by
        rw [Category.assoc]
    _ = fst _ _ ≫ (f ≫ p) := by
        rw [whiskerLeft_fst]

/-- Transitivity for relative homotopies over a base.

Given `H₀₁ : HomotopyRelOver p f g A` and `H₁₂ : HomotopyRelOver p g h A`,
the composite `HomotopyRelOver.trans H₀₁ H₁₂` has start `f` and end `h`
(`ι₀` is `f`, `ι₁` is `h`), is stationary at `f` on `A`, and satisfies the
over-base equation `fst _ _ ≫ (f ≫ p)` (i.e. its underlying homotopy
`transHomotopy H₀₁ H₁₂` satisfies
`(transHomotopy H₀₁ H₁₂) ≫ p = fst _ _ ≫ (f ≫ p)`).

The `[Fibration p]` hypothesis is required for this construction via inner-horn
`Λ[2,1]` lifting. This declaration asserts no associativity, unit, or coherence
law for repeated composition. -/
noncomputable def trans {h : X ⟶ Y} [Fibration p]
    (H₀₁ : HomotopyRelOver p f g A) (H₁₂ : HomotopyRelOver p g h A) :
    HomotopyRelOver p f h A where
  toHomotopyRel :=
    { h := transHomotopy H₀₁ H₁₂
      h₀ := transHomotopy_ι₀ H₀₁ H₁₂
      h₁ := transHomotopy_ι₁ H₀₁ H₁₂
      stationary := fun _ hx t => transHomotopy_stationary H₀₁ H₁₂ hx t }
  over := transHomotopy_over H₀₁ H₁₂

end HomotopyRelOver

end SSet

end
