/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SchemeModulesIsFrameOn
public import MathlibExt.AlgebraicGeometry.Modules.InvertibleTensorSections

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/-- Consumer with the original binders. -/
example {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U V : X.Opens}
    {s : Γ(M, U)}
    (h : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (W : X.Opens)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj M ≅
      SheafOfModules.unit (W : AlgebraicGeometry.Scheme.{u}).ringCatSheaf) :=
  AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit
    h W hWU hWV

/-- Boundary example: the frame hypothesis cannot be dropped. The zero
section is not a frame on `U` when the ring of sections over `U` is
nontrivial, since multiplication by the restricted zero section is not
bijective. -/
example {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (hU : (1 : Γ(X, U)) ≠ 0) :
    ¬ AlgebraicGeometry.Scheme.Modules.IsFrameOn (M := M) (U := U) 0 U := by
  intro h
  have hb := h.bijective (W := U) le_rfl le_rfl
  have h1 : (1 : Γ(X, U)) = 0 := by
    apply hb.1
    simp
  exact hU h1

open MonoidalCategory in
/-- Consumer of both frame developments: the tensor product of two frames on `V` trivializes
the pullback of `L ⊗ M` to any open `W ≤ U ⊓ V`. -/
example {X : AlgebraicGeometry.Scheme.{u}} {L M : X.Modules} {U V : X.Opens}
    {s : Γ(L, U)} {t : Γ(M, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V)
    (ht : AlgebraicGeometry.Scheme.Modules.IsFrameOn t V) (W : X.Opens)
    (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj (L ⊗ M) ≅
      SheafOfModules.unit (W : AlgebraicGeometry.Scheme.{u}).ringCatSheaf) :=
  (hs.tensorSections ht).nonempty_pullback_iso_unit W hWU hWV
