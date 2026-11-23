/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.MinimalFibration.Equivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup

/-!
# Pointed simplices in a minimal Kan complex

This file connects the native pointed-simplex homotopy relation with the
fiberwise relative homotopies used by minimal fibrations.  A homotopy of
pointed simplices is stationary on the whole simplicial boundary, hence over
the terminal simplicial set it is a fiberwise homotopy relative to that
boundary.  Minimality then makes the quotient map from pointed simplices to
the native homotopy group injective; its existing surjectivity gives an
equivalence.

The construction retains the literal relative homotopy and its stationary
boundary equation.  It makes no homology, Hurewicz, or bijectivity claim about
any map other than the defining quotient from pointed simplices.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Simplicial
open scoped Simplicial

universe u

namespace SSet

namespace PtSimplex

namespace Homotopy

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}
variable {p q : X.PtSimplex n x}

/-- A pointed-simplex homotopy is a homotopy relative to the entire boundary.

The endpoint maps are unchanged.  On a boundary simplex, the relative
homotopy equation and the boundary equation of `p` identify every time slice
with the common constant boundary map. -/
def toHomotopyRel (h : p.Homotopy q) :
    SSet.HomotopyRel (RelativeMorphism.map p) (RelativeMorphism.map q)
      (SSet.boundary n) where
  h := h.h
  h₀ := h.h₀
  h₁ := h.h₁
  stationary := by
    intro m z hz t
    have hrel := congrArg
      (fun k => k.app m ⟨⟨z, hz⟩, t⟩) h.rel
    have hp := congrArg
      (fun k => k.app m ⟨z, hz⟩) p.comm
    change h.h.app m ⟨z, t⟩ = _ at hrel
    change (RelativeMorphism.map p).app m z = _ at hp
    exact hrel.trans hp.symm

@[simp]
theorem toHomotopyRel_h (h : p.Homotopy q) :
    h.toHomotopyRel.h = h.h :=
  rfl

theorem toHomotopyRel_h₀ (h : p.Homotopy q) :
    SSet.ι₀ ≫ h.toHomotopyRel.h = RelativeMorphism.map p :=
  h.h₀

theorem toHomotopyRel_h₁ (h : p.Homotopy q) :
    SSet.ι₁ ≫ h.toHomotopyRel.h = RelativeMorphism.map q :=
  h.h₁

/-- A pointed-simplex homotopy, regarded as a fiberwise homotopy over the
terminal simplicial set. -/
def toFiberwiseHomotopyOverTerminal (h : p.Homotopy q) :
    SSet.MinimalFibration.FiberwiseHomotopy (terminal.from X)
      (SSet.yonedaEquiv (RelativeMorphism.map p))
      (SSet.yonedaEquiv (RelativeMorphism.map q)) where
  homotopyRel := by
    simpa using h.toHomotopyRel
  over := terminal.hom_ext _ _

end Homotopy

end PtSimplex

namespace MinimalFibration

namespace IsMinimal

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

/-- In a minimal Kan complex over the point, homotopic pointed simplices are
literally equal. -/
theorem ptSimplex_eq_of_homotopy
    (hmin : IsMinimal (terminal.from X))
    {p q : X.PtSimplex n x} (h : p.Homotopy q) : p = q := by
  apply RelativeMorphism.ext
  apply SSet.yonedaEquiv.injective
  apply hmin
      (SSet.yonedaEquiv (RelativeMorphism.map p))
      (SSet.yonedaEquiv (RelativeMorphism.map q))
  · apply SSet.yonedaEquiv.symm.injective
    exact terminal.hom_ext _ _
  · simpa only [Equiv.symm_apply_apply] using p.comm.trans q.comm.symm
  · exact ⟨SSet.PtSimplex.Homotopy.toFiberwiseHomotopyOverTerminal h⟩

variable [KanComplex X]

/-- In a minimal Kan complex over the point, pointed simplices related by a
native `RelStruct₀` filler are literally equal. -/
theorem ptSimplex_eq_of_relStruct₀
    (hmin : IsMinimal (terminal.from X))
    {p q : X.PtSimplex n x} (h : p.RelStruct₀ q) : p = q :=
  hmin.ptSimplex_eq_of_homotopy h.homotopy

/-- The native quotient map from pointed simplices to `πₙ` is injective in
a minimal Kan complex over the point. -/
theorem piMk_injective (hmin : IsMinimal (terminal.from X)) :
    Function.Injective
      (SSet.KanComplex.π.mk : X.PtSimplex n x → SSet.KanComplex.π n X x) := by
  intro p q hpq
  obtain ⟨h⟩ := SSet.KanComplex.π.mk_eq_mk_iff.mp hpq
  exact hmin.ptSimplex_eq_of_relStruct₀ h

/-- Pointed `n`-simplices are equivalent to the native `πₙ` in a minimal
Kan complex over the point.  The forward map is exactly `π.mk`. -/
noncomputable def ptSimplexEquivPi
    (hmin : IsMinimal (terminal.from X)) :
    X.PtSimplex n x ≃ SSet.KanComplex.π n X x :=
  Equiv.ofBijective SSet.KanComplex.π.mk
    ⟨hmin.piMk_injective, SSet.KanComplex.π.mk_surjective⟩

@[simp]
theorem ptSimplexEquivPi_apply
    (hmin : IsMinimal (terminal.from X)) (p : X.PtSimplex n x) :
    hmin.ptSimplexEquivPi p = SSet.KanComplex.π.mk p :=
  rfl

@[simp]
theorem ptSimplexEquivPi_symm_mk
    (hmin : IsMinimal (terminal.from X)) (p : X.PtSimplex n x) :
    hmin.ptSimplexEquivPi.symm (SSet.KanComplex.π.mk p) = p :=
  hmin.ptSimplexEquivPi.left_inv p

end IsMinimal

end MinimalFibration

end SSet
