/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialSet/Pointed/Circle.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import MathlibExt.AlgebraicTopology.SpectraSource.AlgebraicTopology.SimplicialSet.Pointed.Basic

/-!
# The simplicial circle as `Δ[1]/∂Δ[1]`

Mathlib defines the simplicial circle `SSet.S1` as the coequalizer of the two vertex inclusions
`Δ[0] ⟶ Δ[1]`. This file names its quotient map `MathlibExt.SpectraSource.SSet.S1.quotient`, its
  descent
`MathlibExt.SpectraSource.SSet.S1.desc` and its basepoint
  `MathlibExt.SpectraSource.SSet.S1.basepoint`, shows that both vertices
of the interval are sent to the basepoint, and proves
  `MathlibExt.SpectraSource.SSet.S1.isPushout`: the circle is
the pushout of the boundary inclusion `∂Δ[1] ⟶ Δ[1]` along the collapse `∂Δ[1] ⟶ Δ[0]`, i.e. the
interval with its boundary collapsed to the basepoint.

Like Mathlib's `SSet.S1`, everything in this file lives in universe `0`.

The final section equips the interval and circle with their distinguished vertices.  It gives
the quotient as a based map and packages its universal property directly in `PointedSSet`.
-/

public section

open CategoryTheory Limits
open scoped Simplicial

namespace MathlibExt.SpectraSource

namespace SSet.S1

/-- The map which collapses the boundary of the simplicial interval to `Δ[0]`. -/
def boundaryCollapse : (SSet.boundary 1 : SSet.{0}) ⟶ Δ[0] :=
  SSet.stdSimplex.isTerminalObj₀.from _

/-- The quotient map from the simplicial interval to the simplicial circle. -/
noncomputable def quotient : Δ[1] ⟶ SSet.S1 :=
  coequalizer.π (SSet.stdSimplex.δ 0) (SSet.stdSimplex.δ 1)

noncomputable instance : Epi quotient :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- A map from the simplicial interval which identifies its two vertices descends to the
simplicial circle. -/
noncomputable def desc {X : SSet} (f : Δ[1] ⟶ X)
    (h : SSet.stdSimplex.δ 0 ≫ f = SSet.stdSimplex.δ 1 ≫ f) : SSet.S1 ⟶ X :=
  coequalizer.desc f h

/-- The descent of `f` to the circle restricts back to `f` along the quotient map. -/
@[reassoc (attr := simp)]
lemma quotient_desc {X : SSet} (f : Δ[1] ⟶ X)
    (h : SSet.stdSimplex.δ 0 ≫ f = SSet.stdSimplex.δ 1 ≫ f) : quotient ≫ desc f h = f :=
  coequalizer.π_desc f h

/-- The distinguished vertex of the simplicial circle. -/
noncomputable def basepoint : Δ[0] ⟶ SSet.S1 :=
  SSet.stdSimplex.δ 0 ≫ quotient

/-- Both vertices of the simplicial interval map to the basepoint of the circle. -/
@[reassoc (attr := simp)]
lemma δ_quotient (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ quotient = basepoint := by
  fin_cases i
  · rfl
  · exact (coequalizer.condition (SSet.stdSimplex.δ 0) (SSet.stdSimplex.δ 1)).symm

@[reassoc]
private lemma boundary_ι_boundaryCollapse (i : Fin 2) :
    SSet.boundary.ι i ≫ boundaryCollapse = 𝟙 Δ[0] :=
  SSet.stdSimplex.ext₀

/-- The quotient map agrees with the basepoint after collapsing the boundary. -/
@[reassoc (attr := simp)]
lemma boundary_ι_quotient :
    (SSet.boundary 1).ι ≫ quotient = boundaryCollapse ≫ basepoint := by
  apply SSet.boundary.hom_ext
  intro i
  simp [boundary_ι_boundaryCollapse_assoc]

/-- Maps from the simplicial circle are determined by their composites with the quotient map. -/
@[ext]
lemma hom_ext {X : SSet} {f g : SSet.S1 ⟶ X} (h : quotient ≫ f = quotient ≫ g) : f = g :=
  coequalizer.hom_ext h

private lemma δ_inl (s : PushoutCocone (SSet.boundary 1).ι boundaryCollapse) (i : Fin 2) :
    SSet.stdSimplex.δ i ≫ s.inl = s.inr := by
  simpa [boundary_ι_boundaryCollapse_assoc] using SSet.boundary.ι i ≫= s.condition

/-- The simplicial circle is `Δ[1]/∂Δ[1]`: the pushout of the boundary inclusion along the
collapse of the boundary to the basepoint. -/
lemma isPushout : IsPushout (SSet.boundary 1).ι boundaryCollapse quotient basepoint where
  w := boundary_ι_quotient
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s ↦ desc s.inl ((δ_inl s 0).trans (δ_inl s 1).symm))
    (fun _ ↦ quotient_desc _ _)
    (fun s ↦ by rw [basepoint, Category.assoc, quotient_desc, δ_inl])
    (fun _ _ hm _ ↦ hom_ext (by simpa using hm))⟩

end SSet.S1

namespace PointedSSet

/-- The simplicial interval pointed at vertex `1`, the image of `δ 0`. Its underlying
simplicial set is definitionally `Δ[1]`. -/
noncomputable abbrev interval : PointedSSet.{0} :=
  Under.mk (SSet.stdSimplex.δ 0)

/-- The simplicial circle pointed at the image of either endpoint of the interval. Its underlying
simplicial set is definitionally Mathlib's `SSet.S1`. -/
noncomputable abbrev circle : PointedSSet.{0} :=
  Under.mk SSet.S1.basepoint

/-- The quotient from the pointed interval to the pointed simplicial circle. -/
noncomputable def circleQuotient : interval ⟶ circle :=
  Under.homMk SSet.S1.quotient (SSet.S1.δ_quotient 0)

@[simp]
lemma circleQuotient_right : circleQuotient.right = SSet.S1.quotient := (rfl)

/-- A based map from the interval which also sends vertex `0`, the image of `δ 1`, to the
basepoint descends to a based map from the simplicial circle. -/
noncomputable def circleDesc {X : PointedSSet.{0}} (f : interval ⟶ X)
    (h : SSet.stdSimplex.δ 1 ≫ f.right = X.hom) : circle ⟶ X :=
  Under.homMk (SSet.S1.desc f.right ((Under.w f).trans h.symm)) (by
    rw [show circle.hom = SSet.S1.basepoint by exact Under.mk_hom _,
      SSet.S1.basepoint, Category.assoc, SSet.S1.quotient_desc]
    exact Under.w f)

/-- The underlying map of the based descent is the unpointed circle descent. -/
@[simp]
lemma circleDesc_right {X : PointedSSet.{0}} (f : interval ⟶ X)
    (h : SSet.stdSimplex.δ 1 ≫ f.right = X.hom) :
    (circleDesc f h).right = SSet.S1.desc f.right ((Under.w f).trans h.symm) := (rfl)

/-- Descending a based interval map and then pulling back along the circle quotient recovers the
original map. -/
@[simp]
lemma circleQuotient_circleDesc {X : PointedSSet.{0}} (f : interval ⟶ X)
    (h : SSet.stdSimplex.δ 1 ≫ f.right = X.hom) :
    circleQuotient ≫ circleDesc f h = f := by
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, circleQuotient_right, circleDesc_right,
    SSet.S1.quotient_desc]

/-- Based maps out of the simplicial circle are determined by their pullback to the pointed
interval. -/
@[ext]
lemma circleHom_ext {X : PointedSSet.{0}} {f g : circle ⟶ X}
    (h : circleQuotient ≫ f = circleQuotient ≫ g) : f = g := by
  apply Under.UnderMorphism.ext
  apply SSet.S1.hom_ext
  simpa only [Under.comp_right, circleQuotient_right] using congrArg Under.Hom.right h

/-- Based maps from the simplicial circle are equivalent to based maps from the interval which
send vertex `0`, the image of `δ 1`, to the basepoint. -/
noncomputable def circleHomEquiv (X : PointedSSet.{0}) :
    (circle ⟶ X) ≃
      {f : interval ⟶ X // SSet.stdSimplex.δ 1 ≫ f.right = X.hom} where
  toFun f := ⟨circleQuotient ≫ f, by
    simpa only [Under.comp_right, circleQuotient_right, ← Category.assoc,
      SSet.S1.δ_quotient, Under.mk_hom] using Under.w f⟩
  invFun f := circleDesc f.1 f.2
  left_inv f := circleHom_ext (circleQuotient_circleDesc _ _)
  right_inv f := Subtype.ext (circleQuotient_circleDesc _ _)

@[simp]
lemma circleHomEquiv_apply (X : PointedSSet.{0}) (f : circle ⟶ X) :
    (circleHomEquiv X f).1 = circleQuotient ≫ f := (rfl)

@[simp]
lemma circleHomEquiv_symm_apply (X : PointedSSet.{0})
    (f : {f : interval ⟶ X // SSet.stdSimplex.δ 1 ≫ f.right = X.hom}) :
    (circleHomEquiv X).symm f = circleDesc f.1 f.2 := (rfl)

end PointedSSet

end MathlibExt.SpectraSource
