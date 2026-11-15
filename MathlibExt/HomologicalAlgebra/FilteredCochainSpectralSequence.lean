/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The page-index core is adapted from Mathlib at
56a005855ea17e0b0958f73ec801ae140b0a1679,
Mathlib/Algebra/Homology/SpectralObject/HasSpectralSequence.lean.
Copyright (c) 2026 Joël Riou. All rights reserved.
Licensed under Apache 2.0. Authors: Joël Riou.
Modification notice: the first page is E1 and the filtration is decreasing
in the first cohomological index. The spectral object and every differential
are the native mapping-cone/homology construction of the actual complex.
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.SpectralObject
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.SpectralObject.FirstPage
public import Mathlib.CategoryTheory.Filtration.Basic

/-!
# The actual spectral sequence of a filtered cochain complex

This file supplies no chosen page or differential. It applies Mathlib's
mapping-cone spectral object and cohomology to the actual filtration
diagram, then uses the actual spectral-sequence constructor. On E1,
the objects are cohomology of the consecutive-step cones; for a filtration
by subcomplexes these are the graded quotients.

Generic filtered-complex and spectral-object convergence/graded abutment
results are existing Axiom toolbox. A geometric Rapoport--Zink consumer
must still identify its actual nearby filtration, strata and abutment.
-/

@[expose] public noncomputable section

namespace MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.CategoryTheory.Abelian.SpectralObject

universe u v

/-- The actual decreasing filtration index as a preordered category. -/
def dualToOpposite : OrderDual ℤ ⥤ ℤᵒᵖ where
  obj i := op i
  map f := (homOfLE (leOfHom f)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The exact E1 cohomological indexing recipe. -/
def coreE1 : SpectralSequenceDataCore (OrderDual ℤ)
    (fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) 1 where
  deg pq := pq.1 + pq.2
  i₀ r pq _ := OrderDual.toDual (pq.1 + r)
  i₁ pq := OrderDual.toDual (pq.1 + 1)
  i₂ pq := OrderDual.toDual pq.1
  i₃ r pq _ := OrderDual.toDual (pq.1 - r + 1)
  le₀₁ r pq hr := by change pq.1 + 1 ≤ pq.1 + r; omega
  le₁₂ pq := by change pq.1 ≤ pq.1 + 1; omega
  le₂₃ r pq hr := by change pq.1 - r + 1 ≤ pq.1; omega
  hc := by rintro r pq _ rfl _; dsimp; omega
  hc₀₂ := by rintro r pq _ rfl _; rfl
  hc₁₃ := by
    rintro r ⟨p, q⟩ _ rfl _
    change p + 1 = p + r - r + 1
    omega
  antitone_i₀ r r' pq hr hrr' := by
    change pq.1 + r ≤ pq.1 + r'; omega
  monotone_i₃ r r' pq hr hrr' := by
    change pq.1 - r' + 1 ≤ pq.1 - r + 1; omega
  i₀_prev := by
    rintro r r' ⟨p, q⟩ _ rfl hrr' _
    change p + r' = p + r + 1
    omega
  i₃_next := by
    rintro r r' ⟨p, q⟩ _ rfl hrr' _
    change p + r - r' + 1 = p
    omega

instance coreE1_firstPage : coreE1.HasFirstPageComputation where
  hi₀₁ pq := rfl
  hi₂₃ pq := by change pq.1 = pq.1 - 1 + 1; omega

variable {C : Type u} [Category.{v} C] [Abelian C]
  (F : FilteredObject (CochainComplex C ℤ) ℤᵒᵖ)

/-- The actual cone spectral object of the filtration diagram. -/
def coneSpectralObject :=
  (HomotopyCategory.spectralObjectMappingCone C).precomp
    (dualToOpposite ⋙ F.filtration.diagram)

/-- The actual cohomological spectral object. -/
def cohomologicalSpectralObject :=
  (coneSpectralObject F).mapHomologicalFunctor
    (HomotopyCategory.homologyFunctor C (.up ℤ) 0)

instance hasSpectralSequence :
    (cohomologicalSpectralObject F).HasSpectralSequence coreE1 where
  isZero_H_obj_mk₁_i₀_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq _ rfl
  isZero_H_obj_mk₁_i₃_le r r' pq hpq n hn hrr' hr := by
    exfalso
    exact hpq (pq - (r, 1 - r)) (by simp)

/-- The actual E1 cohomological spectral sequence of this complex. -/
def spectralSequence : CohomologicalSpectralSequence C 1 :=
  (cohomologicalSpectralObject F).spectralSequence coreE1

/-- The E1 object is the actual cohomology of its consecutive-step cone. -/
def firstPageIso (p q : ℤ) :
    ((spectralSequence F).page 1).X (p, q) ≅
      ((cohomologicalSpectralObject F).H (p + q)).obj
        (ComposableArrows.mk₁ (homOfLE
          (show (OrderDual.toDual (p + 1)) ≤ OrderDual.toDual p by
            change p ≤ p + 1
            omega))) :=
  (cohomologicalSpectralObject F).spectralSequenceFirstPageXIso coreE1
    (p, q) _ _ rfl rfl (p + q) rfl

end MathlibExt.HomologicalAlgebra.FilteredCochainSpectralSequence
