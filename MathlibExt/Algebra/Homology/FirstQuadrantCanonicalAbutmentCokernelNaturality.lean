/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import
  MathlibExt.Algebra.Homology.FirstQuadrantStablePageCanonicalNaturality
public import MathlibExt.Algebra.Homology.SpectralObjectCokernelENaturality
public import
  MathlibExt.CategoryTheory.Abelian.DiagramLemmas.ImageQuotientNaturality

/-!
# Naturality of the canonical-abutment cokernel presentation

A bicomplex map induces commuting vertical maps on the two incoming relative
homology terms and their common target.  The resulting canonical map between
the biproduct cokernels agrees, through the canonical cokernel presentation,
with the fixed-`E` map on the canonical abutment term.

This file proves no image-quotient or final associated-graded naturality.
-/

@[expose] public section

open CategoryTheory Limits ComposableArrows

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Map between the biproduct cokernel presentations of the canonical
abutment induced by a bicomplex morphism. -/
noncomputable def horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex
    (f : K ⟶ L) (p q : ℕ) :
    cokernel (biprod.desc
      (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
      (horizontalCanonicalAbutmentBoundaryMap K p q)) ⟶
      cokernel (biprod.desc
        (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
        (horizontalCanonicalAbutmentBoundaryMap L p q)) := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let α := (φ.hom n₁).app
    (mk₁ (horizontalCanonicalAbutmentLowerMap p))
  let χ := (φ.hom n₀).app
    (mk₁ (horizontalCanonicalAbutmentUpperMap p q))
  let β := (φ.hom n₁).app
    (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p))
  have ha : horizontalCanonicalAbutmentPreviousHomologyMap K p q ≫ β =
      α ≫ horizontalCanonicalAbutmentPreviousHomologyMap L p q := by
    simp [φ, n₁, α, β,
      horizontalCanonicalAbutmentPreviousHomologyMap]
  have hx : horizontalCanonicalAbutmentBoundaryMap K p q ≫ β =
      χ ≫ horizontalCanonicalAbutmentBoundaryMap L p q := by
    simp [φ, n₀, n₁, χ, β,
      horizontalCanonicalAbutmentBoundaryMap]
  exact CategoryTheory.biprodQuotientMap
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentBoundaryMap K p q)
    (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
    (horizontalCanonicalAbutmentBoundaryMap L p q)
    α χ β ha hx

/-- The canonical biproduct-cokernel map computes on the cokernel
projection. -/
@[reassoc]
theorem horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex_π
    (f : K ⟶ L) (p q : ℕ) :
    cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q =
      ((horizontalCompleteFiltrationSpectralObjectMap f).hom
          (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
        cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
          (horizontalCanonicalAbutmentBoundaryMap L p q)) := by
  simp [horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex,
    CategoryTheory.cokernel_π_biprodQuotientMap]

/-- The canonical cokernel Iso sends the abstract cokernel projection to the
canonical epimorphism into the fixed `E` object. -/
@[reassoc]
theorem horizontalCanonicalAbutmentCokernelIso_hom_fac
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ))
    (p q : ℕ) :
    cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        (horizontalCanonicalAbutmentCokernelIso K p q).hom =
      (horizontalCanonicalAbutmentCokernelSequence K p q).g := by
  let S := horizontalCanonicalAbutmentCokernelSequence K p q
  have hS : S.Exact :=
    horizontalCanonicalAbutmentCokernelSequence_exact K p q
  have hg : Epi S.g := by
    dsimp [S, horizontalCanonicalAbutmentCokernelSequence]
    infer_instance
  let _ := hg
  have hleg := IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel S.f) hS.gIsCokernel WalkingParallelPair.one
  change cokernel.π (biprod.desc
        (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
        (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
      (horizontalCanonicalAbutmentCokernelIso K p q).hom = S.g at hleg
  exact hleg

/-- The canonical cokernel presentation is natural under bicomplex
morphisms. -/
theorem horizontalCanonicalAbutmentCokernelIso_naturality
    (f : K ⟶ L) (p q : ℕ) :
    horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q ≫
        (horizontalCanonicalAbutmentCokernelIso L p q).hom =
      (horizontalCanonicalAbutmentCokernelIso K p q).hom ≫
        horizontalCanonicalAbutmentMapOfBicomplex f p q := by
  let φ := horizontalCompleteFiltrationSpectralObjectMap f
  let n₀ : ℤ := -((p + q + 1 : ℕ) : ℤ)
  let n₁ : ℤ := -((p + q : ℕ) : ℤ)
  let n₂ : ℤ := -((p + q : ℕ) : ℤ) + 1
  have hE :
      (horizontalCanonicalAbutmentCokernelSequence K p q).g ≫
          horizontalCanonicalAbutmentMapOfBicomplex f p q =
        (φ.hom n₁).app
            (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
          (horizontalCanonicalAbutmentCokernelSequence L p q).g := by
    simpa [φ, n₀, n₁, n₂,
      horizontalCanonicalAbutmentCokernelSequence,
      horizontalCanonicalAbutmentMapOfBicomplex] using
      CategoryTheory.Abelian.SpectralObject.Hom.cokernelSequenceE_g_EMap φ
        (horizontalCanonicalAbutmentLowerMap p)
        (horizontalCanonicalAbutmentMiddleMap p)
        (horizontalCanonicalAbutmentUpperMap p q)
        (horizontalCanonicalAbutmentLowerCompositeMap p)
        (horizontalCanonicalAbutmentLower_comp_middle p)
        n₀ n₁ n₂
  apply (cancel_epi (cokernel.π (biprod.desc
    (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
    (horizontalCanonicalAbutmentBoundaryMap K p q)))).1
  calc
    cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        (horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex f p q ≫
          (horizontalCanonicalAbutmentCokernelIso L p q).hom) =
      (((horizontalCompleteFiltrationSpectralObjectMap f).hom
            (-((p + q : ℕ) : ℤ))).app
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
        cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap L p q)
          (horizontalCanonicalAbutmentBoundaryMap L p q))) ≫
        (horizontalCanonicalAbutmentCokernelIso L p q).hom := by
      rw [← Category.assoc,
        horizontalCanonicalAbutmentBiprodCokernelMapOfBicomplex_π]
    _ = (φ.hom n₁).app
          (mk₁ (horizontalCanonicalAbutmentLowerCompositeMap p)) ≫
        (horizontalCanonicalAbutmentCokernelSequence L p q).g := by
      dsimp only [φ, n₁]
      rw [Category.assoc,
        horizontalCanonicalAbutmentCokernelIso_hom_fac]
    _ = (horizontalCanonicalAbutmentCokernelSequence K p q).g ≫
        horizontalCanonicalAbutmentMapOfBicomplex f p q := hE.symm
    _ = (cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        (horizontalCanonicalAbutmentCokernelIso K p q).hom) ≫
          horizontalCanonicalAbutmentMapOfBicomplex f p q := by
      rw [horizontalCanonicalAbutmentCokernelIso_hom_fac]
    _ = cokernel.π (biprod.desc
          (horizontalCanonicalAbutmentPreviousHomologyMap K p q)
          (horizontalCanonicalAbutmentBoundaryMap K p q)) ≫
        ((horizontalCanonicalAbutmentCokernelIso K p q).hom ≫
          horizontalCanonicalAbutmentMapOfBicomplex f p q) :=
      Category.assoc _ _ _

end HomologicalComplex₂

end
