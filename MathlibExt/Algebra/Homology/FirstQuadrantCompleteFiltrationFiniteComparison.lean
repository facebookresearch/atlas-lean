/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltrationFunctor

/-!
# Comparing complete horizontal filtration stages with finite stages

Let C be preadditive with a zero object and finite coproducts, and K a bicomplex of shape (down
ℕ,down ℕ). For an integer a≥0, the complete stage G_a is canonically isomorphic to the ath
finite horizontal stage G^fin_a. The isomorphism preserves their monic inclusions into Tot K.

These comparisons commute with a bicomplex morphism f:K→L at each nonnegative integer cut and
with the transitions induced by a≤b. Thus restriction of the complete filtration to nonnegative
integer cuts agrees with the finite horizontal filtration as a diagram of subcomplexes. No
abelian or bounded-support hypothesis is needed, and category universes are arbitrary.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be preadditive with a zero object and finite coproducts, K a bicomplex of shape (down
ℕ,down ℕ), and a∈ℤ with a≥0. This is the canonical chain-complex isomorphism
e_{K,a}:G_a(K)≅G^fin_a(K) from the complete horizontal stage at integer cut a to the finite
horizontal stage indexed by the same nonnegative integer. -/
noncomputable def horizontalCompleteFilteredTotalComplexFiniteIso
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (a : ℤ) (ha : 0 ≤ a) :
    horizontalCompleteFilteredTotalComplex K (a : EInt) ≅
      horizontalFilteredTotalComplex K a.toNat :=
  eqToIso (horizontalCompleteFilteredTotalComplex_coe_of_nonneg K a ha)

/-- For a first-quadrant bicomplex K in a preadditive category with a zero object and finite
coproducts and an integer a≥0, let e_{K,a}:G_a(K)≅G^fin_a(K) be the complete-to-finite stage
comparison. If ι^fin_a:G^fin_a(K)→Tot K and ι_a:G_a(K)→Tot K are the canonical inclusions, then
e_{K,a}.hom≫ι^fin_a=ι_a. -/
@[reassoc (attr := simp)]
theorem horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexToTotal K a.toNat =
      horizontalCompleteFilteredTotalToTotal K (a : EInt) := by
  have hmono : horizontalCompleteFilteredTotalMonoOver K (a : EInt) =
      (horizontalTotalFiltration K).toMonoOver.obj a.toNat := by
    simp only [horizontalCompleteFilteredTotalMonoOver, WithBotTop.rec_coe,
      ite_eq_left ha]
  have harrow (S T : MonoOver (K.total (ComplexShape.down ℕ))) (h : S = T) :
      HEq S.arrow T.arrow := by
    cases h
    rfl
  have hstage : HEq (horizontalCompleteFilteredTotalToTotal K (a : EInt))
      ((horizontalTotalFiltration K).ι.app a.toNat) := by
    simpa only [horizontalCompleteFilteredTotalToTotal, Filtration.ι_app,
      MonoOver.arrow] using harrow _ _ hmono
  have hincl : HEq (horizontalCompleteFilteredTotalToTotal K (a : EInt))
      (horizontalFilteredTotalComplexToTotal K a.toNat) :=
    hstage.trans (heq_of_eq (horizontalTotalFiltration_ι_app K a.toNat))
  apply eq_of_heq
  rw [horizontalCompleteFilteredTotalComplexFiniteIso, eqToIso.hom,
    eqToHom_comp_heq_iff]
  exact hincl.symm

/-- Let C be preadditive with a zero object and finite coproducts, f:K→L a morphism of bicomplexes
of shape (down ℕ,down ℕ), and a∈ℤ with a≥0. For e_{K,a}:G_a(K)≅G^fin_a(K) and e_{L,a}, the
induced complete and finite stage maps satisfy e_{K,a}.hom≫G^fin_a(f)=G_a(f)≫e_{L,a}.hom. -/
theorem horizontalCompleteFilteredTotalComplexFiniteIso_naturality
    (f : K ⟶ L) (a : ℤ) (ha : 0 ≤ a) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexMapOfBicomplex f a.toNat =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).hom := by
  apply (cancel_mono
    (horizontalFilteredTotalComplexToTotal L a.toNat)).1
  calc
    ((horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
          horizontalFilteredTotalComplexMapOfBicomplex f a.toNat) ≫
        horizontalFilteredTotalComplexToTotal L a.toNat =
      (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        (horizontalFilteredTotalComplexMapOfBicomplex f a.toNat ≫
          horizontalFilteredTotalComplexToTotal L a.toNat) :=
      Category.assoc _ _ _
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        (horizontalFilteredTotalComplexToTotal K a.toNat ≫
          total.map f (ComplexShape.down ℕ)) := by
      rw [horizontalFilteredTotalComplexMapOfBicomplex_toTotal]
    _ = ((horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
          horizontalFilteredTotalComplexToTotal K a.toNat) ≫
        total.map f (ComplexShape.down ℕ) :=
      (Category.assoc _ _ _).symm
    _ = horizontalCompleteFilteredTotalToTotal K (a : EInt) ≫
        total.map f (ComplexShape.down ℕ) := by
      rw [horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal]
    _ = horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
        horizontalCompleteFilteredTotalToTotal L (a : EInt) := by
      rw [horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal]
    _ = horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
        ((horizontalCompleteFilteredTotalComplexFiniteIso L a ha).hom ≫
          horizontalFilteredTotalComplexToTotal L a.toNat) := by
      rw [horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal]
    _ = (horizontalCompleteFilteredTotalComplexMapOfBicomplex f (a : EInt) ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso L a ha).hom) ≫
        horizontalFilteredTotalComplexToTotal L a.toNat :=
      (Category.assoc _ _ _).symm

/-- For a first-quadrant bicomplex K in a preadditive category with a zero object and finite
coproducts, let a,b∈ℤ satisfy 0≤a≤b. The stage comparisons e_a:G_a(K)≅G^fin_a(K) and
e_b:G_b(K)≅G^fin_b(K) intertwine the complete transition t_{a,b} and the finite horizontal
transition t^fin_{a,b}: e_a.hom≫t^fin_{a,b}=t_{a,b}≫e_b.hom. -/
theorem horizontalCompleteFilteredTotalComplexFiniteIso_transition
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (a b : ℤ) (ha : 0 ≤ a) (hab : a ≤ b) :
    (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexMap K (Int.toNat_le_toNat hab) =
      horizontalCompleteFilteredTotalMap K
          (WithBotTop.coe_monotone hab) ≫
        (horizontalCompleteFilteredTotalComplexFiniteIso K b
          (ha.trans hab)).hom := by
  apply (cancel_mono
    (horizontalFilteredTotalComplexToTotal K b.toNat)).1
  calc
    ((horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
          horizontalFilteredTotalComplexMap K
            (Int.toNat_le_toNat hab)) ≫
        horizontalFilteredTotalComplexToTotal K b.toNat =
      (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        (horizontalFilteredTotalComplexMap K
            (Int.toNat_le_toNat hab) ≫
          horizontalFilteredTotalComplexToTotal K b.toNat) :=
      Category.assoc _ _ _
    _ = (horizontalCompleteFilteredTotalComplexFiniteIso K a ha).hom ≫
        horizontalFilteredTotalComplexToTotal K a.toNat := by
      rw [horizontalFilteredTotalComplexMap_toTotal]
    _ = horizontalCompleteFilteredTotalToTotal K (a : EInt) :=
      horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal K a ha
    _ = horizontalCompleteFilteredTotalMap K
          (WithBotTop.coe_monotone hab) ≫
        horizontalCompleteFilteredTotalToTotal K (b : EInt) := by
      rw [horizontalCompleteFilteredTotalMap_toTotal]
    _ = horizontalCompleteFilteredTotalMap K
          (WithBotTop.coe_monotone hab) ≫
        ((horizontalCompleteFilteredTotalComplexFiniteIso K b
            (ha.trans hab)).hom ≫
          horizontalFilteredTotalComplexToTotal K b.toNat) := by
      rw [horizontalCompleteFilteredTotalComplexFiniteIso_hom_toTotal]
    _ = (horizontalCompleteFilteredTotalMap K
            (WithBotTop.coe_monotone hab) ≫
          (horizontalCompleteFilteredTotalComplexFiniteIso K b
            (ha.trans hab)).hom) ≫
        horizontalFilteredTotalComplexToTotal K b.toNat :=
      (Category.assoc _ _ _).symm

end HomologicalComplex₂

end
