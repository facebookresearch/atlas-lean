/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Module.SpanRank
public import MathlibExt.Algebra.DirectSum.InternalGradeAlgebra
public import MathlibExt.RingTheory.GradedAlgebra.Standard
public import MathlibExt.RingTheory.Ideal.AssociatedGraded.Ring

/-!
# Minimal standard presentations of associated-graded rings

A finite family generating an ideal gives degree-one initial forms that
generate its total associated-graded ring over the degree-zero quotient.
Choosing a generating family of cardinality `I.spanFinrank` yields the
minimal-cardinality standard graded presentation used by later
Hilbert--Serre arguments.

This file proves no polynomial-ring injectivity or equivalence, no Rees
comparison, no graded free presentation for modules, no Hilbert--Serre
polynomiality, and no dimension result.

## Main declarations

* `Ideal.associatedGradedStandardPresentationOfSpan`
* `Ideal.coe_associatedGradedStandardPresentationOfSpan_generator`
* `Ideal.associatedGradedStandardPresentation`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Ideal

universe u

variable {R : Type u} [CommRing R]

private theorem associatedGraded_adjoin_degreeOne_eq_top
    (I : Ideal R) {r : ℕ} (g : Fin r → R)
    (hg : Ideal.span (Set.range g) = I) :
    Algebra.adjoin (R ⧸ I)
      (Set.range fun i =>
        DirectSum.of I.AssociatedGradedPiece 1
          (I.initialForm 1
            ⟨g i, by
              simpa only [pow_one] using
                hg.le (Ideal.subset_span ⟨i, rfl⟩)⟩)) = ⊤ := by
  let gen : Fin r → I.AssociatedGraded := fun i =>
    DirectSum.of I.AssociatedGradedPiece 1
      (I.initialForm 1
        ⟨g i, by
          simpa only [pow_one] using
            hg.le (Ideal.subset_span ⟨i, rfl⟩)⟩)
  let P : Subalgebra (R ⧸ I) I.AssociatedGraded :=
    Algebra.adjoin (R ⧸ I) (Set.range gen)
  change P = ⊤
  apply top_unique
  intro z hz
  clear hz
  induction z using DirectSum.induction_on with
  | zero => exact P.zero_mem
  | add x y hx hy => exact P.add_mem hx hy
  | of n q =>
      obtain ⟨x, rfl⟩ := I.initialForm_surjective n q
      exact Submodule.pow_induction_on_right'
        (M := (I : Submodule R R))
        (C := fun n x hx =>
          DirectSum.of I.AssociatedGradedPiece n
            (I.initialForm n ⟨x, hx⟩) ∈ P)
        (fun a => by
          have h := P.algebraMap_mem (Ideal.Quotient.mk I a)
          rw [DirectSum.algebraMap_apply,
            I.associatedGradedGAlgebra_toFun_mk] at h
          exact h)
        (fun x y n hx hy hxP hyP => by
          have heq : (⟨x + y, Submodule.add_mem _ hx hy⟩ :
              (I ^ n : Ideal R)) = ⟨x, hx⟩ + ⟨y, hy⟩ := by
            apply Subtype.ext
            rfl
          rw [heq, map_add, map_add]
          exact P.add_mem hxP hyP)
        (fun n x hx hxP m hm => by
          have hm' : m ∈ Submodule.span R (Set.range g) := by
            rw [Ideal.submodule_span_eq, hg]
            exact hm
          refine Submodule.span_induction
            (p := fun m hmSpan =>
              DirectSum.of I.AssociatedGradedPiece (n + 1)
                (I.initialForm (n + 1)
                  ⟨x * m, Ideal.mul_mem_mul hx (by
                    rw [← hg, ← Ideal.submodule_span_eq]
                    exact hmSpan)⟩) ∈ P)
            ?_ ?_ ?_ ?_ hm'
          · intro y hy
            obtain ⟨i, rfl⟩ := hy
            have hgen : gen i ∈ P :=
              Algebra.subset_adjoin ⟨i, rfl⟩
            have hmul := P.mul_mem hxP hgen
            dsimp only [gen] at hmul
            rw [DirectSum.of_mul_of] at hmul
            change DirectSum.of I.AssociatedGradedPiece (n + 1)
              (I.adicGradedMul n 1 (I.adicSymbol n ⟨x, hx⟩)
                (I.adicSymbol 1 ⟨g i, by
                  simpa only [pow_one] using
                    hg.le (Ideal.subset_span ⟨i, rfl⟩)⟩)) ∈ P at hmul
            rw [I.adicGradedMul_symbol] at hmul
            exact hmul
          · have hz : I.initialForm (n + 1)
                ⟨x * 0, Ideal.mul_mem_mul hx (by
                  rw [← hg, ← Ideal.submodule_span_eq]
                  exact Submodule.zero_mem _)⟩ = 0 := by
              let z0 : (I ^ (n + 1) : Ideal R) := ⟨x * 0, by simp⟩
              change I.initialForm (n + 1) z0 = 0
              rw [show z0 = 0 by
                apply Subtype.ext
                change x * 0 = 0
                exact mul_zero x, map_zero]
            rw [hz, map_zero]
            exact P.zero_mem
          · intro a b ha hb ihA ihB
            have heq : (⟨x * (a + b), by
                  rw [mul_add]
                  exact Submodule.add_mem _
                    (Ideal.mul_mem_mul hx (by
                      rw [← hg, ← Ideal.submodule_span_eq]
                      exact ha))
                    (Ideal.mul_mem_mul hx (by
                      rw [← hg, ← Ideal.submodule_span_eq]
                      exact hb))⟩ :
                (I ^ (n + 1) : Ideal R)) =
              ⟨x * a, Ideal.mul_mem_mul hx (by
                rw [← hg, ← Ideal.submodule_span_eq]
                exact ha)⟩ +
                ⟨x * b, Ideal.mul_mem_mul hx (by
                  rw [← hg, ← Ideal.submodule_span_eq]
                  exact hb)⟩ := by
              apply Subtype.ext
              exact mul_add x a b
            rw [heq, map_add, map_add]
            exact P.add_mem ihA ihB
          · intro a m hm ih
            have hsmul := P.smul_mem ih (Ideal.Quotient.mk I a)
            rw [← DirectSum.of_smul, I.initialForm_apply,
              Module.Quotient.mk_smul_mk] at hsmul
            rw [I.initialForm_apply]
            convert hsmul using 1
            apply congrArg (DirectSum.of I.AssociatedGradedPiece (n + 1))
            apply congrArg Submodule.Quotient.mk
            apply Subtype.ext
            exact mul_left_comm x a m)
        x.2

/-- A named finite generating family for an ideal gives a standard graded
presentation of its associated-graded ring by the degree-one initial forms. -/
@[no_expose]
noncomputable def associatedGradedStandardPresentationOfSpan
    (I : Ideal R) {r : ℕ} (g : Fin r → R)
    (hg : Ideal.span (Set.range g) = I) :
    HilbertSamuel.StandardGradedPresentation
      (R ⧸ I) I.AssociatedGraded
      (DirectSum.algebraInternalGrade
        (R ⧸ I) I.AssociatedGradedPiece)
      r where
  generator i :=
    ⟨DirectSum.of I.AssociatedGradedPiece 1
      (I.initialForm 1
        ⟨g i, by
          simpa only [pow_one] using
            hg.le (Ideal.subset_span ⟨i, rfl⟩)⟩),
      (DirectSum.mem_algebraInternalGrade_iff
        (R ⧸ I) I.AssociatedGradedPiece _ 1).2 ⟨_, rfl⟩⟩
  adjoin_eq_top := associatedGraded_adjoin_degreeOne_eq_top I g hg

/-- A named generator in the standard presentation is literally its total
degree-one initial form. -/
@[simp]
theorem coe_associatedGradedStandardPresentationOfSpan_generator
    (I : Ideal R) {r : ℕ} (g : Fin r → R)
    (hg : Ideal.span (Set.range g) = I) (i : Fin r) :
    ((I.associatedGradedStandardPresentationOfSpan g hg).generator i :
        I.AssociatedGraded) =
      DirectSum.of I.AssociatedGradedPiece 1
        (I.initialForm 1
          ⟨g i, by
            simpa only [pow_one] using
              hg.le (Ideal.subset_span ⟨i, rfl⟩)⟩) := by
  rfl

private noncomputable def associatedGradedSpanFinrankGenerators
    (I : Ideal R) (hI : I.FG) :
    {g : Fin I.spanFinrank → R // Ideal.span (Set.range g) = I} := by
  have hgen : Nonempty {s : Finset R //
      s.card = I.spanFinrank ∧ Submodule.span R (s : Set R) = I} := by
    rcases Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (p := (I : Submodule R R)) hI with ⟨s, hsCard, hsSpan⟩
    exact ⟨⟨s, hsCard, hsSpan⟩⟩
  let s := Classical.choice hgen
  have hsCard : s.1.card = I.spanFinrank := s.2.1
  have hsSpan : Submodule.span R (s.1 : Set R) = I := s.2.2
  let e : s.1 ≃ Fin I.spanFinrank := Finset.equivFinOfCardEq hsCard
  let g : Fin I.spanFinrank → R := fun i => (e.symm i : s.1).1
  refine ⟨g, ?_⟩
  have hrange : Set.range g = (s.1 : Set R) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm i : s.1).2
    · intro hx
      let y : s.1 := ⟨x, hx⟩
      exact ⟨e y, by simp [g, y]⟩
  rw [← Ideal.submodule_span_eq]
  simpa only [hrange] using hsSpan

/-- A finitely generated ideal has a standard graded presentation with the
minimal number `I.spanFinrank` of degree-one generators. -/
@[no_expose]
noncomputable def associatedGradedStandardPresentation
    (I : Ideal R) (hI : I.FG) :
    HilbertSamuel.StandardGradedPresentation
      (R ⧸ I) I.AssociatedGraded
      (DirectSum.algebraInternalGrade
        (R ⧸ I) I.AssociatedGradedPiece)
      I.spanFinrank :=
  I.associatedGradedStandardPresentationOfSpan
    (associatedGradedSpanFinrankGenerators I hI).1
    (associatedGradedSpanFinrankGenerators I hI).2

end Ideal
