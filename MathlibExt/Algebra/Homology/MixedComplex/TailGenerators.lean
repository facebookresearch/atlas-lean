/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.MixedComplex.Comparison
public import MathlibExt.Algebra.Homology.PartialTotalCoordinates

/-!
# Generators of mixed-complex Connes tails

Positive-column coprojections generate the translated Connes tail.
Their relations and degree comparisons give an extensionality principle
for maps out of the tail.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace MixedComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {M : MixedComplex A}

/-- A full-total generator followed by the quotient and a chosen shift-zero
coordinate.  This packages the raw generator used by tail extensionality. -/
noncomputable def genericMixedConnesTailGenerator
    (D : ConnesDoubleData M) (i j n : ℕ) (hn : i + j = n)
    (z : ℤ)
    (hz : (ComplexShape.embeddingDownNatToIntShift 0).f n = z) :
    (D.K.X i).X j ⟶
      ((genericMixedConnesTail D).extend
        (ComplexShape.embeddingDownNatToIntShift 0)).X z :=
  D.K.partialTotalCokernelGenerator 0 0 i j n hn z hz

/-- The named two-column source is the canonical tail generator. -/
theorem genericMixedTailSourceComponent_eq_generator
    (D : ConnesDoubleData M) (p q : ℕ) :
    genericMixedTailSourceComponent D p q =
      genericMixedConnesTailGenerator D (p + 1) (q + 1)
        (p + q + 2) (by omega) (2 + ((p + q : ℕ) : ℤ)) (by
          rw [ComplexShape.embeddingDownNatToIntShift_f]
          push_cast
          omega) := by
  rfl

/-- At the native shift-zero degree, the general tail generator is the
standard shifted-extension coordinate used by tail extensionality. -/
@[reassoc]
theorem genericMixedConnesTailGenerator_zeroShift_eq
    (D : ConnesDoubleData M) (i j n : ℕ) (hn : i + j = n) :
    genericMixedConnesTailGenerator D i j n hn (0 + (n : ℤ)) (by
      rw [ComplexShape.embeddingDownNatToIntShift_f]) =
      D.K.ιTotal (ComplexShape.down ℕ) i j n hn ≫
        (cokernel.π (genericMixedFirstColumnι D)).f n ≫
        (HomologicalComplex.extendDownNatToIntShiftXIso
          (genericMixedConnesTail D) 0 n).inv := by
  rfl

/-- Reindexing the total and shifted degrees of a tail generator only
transports the resulting composite. -/
theorem genericMixedConnesTailGenerator_comp_heq
    (D : ConnesDoubleData M) (i j : ℕ)
    {n n' : ℕ} (hn : i + j = n) (hn' : i + j = n')
    {z z' : ℤ}
    (hz : (ComplexShape.embeddingDownNatToIntShift 0).f n = z)
    (hz' : (ComplexShape.embeddingDownNatToIntShift 0).f n' = z')
    (hnn : n = n') (hzz : z = z')
    {L : ChainComplex A ℤ}
    (α : (genericMixedConnesTail D).extend
      (ComplexShape.embeddingDownNatToIntShift 0) ⟶ L) :
    HEq (genericMixedConnesTailGenerator D i j n hn z hz ≫ α.f z)
      (genericMixedConnesTailGenerator D i j n' hn' z' hz' ≫ α.f z') := by
  exact D.K.partialTotalCokernelGenerator_comp_heq
    0 0 i j hn hn' hz hz' hnn hzz α

/-- The zero-column tail generator vanishes because it factors through the
first partial total before the cokernel projection. -/
theorem genericMixedConnesTailGenerator_zero
    (D : ConnesDoubleData M) (j n : ℕ) (hn : 0 + j = n)
    (z : ℤ)
    (hz : (ComplexShape.embeddingDownNatToIntShift 0).f n = z) :
    genericMixedConnesTailGenerator D 0 j n hn z hz = 0 := by
  exact D.K.partialTotalCokernelGenerator_eq_zero
    0 0 0 j n (by omega) hn z hz


/-- Maps from the shifted Connes tail agree when they agree on every
canonical positive-column tail generator.  Column zero is discharged
internally by the cokernel relation. -/
theorem genericMixedConnesTail_extend_hom_ext_of_tailGenerators
    (D : ConnesDoubleData M)
    {L : ChainComplex A ℤ}
    {α β : (genericMixedConnesTail D).extend
      (ComplexShape.embeddingDownNatToIntShift 0) ⟶ L}
    (h : ∀ (p q : ℕ),
      genericMixedTailSourceComponent D p q ≫
          α.f (2 + ((p + q : ℕ) : ℤ)) =
        genericMixedTailSourceComponent D p q ≫
          β.f (2 + ((p + q : ℕ) : ℤ))) :
    α = β := by
  apply D.K.partialTotalCokernel_extend_hom_ext_of_tail 0 0
  intro i j n hn hi
  cases i with
  | zero => omega
  | succ p =>
      cases j with
      | zero =>
          exact (D.isZero (p + 1) 0 (by omega)).eq_of_src _ _
      | succ q =>
          have hn' : (p + 1) + (q + 1) = p + q + 2 := by omega
          have hnn : n = p + q + 2 := by omega
          have hz : (ComplexShape.embeddingDownNatToIntShift 0).f n =
              0 + (n : ℤ) := by
            rw [ComplexShape.embeddingDownNatToIntShift_f]
          have hz' : (ComplexShape.embeddingDownNatToIntShift 0).f
              (p + q + 2) = 2 + ((p + q : ℕ) : ℤ) := by
            rw [ComplexShape.embeddingDownNatToIntShift_f]
            push_cast
            omega
          have hzz : (0 : ℤ) + (n : ℤ) =
              2 + ((p + q : ℕ) : ℤ) := by
            rw [hnn]
            push_cast
            omega
          have hc := h p q
          rw [genericMixedTailSourceComponent_eq_generator] at hc
          unfold genericMixedConnesTailGenerator at hc
          convert hc using 1
          · rw [hzz]
          · exact genericMixedConnesTailGenerator_comp_heq D
              (p + 1) (q + 1) hn hn' hz hz' hnn hzz α
          · exact genericMixedConnesTailGenerator_comp_heq D
              (p + 1) (q + 1) hn hn' hz hz' hnn hzz β


end MixedComplex
