/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.Bifunctor
public import MathlibExt.Algebra.Homology.ChainComplex.BalancedTensor
public import MathlibExt.Algebra.Category.ModuleCat.BalancedTensor.Flat
public import MathlibExt.Algebra.Homology.TotalComplexExact
public import Mathlib.Algebra.Category.Grp.AB

/-!
# Flat cycles/image tensor sequences on integer totals

Tensor the cycles, term and outgoing-image complex sequence with an
arbitrary left-module complex. The end complexes have zero first-variable
differentials, while the middle retains its differential; all
second-variable differentials are retained. Flat outgoing images make
the degreewise tensor sequence short exact. Exact coproducts along integer
diagonals give the total short exact sequence.

Boundedness, projectivity of terms and zero coefficient differentials are
not required.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

universe u v

namespace ChainComplex.BalancedTensor

variable (R : Type u) [Ring R]

local notation "c" => ComplexShape.down ℤ

/-- The original canonical complex sequence after the actual fixed-Q raw bifunctor. -/
def cyclesTensorBicomplexSequence (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) : ShortComplex (HomologicalComplex₂ AddCommGrpCat.{v}
      c c) :=
  (HomologicalComplex.cyclesComplexSequence P).map
    (((ModuleCat.BalancedTensor.groupBifunctor R).mapBifunctorHomologicalComplex c c).flip.obj Q)

/-- The actual canonical tensor sequence is functorial in the original right complex. -/
def cyclesTensorSequenceFunctor (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ ⥤ ShortComplex (ChainComplex AddCommGrpCat.{v} ℤ) :=
  HomologicalComplex.cyclesComplexSequenceFunctor ⋙
    (((ModuleCat.BalancedTensor.groupBifunctor R).mapBifunctorHomologicalComplex c c).flip.obj
      Q).mapShortComplex ⋙
    (HomologicalComplex₂.totalFunctor AddCommGrpCat.{v} c c c).mapShortComplex

/-- The native full direct-sum total of the actual cycles/image tensor bicomplex sequence. -/
def cyclesTensorSequence (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) : ShortComplex (ChainComplex AddCommGrpCat.{v} ℤ) :=
  (cyclesTensorSequenceFunctor R Q).obj P

/-- The total sequence is the native total image of the actual raw sequence. -/
theorem cyclesTensorSequence_eq_total_map (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    cyclesTensorSequence R P Q =
      (cyclesTensorBicomplexSequence R P Q).map
        (HomologicalComplex₂.totalFunctor AddCommGrpCat.{v} c c c) := rfl

/-- The left term is the original cycles-zero-complex tensor total. -/
theorem cyclesTensorSequence_X₁ (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    (cyclesTensorSequence R P Q).X₁ = complex R (HomologicalComplex.cyclesZeroComplex P) Q := rfl

/-- The middle term is the actual original tensor complex, with both differentials. -/
theorem cyclesTensorSequence_X₂ (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    (cyclesTensorSequence R P Q).X₂ = complex R P Q := rfl

/-- The right term retains the actual outgoing images and genuine Q differential. -/
theorem cyclesTensorSequence_X₃ (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    (cyclesTensorSequence R P Q).X₃ =
      complex R (HomologicalComplex.outgoingImageZeroComplex P) Q := rfl

/-- The first total map is tensoring the original cycles inclusion with the identity of Q. -/
theorem cyclesTensorSequence_f (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    (cyclesTensorSequence R P Q).f =
      map R (HomologicalComplex.cyclesComplexInclusion.app P) (𝟙 Q) := by
  let G := (ModuleCat.BalancedTensor.groupBifunctor R).mapBifunctorHomologicalComplex c c
  let α : HomologicalComplex.cyclesZeroComplex P ⟶ P :=
    HomologicalComplex.cyclesComplexInclusion.app P
  let m := (G.map α).app Q
  change HomologicalComplex₂.total.map m c =
    HomologicalComplex₂.total.map (m ≫ (G.obj P).map (𝟙 Q)) c
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The second total map is the original quotient onto outgoing images tensored with Q. -/
theorem cyclesTensorSequence_g (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    (cyclesTensorSequence R P Q).g =
      map R (HomologicalComplex.cyclesComplexProjection.app P) (𝟙 Q) := by
  let G := (ModuleCat.BalancedTensor.groupBifunctor R).mapBifunctorHomologicalComplex c c
  let I := HomologicalComplex.outgoingImageZeroComplex P
  let α : P ⟶ I := HomologicalComplex.cyclesComplexProjection.app P
  let m := (G.map α).app Q
  change HomologicalComplex₂.total.map m c =
    HomologicalComplex₂.total.map (m ≫ (G.obj I).map (𝟙 Q)) c
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

/-- The natural sequence map keeps the genuine original tensor-complex map in the middle. -/
theorem cyclesTensorSequenceFunctor_map_τ₂
    {P P' : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ} (f : P ⟶ P')
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    ((cyclesTensorSequenceFunctor R Q).map f).τ₂ = map R f (𝟙 Q) := by
  let G := (ModuleCat.BalancedTensor.groupBifunctor R).mapBifunctorHomologicalComplex c c
  let m := (G.map f).app Q
  change HomologicalComplex₂.total.map m c =
    HomologicalComplex₂.total.map (m ≫ (G.obj P').map (𝟙 Q)) c
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

section Exactness

variable [HasProjectiveResolutions (ModuleCat.{v} Rᵐᵒᵖ)]

/-- The raw tensor sequence is exact when the image Tor₁ value vanishes at
each actual coefficient term of this fixed Q. -/
theorem cyclesTensorBicomplexSequence_shortExact_of_Q_terms
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (hQ : ∀ i j, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (Abelian.image (P.d i ((ComplexShape.down ℤ).next i)))).obj (Q.X j))) :
    (cyclesTensorBicomplexSequence R P Q).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  change ((HomologicalComplex.cyclesImageSequence P i ((ComplexShape.down ℤ).next i)).map
    ((ModuleCat.BalancedTensor.groupBifunctor R).flip.obj (Q.X j))).ShortExact
  exact ModuleCat.BalancedTensor.shortExact_map_tensor_of_isZero_torFirst_one R
    (HomologicalComplex.cyclesImageSequence_shortExact P i
      ((ComplexShape.down ℤ).next i) rfl) (Q.X j) (hQ i j)

/-- Exact diagonal sums totalize this fixed-Q pointwise exact tensor sequence. -/
theorem cyclesTensorSequence_shortExact_of_Q_terms
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (hQ : ∀ i j, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (Abelian.image (P.d i ((ComplexShape.down ℤ).next i)))).obj (Q.X j))) :
    (cyclesTensorSequence R P Q).ShortExact := by
  rw [cyclesTensorSequence_eq_total_map]
  exact HomologicalComplex₂.totalFunctor_map_shortExact_of_exact_fibers
    (cyclesTensorBicomplexSequence R P Q)
    (cyclesTensorBicomplexSequence_shortExact_of_Q_terms R P Q hQ)

/-- Flat outgoing images supply the fixed-Q term conditions for every genuine Q. -/
theorem cyclesTensorBicomplexSequence_shortExact
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (hI : ∀ i B, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (Abelian.image (P.d i ((ComplexShape.down ℤ).next i)))).obj B)) :
    (cyclesTensorBicomplexSequence R P Q).ShortExact :=
  cyclesTensorBicomplexSequence_shortExact_of_Q_terms R P Q (fun i j => hI i (Q.X j))

/-- Flat outgoing images give the actual short exact sequence of full tensor totals. -/
theorem cyclesTensorSequence_shortExact
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (hI : ∀ i B, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (Abelian.image (P.d i ((ComplexShape.down ℤ).next i)))).obj B)) :
    (cyclesTensorSequence R P Q).ShortExact :=
  cyclesTensorSequence_shortExact_of_Q_terms R P Q (fun i j => hI i (Q.X j))

end Exactness

end ChainComplex.BalancedTensor
