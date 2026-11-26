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
# Tensor sequences of cycles and outgoing images

For a right `R`-module chain complex `P`, the degreewise sequence from its cycles to `P` to
its outgoing differential images is short exact. The cycles and outgoing-image complexes in
this sequence have zero differentials. Tensoring with an arbitrary integer complex `Q` of left
modules retains every second-variable differential, with the tensor-total signs.

If `Tor¹_R(im(d_P)_i, Q_j)` vanishes for every pair of integer indices, the tensor bicomplex
sequence is degreewise short exact. Exact direct sums along integer diagonals give a short
exact sequence of total complexes. Uniform Tor-one vanishing of each outgoing image against
all left modules is a sufficient condition. The exactness statements use projective
resolutions in the right module category; the input complexes may be unbounded.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits

universe u v

namespace ChainComplex.BalancedTensor

variable (R : Type u) [Ring R]

local notation "c" => ComplexShape.down ℤ

/-- Tensor bicomplex sequence from cycles to terms to outgoing images.

Apply the balanced tensor bicomplex construction with fixed `Q` to the short complex
`cyclesZeroComplex P ⟶ P ⟶ outgoingImageZeroComplex P`. -/
def cyclesTensorBicomplexSequence (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) : ShortComplex (HomologicalComplex₂ AddCommGrpCat.{v}
      c c) :=
  (HomologicalComplex.cyclesComplexSequence P).map
    (((ModuleCat.BalancedTensor.groupBifunctor R).mapBifunctorHomologicalComplex c c).flip.obj Q)

/-- Cycles tensor total sequences vary functorially in the right complex.

For fixed left complex `Q`, the cycles-complex short sequence, tensor bicomplex construction,
and totalization give a functor from right-module chain complexes to short complexes of
additive-group chain complexes. -/
def cyclesTensorSequenceFunctor (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ ⥤ ShortComplex (ChainComplex AddCommGrpCat.{v} ℤ) :=
  HomologicalComplex.cyclesComplexSequenceFunctor ⋙
    (((ModuleCat.BalancedTensor.groupBifunctor R).mapBifunctorHomologicalComplex c c).flip.obj
      Q).mapShortComplex ⋙
    (HomologicalComplex₂.totalFunctor AddCommGrpCat.{v} c c c).mapShortComplex

/-- Total tensor sequence of cycles and outgoing images.

For `P` and `Q`, the short complex `cyclesTensorSequence R P Q` is the direct-sum totalization
of the corresponding tensor bicomplex sequence. -/
def cyclesTensorSequence (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) : ShortComplex (ChainComplex AddCommGrpCat.{v} ℤ) :=
  (cyclesTensorSequenceFunctor R Q).obj P

/-- Cycles tensor sequence is the totalized bicomplex short complex.

The short complex of tensor totals equals the image of `cyclesTensorBicomplexSequence R P Q`
under the integer total-complex functor. -/
theorem cyclesTensorSequence_eq_total_map (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    cyclesTensorSequence R P Q =
      (cyclesTensorBicomplexSequence R P Q).map
        (HomologicalComplex₂.totalFunctor AddCommGrpCat.{v} c c c) := rfl

/-- Left term of the cycles tensor sequence.

The first complex is `complex R (HomologicalComplex.cyclesZeroComplex P) Q`, with zero first-
factor differential and the full differential of `Q`. -/
theorem cyclesTensorSequence_X₁ (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    (cyclesTensorSequence R P Q).X₁ = complex R (HomologicalComplex.cyclesZeroComplex P) Q := rfl

/-- Middle term of the cycles tensor sequence.

The middle complex is `complex R P Q`, retaining both tensor differential contributions. -/
theorem cyclesTensorSequence_X₂ (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    (cyclesTensorSequence R P Q).X₂ = complex R P Q := rfl

/-- Right term of the cycles tensor sequence.

The third complex is `complex R (HomologicalComplex.outgoingImageZeroComplex P) Q`, with zero
first-factor differential and the full differential of `Q`. -/
theorem cyclesTensorSequence_X₃ (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ)
    (Q : ChainComplex (ModuleCat.{v} R) ℤ) :
    (cyclesTensorSequence R P Q).X₃ =
      complex R (HomologicalComplex.outgoingImageZeroComplex P) Q := rfl

/-- First arrow of the cycles tensor sequence is the tensor inclusion.

The first arrow is the tensor-total map of the cycles-complex inclusion into `P` and the
identity on `Q`. -/
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

/-- Second arrow of the cycles tensor sequence is the tensor projection.

The second arrow is the tensor-total map of the projection from `P` to its outgoing-image zero
complex and the identity on `Q`. -/
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

/-- Middle map of a cycles tensor sequence morphism.

For a chain map `f : P ⟶ P'`, the middle component of the induced short-complex morphism is
`map R f (𝟙 Q)`. -/
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

/-- Pairwise outgoing-image Tor vanishing gives tensor bicomplex exactness.

If `Tor¹_R(im(P.d i (i-1)), Q.X j)` is zero for every pair of integer indices `i` and `j`, the
cycles tensor bicomplex sequence is short exact. -/
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

/-- Pairwise outgoing-image Tor vanishing gives total tensor exactness.

Under vanishing of `Tor¹` between each outgoing image of `P` and each term of `Q`, the direct-
sum total cycles tensor sequence is short exact. -/
theorem cyclesTensorSequence_shortExact_of_Q_terms
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (hQ : ∀ i j, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (Abelian.image (P.d i ((ComplexShape.down ℤ).next i)))).obj (Q.X j))) :
    (cyclesTensorSequence R P Q).ShortExact := by
  rw [cyclesTensorSequence_eq_total_map]
  exact HomologicalComplex₂.totalFunctor_map_shortExact_of_exact_fibers
    (cyclesTensorBicomplexSequence R P Q)
    (cyclesTensorBicomplexSequence_shortExact_of_Q_terms R P Q hQ)

/-- Flat outgoing images give tensor bicomplex exactness.

If every outgoing differential image of `P` has zero `Tor¹` against every left `R`-module,
then the cycles tensor bicomplex sequence with any left complex `Q` is short exact. -/
theorem cyclesTensorBicomplexSequence_shortExact
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (hI : ∀ i B, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (Abelian.image (P.d i ((ComplexShape.down ℤ).next i)))).obj B)) :
    (cyclesTensorBicomplexSequence R P Q).ShortExact :=
  cyclesTensorBicomplexSequence_shortExact_of_Q_terms R P Q (fun i j => hI i (Q.X j))

/-- Flat outgoing images give total cycles tensor exactness.

Uniform Tor-one vanishing of the outgoing differential images of `P` makes the total cycles
tensor sequence with `Q` short exact. -/
theorem cyclesTensorSequence_shortExact
    (P : ChainComplex (ModuleCat.{v} Rᵐᵒᵖ) ℤ) (Q : ChainComplex (ModuleCat.{v} R) ℤ)
    (hI : ∀ i B, IsZero (((ModuleCat.BalancedTensor.torFirst R 1).obj
      (Abelian.image (P.d i ((ComplexShape.down ℤ).next i)))).obj B)) :
    (cyclesTensorSequence R P Q).ShortExact :=
  cyclesTensorSequence_shortExact_of_Q_terms R P Q (fun i j => hI i (Q.X j))

end Exactness

end ChainComplex.BalancedTensor
