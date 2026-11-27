/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import
  MathlibExt.RepresentationTheory.Homological.ContCohomology.DiscreteCoefficientLongExact

/-!
# Natural exact windows for discrete continuous coefficients

Let G be a profinite group in universe v. Discrete abelian coefficients lie in
universe max(v,w), with jointly continuous G-action. An exact coefficient sequence
gives a short exact sequence of homogeneous cochain complexes.

The continuous/cochain homology comparisons form a natural isomorphism of the
complete six-term cohomology windows. The connecting maps form a natural
transformation on exact coefficient sequences, and the comparison intertwines
this transformation with the connecting transformation of cochain homology.

The group and coefficient universes remain independent. Exactness is the existing
injectivity, image–kernel equality and surjectivity predicate on coefficients.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe v w

namespace ContinuousCohomology

/-- Continuous cohomology and the homology of homogeneous abelian cochains are
naturally isomorphic in the coefficient. The component is the canonical
homology-preservation comparison. -/
def discreteCoefficientHomologyNatIso (G : ProfiniteGrp.{v}) (n : ℕ) :
    discreteCoefficientCohomologyFunctor.{v, w} G n ≅
      discreteCoefficientCochainFunctor.{v, w} G ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max v w}
          (ComplexShape.up ℕ) n :=
  NatIso.ofComponents
    (fun A => discreteCoefficientHomologyIso.{v, w} G A n)
    (fun f => discreteCoefficientHomologyIso_naturality.{v, w} f n)

/-- The coefficient-natural homology comparison has its prescribed component. -/
@[simp]
theorem discreteCoefficientHomologyNatIso_hom_app
    (G : ProfiniteGrp.{v}) (n : ℕ)
    (A : DiscreteContAction (TopModuleCat.{max v w} ℤ) G) :
    (discreteCoefficientHomologyNatIso.{v, w} G n).hom.app A =
      (discreteCoefficientHomologyIso.{v, w} G A n).hom :=
  rfl

/-- Exact discrete coefficient sequences map to short exact homogeneous cochain
sequences. Morphisms are the original coefficient diagrams mapped by the existing
cochain functor. -/
def discreteCoefficientShortExactCochainFunctor (G : ProfiniteGrp.{v}) :
    DiscreteCoefficientExactSequences.{v, w} G ⥤
      ShortComplex.ShortExactSequences (CochainComplex AddCommGrpCat.{max v w} ℕ) :=
  (ShortComplex.isShortExact (CochainComplex AddCommGrpCat.{max v w} ℕ)).lift
    ((discreteCoefficientExactProperty.{v, w} G).ι ⋙
      (discreteCoefficientCochainFunctor.{v, w} G).mapShortComplex)
    (fun S => discreteCoefficientCochain_shortExact.{v, w} S.obj S.property)

/-- The six-term continuous cohomology functor takes values in exact sequences,
with the original coefficient maps and connecting morphism. -/
def discreteCoefficientExactWindowFunctor (G : ProfiniteGrp.{v}) (n : ℕ) :
    DiscreteCoefficientExactSequences.{v, w} G ⥤
      ComposableArrows.ExactSequences AddCommGrpCat.{max v w} 5 :=
  (ComposableArrows.exactSequences AddCommGrpCat.{max v w} 5).lift
    (discreteCoefficientLongSequenceFunctor.{v, w} G n)
    (fun S => discreteCoefficientLongSequence_exact.{v, w} S.obj S.property n)

/-- The complete exact continuous-cohomology window is naturally isomorphic to
the exact homology window of the corresponding short exact cochain sequence.
All six components are the canonical coefficient homology comparisons. -/
def discreteCoefficientExactWindowNatIso (G : ProfiniteGrp.{v}) (n : ℕ) :
    discreteCoefficientExactWindowFunctor.{v, w} G n ≅
      discreteCoefficientShortExactCochainFunctor.{v, w} G ⋙
        HomologicalComplex.HomologySequence.exactSequenceFunctor
          n (n + 1) (discreteCoefficientUpRel n) :=
  NatIso.ofComponents
    (fun S => (ComposableArrows.exactSequences AddCommGrpCat.{max v w} 5).isoMk
      (discreteCoefficientLongSequenceIso.{v, w} S.obj S.property n))
    (fun f => by
      apply ObjectProperty.hom_ext
      apply ComposableArrows.hom_ext₅
      · exact discreteCoefficientHomologyIso_naturality.{v, w} f.hom.τ₁ n
      · exact discreteCoefficientHomologyIso_naturality.{v, w} f.hom.τ₂ n
      · exact discreteCoefficientHomologyIso_naturality.{v, w} f.hom.τ₃ n
      · exact discreteCoefficientHomologyIso_naturality.{v, w} f.hom.τ₁ (n + 1)
      · exact discreteCoefficientHomologyIso_naturality.{v, w} f.hom.τ₂ (n + 1)
      · exact discreteCoefficientHomologyIso_naturality.{v, w} f.hom.τ₃ (n + 1))

/-- The exact-window comparison retains the original comparison morphism. -/
@[simp]
theorem discreteCoefficientExactWindowNatIso_hom_app_hom
    (G : ProfiniteGrp.{v}) (n : ℕ) (S : DiscreteCoefficientExactSequences.{v, w} G) :
    ((discreteCoefficientExactWindowNatIso.{v, w} G n).hom.app S).hom =
      (discreteCoefficientLongSequenceIso.{v, w} S.obj S.property n).hom :=
  rfl

/-- The connecting maps are a natural transformation from third-term cohomology
in degree n to first-term cohomology in degree n+1 on exact coefficient sequences. -/
def discreteCoefficientConnectingNatTrans (G : ProfiniteGrp.{v}) (n : ℕ) :
    (discreteCoefficientExactProperty.{v, w} G).ι ⋙ ShortComplex.π₃ ⋙
        discreteCoefficientCohomologyFunctor.{v, w} G n ⟶
      (discreteCoefficientExactProperty.{v, w} G).ι ⋙ ShortComplex.π₁ ⋙
        discreteCoefficientCohomologyFunctor.{v, w} G (n + 1) where
  app S := discreteCoefficientConnecting.{v, w} S.obj S.property n
  naturality S T f :=
    (discreteCoefficientConnecting_naturality.{v, w} f.hom S.property T.property n).symm

/-- The coefficient-natural connecting transformation has the original boundary
as its component. -/
@[simp]
theorem discreteCoefficientConnectingNatTrans_app
    (G : ProfiniteGrp.{v}) (n : ℕ) (S : DiscreteCoefficientExactSequences.{v, w} G) :
    (discreteCoefficientConnectingNatTrans.{v, w} G n).app S =
      discreteCoefficientConnecting.{v, w} S.obj S.property n :=
  rfl

/-- The natural homology comparisons intertwine the continuous connecting
transformation with the native cochain-homology connecting transformation. -/
theorem discreteCoefficientConnectingNatTrans_comparison
    (G : ProfiniteGrp.{v}) (n : ℕ) :
    discreteCoefficientConnectingNatTrans.{v, w} G n ≫
        (Functor.isoWhiskerLeft
          ((discreteCoefficientExactProperty.{v, w} G).ι ⋙ ShortComplex.π₁)
          (discreteCoefficientHomologyNatIso.{v, w} G (n + 1))).hom =
      (Functor.isoWhiskerLeft
        ((discreteCoefficientExactProperty.{v, w} G).ι ⋙ ShortComplex.π₃)
        (discreteCoefficientHomologyNatIso.{v, w} G n)).hom ≫
        whiskerLeft (discreteCoefficientShortExactCochainFunctor.{v, w} G)
          (HomologicalComplex.HomologySequence.δNatTrans
            n (n + 1) (discreteCoefficientUpRel n)) := by
  apply NatTrans.ext
  intro S
  exact discreteCoefficientConnecting_comparison.{v, w} S.obj S.property n

end ContinuousCohomology
