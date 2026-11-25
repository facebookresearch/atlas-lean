/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.StructuralDeRhamPeriodSources
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Teichmuller

/-!
# Original regular completion and residue-qualified structural Witt scalars

The original regular ring is the sheafified p-inversion of the ORIGINAL
positive ring. Its map to the completed regular ring is constructed from
that p-inversion comparison and the native positive completion unit.
Structural Witt scalars are native coefficientwise Witt maps of the
actual residue field into the original tilt. All tilt projections are
fixed by the Cohen/Teichmuller positive scalar units and inverse
Frobenius on the perfect residue field.

Reference: Scholze, arXiv:1205.3463v2, Definition 6.8.
Native Mathlib Witt vectors, perfect rings and sheaf maps: Apache 2.0,
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.WittStructuralScalarBindings

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry.GeneralPadicCoefficientFields
open SheafScalarQuotients SheafWittSource UntiltingSheafSources
open SheafKernelCompletion StructuralDeRhamPeriodSources

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J CommRingCat.{1}] (p : ℕ) [Fact p.Prime]
  (O Rplus : Sheaf J CommRingCat.{1}) (positiveInclusion : Rplus ⟶ O)

/-- This is a source comparison for the original uncompleted regular ring, before theta completion. -/
structure RegularLocalizationSource where
  iso : localizeP p Rplus ≅ O
  unit_source : localizePUnit p Rplus ≫ iso.hom = positiveInclusion

namespace RegularLocalizationSource

variable (L : RegularLocalizationSource p O Rplus positiveInclusion)

/-- The actual original-to-completed map, from the native completion and p-inversion units. -/
def originalTheta : O ⟶ completedRegular p Rplus :=
  L.iso.inv ≫ localizePMap p
    (completionUnit Rplus (modP p Rplus) (modPUnit p Rplus))

end RegularLocalizationSource

variable (K : BaseField p)

/-- The Cohen embedding lands in the actual ring of integers; all p-adic finite coordinates are fixed. -/
structure CohenWittSource where
  embedding : WittVector p (BaseField.residueField p K) →+* BaseField.integralRing p K
  residue : ∀ w, BaseField.reduction p K (embedding w) = w.coeff 0
  adic_bound : ∀ (w z : WittVector p (BaseField.residueField p K)) (n : ℕ),
    (∀ i : ℕ, i < n → w.coeff i = z.coeff i) →
      ‖((embedding w : BaseField.integralRing p K) : BaseField.carrier p K) -
        ((embedding z : BaseField.integralRing p K) : BaseField.carrier p K)‖ ≤
      ‖(p : BaseField.carrier p K)‖ ^ n

/-- The positive scalar is analytically qualified against this actual Cohen embedding separately.
Every residue coefficient and every native tilt projection is fixed here. -/
structure ResidueScalarSource where
  positive : constantWitt p K ⟶ Rplus
  residue : ∀ U : Cᵒᵖ, BaseField.residueField p K →+* (tilt p Rplus).obj.obj U
  natural : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (r : BaseField.residueField p K),
    ((tilt p Rplus).obj.map f).hom (residue U r) = residue V r
  projection_source : ∀ (U : Cᵒᵖ) (r : BaseField.residueField p K) (n : ℕ),
    (((tiltProjection p Rplus n).hom.app U).hom) (residue U r) =
      (((modPUnit p Rplus).hom.app U).hom)
        (((positive.hom.app U).hom)
          (((toSheafify J ((Functor.const Cᵒᵖ).obj
            (CommRingCat.of (ULift.{1} (WittVector p (BaseField.residueField p K)))))).app U).hom
              (ULift.up (WittVector.teichmuller p
                ((iterateFrobeniusEquiv (BaseField.residueField p K) p n).symm r)))))

namespace ResidueScalarSource

variable (S : ResidueScalarSource p Rplus K)

/-- Native coefficientwise Witt map of the actual residue scalar. -/
def rawWitt : ((Functor.const Cᵒᵖ).obj
    (CommRingCat.of (ULift.{1} (WittVector p (BaseField.residueField p K))))) ⟶
      wittPresheaf p (tilt p Rplus) where
  app U := CommRingCat.ofHom
    ((WittVector.map (p := p) (S.residue U)).comp
      { toFun := ULift.down
        map_one' := rfl
        map_mul' _ _ := rfl
        map_zero' := rfl
        map_add' _ _ := rfl })
  naturality {U V} f := by
    ext w
    apply WittVector.ext
    intro n
    exact (S.natural f (w.down.coeff n)).symm

def toInf : constantWitt p K ⟶ inf p Rplus :=
  ((sheafificationAdjunction J CommRingCat.{1}).homEquiv
    ((Functor.const Cᵒᵖ).obj
      (CommRingCat.of (ULift.{1} (WittVector p (BaseField.residueField p K)))))
    (inf p Rplus)).symm
      (S.rawWitt ≫ toSheafify J (wittPresheaf p (tilt p Rplus)))

def toRationalInf : constantWitt p K ⟶ rationalInf p Rplus :=
  S.toInf ≫ localizePUnit p (inf p Rplus)

def toOriginal : constantWitt p K ⟶ O := S.positive ≫ positiveInclusion

/-- This source proof concerns only the original scalar square, not a higher comparison. -/
def ScalarSquare (L : RegularLocalizationSource p O Rplus positiveInclusion)
    (A : UntiltingData p Rplus) : Prop :=
  toOriginal (p := p) (O := O) (Rplus := Rplus) (positiveInclusion := positiveInclusion)
    (K := K) (S := S) ≫ L.originalTheta = S.toRationalInf ≫ A.rationalTheta

/-- The structural source is built from the specified ORIGINAL scalar maps. -/
def structuralScalars (L : RegularLocalizationSource p O Rplus positiveInclusion)
    (A : UntiltingData p Rplus)
    (h : ScalarSquare (p := p) (O := O) (Rplus := Rplus) (positiveInclusion := positiveInclusion)
      (K := K) (S := S) L A) :
    WittScalarSource p K O Rplus A where
  toOriginal := toOriginal (p := p) (O := O) (Rplus := Rplus) (positiveInclusion := positiveInclusion)
    (K := K) (S := S)
  toInf := S.toRationalInf
  originalTheta := L.originalTheta
  scalar_square := h

end ResidueScalarSource

end MathlibExt.CategoryTheory.WittStructuralScalarBindings
