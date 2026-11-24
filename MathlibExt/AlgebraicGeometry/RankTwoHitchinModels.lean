/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoHiggsModuliModels
public import MathlibExt.AlgebraicGeometry.ExpansionParameterModels

/-!
# The canonical-line Hitchin base and characteristic map

The affine base is the polynomial-coordinate scheme of the actual spaces
of global sections of K and K squared. Chosen bases only choose coordinates.
The universal coefficients are literal sums of the pulled basis sections.
The Hitchin morphism is fixed on every stable family by its actual framed
characteristic sections and native pullback-power comparison.

Source: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2,
Sections 1.2.2 and 1.3.1, equation (1.3.1). The canonical-line dimensions
are g and 3g-3, so the number of affine coordinates is 4g-3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RankTwoHitchinModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels GeometricHiggsFamilies
open CoherentCurveLinearSeries LineBundleTaskContracts RelativeLambdaReindexing
open scoped BigOperators

abbrev CanonicalSections (C : ComplexScheme) (n : ℕ) :=
  (sectionsFunctor C.hom).obj (power (canonicalLine C) n)

/-- Bases of the actual two spaces of canonical-line sections. -/
structure SectionBases (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] where
  one : Module.Basis (Fin (genus C.hom)) ℂ (CanonicalSections C 1)
  two : Module.Basis (Fin (3 * genus C.hom - 3)) ℂ (CanonicalSections C 2)

abbrev CoordinateIndex (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] :=
  Fin (genus C.hom) ⊕ Fin (3 * genus C.hom - 3)

abbrev CoordinateRing (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] := MvPolynomial (CoordinateIndex C) ℂ

def base (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] : ComplexScheme :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateRing C))))

def coordinate (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] (i : CoordinateIndex C) : Γ((base C).left, ⊤) :=
  (Scheme.ΓSpecIso (.of (CoordinateRing C))).inv.hom (MvPolynomial.X i)

/-- The dimension parameter is the number of actual section coordinates. -/
def baseDimension (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] : ℕ := Fintype.card (CoordinateIndex C)

theorem baseDimension_eq (C : ComplexScheme) [CurveSource C] :
    baseDimension C = 4 * genus C.hom - 3 := by
  have h := CurveSource.genusRange (C := C)
  simp only [baseDimension, CoordinateIndex, Fintype.card_sum, Fintype.card_fin]
  omega

def parameterCoefficient {C T : ComplexScheme} [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] (f : T ⟶ base C)
    (i : CoordinateIndex C) : Γ(T.left, ⊤) := f.left.appTop.hom (coordinate C i)

def relativeLinePower (C T : ComplexScheme) (n : ℕ) : (prod C T).left.Modules :=
  (Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj (power (canonicalLine C) n)

/-- Pull an actual global section by the native module adjunction unit. -/
def pulledBasisSection (C T : ComplexScheme) (n : ℕ) (s : CanonicalSections C n) :
    Γ(relativeLinePower C T n, ⊤) := by
  change ((Scheme.Modules.pullback (prod.fst : prod C T ⟶ C).left).obj
    (power (canonicalLine C) n)).val.obj (op ⊤)
  simpa [relativeLinePower] using pullSection (prod.fst : prod C T ⟶ C).left
    (power (canonicalLine C) n) ⊤ s

structure SectionPair (C T : ComplexScheme) where
  one : Γ(relativeLinePower C T 1, ⊤)
  two : Γ(relativeLinePower C T 2, ⊤)

/-- Evaluate the affine section coordinates on any coefficient scheme. -/
def parameterSections (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] (S : SectionBases C)
    (T : ComplexScheme) (f : T ⟶ base C) : SectionPair C T where
  one := ∑ i : Fin (genus C.hom),
    (prod.snd : prod C T ⟶ T).left.appTop.hom (parameterCoefficient f (.inl i)) •
      pulledBasisSection C T 1 (S.one i)
  two := ∑ i : Fin (3 * genus C.hom - 3),
    (prod.snd : prod C T ⟶ T).left.appTop.hom (parameterCoefficient f (.inr i)) •
      pulledBasisSection C T 2 (S.two i)

/-- Move a genuine characteristic coefficient to the pulled canonical power. -/
def characteristicOnBase (C T : ComplexScheme) (E : Family C T)
    (K : CharacteristicSections E)
    (P : PullbackPowers (prod.fst : prod C T ⟶ C).left) (n : ℕ) :
    Γ(relativeLinePower C T n, ⊤) :=
  (((P.comparison n).inv.app (canonicalLine C)).val.app (op ⊤)).hom
    (((K.coefficient n).val.app (op ⊤)).hom (1 : Γ((prod C T).left, ⊤)))

/-- The scaling map is fixed on every affine coordinate, with weights one and two. -/
structure BaseScaling (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] where
  map : prod (ExpansionParameterModels.affineLine ℂ) (base C) ⟶ base C
  one : ∀ i : Fin (genus C.hom),
    map.left.appTop.hom (coordinate C (.inl i)) =
      (prod.fst : prod (ExpansionParameterModels.affineLine ℂ) (base C) ⟶
        ExpansionParameterModels.affineLine ℂ).left.appTop.hom
        (ExpansionParameterModels.affineCoordinate ℂ) *
      (prod.snd : prod (ExpansionParameterModels.affineLine ℂ) (base C) ⟶ base C).left.appTop.hom
        (coordinate C (.inl i))
  two : ∀ i : Fin (3 * genus C.hom - 3),
    map.left.appTop.hom (coordinate C (.inr i)) =
      ((prod.fst : prod (ExpansionParameterModels.affineLine ℂ) (base C) ⟶
        ExpansionParameterModels.affineLine ℂ).left.appTop.hom
        (ExpansionParameterModels.affineCoordinate ℂ)) ^ 2 *
      (prod.snd : prod (ExpansionParameterModels.affineLine ℂ) (base C) ⟶ base C).left.appTop.hom
        (coordinate C (.inr i))

/-- The actual proper Hitchin morphism and its all-family coefficient normalization. -/
structure HitchinModel (C : ComplexScheme) [IsProperCurve C.hom]
    [HasConstantGlobalSections C.hom] (B : BaseChanges C)
    (M : ModuliModel C B) (S : SectionBases C) where
  map : M.scheme ⟶ base C
  proper : IsProper map.left
  baseVariety : PerverseSheaves.IsComplexVariety (base C)
  powers : ∀ T : ComplexScheme, PullbackPowers (prod.fst : prod C T ⟶ C).left
  characteristic : ∀ (T : ComplexScheme) (E : StableFamily C T), CharacteristicSections E.obj
  trace : ∀ (T : ComplexScheme) (E : StableFamily C T),
    (parameterSections C S T (M.classes.map T E ≫ map)).one =
      characteristicOnBase C T E.obj (characteristic T E) (powers T) 1
  determinant : ∀ (T : ComplexScheme) (E : StableFamily C T),
    (parameterSections C S T (M.classes.map T E ≫ map)).two =
      characteristicOnBase C T E.obj (characteristic T E) (powers T) 2
  scaling : BaseScaling C

end MathlibExt.AlgebraicGeometry.RankTwoHitchinModels
