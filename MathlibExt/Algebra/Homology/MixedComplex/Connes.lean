/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Functor.OfSequence
public import MathlibExt.Algebra.Homology.ConnesSBI
public import MathlibExt.Algebra.Homology.MixedComplex.Basic
public import MathlibExt.Algebra.Homology.PartialTotalCokernel
public import MathlibExt.Algebra.Homology.PartialTotalCoordinates
public import MathlibExt.Algebra.Homology.Embedding.DownNatToIntShift
public import MathlibExt.Algebra.Homology.HomologyDegreeTransport
public import MathlibExt.Algebra.Homology.PartialTotalSuccessor
public import MathlibExt.Algebra.Homology.TotalComplexDownNat

/-!
# Connes bicomplexes and SBI data

Connes bicomplex data specify the component maps, finite-diagonal totals
and SBI maps of a mixed complex. Tail comparisons use even translations
of integer chain complexes. The interfaces record their component
identifications and cofinal tail maps.
-/

@[expose] public section

namespace MixedComplex

open CategoryTheory Limits Opposite
open scoped ZeroObject

universe w v u

/-- Degree `n` of the underlying chain complex. This is a reducible notation
bridge for the component formulas below, not a second mixed-complex object. -/
abbrev mixedObject {A : Type u} [Category.{w} A] [Preadditive A]
    (M : MixedComplex A) (n : ℕ) : A :=
  M.underlying.X n

/-- The degree-`n` differential of the underlying chain complex. -/
abbrev mixedDifferential {A : Type u} [Category.{w} A] [Preadditive A]
    (M : MixedComplex A) (n : ℕ) :
    mixedObject M (n + 1) ⟶ mixedObject M n :=
  M.underlying.d (n + 1) n

/-- The chain complex `(M,b)` underlying a mixed complex in any
preadditive category. -/
noncomputable abbrev genericMixedChainComplex
    {A : Type u} [Category.{w} A] [Preadditive A]
    (M : MixedComplex A) : ChainComplex A ℕ :=
  (MixedComplex.underlyingFunctor A).obj M

/-- Actual homology of the underlying complex in an arbitrary abelian
category. -/
noncomputable abbrev genericMixedHomology
    {A : Type u} [Category.{w} A] [Abelian A]
    (M : MixedComplex A) (n : ℕ) : A :=
  (genericMixedChainComplex M).homology n

/-- A fully characterized Connes bicomplex over an arbitrary preadditive
category. The stored vertical differential is `(-1)^p b`; native totalization
inserts the second sign to recover the usual Connes differential. -/
structure ConnesDoubleData
    {A : Type u} [Category.{w} A] [Preadditive A]
    (M : MixedComplex A) where
  /-- The signed first-quadrant bicomplex. -/
  K : HomologicalComplex₂ A (ComplexShape.down ℕ)
    (ComplexShape.down ℕ)
  /-- Identification of each supported cell with `M_(q-p)`. -/
  objIso : ∀ (p q : ℕ) (_h : p ≤ q),
    (K.X p).X q ≅ mixedObject M (q - p)
  isZero : ∀ (p q : ℕ) (_h : q < p), IsZero ((K.X p).X q)
  vertical_spec : ∀ (p q : ℕ) (h : p ≤ q) (h' : p ≤ q + 1),
    (objIso p (q + 1) h').hom ≫
        eqToHom (congrArg (mixedObject M)
          (by omega : q + 1 - p = q - p + 1)) ≫
        (((-1 : ℤ) ^ p) • mixedDifferential M (q - p)) =
      (K.X p).d (q + 1) q ≫ (objIso p q h).hom
  horizontal_spec : ∀ (p q : ℕ) (h : p + 1 ≤ q) (h' : p ≤ q),
    (objIso (p + 1) q h).hom ≫ M.B (q - (p + 1)) ≫
        eqToHom (congrArg (mixedObject M)
          (by omega : q - (p + 1) + 1 = q - p)) =
      (K.d (p + 1) p).f q ≫ (objIso p q h').hom

/-! The following constructions give the ordinary Connes total and SBI maps
in every abelian category. -/

section GenericConnes

variable {A : Type u} [Category.{w} A] [Abelian A]
variable {M : MixedComplex A}

/-- The ordinary finite-diagonal total of the generic Connes bicomplex. -/
noncomputable abbrev genericMixedConnesTotal
    (D : ConnesDoubleData M) : ChainComplex A ℕ :=
  D.K.total (ComplexShape.down ℕ)

/-- The column-zero partial total of the generic Connes bicomplex. -/
noncomputable abbrev genericMixedFirstColumn
    (D : ConnesDoubleData M) : ChainComplex A ℕ :=
  D.K.partialTotal 0

/-- The literal inclusion of the first column into the generic total. -/
noncomputable abbrev genericMixedFirstColumnι
    (D : ConnesDoubleData M) :
    genericMixedFirstColumn D ⟶ genericMixedConnesTotal D :=
  D.K.partialTotalι 0

/-- The cokernel of the generic first-column inclusion. -/
noncomputable abbrev genericMixedConnesTail
    (D : ConnesDoubleData M) : ChainComplex A ℕ :=
  cokernel (genericMixedFirstColumnι D)

/-- The literal column/cokernel short complex in an arbitrary abelian
category. -/
noncomputable abbrev genericMixedConnesShortComplex
    (D : ConnesDoubleData M) :
    ShortComplex (ChainComplex A ℕ) :=
  D.K.partialTotalCokernelShortComplex 0

theorem genericMixedConnesShortComplex_shortExact
    (D : ConnesDoubleData M) :
    (genericMixedConnesShortComplex D).ShortExact := by
  exact D.K.partialTotalCokernelShortExact 0

/-- Canonical component of the generic column-zero inclusion. -/
noncomputable def genericMixedColumnιComponent
    (D : ConnesDoubleData M) (q : ℕ) :
    mixedObject M q ⟶ (genericMixedFirstColumn D).X q := by
  exact (D.objIso 0 q (Nat.zero_le q)).inv ≫
    D.K.partialTotalComponent 0 (0 : Fin 1) q q (Nat.zero_add q)

/-- Source coordinate for the generic two-column tail translation. -/
noncomputable def genericMixedTailSourceComponent
    (D : ConnesDoubleData M) (p q : ℕ) :
    (D.K.X (p + 1)).X (q + 1) ⟶
      ((genericMixedConnesTail D).extend
        (ComplexShape.embeddingDownNatToIntShift 0)).X
          (2 + ((p + q : ℕ) : ℤ)) := by
  exact D.K.partialTotalCokernelGenerator 0 0 (p + 1) (q + 1)
    (p + q + 2) (by omega) (2 + ((p + q : ℕ) : ℤ)) (by
      rw [ComplexShape.embeddingDownNatToIntShift_f]
      push_cast
      omega)

/-- Target coordinate for the generic two-column tail translation. -/
noncomputable def genericMixedTailTargetComponent
    (D : ConnesDoubleData M) (p q : ℕ) (h : p ≤ q) :
    (D.K.X (p + 1)).X (q + 1) ⟶
      ((genericMixedConnesTotal D).extend
        (ComplexShape.embeddingDownNatToIntShift 2)).X
          (2 + ((p + q : ℕ) : ℤ)) :=
  (D.objIso (p + 1) (q + 1) (by omega)).hom ≫
    eqToHom (congrArg (mixedObject M)
      (by omega : q + 1 - (p + 1) = q - p)) ≫
    (D.objIso p q h).inv ≫
    D.K.ιTotal (ComplexShape.down ℕ) p q (p + q) rfl ≫
    (HomologicalComplex.extendDownNatToIntShiftXIso
      (genericMixedConnesTotal D) 2 (p + q)).inv

/-- Cyclic-homology and SBI data specified by chain comparisons with prescribed
components. The homology maps are induced by the total, inclusion, quotient
and connecting morphism. -/
structure GenericMixedCyclicData (M : MixedComplex A) where
  /-- The component-characterized Connes bicomplex. -/
  model : ConnesDoubleData M
  /-- The canonical comparison from `(M,b)` to column zero. -/
  columnMap : genericMixedChainComplex M ⟶
    genericMixedFirstColumn model
  columnMap_spec : ∀ q : ℕ,
    columnMap.f q = genericMixedColumnιComponent model q
  [columnMapQuasiIso : QuasiIso columnMap]
  /-- The chain-level translation from the column-zero quotient to the
  total shifted by two. -/
  tailMap :
    (genericMixedConnesTail model).extend
        (ComplexShape.embeddingDownNatToIntShift 0) ⟶
      (genericMixedConnesTotal model).extend
        (ComplexShape.embeddingDownNatToIntShift 2)
  [tailMapIsIso : IsIso tailMap]
  tailMap_spec : ∀ (p q : ℕ) (h : p ≤ q),
    genericMixedTailSourceComponent model p q ≫
      tailMap.f (2 + ((p + q : ℕ) : ℤ)) =
        genericMixedTailTargetComponent model p q h

/-- The general chain-level SBI presentation underlying generic mixed
cyclic data. -/
noncomputable abbrev GenericMixedCyclicData.toConnesSBIPresentation
    (MC : GenericMixedCyclicData M) :
    ConnesSBIPresentation (A := A) where
  ordinary := genericMixedChainComplex M
  shortComplex := genericMixedConnesShortComplex MC.model
  shortExact := genericMixedConnesShortComplex_shortExact MC.model
  ordinaryComparison := MC.columnMap
  ordinaryComparisonQuasiIso := MC.columnMapQuasiIso
  tailIso := by
    let _ := MC.tailMapIsIso
    exact asIso MC.tailMap

namespace GenericMixedCyclicData

/-- Generic cyclic homology, defined as homology of the total. -/
noncomputable abbrev HC (MC : GenericMixedCyclicData M) (n : ℕ) : A :=
  (genericMixedConnesTotal MC.model).homology n

/-- Homology comparison induced by the column map. -/
noncomputable def hIso (MC : GenericMixedCyclicData M) (n : ℕ) :
    (genericMixedChainComplex M).homology n ≅
      (genericMixedFirstColumn MC.model).homology n :=
  MC.toConnesSBIPresentation.hIso n

/-- Homology comparison induced by the tail map with its prescribed components. -/
noncomputable def tailHomologyIso
    (MC : GenericMixedCyclicData M) (n : ℕ) :
    (genericMixedConnesTail MC.model).homology (n + 2) ≅ MC.HC n :=
  MC.toConnesSBIPresentation.tailHomologyIso n

/-- The generic SBI inclusion map. -/
noncomputable def I (MC : GenericMixedCyclicData M) (n : ℕ) :
    (genericMixedChainComplex M).homology n ⟶ MC.HC n :=
  MC.toConnesSBIPresentation.I n

/-- The generic SBI periodicity map. -/
noncomputable def S (MC : GenericMixedCyclicData M) (n : ℕ) :
    MC.HC (n + 2) ⟶ MC.HC n :=
  MC.toConnesSBIPresentation.S n

/-- The generic SBI connecting map. -/
noncomputable def B (MC : GenericMixedCyclicData M) (n : ℕ) :
    MC.HC n ⟶ (genericMixedChainComplex M).homology (n + 1) :=
  MC.toConnesSBIPresentation.B n

@[reassoc]
theorem S_comp_B (MC : GenericMixedCyclicData M) (n : ℕ) :
    MC.S n ≫ MC.B n = 0 := by
  simpa only [S, B] using MC.toConnesSBIPresentation.S_comp_B n

@[reassoc]
theorem B_comp_I (MC : GenericMixedCyclicData M) (n : ℕ) :
    MC.B n ≫ MC.I (n + 1) = 0 := by
  simpa only [B, I] using MC.toConnesSBIPresentation.B_comp_I n

@[reassoc]
theorem I_comp_S (MC : GenericMixedCyclicData M) (n : ℕ) :
    MC.I (n + 2) ≫ MC.S n = 0 := by
  simpa only [I, S] using MC.toConnesSBIPresentation.I_comp_S n

/-- Exactness at the `HC_n` term of the generic SBI sequence. -/
theorem exact_SB (MC : GenericMixedCyclicData M) (n : ℕ) :
    (ShortComplex.mk (MC.S n) (MC.B n) (MC.S_comp_B n)).Exact := by
  simpa only [S, B] using MC.toConnesSBIPresentation.exact_SB n

/-- Exactness at the `H_(n+1)(M)` term of the generic SBI sequence. -/
theorem exact_BI (MC : GenericMixedCyclicData M) (n : ℕ) :
    (ShortComplex.mk (MC.B n) (MC.I (n + 1))
      (MC.B_comp_I n)).Exact := by
  simpa only [B, I] using MC.toConnesSBIPresentation.exact_BI n

/-- Exactness at the `HC_(n+2)` term of the generic SBI sequence. -/
theorem exact_IS (MC : GenericMixedCyclicData M) (n : ℕ) :
    (ShortComplex.mk (MC.I (n + 2)) (MC.S n)
      (MC.I_comp_S n)).Exact := by
  simpa only [I, S] using MC.toConnesSBIPresentation.exact_IS n

/-- The homology-level SBI diagram of generic mixed cyclic data. -/
noncomputable abbrev sbiDiagram (MC : GenericMixedCyclicData M) :
    NatSBIDiagram (A := A) :=
  MC.toConnesSBIPresentation.sbiDiagram

/-- Exactness of the homology-level SBI diagram. -/
theorem sbiDiagram_exact (MC : GenericMixedCyclicData M) :
    MC.sbiDiagram.Exact :=
  MC.toConnesSBIPresentation.sbiDiagram_exact

/-- Homology of the Connes tail vanishes in degrees zero and one. -/
theorem isZero_tailHomology_of_lt_two (MC : GenericMixedCyclicData M)
    (n : ℕ) (hn : n < 2) :
    IsZero ((genericMixedConnesTail MC.model).homology n) :=
  MC.toConnesSBIPresentation.isZero_tailHomology_of_lt_two n hn

/-- The degree-zero SBI inclusion is an isomorphism. -/
theorem isIso_I_zero (MC : GenericMixedCyclicData M) : IsIso (MC.I 0) :=
  MC.toConnesSBIPresentation.isIso_I_zero

/-- The degree-one SBI inclusion is an epimorphism. -/
theorem epi_I_one (MC : GenericMixedCyclicData M) : Epi (MC.I 1) :=
  MC.toConnesSBIPresentation.epi_I_one

/-- Connective boundary conditions of the homology-level SBI diagram. -/
theorem sbiDiagram_connectiveBoundary (MC : GenericMixedCyclicData M) :
    MC.sbiDiagram.ConnectiveBoundary :=
  MC.toConnesSBIPresentation.sbiDiagram_connectiveBoundary

end GenericMixedCyclicData

end GenericConnes

/-! ### Even translation and cofinal tails -/

section EvenTranslation

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Translation down by two integer chain degrees. Because the translation
is even, its differential carries no Koszul sign. -/
abbrev chainTranslateByNegTwo (K : ChainComplex C ℤ) : ChainComplex C ℤ where
  X n := K.X (n + 2)
  d i j := K.d (i + 2) (j + 2)
  shape i j hij := K.shape (i + 2) (j + 2) (by
    intro h
    apply hij
    change j + 1 = i
    change j + 2 + 1 = i + 2 at h
    omega)
  d_comp_d' i j k _ _ := K.d_comp_d (i + 2) (j + 2) (k + 2)

/-- Translation of a chain map down by two degrees. -/
abbrev chainTranslateByNegTwoMap {K L : ChainComplex C ℤ} (f : K ⟶ L) :
    chainTranslateByNegTwo K ⟶ chainTranslateByNegTwo L where
  f n := f.f (n + 2)
  comm' i j _ := f.comm (i + 2) (j + 2)

/-- The even translation functor on integer chain complexes. -/
abbrev chainTranslateByNegTwoFunctor :
    ChainComplex C ℤ ⥤ ChainComplex C ℤ where
  obj := chainTranslateByNegTwo
  map := chainTranslateByNegTwoMap
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp]
private theorem chainTranslateByNegTwoFunctor_obj_X
    (K : ChainComplex C ℤ) (n : ℤ) :
    ((chainTranslateByNegTwoFunctor : ChainComplex C ℤ ⥤ _).obj K).X n =
      K.X (n + 2) := rfl

@[simp]
private theorem chainTranslateByNegTwoFunctor_map_f
    {K L : ChainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    ((chainTranslateByNegTwoFunctor : ChainComplex C ℤ ⥤ _).map f).f n =
      f.f (n + 2) := rfl

end EvenTranslation

section EvenTranslationHomology

variable {D : Type u} [Category.{v} D] [Abelian D]

/-- Homology of an even translated complex in degree `n` is homology of the
original complex in degree `n+2`. -/
noncomputable def chainTranslateByNegTwoHomologyIso
    (K : ChainComplex D ℤ) (n : ℤ) :
    (chainTranslateByNegTwo K).homology n ≅ K.homology (n + 2) :=
  ShortComplex.homologyMapIso (by
    let hp : (ComplexShape.down ℤ).prev n + 2 =
        (ComplexShape.down ℤ).prev (n + 2) := by
      simp
      omega
    let hn : (ComplexShape.down ℤ).next n + 2 =
        (ComplexShape.down ℤ).next (n + 2) := by
      simp
      omega
    refine ShortComplex.isoMk
      (K.XIsoOfEq hp) (Iso.refl _) (K.XIsoOfEq hn) ?_ ?_
    · change (K.XIsoOfEq hp).hom ≫
          K.d ((ComplexShape.down ℤ).prev (n + 2)) (n + 2) =
        K.d ((ComplexShape.down ℤ).prev n + 2) (n + 2) ≫ 𝟙 _
      rw [Category.comp_id]
      exact K.XIsoOfEq_hom_comp_d hp (n + 2)
    · change 𝟙 _ ≫ K.d (n + 2) ((ComplexShape.down ℤ).next (n + 2)) =
        K.d (n + 2) ((ComplexShape.down ℤ).next n + 2) ≫
          (K.XIsoOfEq hn).hom
      rw [Category.id_comp]
      exact (K.d_comp_XIsoOfEq_hom hn (n + 2)).symm)

variable [HasLimitsOfShape ℕᵒᵖ D]

/-- Evaluation after even translation agrees with evaluation two degrees
later. -/
abbrev chainTranslateByNegTwoEvalIso
    (F : ℕᵒᵖ ⥤ ChainComplex D ℤ) (n : ℤ) :
    (F ⋙ chainTranslateByNegTwoFunctor) ⋙
        HomologicalComplex.eval D (ComplexShape.down ℤ) n ≅
      F ⋙ HomologicalComplex.eval D (ComplexShape.down ℤ) (n + 2) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

omit [HasLimitsOfShape ℕᵒᵖ D] in
@[simp]
theorem chainTranslateByNegTwoEvalIso_hom_app
    (F : ℕᵒᵖ ⥤ ChainComplex D ℤ) (n : ℤ) (p : ℕᵒᵖ) :
    (chainTranslateByNegTwoEvalIso F n).hom.app p = 𝟙 _ := rfl

/-- Degree component of the canonical comparison between the limit of an
even-translated tower and the even translation of its limit. -/
noncomputable def limitChainTranslateByNegTwoXIso
    (F : ℕᵒᵖ ⥤ ChainComplex D ℤ) (n : ℤ) :
    (limit (F ⋙ chainTranslateByNegTwoFunctor)).X n ≅
      (limit F).X (n + 2) :=
  preservesLimitIso (HomologicalComplex.eval D (ComplexShape.down ℤ) n)
      (F ⋙ chainTranslateByNegTwoFunctor) ≪≫
    HasLimit.isoOfNatIso (chainTranslateByNegTwoEvalIso F n) ≪≫
    (preservesLimitIso
      (HomologicalComplex.eval D (ComplexShape.down ℤ) (n + 2)) F).symm

@[reassoc]
theorem limitChainTranslateByNegTwoXIso_hom_π
    (F : ℕᵒᵖ ⥤ ChainComplex D ℤ) (n : ℤ) (p : ℕᵒᵖ) :
    (limitChainTranslateByNegTwoXIso F n).hom ≫
        (limit.π F p).f (n + 2) =
      (limit.π (F ⋙ chainTranslateByNegTwoFunctor) p).f n := by
  let En := HomologicalComplex.eval D (ComplexShape.down ℤ) n
  let En2 := HomologicalComplex.eval D (ComplexShape.down ℤ) (n + 2)
  let A := preservesLimitIso En (F ⋙ chainTranslateByNegTwoFunctor)
  let B := HasLimit.isoOfNatIso (chainTranslateByNegTwoEvalIso F n)
  let E := preservesLimitIso En2 F
  have hE : E.inv ≫ (limit.π F p).f (n + 2) =
      limit.π (F ⋙ En2) p := by
    simpa [E, En2] using preservesLimitIso_inv_π En2 F p
  have hB : B.hom ≫ limit.π (F ⋙ En2) p =
      limit.π ((F ⋙ chainTranslateByNegTwoFunctor) ⋙ En) p := by
    dsimp [B, En, En2]
    rw [HasLimit.isoOfNatIso_hom_π,
      chainTranslateByNegTwoEvalIso_hom_app, Category.comp_id]
  have hA : A.hom ≫
      limit.π ((F ⋙ chainTranslateByNegTwoFunctor) ⋙ En) p =
        (limit.π (F ⋙ chainTranslateByNegTwoFunctor) p).f n := by
    dsimp [A, En]
    exact preservesLimitIso_hom_π En (F ⋙ chainTranslateByNegTwoFunctor) p
  change (A ≪≫ B ≪≫ E.symm).hom ≫ (limit.π F p).f (n + 2) = _
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hE, hB]
  exact hA

/-- Canonical chain isomorphism: countable inverse limits commute with the
even degree translation. -/
noncomputable def limitChainTranslateByNegTwoIso
    (F : ℕᵒᵖ ⥤ ChainComplex D ℤ) :
    limit (F ⋙ chainTranslateByNegTwoFunctor) ≅
      chainTranslateByNegTwo (limit F) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (limitChainTranslateByNegTwoXIso F) ?_
  intro i j hij
  apply (cancel_mono (preservesLimitIso
    (HomologicalComplex.eval D (ComplexShape.down ℤ) (j + 2)) F).hom).1
  apply limit.hom_ext
  intro p
  simp only [Category.assoc, preservesLimitIso_hom_π]
  let eᵢ := limitChainTranslateByNegTwoXIso F i
  let eⱼ := limitChainTranslateByNegTwoXIso F j
  let πF := limit.π F p
  let πT := limit.π (F ⋙ chainTranslateByNegTwoFunctor) p
  have hi : eᵢ.hom ≫ πF.f (i + 2) = πT.f i :=
    limitChainTranslateByNegTwoXIso_hom_π F i p
  have hj : eⱼ.hom ≫ πF.f (j + 2) = πT.f j :=
    limitChainTranslateByNegTwoXIso_hom_π F j p
  have hF : πF.f (i + 2) ≫ (F.obj p).d (i + 2) (j + 2) =
      (limit F).d (i + 2) (j + 2) ≫ πF.f (j + 2) :=
    πF.comm (i + 2) (j + 2)
  have hT : πT.f i ≫ (chainTranslateByNegTwo (F.obj p)).d i j =
      (limit (F ⋙ chainTranslateByNegTwoFunctor)).d i j ≫ πT.f j :=
    πT.comm i j
  have hcalc :
      (eᵢ.hom ≫ (limit F).d (i + 2) (j + 2)) ≫ πF.f (j + 2) =
        ((limit (F ⋙ chainTranslateByNegTwoFunctor)).d i j ≫ eⱼ.hom) ≫
          πF.f (j + 2) := by
    calc
      (eᵢ.hom ≫ (limit F).d (i + 2) (j + 2)) ≫ πF.f (j + 2) =
          eᵢ.hom ≫ ((limit F).d (i + 2) (j + 2) ≫ πF.f (j + 2)) :=
        Category.assoc _ _ _
      _ = eᵢ.hom ≫ (πF.f (i + 2) ≫ (F.obj p).d (i + 2) (j + 2)) := by
        rw [hF]
      _ = (eᵢ.hom ≫ πF.f (i + 2)) ≫ (F.obj p).d (i + 2) (j + 2) := by
        rw [Category.assoc]
      _ = πT.f i ≫ (F.obj p).d (i + 2) (j + 2) := by rw [hi]
      _ = πT.f i ≫ (chainTranslateByNegTwo (F.obj p)).d i j := rfl
      _ = (limit (F ⋙ chainTranslateByNegTwoFunctor)).d i j ≫ πT.f j := hT
      _ = (limit (F ⋙ chainTranslateByNegTwoFunctor)).d i j ≫
          (eⱼ.hom ≫ πF.f (j + 2)) := by rw [hj]
      _ = ((limit (F ⋙ chainTranslateByNegTwoFunctor)).d i j ≫ eⱼ.hom) ≫
          πF.f (j + 2) := by rw [Category.assoc]
  simp only [HomologicalComplex.eval_map]
  simpa only [eᵢ, eⱼ, πF, Category.assoc] using hcalc

@[simp]
private theorem limitChainTranslateByNegTwoIso_hom_f
    (F : ℕᵒᵖ ⥤ ChainComplex D ℤ) (n : ℤ) :
    (limitChainTranslateByNegTwoIso F).hom.f n =
      (limitChainTranslateByNegTwoXIso F n).hom := rfl

@[simp]
private theorem limitChainTranslateByNegTwoIso_inv_f
    (F : ℕᵒᵖ ⥤ ChainComplex D ℤ) (n : ℤ) :
    (limitChainTranslateByNegTwoIso F).inv.f n =
      (limitChainTranslateByNegTwoXIso F n).inv := rfl

end EvenTranslationHomology

section SequentialTail

/-- Delete the initial object of an inverse sequence. -/
abbrev sequentialTailFunctor : ℕᵒᵖ ⥤ ℕᵒᵖ where
  obj n := op (n.unop + 1)
  map {_i _j} f :=
    (homOfLE (Nat.succ_le_succ (leOfHom f.unop))).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
private theorem sequentialTailFunctor_obj (n : ℕ) :
    sequentialTailFunctor.obj (op n) = op (n + 1) := rfl

@[simp]
private theorem sequentialTailFunctor_map_succ (n : ℕ) :
    sequentialTailFunctor.map (homOfLE (Nat.le_succ n)).op =
      (homOfLE (Nat.le_succ (n + 1))).op :=
  Subsingleton.elim _ _

/-- The one-stage tail of an inverse sequence. -/
abbrev sequentialTail {C : Type u} [Category.{v} C] (F : ℕᵒᵖ ⥤ C) :
    ℕᵒᵖ ⥤ C := sequentialTailFunctor ⋙ F

@[simp]
private theorem sequentialTail_map_succ {C : Type u} [Category.{v} C]
    (F : ℕᵒᵖ ⥤ C) (n : ℕ) :
    (sequentialTail F).map (homOfLE (Nat.le_succ n)).op =
      F.map (homOfLE (Nat.le_succ (n + 1))).op := rfl

variable {C : Type u} [Category.{v} C]

/-- Components of the cone from the tail limit to the original sequence. -/
noncomputable def sequentialTailConeApp
    (F : ℕᵒᵖ ⥤ C) [HasLimit (sequentialTail F)] :
    ∀ n : ℕ, limit (sequentialTail F) ⟶ F.obj (op n)
  | 0 => limit.π (sequentialTail F) (op 0) ≫
      F.map (homOfLE (Nat.le_succ 0)).op
  | n + 1 => limit.π (sequentialTail F) (op n)

theorem sequentialTailConeApp_naturality
    (F : ℕᵒᵖ ⥤ C) [HasLimit (sequentialTail F)] (n : ℕ) :
    sequentialTailConeApp F (n + 1) ≫
        F.map (homOfLE (Nat.le_succ n)).op =
      sequentialTailConeApp F n := by
  rcases n with _ | n
  · rfl
  · exact limit.w (sequentialTail F) (homOfLE (Nat.le_succ n)).op

/-- The cone from the tail limit to the original sequence. -/
noncomputable abbrev sequentialTailCone
    (F : ℕᵒᵖ ⥤ C) [HasLimit (sequentialTail F)] : Cone F where
  pt := limit (sequentialTail F)
  π := NatTrans.ofOpSequence (sequentialTailConeApp F) (by
    intro n
    simpa using (sequentialTailConeApp_naturality F n).symm)

/-- The canonical map from the tail limit to the original limit. -/
noncomputable def sequentialTailLimitToLimit
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] [HasLimit (sequentialTail F)] :
    limit (sequentialTail F) ⟶ limit F :=
  limit.lift F (sequentialTailCone F)

/-- The original limiting cone restricted to the one-stage tail. -/
noncomputable abbrev sequentialRestrictCone
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] : Cone (sequentialTail F) where
  pt := limit F
  π := NatTrans.ofOpSequence (fun n => limit.π F (op (n + 1))) (by
    intro n
    simp)

@[simp]
theorem sequentialRestrictCone_π_app
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] (n : ℕ) :
    (sequentialRestrictCone F).π.app (op n) =
      limit.π F (op (n + 1)) := rfl

/-- The canonical map from the original limit to the tail limit. -/
noncomputable def sequentialLimitToTailLimit
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] [HasLimit (sequentialTail F)] :
    limit F ⟶ limit (sequentialTail F) :=
  limit.lift (sequentialTail F) (sequentialRestrictCone F)

/-- Cofinal invariance of a sequential inverse limit after deleting the
initial stage. -/
noncomputable def sequentialLimitTailIso
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] [HasLimit (sequentialTail F)] :
    limit (sequentialTail F) ≅ limit F where
  hom := sequentialTailLimitToLimit F
  inv := sequentialLimitToTailLimit F
  hom_inv_id := by
    apply limit.hom_ext
    intro j
    obtain ⟨n⟩ := j
    unfold sequentialLimitToTailLimit
    rw [Category.assoc, limit.lift_π]
    change sequentialTailLimitToLimit F ≫ limit.π F (op (n + 1)) =
      𝟙 (limit (sequentialTail F)) ≫
        limit.π (sequentialTail F) (op n)
    unfold sequentialTailLimitToLimit
    rw [limit.lift_π]
    change limit.π (sequentialTail F) (op n) =
      𝟙 (limit (sequentialTail F)) ≫
        limit.π (sequentialTail F) (op n)
    simp only [Category.id_comp]
  inv_hom_id := by
    apply limit.hom_ext
    intro j
    obtain ⟨n⟩ := j
    rcases n with _ | n
    · unfold sequentialTailLimitToLimit
      rw [Category.assoc, limit.lift_π]
      change sequentialLimitToTailLimit F ≫
          (limit.π (sequentialTail F) (op 0) ≫
            F.map (homOfLE (Nat.le_succ 0)).op) =
        𝟙 (limit F) ≫ limit.π F (op 0)
      rw [← Category.assoc]
      rw [sequentialLimitToTailLimit, limit.lift_π]
      rw [sequentialRestrictCone_π_app]
      simpa only [Category.id_comp] using
        limit.w F (homOfLE (Nat.le_succ 0)).op
    · unfold sequentialTailLimitToLimit
      rw [Category.assoc, limit.lift_π]
      change sequentialLimitToTailLimit F ≫
          limit.π (sequentialTail F) (op n) =
        𝟙 (limit F) ≫ limit.π F (op (n + 1))
      rw [sequentialLimitToTailLimit, limit.lift_π]
      rw [sequentialRestrictCone_π_app]
      simp only [Category.id_comp]

@[reassoc]
theorem sequentialLimitTailIso_hom_π_zero
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] [HasLimit (sequentialTail F)] :
    (sequentialLimitTailIso F).hom ≫ limit.π F (op 0) =
      limit.π (sequentialTail F) (op 0) ≫
        F.map (homOfLE (Nat.le_succ 0)).op := by
  exact limit.lift_π (sequentialTailCone F) (op 0)

@[reassoc]
theorem sequentialLimitTailIso_hom_π_succ
    (F : ℕᵒᵖ ⥤ C) [HasLimit F] [HasLimit (sequentialTail F)] (n : ℕ) :
    (sequentialLimitTailIso F).hom ≫ limit.π F (op (n + 1)) =
      limit.π (sequentialTail F) (op n) := by
  exact limit.lift_π (sequentialTailCone F) (op (n + 1))

end SequentialTail

end MixedComplex
