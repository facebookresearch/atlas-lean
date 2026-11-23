/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells.Enveloping
import MathlibExt.AlgebraicTopology.ModelCategory.OperadicAcyclicCells.OrdinalSources
import MathlibExt.CategoryTheory.MorphismProperty.MappedCoproducts
import MathlibExt.CategoryTheory.SmallObject.Image

/-!
# Acyclicity of the entire original operadic free-J class

The enveloping-operad filtration proves couniversal weakness for actual free
attachments. The free functor handles arbitrary coproducts before forgetting.
The forgetful functor is used only on nonempty ordinal colimits, which it
actually creates. Mapping the caller's entire original history, followed by
the actual small-object retract, proves acyclicity of the unrestricted J-left
class under the source weak-transfinite hypothesis.
-/

set_option autoImplicit false
noncomputable section

universe uW v u us

open CategoryTheory Limits MorphismProperty SmallObject
open CategoryTheory.Operad CategoryTheory.Operad.Tensor
open CategoryTheory.Operad.Tensor.Enveloping
open CategoryTheory.OperadicOrbitCells

namespace HomotopicalAlgebra.OperadicTransfer

variable (S : SourceContext.{uW, v, u, us})

/-- Use the original finite tensor operations in the acyclic-cell construction. -/
local instance acyclicOriginalFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance acyclicOriginalTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} S.C :=
  S.finiteTensorPreservation
local instance acyclicOriginalProfiles (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C :=
  S.profileColimits d

/-- Read the original carrier at the original color. -/
def carrierAt (O : ColoredOperadObj S.W S.C) (d : S.W) : Algebra O ⥤ S.C :=
  Algebra.forget O ⋙ Pi.eval (fun _ : S.W => S.C) d

/-- The actual forgetful and evaluation functors preserve the source-sized filtered colimits. -/
theorem carrierAt_preservesFilteredColimits (O : ColoredOperadObj S.W S.C) (d : S.W)
    (T : Type us) [Category.{us} T] [IsFiltered T] :
    PreservesColimitsOfShape T (carrierAt S O d) := by
  let : HasColimitsOfShape T S.C := HasColimitsOfShape.of_essentiallySmall S.C T
  let : CreatesColimitsOfShape T (Algebra.forget O) := S.operadicCreatesFilteredColimits O
  let : PreservesColimitsOfShape T (Algebra.forget O) :=
    preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape (Algebra.forget O)
  let : PreservesColimitsOfShape T (Pi.eval (fun _ : S.W => S.C) d) :=
    preservesColimitsOfShape_of_natIso (piEquivalenceFunctorDiscreteCompEvaluationIso S.C d)
  dsimp only [carrierAt]
  infer_instance

/-- Every original nonempty principal segment is preserved at that same original color. -/
theorem carrierAt_preservesWellOrderContinuous (O : ColoredOperadObj S.W S.C) (d : S.W)
    (T : Type us) [LinearOrder T] [OrderBot T] :
    PreservesWellOrderContinuousOfShape T (carrierAt S O d) where
  preservesColimitsOfShape t ht := by
    let : Nonempty (Set.Iio t) := ⟨⟨⊥, ht.bot_lt⟩⟩
    exact carrierAt_preservesFilteredColimits S O d (Set.Iio t)

private theorem pointwiseTrivialCofibrations_stableCoproducts :
    IsStableUnderCoproducts.{us}
      (SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C)) := by
  let : ModelCategory (S.W → S.C) := SemiModel.ColorSource.pointwiseModelCategory S.C S.W
  rw [← SemiModel.ColorSource.trivialCofibrations_eq S.C S.W,
    ← fibrations_llp (S.W → S.C)]
  infer_instance

section WeakTransfinite

variable [(weakEquivalences S.C).IsStableUnderTransfiniteComposition.{us}]

/-- Every actual pushout of a whole original free trivial-cofibration map is couniversally weak. -/
theorem freePushout_underlying_couniversal
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) {K L : S.W → S.C} (x : K ⟶ L)
    (hx : ∀ d, trivialCofibrations S.C (x d)) {A B : Algebra O}
    (a : freeAlgebra O K ⟶ A) (b : freeAlgebra O L ⟶ B) (g : A ⟶ B)
    (sq : IsPushout a ((freeAlgebraFunctor O).map x) g b) (d : S.W) :
    couniversalWeakEquivalences S.C ((carrierAt S O d).map g) := by
  have ho := OperadicAcyclicCells.Attachments.actualOriginalOldLeg_weak_transfinite
    h O A x a hx
  let e := ho.1.isColimit.coconePointUniqueUpToIso sq.isColimit
  have he : OriginalAttachment.oldMap O A x a ≫ e.hom = g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom ho.1.isColimit sq.isColimit WalkingSpan.left
  let ae : Arrow.mk (OriginalAttachment.oldMap O A x a) ≅ Arrow.mk g :=
    Arrow.isoMk (Iso.refl A) e (by
      change 𝟙 A ≫ g = OriginalAttachment.oldMap O A x a ≫ e.hom
      exact (Category.id_comp g).trans he.symm)
  exact ((couniversalWeakEquivalences S.C).arrow_iso_iff
    ((carrierAt S O d).mapArrow.mapIso ae)).mp (ho.2 d)

/-- Arbitrary coproducts of literal free maps are handled by the actual source coproduct,
before the original algebra pushout is forgotten. -/
theorem freeTrivialCoproductPushouts_underlying_couniversal
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (d : S.W) :
    ((SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C)).strictMap
      (freeAlgebraFunctor O)).coproducts.{us}.pushouts ≤
        (couniversalWeakEquivalences S.C).inverseImage (carrierAt S O d) := by
  let : IsStableUnderCoproducts.{us}
      (SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C)) :=
    pointwiseTrivialCofibrations_stableCoproducts S
  let : (freeAlgebraFunctor O).IsLeftAdjoint := ⟨Algebra.forget O, ⟨S.operadicAdjunction O⟩⟩
  intro A B g hg
  obtain ⟨X, Y, q, a, b, hq, sq⟩ := hg
  have hFree := MorphismProperty.coproducts_strictMap_le_map
    (SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C))
    (freeAlgebraFunctor O) q hq
  obtain ⟨K, L, x, hx, ⟨χ⟩⟩ := hFree
  let s := Arrow.leftFunc.mapIso χ
  let t := Arrow.rightFunc.mapIso χ
  have hχ : s.hom ≫ q = (freeAlgebraFunctor O).map x ≫ t.hom := χ.hom.w
  have sq' : IsPushout (s.hom ≫ a) ((freeAlgebraFunctor O).map x) g (t.hom ≫ b) :=
    sq.of_iso' s (Iso.refl A) t (Iso.refl B)
      (by simp) hχ (by simp) (by simp)
  exact freePushout_underlying_couniversal S h O x hx
    (s.hom ≫ a) (t.hom ≫ b) g sq' d

/-- The actual source fibration equation makes every original supported J-map trivial. -/
theorem freeJCoproductPushouts_underlying_couniversal
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C) (d : S.W) :
    (freeGenerators S O J).coproducts.{us}.pushouts ≤
      (couniversalWeakEquivalences S.C).inverseImage (carrierAt S O d) := by
  let : ModelCategory (S.W → S.C) := SemiModel.ColorSource.pointwiseModelCategory S.C S.W
  have hj : SemiModel.ColorSource.colorGenerators S.C S.W J ≤
      SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C) := by
    rw [← SemiModel.ColorSource.trivialCofibrations_eq S.C S.W]
    exact SemiModel.ColorSource.colorJGenerators_le_trivialCofibrations S.C S.W J hJ
  exact (pushouts_monotone (coproducts_monotone
    (monotone_strictMap (freeAlgebraFunctor O) hj))).trans
      (freeTrivialCoproductPushouts_underlying_couniversal S h O d)

/-- The entire caller-supplied free-J history maps to a couniversal weak history,
with exactly its original stage functor, original endpoint and original inclusions. -/
def freeJCellMappedCouniversalHistory
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    {T : Type us} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Algebra O} {f : A ⟶ B}
    (c : ((freeGenerators S O J).coproducts.{us}).pushouts.TransfiniteCompositionOfShape T f)
    (d : S.W) :
    (couniversalWeakEquivalences S.C).TransfiniteCompositionOfShape T
      ((carrierAt S O d).map f) := by
  let : PreservesColimitsOfShape T (carrierAt S O d) :=
    carrierAt_preservesFilteredColimits S O d T
  let : PreservesWellOrderContinuousOfShape T (carrierAt S O d) :=
    carrierAt_preservesWellOrderContinuous S O d T
  exact (c.ofLE (freeJCoproductPushouts_underlying_couniversal S h O J hJ d)).map

/-- The original source weak-transfinite law closes that entire supplied free-J history. -/
theorem freeJCell_underlying_weak
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    {T : Type us} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Algebra O} {f : A ⟶ B}
    (c : ((freeGenerators S O J).coproducts.{us}).pushouts.TransfiniteCompositionOfShape T f)
    (d : S.W) : weakEquivalences S.C ((carrierAt S O d).map f) := by
  let : (couniversalWeakEquivalences S.C).IsStableUnderTransfiniteComposition.{us} :=
    couniversalWeakEquivalences_isStableUnderTransfiniteComposition
  exact couniversalWeakEquivalences_le_weakEquivalences _
    ((couniversalWeakEquivalences S.C).transfiniteCompositionsOfShape_le T _
      (freeJCellMappedCouniversalHistory S h O J hJ c d).mem)

/-- The actual relative free-J complex retains all labels and its supplied endpoint. -/
theorem freeJRelativeCellComplex_underlying_weak
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    {T : Type us} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Algebra O} {f : A ⟶ B}
    (c : RelativeCellComplex.{us} (fun _ : T => (freeGenerators S O J).homFamily) f)
    (d : S.W) : weakEquivalences S.C ((carrierAt S O d).map f) :=
  freeJCell_underlying_weak S h O J hJ
    (c.transfiniteCompositionOfShape' (fun s => s.i.2)) d

/-- The actual original small-object factor and its mapped retract prove the full,
unrestricted free-J left lifting class weak at every original color. -/
theorem freeJLeft_underlying_weak
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(freeGenerators S O J).IsCardinalForSmallObjectArgument κ] :
    (freeGenerators S O J).rlp.llp ≤ weakClass S O := by
  intro A B f hf d
  apply rlp_llp_le_inverseImage_of_cardinal_cells
    (freeGenerators S O J) (weakEquivalences S.C) (carrierAt S O d) κ
      (fun f c => freeJRelativeCellComplex_underlying_weak S h O J hJ c d) f hf

end WeakTransfinite

section CompactSources

/-- The actual coefficient-orbit cofibration cells, retaining their full couniversal condition. -/
def compactCellClass : MorphismProperty S.C :=
  couniversalWeakEquivalences S.C ⊓ OperadicAcyclicCells.cofibrationCells.{us, us} S.C

private theorem compactCellClass_stable
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hStrong : OperadicAcyclicCells.StrongAdmissibleGeneration.{us, us} S.C I) :
    (compactCellClass S).IsStableUnderTransfiniteComposition.{us} := by
  let P := OperadicAcyclicCells.cofibrationCells.{us, us} S.C
  let : P.IsStableUnderCobaseChange := OperadicAcyclicCells.cofibrationCells_stable.1
  let : P.IsStableUnderTransfiniteComposition.{us} :=
    OperadicAcyclicCells.cofibrationCells_stable.2.2
  exact couniversalIntersection_isStableUnderTransfiniteComposition_of_compact
    I P hI hStrong OperadicAcyclicCells.cofibrations_le_cofibrationCells

private theorem compactCellClass_respectsIso : (compactCellClass S).RespectsIso := by
  let : (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).IsStableUnderCobaseChange :=
    OperadicAcyclicCells.cofibrationCells_stable.1
  dsimp only [compactCellClass]
  infer_instance

/-- Compact source bounds close the same complete original free attachment,
without replacing its ordinal, endpoint or original color. -/
theorem originalAttachment_compactCellClass
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hStrong : OperadicAcyclicCells.StrongAdmissibleGeneration.{us, us} S.C I)
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (A : Algebra O)
    {K L : S.W → S.C} (x : K ⟶ L) (a : freeAlgebra O K ⟶ A)
    (hx : ∀ d, trivialCofibrations S.C (x d)) (d : S.W) :
    compactCellClass S ((OriginalAttachment.oldMap O A x a).hom d) := by
  let Q := compactCellClass S
  let : (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).IsStableUnderCobaseChange :=
    OperadicAcyclicCells.cofibrationCells_stable.1
  let : Q.IsStableUnderCobaseChange := by dsimp only [Q, compactCellClass]; infer_instance
  let hTrans : Q.IsStableUnderTransfiniteComposition.{us} :=
    compactCellClass_stable S I hI hStrong
  let : Q.IsStableUnderCoproducts.{us} :=
    @isStableUnderCoproducts_of_cobase_transfinite S.C inferInstance Q inferInstance
      hTrans
      (inferInstance : HasCoproducts.{us} S.C)
  let : Q.IsStableUnderTransfiniteComposition.{0} :=
    IsStableUnderTransfiniteComposition.shrink₀ (W := Q)
  have hc : (orbitGenerators (trivialCofibrations S.C)).isoClosure ≤
      couniversalWeakEquivalences S.C :=
    (isoClosure_le_iff _ _).2 h.generators_le
  have hp : (orbitGenerators (trivialCofibrations S.C)).isoClosure ≤
      OperadicAcyclicCells.cofibrationCells.{us, us} S.C :=
    (isoClosure_le_iff _ _).2 OperadicAcyclicCells.trivialOrbitGenerators_le_cofibrationCells
  have hg : (orbitGenerators (trivialCofibrations S.C)).isoClosure ≤ Q := le_inf hc hp
  let c := OperadicAcyclicCells.Attachments.evaluatedOriginalRelativeCellComplex O A x a d
  apply Q.transfiniteCompositionsOfShape_le ℕ _
  have hpush : (Q.coproducts.{us}).pushouts ≤ Q :=
    (pushouts_le_iff (P := Q.coproducts.{us}) (Q := Q)).2 (coproducts_le Q)
  exact ((c.transfiniteCompositionOfShape' (fun s => hg _
    (OperadicAcyclicCells.Attachments.occurringOriginalCell_mem O A x hx d s.j s.i))).ofLE hpush).mem

/-- The whole actual arbitrary free pushout belongs to the compact-source class. -/
theorem freePushout_underlying_compactCellClass
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hStrong : OperadicAcyclicCells.StrongAdmissibleGeneration.{us, us} S.C I)
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) {K L : S.W → S.C} (x : K ⟶ L)
    (hx : ∀ d, trivialCofibrations S.C (x d)) {A B : Algebra O}
    (a : freeAlgebra O K ⟶ A) (b : freeAlgebra O L ⟶ B) (g : A ⟶ B)
    (sq : IsPushout a ((freeAlgebraFunctor O).map x) g b) (d : S.W) :
    compactCellClass S ((carrierAt S O d).map g) := by
  let : (compactCellClass S).RespectsIso := compactCellClass_respectsIso S
  let s := OriginalAttachment.isPushout O A x a
  let e := s.isColimit.coconePointUniqueUpToIso sq.isColimit
  have he : OriginalAttachment.oldMap O A x a ≫ e.hom = g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom s.isColimit sq.isColimit WalkingSpan.left
  let ae : Arrow.mk (OriginalAttachment.oldMap O A x a) ≅ Arrow.mk g :=
    Arrow.isoMk (Iso.refl A) e (by
      change 𝟙 A ≫ g = OriginalAttachment.oldMap O A x a ≫ e.hom
      exact (Category.id_comp g).trans he.symm)
  exact ((compactCellClass S).arrow_iso_iff ((carrierAt S O d).mapArrow.mapIso ae)).mp
    (originalAttachment_compactCellClass S I hI hStrong h O A x a hx d)

private theorem freeTrivialCoproductPushouts_property
    (O : ColoredOperadObj S.W S.C) (d : S.W) (Q : MorphismProperty S.C)
    (hPushout : ∀ {K L : S.W → S.C} (x : K ⟶ L),
      (∀ d, trivialCofibrations S.C (x d)) → ∀ {A B : Algebra O}
      (a : freeAlgebra O K ⟶ A) (b : freeAlgebra O L ⟶ B) (g : A ⟶ B),
      IsPushout a ((freeAlgebraFunctor O).map x) g b → Q ((carrierAt S O d).map g)) :
    ((SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C)).strictMap
      (freeAlgebraFunctor O)).coproducts.{us}.pushouts ≤ Q.inverseImage (carrierAt S O d) := by
  let : IsStableUnderCoproducts.{us}
      (SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C)) :=
    pointwiseTrivialCofibrations_stableCoproducts S
  let : (freeAlgebraFunctor O).IsLeftAdjoint := ⟨Algebra.forget O, ⟨S.operadicAdjunction O⟩⟩
  intro A B g hg
  obtain ⟨X, Y, q, a, b, hq, sq⟩ := hg
  have hFree := MorphismProperty.coproducts_strictMap_le_map
    (SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C))
    (freeAlgebraFunctor O) q hq
  obtain ⟨K, L, x, hx, ⟨χ⟩⟩ := hFree
  let s := Arrow.leftFunc.mapIso χ
  let t := Arrow.rightFunc.mapIso χ
  have hχ : s.hom ≫ q = (freeAlgebraFunctor O).map x ≫ t.hom := χ.hom.w
  have sq' : IsPushout (s.hom ≫ a) ((freeAlgebraFunctor O).map x) g (t.hom ≫ b) :=
    sq.of_iso' s (Iso.refl A) t (Iso.refl B)
      (by simp) hχ (by simp) (by simp)
  exact hPushout x hx (s.hom ≫ a) (t.hom ≫ b) g sq'

/-- Arbitrary original free-J coproduct attachments retain both compact-source conditions. -/
theorem freeJCoproductPushouts_underlying_compactCellClass
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hStrong : OperadicAcyclicCells.StrongAdmissibleGeneration.{us, us} S.C I)
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C) (d : S.W) :
    (freeGenerators S O J).coproducts.{us}.pushouts ≤
      (compactCellClass S).inverseImage (carrierAt S O d) := by
  let : ModelCategory (S.W → S.C) := SemiModel.ColorSource.pointwiseModelCategory S.C S.W
  have hj : SemiModel.ColorSource.colorGenerators S.C S.W J ≤
      SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C) := by
    rw [← SemiModel.ColorSource.trivialCofibrations_eq S.C S.W]
    exact SemiModel.ColorSource.colorJGenerators_le_trivialCofibrations S.C S.W J hJ
  exact (pushouts_monotone (coproducts_monotone
    (monotone_strictMap (freeAlgebraFunctor O) hj))).trans
      (freeTrivialCoproductPushouts_property S O d (compactCellClass S)
        (fun {K L} x hx {A B} a b g sq => freePushout_underlying_compactCellClass
          S I hI hStrong h O x hx a b g sq d))

/-- The same supplied free-J history is weak by actual compact source bounds,
with no blanket weak-transfinite closure or additional properness hypothesis. -/
theorem freeJCell_underlying_weak_compact
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hStrong : OperadicAcyclicCells.StrongAdmissibleGeneration.{us, us} S.C I)
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    {T : Type us} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Algebra O} {f : A ⟶ B}
    (c : ((freeGenerators S O J).coproducts.{us}).pushouts.TransfiniteCompositionOfShape T f)
    (d : S.W) : weakEquivalences S.C ((carrierAt S O d).map f) := by
  let : (compactCellClass S).IsStableUnderTransfiniteComposition.{us} :=
    compactCellClass_stable S I hI hStrong
  let : PreservesColimitsOfShape T (carrierAt S O d) :=
    carrierAt_preservesFilteredColimits S O d T
  let : PreservesWellOrderContinuousOfShape T (carrierAt S O d) :=
    carrierAt_preservesWellOrderContinuous S O d T
  let m : (compactCellClass S).TransfiniteCompositionOfShape T ((carrierAt S O d).map f) :=
    (c.ofLE (freeJCoproductPushouts_underlying_compactCellClass S I hI hStrong h O J hJ d)).map
  exact couniversalWeakEquivalences_le_weakEquivalences _
    ((compactCellClass S).transfiniteCompositionsOfShape_le T _ m.mem).1

/-- The actual original free-J small-object factor and retract are weak on the compact route. -/
theorem freeJLeft_underlying_weak_compact
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hStrong : OperadicAcyclicCells.StrongAdmissibleGeneration.{us, us} S.C I)
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(freeGenerators S O J).IsCardinalForSmallObjectArgument κ] :
    (freeGenerators S O J).rlp.llp ≤ weakClass S O := by
  intro A B f hf d
  apply rlp_llp_le_inverseImage_of_cardinal_cells
    (freeGenerators S O J) (weakEquivalences S.C) (carrierAt S O d) κ
      (fun f c => freeJCell_underlying_weak_compact S I hI hStrong h O J hJ
        (c.transfiniteCompositionOfShape' (fun s => s.i.2)) d) f hf

end CompactSources

section OrdinalSources

private theorem ordinalCellClass_stable
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C)) :
    (compactCellClass S).IsStableUnderTransfiniteComposition.{us} := by
  let P := OperadicAcyclicCells.cofibrationCells.{us, us} S.C
  let : P.IsStableUnderCobaseChange := OperadicAcyclicCells.cofibrationCells_stable.1
  let : P.IsStableUnderTransfiniteComposition.{us} :=
    OperadicAcyclicCells.cofibrationCells_stable.2.2
  exact OperadicAcyclicCells.OrdinalSources.couniversalIntersection_stableUnderTransfiniteComposition
    I P hI hSources OperadicAcyclicCells.cofibrations_le_cofibrationCells

/-- Both original generator endpoints need only the actual ordinal source-Hom comparisons.
The original A5 attachment, every profile occurrence, and its original old leg are retained. -/
theorem originalAttachment_ordinalCellClass
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (A : Algebra O)
    {K L : S.W → S.C} (x : K ⟶ L) (a : freeAlgebra O K ⟶ A)
    (hx : ∀ d, trivialCofibrations S.C (x d)) (d : S.W) :
    compactCellClass S ((OriginalAttachment.oldMap O A x a).hom d) := by
  let Q := compactCellClass S
  let : (OperadicAcyclicCells.cofibrationCells.{us, us} S.C).IsStableUnderCobaseChange :=
    OperadicAcyclicCells.cofibrationCells_stable.1
  let : Q.IsStableUnderCobaseChange := by dsimp only [Q, compactCellClass]; infer_instance
  let hTrans : Q.IsStableUnderTransfiniteComposition.{us} :=
    ordinalCellClass_stable S I hI hSources
  let : Q.IsStableUnderCoproducts.{us} :=
    @isStableUnderCoproducts_of_cobase_transfinite S.C inferInstance Q inferInstance
      hTrans (inferInstance : HasCoproducts.{us} S.C)
  let : Q.IsStableUnderTransfiniteComposition.{0} :=
    IsStableUnderTransfiniteComposition.shrink₀ (W := Q)
  have hc : (orbitGenerators (trivialCofibrations S.C)).isoClosure ≤
      couniversalWeakEquivalences S.C := (isoClosure_le_iff _ _).2 h.generators_le
  have hp : (orbitGenerators (trivialCofibrations S.C)).isoClosure ≤
      OperadicAcyclicCells.cofibrationCells.{us, us} S.C :=
    (isoClosure_le_iff _ _).2 OperadicAcyclicCells.trivialOrbitGenerators_le_cofibrationCells
  have hg : (orbitGenerators (trivialCofibrations S.C)).isoClosure ≤ Q := le_inf hc hp
  let c := OperadicAcyclicCells.Attachments.evaluatedOriginalRelativeCellComplex O A x a d
  apply Q.transfiniteCompositionsOfShape_le ℕ _
  have hpush : (Q.coproducts.{us}).pushouts ≤ Q :=
    (pushouts_le_iff (P := Q.coproducts.{us}) (Q := Q)).2 (coproducts_le Q)
  exact ((c.transfiniteCompositionOfShape' (fun s => hg _
    (OperadicAcyclicCells.Attachments.occurringOriginalCell_mem O A x hx d s.j s.i))).ofLE hpush).mem

/-- The caller's original algebra pushout has both source-cell conditions under ordinal Hom. -/
theorem freePushout_underlying_ordinalCellClass
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) {K L : S.W → S.C} (x : K ⟶ L)
    (hx : ∀ d, trivialCofibrations S.C (x d)) {A B : Algebra O}
    (a : freeAlgebra O K ⟶ A) (b : freeAlgebra O L ⟶ B) (g : A ⟶ B)
    (sq : IsPushout a ((freeAlgebraFunctor O).map x) g b) (d : S.W) :
    compactCellClass S ((carrierAt S O d).map g) := by
  let : (compactCellClass S).RespectsIso := compactCellClass_respectsIso S
  let s := OriginalAttachment.isPushout O A x a
  let e := s.isColimit.coconePointUniqueUpToIso sq.isColimit
  have he : OriginalAttachment.oldMap O A x a ≫ e.hom = g :=
    IsColimit.comp_coconePointUniqueUpToIso_hom s.isColimit sq.isColimit WalkingSpan.left
  let ae : Arrow.mk (OriginalAttachment.oldMap O A x a) ≅ Arrow.mk g :=
    Arrow.isoMk (Iso.refl A) e (by
      change 𝟙 A ≫ g = OriginalAttachment.oldMap O A x a ≫ e.hom
      exact (Category.id_comp g).trans he.symm)
  exact ((compactCellClass S).arrow_iso_iff ((carrierAt S O d).mapArrow.mapIso ae)).mp
    (originalAttachment_ordinalCellClass S I hI hSources h O A x a hx d)

/-- The entire original coproduct of free J-generators is normalized before forgetting. -/
theorem freeJCoproductPushouts_underlying_ordinalCellClass
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C) (d : S.W) :
    (freeGenerators S O J).coproducts.{us}.pushouts ≤
      (compactCellClass S).inverseImage (carrierAt S O d) := by
  let : ModelCategory (S.W → S.C) := SemiModel.ColorSource.pointwiseModelCategory S.C S.W
  have hj : SemiModel.ColorSource.colorGenerators S.C S.W J ≤
      SemiModel.ColorSource.pointwiseProperty S.C S.W (trivialCofibrations S.C) := by
    rw [← SemiModel.ColorSource.trivialCofibrations_eq S.C S.W]
    exact SemiModel.ColorSource.colorJGenerators_le_trivialCofibrations S.C S.W J hJ
  exact (pushouts_monotone (coproducts_monotone
    (monotone_strictMap (freeAlgebraFunctor O) hj))).trans
      (freeTrivialCoproductPushouts_property S O d (compactCellClass S)
        (fun {K L} x hx {A B} a b g sq => freePushout_underlying_ordinalCellClass
          S I hI hSources h O x hx a b g sq d))

/-- The whole caller-supplied history has its literal mapped stage functor, endpoint,
bottom isomorphism and inclusions. Only genuine nonempty ordinal colimits are preserved. -/
def freeJCellMappedOrdinalHistory
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    {T : Type us} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Algebra O} {f : A ⟶ B}
    (c : ((freeGenerators S O J).coproducts.{us}).pushouts.TransfiniteCompositionOfShape T f)
    (d : S.W) :
    (compactCellClass S).TransfiniteCompositionOfShape T ((carrierAt S O d).map f) := by
  let : PreservesColimitsOfShape T (carrierAt S O d) :=
    carrierAt_preservesFilteredColimits S O d T
  let : PreservesWellOrderContinuousOfShape T (carrierAt S O d) :=
    carrierAt_preservesWellOrderContinuous S O d T
  exact (c.ofLE (freeJCoproductPushouts_underlying_ordinalCellClass S I hI hSources h O J hJ d)).map

/-- Ordinal source Hom closes the same entire supplied free-J history without an
unrestricted filtered-compactness or weak-transfinite premise. -/
theorem freeJCell_underlying_weak_ordinal
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    {T : Type us} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
    {A B : Algebra O} {f : A ⟶ B}
    (c : ((freeGenerators S O J).coproducts.{us}).pushouts.TransfiniteCompositionOfShape T f)
    (d : S.W) : weakEquivalences S.C ((carrierAt S O d).map f) := by
  let : (compactCellClass S).IsStableUnderTransfiniteComposition.{us} :=
    ordinalCellClass_stable S I hI hSources
  exact couniversalWeakEquivalences_le_weakEquivalences _
    ((compactCellClass S).transfiniteCompositionsOfShape_le T _
      (freeJCellMappedOrdinalHistory S I hI hSources h O J hJ c d).mem).1

/-- The original small-object factor and its actual mapped retract close the full
free-J left lifting class on arbitrary source objects using ordinal source Hom. -/
theorem freeJLeft_underlying_weak_ordinal
    (I : MorphismProperty S.C) (hI : I.rlp = trivialFibrations S.C)
    (hSources : SourceHomPreservation.{u, v, us} I
      (OperadicAcyclicCells.cofibrationCells.{us, us} S.C))
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (O : ColoredOperadObj S.W S.C) (J : MorphismProperty S.C)
    (hJ : J.rlp = fibrations S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    [(freeGenerators S O J).IsCardinalForSmallObjectArgument κ] :
    (freeGenerators S O J).rlp.llp ≤ weakClass S O := by
  intro A B f hf d
  apply rlp_llp_le_inverseImage_of_cardinal_cells
    (freeGenerators S O J) (weakEquivalences S.C) (carrierAt S O d) κ
      (fun f c => freeJCell_underlying_weak_ordinal S I hI hSources h O J hJ
        (c.transfiniteCompositionOfShape' (fun s => s.i.2)) d) f hf

end OrdinalSources


end HomotopicalAlgebra.OperadicTransfer
