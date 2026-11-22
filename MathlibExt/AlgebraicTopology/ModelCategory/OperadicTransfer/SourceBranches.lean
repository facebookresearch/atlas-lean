/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.Acyclicity
import MathlibExt.AlgebraicTopology.ModelCategory.OperadicTransfer.RelativeSmallness
import MathlibExt.AlgebraicTopology.ModelCategory.RightTransfer
import MathlibExt.CategoryTheory.Monad.ReflexiveCocompleteness
import Mathlib.CategoryTheory.Monad.Limits

/-!
# Full colored operadic transfer: the Pavlov–Scholbach weak-transfinite branch

Mathematical source: Dmitri Pavlov and Jakob Scholbach,
*Admissibility and rectification of colored symmetric operads*,
arXiv:1410.5675v4, Theorem 5.11(a) and Remark 5.13:
https://arxiv.org/pdf/1410.5675v4.
The constructor below uses the prescribed source weak-transfinite branch;
its source conditions remain explicit in the statements.

The actual tensor algebra category is proved complete and cocomplete from the
source category, its explicit monadic equivalence, and its created reflexive
coequalizers. Original free-source bounds and the derived entire free-J
acyclicity are then supplied to the canonical full right-transfer constructor.
The ordinary-admissible branch remains separate from these proved conditions.
-/

set_option autoImplicit false
noncomputable section

universe uW v u us

open CategoryTheory Limits MorphismProperty SmallObject
open CategoryTheory.Operad CategoryTheory.Operad.Tensor

namespace HomotopicalAlgebra.OperadicTransfer

variable (S : SourceContext.{uW, v, u, us})
/-- Use the original finite tensor operations in the model-transfer source branches. -/
local instance branchOriginalFiniteTensor : FiniteTensor S.C := S.finiteTensor
local instance branchOriginalTensorSlots : FiniteTensorPreservesColimitsInEachSlot.{v, u, us} S.C :=
  S.finiteTensorPreservation
local instance branchOriginalProfiles (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C :=
  S.profileColimits d

private theorem colorFamily_hasLimits : HasLimitsOfSize.{us, us} (S.W → S.C) :=
  ⟨fun J _ => by
    let : HasLimitsOfShape J (Discrete S.W ⥤ S.C) := inferInstance
    exact Adjunction.hasLimitsOfShape_of_equivalence
      (piEquivalenceFunctorDiscrete S.W S.C).functor⟩

private theorem colorFamily_hasColimits : HasColimitsOfSize.{us, us} (S.W → S.C) :=
  ⟨fun J _ => by
    let : HasColimitsOfShape J (Discrete S.W ⥤ S.C) := inferInstance
    exact Adjunction.hasColimitsOfShape_of_equivalence
      (piEquivalenceFunctorDiscrete S.W S.C).functor⟩

/-- The original tensor algebra category has all source-sized limits by its actual monadic equivalence. -/
theorem tensorAlgebra_hasLimits (O : ColoredOperadObj S.W S.C) :
    HasLimitsOfSize.{us, us} (Algebra O) := by
  let : HasLimitsOfSize.{us, us} (S.W → S.C) := colorFamily_hasLimits S
  let : HasLimitsOfSize.{us, us} (Monad.Algebra (profileMonad O)) :=
    ⟨fun J _ => ⟨fun D => Monad.hasLimit_of_comp_forget_hasLimit D⟩⟩
  exact ⟨fun J _ => Adjunction.hasLimitsOfShape_of_equivalence
    (tensorAlgebraEMEquivalence O).functor⟩

/-- The source tensor construction creates the actual algebra reflexive colimits. -/
theorem tensorAlgebra_hasReflexiveColimits (O : ColoredOperadObj S.W S.C) :
    HasColimitsOfShape WalkingReflexivePair (Algebra O) := by
  let : HasColimitsOfSize.{us, us} (S.W → S.C) := colorFamily_hasColimits S
  let : HasColimitsOfSize.{0, 0} (S.W → S.C) :=
    hasColimitsOfSizeOfUnivLE.{us, us} (S.W → S.C)
  let : CreatesColimitsOfShape WalkingReflexivePair (Algebra.forget O) :=
    tensorAlgebraForgetCreatesReflexivePairs O
  exact ⟨fun D => hasColimit_of_created D (Algebra.forget O)⟩

/-- Actual reflexive algebra colimits construct all target colimits, rather than assuming them. -/
theorem tensorAlgebra_hasColimits (O : ColoredOperadObj S.W S.C) :
    HasColimitsOfSize.{us, us} (Algebra O) := by
  let : HasColimitsOfSize.{us, us} (S.W → S.C) := colorFamily_hasColimits S
  let : HasColimitsOfShape WalkingReflexivePair (Algebra O) :=
    tensorAlgebra_hasReflexiveColimits S O
  let : HasColimitsOfShape WalkingReflexivePair (Monad.Algebra (profileMonad O)) :=
    Adjunction.hasColimitsOfShape_of_equivalence (tensorAlgebraEMEquivalence O).inverse
  let : HasReflexiveCoequalizers (Monad.Algebra (profileMonad O)) :=
    hasReflexiveCoequalizers_iff.mp inferInstance
  let : HasColimitsOfSize.{us, us} (Monad.Algebra (profileMonad O)) :=
    Monad.ReflexiveCocompleteness.hasColimitsOfSize (profileMonad O)
  exact ⟨fun J _ => Adjunction.hasColimitsOfShape_of_equivalence
    (tensorAlgebraEMEquivalence O).functor⟩

/-- The original source endpoint bounds and complete transferred model data are retained together. -/
structure FullOperadicModelTransfer (O : ColoredOperadObj S.W S.C)
    (I J : MorphismProperty S.C) (κ₀ : Cardinal.{us}) where
  /-- The produced presentability witnesses retain the original free source endpoints. -/
  sourceBounds : PresentableFreeSourceBounds S O I J κ₀
  /-- The exact original algebra adjunction and free generators carry the full model. -/
  targetTransfer :
    letI : ModelCategory (S.W → S.C) := SemiModel.ColorSource.pointwiseModelCategory S.C S.W
    RightTransfer.FullModelTransfer (freeAlgebraFunctor O) (Algebra.forget O)
      (SemiModel.ColorSource.colorGenerators S.C S.W I)
      (SemiModel.ColorSource.colorGenerators S.C S.W J)
      sourceBounds.I_relative sourceBounds.J_relative

section WeakTransfinite

variable [(weakEquivalences S.C).IsStableUnderTransfiniteComposition.{us}]

/-- The source locally presentable weak-transfinite branch gives the full actual algebra model,
with no target model, target general colimits or free-J acyclicity supplied as an outcome premise. -/
def fullOperadicModelTransferOfWeakTransfinite
    (O : ColoredOperadObj S.W S.C) (I J : MorphismProperty S.C)
    [I.IsSmall.{us}] [J.IsSmall.{us}] [LocallySmall.{us} S.C]
    [IsLocallyPresentable.{us} S.C]
    (hI : I.rlp = trivialFibrations S.C) (hJ : J.rlp = fibrations S.C)
    (κ₀ : Cardinal.{us}) [Fact κ₀.IsRegular]
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C) :
    FullOperadicModelTransfer S O I J κ₀ := by
  let b := presentableFreeSourceBounds S O I J κ₀
  letI : ModelCategory (S.W → S.C) := SemiModel.ColorSource.pointwiseModelCategory S.C S.W
  letI : HasLimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasLimits S O
  letI : HasColimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasColimits S O
  letI : LocallySmall.{us} (S.W → S.C) :=
    { hom_small X Y := by
        change Small.{us} (∀ d, X d ⟶ Y d)
        infer_instance }
  letI : LocallySmall.{us} (Algebra O) := locallySmall_of_faithful (Algebra.forget O)
  letI : (SemiModel.ColorSource.colorGenerators S.C S.W I).IsSmall.{us} :=
    SemiModel.ColorSource.colorGenerators_isSmall S.C S.W I
  letI : (SemiModel.ColorSource.colorGenerators S.C S.W J).IsSmall.{us} :=
    SemiModel.ColorSource.colorGenerators_isSmall S.C S.W J
  let t := RightTransfer.fullModelTransfer (freeAlgebraFunctor O) (Algebra.forget O)
    (S.operadicAdjunction O)
    (SemiModel.ColorSource.colorGenerators S.C S.W I)
    (SemiModel.ColorSource.colorGenerators S.C S.W J)
    (SemiModel.ColorSource.colorIGenerators_rlp_eq S.C S.W I hI)
    (SemiModel.ColorSource.colorJGenerators_rlp_eq S.C S.W J hJ)
    b.I_relative b.J_relative (fun κ hreg hbot hsmall => by
      let : Fact κ.IsRegular := hreg
      let : OrderBot κ.ord.ToType := hbot
      let : (freeGenerators S O J).IsCardinalForSmallObjectArgument κ := hsmall
      change (freeGenerators S O J).rlp.llp ≤ weakClass S O
      exact freeJLeft_underlying_weak S h O J hJ κ)
  exact ⟨b, t⟩

end WeakTransfinite

/-- The original free-generator Hom functor preserves the supplied original cell endpoint. -/
def ActualFreeCellSourceSmallness (O : ColoredOperadObj S.W S.C)
    (P : MorphismProperty S.C) (κ : Cardinal.{us}) [OrderBot κ.ord.ToType] : Prop :=
  ∀ {A B X Y : Algebra O} (i : A ⟶ B) (_ : freeGenerators S O P i) (f : X ⟶ Y)
    (c : RelativeCellComplex.{us}
      (fun _ : κ.ord.ToType => (freeGenerators S O P).homFamily) f),
    PreservesColimit c.F (coyoneda.obj (Opposite.op A))

/-- The compact source route constructs the full model at the caller's original cardinal.
Its source-smallness hypotheses concern actual source-Hom functors, not factor or model outcomes. -/
@[instance_reducible]
def modelAtOriginalCardinalOfCompactSources
    (O : ColoredOperadObj S.W S.C) (I J : MorphismProperty S.C)
    [I.IsSmall.{us}] [J.IsSmall.{us}] [LocallySmall.{us} S.C]
    (hI : I.rlp = trivialFibrations S.C) (hJ : J.rlp = fibrations S.C)
    (hStrong : OperadicAcyclicCells.StrongAdmissibleGeneration.{us, us} S.C I)
    (h : OperadicAcyclicCells.AcyclicSymmetricHMonoidality S.C)
    (κ : Cardinal.{us}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
    (hSourceI : ActualFreeCellSourceSmallness S O I κ)
    (hSourceJ : ActualFreeCellSourceSmallness S O J κ) : ModelCategory (Algebra O) := by
  letI : HasLimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasLimits S O
  letI : HasColimitsOfSize.{us, us} (Algebra O) := tensorAlgebra_hasColimits S O
  letI : HasLimitsOfSize.{0, 0} (Algebra O) := hasLimitsOfSizeOfUnivLE.{us, us} (Algebra O)
  letI : HasColimitsOfSize.{0, 0} (Algebra O) := hasColimitsOfSizeOfUnivLE.{us, us} (Algebra O)
  letI : LocallySmall.{us} (S.W → S.C) :=
    { hom_small X Y := by
        change Small.{us} (∀ d, X d ⟶ Y d)
        infer_instance }
  letI : LocallySmall.{us} (Algebra O) := locallySmall_of_faithful (Algebra.forget O)
  letI : (freeGenerators S O I).IsSmall.{us} := freeGenerators_isSmall S O I
  letI : (freeGenerators S O J).IsSmall.{us} := freeGenerators_isSmall S O J
  letI : (freeGenerators S O I).IsCardinalForSmallObjectArgument κ :=
    { preservesColimit := fun i hi f c => hSourceI i hi f c }
  letI : (freeGenerators S O J).IsCardinalForSmallObjectArgument κ :=
    { preservesColimit := fun i hi f c => hSourceJ i hi f c }
  exact modelCategoryAtCardinal S O I J hI hJ κ
    (freeJLeft_underlying_weak_compact S I hI hStrong h O J hJ κ)


end HomotopicalAlgebra.OperadicTransfer
