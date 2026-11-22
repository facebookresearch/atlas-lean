/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Operad.Tensor.SourceContext
public import MathlibExt.CategoryTheory.Monoidal.Unbiased.OfSymmetric
public import MathlibExt.CategoryTheory.Operad.Tensor.FreeAlgebraConstruction
public import MathlibExt.CategoryTheory.Operad.Tensor.CreatedColimits

/-!
# Free tensor-operadic algebras in a closed symmetric monoidal context

The chosen complete and cocomplete closed symmetric monoidal context
with small colors supplies a coherent finite tensor and profile
colimits. These give the profile monad, its equivalence with tensor
algebras, the free-forgetful adjunction, and creation of filtered
colimits and reflexive coequalizers.
-/

section source_TensorOperadicSourceTensor
/-!
## Finite tensor coherence and colimit preservation
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

/-- The coherent finite tensor of the chosen source context
is produced from its actual original binary symmetric tensor. -/
@[instance_reducible]
def SourceContext.finiteTensor (S : SourceContext.{u, v, w, us}) : FiniteTensor S.C :=
  FiniteTensor.ofSymmetric S.C

/-- The required original separate finite tensor colimit
commutation is proved from the source closed adjunctions and the
constructed binary symmetric finite tensor. -/
theorem SourceContext.finiteTensorPreservation (S : SourceContext.{u, v, w, us}) :
    @FiniteTensorPreservesColimitsInEachSlot.{v, w, us} S.C S.category S.finiteTensor :=
  FiniteTensor.ofSymmetric_preservesColimitsInEachSlot S.C

/-- Every original output color has the actual small profile
coinvariant colimits, supplied by source cocompleteness and small colors. -/
theorem SourceContext.profileColimits (S : SourceContext.{u, v, w, us}) (d : S.W) :
    HasColimitsOfShape (AnalyticIndex S.W d) S.C := hasProfileColimitsOfSmallColors S.C d

end CategoryTheory.Operad.Tensor
end
end
end source_TensorOperadicSourceTensor


section source_TensorOperadicSourceTheorem
/-!
## Free algebras, monads and created colimits
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u v w us uJ vJ

namespace CategoryTheory.Operad.Tensor

open CategoryTheory Limits

variable (S : SourceContext.{u, v, w, us})

/-- Use the finite tensor constructed from the original symmetric source context. -/
local instance : FiniteTensor S.C := S.finiteTensor
local instance : FiniteTensorPreservesColimitsInEachSlot.{v, w, us} S.C :=
  S.finiteTensorPreservation
local instance (d : S.W) : HasColimitsOfShape (AnalyticIndex S.W d) S.C := S.profileColimits d

/-- The original complete/cocomplete closed symmetric monoidal
model source and small colors yield the actual operation-weighted
profile coinvariant monad, with all laws proved from original
operadic units/substitution and tensor colimit constructions. -/
def SourceContext.operadicMonad (O : ColoredOperadObj S.W S.C) : Monad (S.W → S.C) :=
  profileMonad O

/-- The original source tensor-operation algebras and all their
operation-preserving morphisms are the actual Eilenberg–Moore
category, through the explicit original action/operation inverses. -/
def SourceContext.operadicEMEquivalence (O : ColoredOperadObj S.W S.C) :
    Algebra O ≌ Monad.Algebra (S.operadicMonad O) := tensorAlgebraEMEquivalence O

/-- The actual original tensor free algebra functor is left
adjoint to the original operation-map forgetful functor in the
article's exact model source setting. -/
def SourceContext.operadicAdjunction (O : ColoredOperadObj S.W S.C) :
    freeAlgebraFunctor O ⊣ Algebra.forget O := tensorFreeAdjunction O

/-- Every source-sized filtered original algebra diagram has
the actual created carrier colimit with all original tensor
operations, injection squares and universal algebra maps. -/
@[instance_reducible]
def SourceContext.operadicCreatesFilteredColimits (O : ColoredOperadObj S.W S.C)
    {J : Type uJ} [Category.{vJ} J] [IsFiltered J] [EssentiallySmall.{us} J] :
    CreatesColimitsOfShape J (Algebra.forget O) := tensorAlgebraForgetCreatesFilteredColimits O

/-- Every original reflexive algebra pair has the constructed
coequalizer on its original carrier coequalizer, with the full
original tensor operations and unique operation-preserving maps. -/
@[instance_reducible]
def SourceContext.operadicCreatesReflexiveCoequalizer (O : ColoredOperadObj S.W S.C)
    {A B : Algebra O} (f g : A ⟶ B) [IsReflexivePair f g] :
    CreatesColimit (parallelPair f g) (Algebra.forget O) :=
  tensorAlgebraForgetCreatesReflexiveCoequalizer O f g


end CategoryTheory.Operad.Tensor
end
end
end source_TensorOperadicSourceTheorem
