/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalIdentityQuillen
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveMappingSupport

/-!
# Scalar tensor and the original end for the localized model

An arbitrary original presheaf is an allowed tensor source. The right adjoint
is the actual scalar end, and its fibration arguments use global lifting
classes. Neither a Cartesian criterion nor a model witness is a premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u v w i

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
  HomotopicalAlgebra Opposite
open SimplicialPresheaf.OriginalLocalDerived
open scoped SSet.modelCategoryQuillen
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable {D : Type w} [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]
  {I : Type i} [Small.{u} I]

/-- Global localized fibrations induce Kan fibrations of the original scalar
end from every original source. -/
theorem originalLocalizedRawPostcomp_fibration
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (hp : (originalLocalSmithModel S).categoryWithFibrations.fibrations p) :
    fibrations SSet.{u} (innerHomPost A p) := by
  have hbase : fibrations (SimplicialPresheaf.{u} D) p := by
    change (data D).model.categoryWithFibrations.fibrations p
    rw [(data D).fibrations_eq]
    exact originalLocalFibrations_le_injectiveFibrations S p hp
  exact rawPostcomp_fibration_of_fibration A p hbase

/-- The unchanged global trivial-fibration class induces trivial fibrations of
the original end, without any source or target fibrancy premise. -/
theorem originalLocalizedRawPostcomp_trivialFibration
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (hp : (originalLocalSmithModel S).categoryWithFibrations.fibrations p ∧
      (originalLocalSmithModel S).categoryWithWeakEquivalences.weakEquivalences p) :
    trivialFibrations SSet.{u} (innerHomPost A p) := by
  have hbase : trivialFibrations (SimplicialPresheaf.{u} D) p := by
    change ((data D).model.categoryWithFibrations.fibrations ⊓
      (data D).model.categoryWithWeakEquivalences.weakEquivalences) p
    rw [← originalLocalTrivialFibrations_eq_injectiveTrivialFibrations S]
    exact hp
  exact rawPostcomp_trivialFibration_of_trivialFibration A p hbase

/-- Scalar tensor with every original presheaf is genuinely left Quillen for
the internally constructed localized model and the fixed scalar Kan model. -/
theorem originalLocalScalarTensorHom_isQuillenAdjunction
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (A : SimplicialPresheaf.{u} D) :
    @CategoryTheory.Adjunction.IsQuillenAdjunction
      SSet.{u} inferInstance (SimplicialPresheaf.{u} D) inferInstance
      (inferInstance : ModelCategory SSet.{u}) (originalLocalSmithModel S)
      (scalarTensor.obj A) (innerHomFunctor.obj (op A))
      (scalarTensorHomAdjunction A) := by
  let _ : ModelCategory (SimplicialPresheaf.{u} D) := originalLocalSmithModel S
  apply CategoryTheory.Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (adj := scalarTensorHomAdjunction A)
  · intro X Y p hp
    change (originalLocalSmithModel S).categoryWithFibrations.fibrations p at hp
    change fibrations SSet.{u} (innerHomPost A p)
    exact originalLocalizedRawPostcomp_fibration S A p hp
  · intro X Y p hp
    change (originalLocalSmithModel S).categoryWithFibrations.fibrations p ∧
      (originalLocalSmithModel S).categoryWithWeakEquivalences.weakEquivalences p at hp
    change trivialFibrations SSet.{u} (innerHomPost A p)
    exact originalLocalizedRawPostcomp_trivialFibration S A p hp

omit [Small.{u} I] in
/-- The original end is Kan at every original local-fibrant target. -/
theorem originalLocal_innerHom_isFibrant
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (A Z : SimplicialPresheaf.{u} D)
    (hZ : isOriginalLocalFibrant S Z) : IsFibrant (innerHom A Z) :=
  innerHom_isFibrant A Z hZ.1

omit [Small.{u} I] in
/-- Raw postcomposition preserves local weakness between local-fibrant endpoints. -/
theorem originalLocalizedRawPostcomp_weak_of_localFibrant
    (S : I → Arrow (SimplicialPresheaf.{u} D)) (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (p : X ⟶ Y)
    (hp : originalLocalEquivalences S p)
    (hX : isOriginalLocalFibrant S X) (hY : isOriginalLocalFibrant S Y) :
    SSet.realizationWeakEquivalences.{u} (innerHomPost A p) := by
  have hbase : weakEquivalences (SimplicialPresheaf.{u} D) p := by
    change (data D).model.categoryWithWeakEquivalences.weakEquivalences p
    rw [(data D).weakEquivalences_eq]
    exact (originalLocalEquivalence_iff_objectwiseWeak_of_localFibrant S p hX hY).mp hp
  exact innerHomPost_weak_of_weakEquivalence A p hbase hX.1 hY.1

omit [Small.{u} I] in
/-- Every monic local weak map induces a trivial fibration of original scalar
ends into an original local-fibrant target. -/
theorem originalLocalizedRawPrecomp_trivialFibration
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    {A B : SimplicialPresheaf.{u} D} (i : A ⟶ B)
    (hi : localTrivialMonomorphisms S i)
    (Z : SimplicialPresheaf.{u} D) (hZ : isOriginalLocalFibrant S Z) :
    trivialFibrations SSet.{u} (innerHomPre i Z) := by
  have hcof : cofibrations (SimplicialPresheaf.{u} D) i := by
    change (data D).model.categoryWithCofibrations.cofibrations i
    rw [(data D).cofibrations_eq]
    exact hi.1
  change fibrations SSet.{u} (innerHomPre i Z) ∧
    SSet.realizationWeakEquivalences.{u} (innerHomPre i Z)
  exact ⟨rawPrecomp_fibration_of_cofibration i Z hcof hZ.1,hi.2 Z hZ⟩

/-- The actual Smith localization unit induces a trivial fibration on the
original end at every original local-fibrant target. -/
theorem originalLocalUnitRawPrecomp_trivialFibration
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X Z : SimplicialPresheaf.{u} D) (hZ : isOriginalLocalFibrant S Z) :
    trivialFibrations SSet.{u} (innerHomPre ((localRUnit S).app X) Z) :=
  originalLocalizedRawPrecomp_trivialFibration S ((localRUnit S).app X)
    (localRUnit_localTrivialCofibration S X) Z hZ

/-- Every original map into a local-fibrant target extends along the actual
constructed localization unit as one globally natural presheaf map. -/
theorem exists_originalLocalUnit_extension
    (S : I → Arrow (SimplicialPresheaf.{u} D))
    (X Z : SimplicialPresheaf.{u} D) (hZ : isOriginalLocalFibrant S Z)
    (f : X ⟶ Z) :
    ∃ g : (localR S).obj X ⟶ Z, (localRUnit S).app X ≫ g = f := by
  let Y := (localR S).obj X
  let i := (localRUnit S).app X
  have hright : (localTrivialMonomorphisms S).rlp (terminal.from Z) :=
    ((originalLocalSmithData S).terminal_iff Z).mpr hZ
  let _ : HasLiftingProperty i (terminal.from Z) :=
    hright i (localRUnit_localTrivialCofibration S X)
  have square : CommSq f i (terminal.from Z) (terminal.from Y) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨square.lift,square.fac_left⟩

end SimplicialPresheaf.InjectiveKan
