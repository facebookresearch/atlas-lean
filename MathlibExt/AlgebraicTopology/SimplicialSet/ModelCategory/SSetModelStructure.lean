/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.BoundaryRLPRealizationWeakEquivalence
public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SmallObject
public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.HornRLPSingularRLP
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHornCellWeakHomotopy
public import Mathlib.AlgebraicTopology.ModelCategory.Basic
public import Mathlib.AlgebraicTopology.ModelCategory.JoyalTrick

/-!
# Kan–Quillen model structures from realization weak equivalences

A model structure on simplicial sets can be constructed from a weak-equivalence
property `W` with two-out-of-three and retract stability, a functorial factorization
into monomorphisms in `W` followed by Kan fibrations, and the recognition equality
between boundary right lifting and Kan fibrations in `W`.

Taking `W` to be the maps whose geometric realizations are weak homotopy equivalences
gives the Kan–Quillen model structure in every universe: cofibrations are monomorphisms
and fibrations are Kan fibrations. The associated weak-equivalence category and model
category are provided as scoped instances.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace SSet.modelCategoryQuillen

open scoped SSet.modelCategoryQuillen in
/--
The model structure on simplicial sets determined by a weak-equivalence property
`W` with two-out-of-three and retract stability, functorial factorization into
monomorphisms in `W` followed by horn-right-lifting maps, and the equality
`I.rlp = J.rlp ∩ W` for boundary and horn inclusions.
-/
@[instance_reducible]
noncomputable def modelCategoryOf
    (W : MorphismProperty SSet.{u})
    [W.HasTwoOutOfThreeProperty]
    [W.IsStableUnderRetracts]
    (hFactor : HasFunctorialFactorization
      (monomorphisms SSet.{u} ⊓ W) J.rlp)
    (hRec : I.rlp = J.rlp ⊓ W) :
    ModelCategory SSet.{u} := by
  let fibParent : CategoryWithFibrations SSet.{u} := inferInstance
  let cofParent : CategoryWithCofibrations SSet.{u} := inferInstance
  let weakParent : CategoryWithWeakEquivalences SSet.{u} :=
    { weakEquivalences := W }
  let _ : CategoryWithWeakEquivalences SSet.{u} := weakParent
  let _ : (weakEquivalences SSet.{u}).HasTwoOutOfThreeProperty := by
    change W.HasTwoOutOfThreeProperty
    infer_instance
  let _ : (weakEquivalences SSet.{u}).IsStableUnderRetracts := by
    change W.IsStableUnderRetracts
    infer_instance
  let _ : (fibrations SSet.{u}).IsStableUnderBaseChange := by
    rw [fibrations_eq]
    infer_instance
  let _ : HasFunctorialFactorization
      (monomorphisms SSet.{u} ⊓ W) J.rlp := hFactor
  let _ : HasFactorization
      (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) := by
    change HasFactorization (monomorphisms SSet.{u} ⊓ W) J.rlp
    infer_instance
  let _ : HasFactorization
      (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) := by
    change HasFactorization (monomorphisms SSet.{u}) (J.rlp ⊓ W)
    rw [← hRec, ← SSet.rlp_monomorphisms]
    infer_instance
  have hcm4b : ∀ {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
      [Cofibration i] [WeakEquivalence p] [Fibration p],
      HasLiftingProperty i p := by
    intro A B X Y i p _ _ _
    have hp : I.rlp p := by
      rw [hRec]
      exact ⟨(fibration_iff p).mp inferInstance,
        (weakEquivalence_iff p).mp inferInstance⟩
    rw [← SSet.rlp_monomorphisms] at hp
    exact hp i ((cofibration_iff i).mp inferInstance)
  exact
    { categoryWithFibrations := fibParent
      categoryWithCofibrations := cofParent
      categoryWithWeakEquivalences := weakParent
      cm2 := by
        change W.HasTwoOutOfThreeProperty
        infer_instance
      cm3a := by
        change W.IsStableUnderRetracts
        infer_instance
      cm4a := fun i p _ _ _ ↦
        ModelCategory.hasLiftingProperty_of_joyalTrickDual hcm4b i p
      cm4b := fun i p _ _ _ ↦ hcm4b i p
      cm5a := inferInstance
      cm5b := inferInstance }

/--
The scoped category-with-weak-equivalences structure whose weak equivalences are
simplicial maps inducing weak homotopy equivalences on geometric realization.
-/
@[instance_reducible]
scoped instance instCategoryWithWeakEquivalences :
    CategoryWithWeakEquivalences SSet.{u} where
  weakEquivalences := SSet.realizationWeakEquivalences

open scoped SSet.modelCategoryQuillen in
/--
The model category structure with monomorphisms as cofibrations, Kan fibrations
as fibrations, and geometric-realization weak homotopy equivalences as weak equivalences,
in the specified simplicial-set universe.
-/
@[instance_reducible]
noncomputable def modelCategory : ModelCategory SSet.{u} := by
  have hAnodyneWeak :
      SSet.anodyneExtensions.{u} ≤
        SSet.realizationWeakEquivalences.{u} := by
    intro X Y f hf
    change TopCat.weakHomotopyEquivalences (SSet.toTop.map f)
    apply TopCat.horn_llp_le_weakHomotopyEquivalences
    rw [SSet.anodyneExtensions_eq_llp_rlp] at hf
    intro A B p hp
    exact (sSetTopAdj.hasLiftingProperty_iff f p).mpr
      (hf _ ((TopCat.hornRLP_iff_toSSet_mem_J_rlp).mp hp))
  have hAnodyneMono :
      SSet.anodyneExtensions.{u} ≤ monomorphisms SSet.{u} := by
    rw [SSet.anodyneExtensions_eq_llp_rlp, ← llp_rlp_I,
      ← SSet.rlp_monomorphisms]
    exact antitone_llp (antitone_rlp J_le_monomorphisms)
  let hFactor : HasFunctorialFactorization
      (monomorphisms SSet.{u} ⊓ SSet.realizationWeakEquivalences.{u})
      J.rlp :=
    ⟨⟨anodyneFunctorialFactorizationData.ofLE
      (le_inf hAnodyneMono hAnodyneWeak)
      (by rw [fibrations_eq])⟩⟩
  have hRec : I.{u}.rlp =
      J.rlp ⊓ SSet.realizationWeakEquivalences := by
    ext E B p
    constructor
    · intro hp
      have hp' : (monomorphisms SSet.{u}).rlp p := by
        rw [SSet.rlp_monomorphisms]
        exact hp
      have hFib : J.rlp p :=
        (antitone_rlp J_le_monomorphisms) _ hp'
      let _ : Fibration p := (fibration_iff p).mpr hFib
      exact ⟨hFib,
        (I_rlp_iff_realizationWeakEquivalence_of_fibration p).mp hp⟩
    · rintro ⟨hFib, hW⟩
      let _ : Fibration p := (fibration_iff p).mpr hFib
      exact (I_rlp_iff_realizationWeakEquivalence_of_fibration p).mpr hW
  exact modelCategoryOf SSet.realizationWeakEquivalences hFactor hRec

/--
The scoped Kan–Quillen model category instance on simplicial sets, with realization
weak equivalences, monomorphic cofibrations, and Kan fibrations.
-/
noncomputable scoped instance instModelCategory :
    ModelCategory SSet.{u} :=
  modelCategory

end SSet.modelCategoryQuillen
