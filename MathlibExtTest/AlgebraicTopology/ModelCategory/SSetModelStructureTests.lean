/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import
  MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SSetModelStructure

/-!
# Public clients for the scoped SSet model structure

These tests cover the generic constructor, the named universe-polymorphic model,
the opt-in scoped instances, the model axioms, and scope/API boundaries.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory HomotopicalAlgebra MorphismProperty

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.SSetModelStructureTests

universe u

section PublicSurface

#check SSet.modelCategoryQuillen.modelCategoryOf
#check SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences
#check SSet.modelCategoryQuillen.modelCategory
#check SSet.modelCategoryQuillen.instModelCategory

noncomputable example : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory

end PublicSurface

section NoScope

/--
error: failed to synthesize
  CategoryWithCofibrations SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithCofibrations SSet.{u}

/--
error: failed to synthesize
  CategoryWithFibrations SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithFibrations SSet.{u}

/--
error: failed to synthesize
  CategoryWithWeakEquivalences SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithWeakEquivalences SSet.{u}

/--
error: failed to synthesize
  ModelCategory SSet
-/
#guard_msgs (error, substring := true) in
#synth ModelCategory SSet.{u}

end NoScope

section WeakOnly

attribute [local instance]
  SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences

#synth CategoryWithWeakEquivalences SSet.{u}
#synth SSet.realizationWeakEquivalences.{u}.ContainsIdentities
#synth SSet.realizationWeakEquivalences.{u}.HasTwoOutOfThreeProperty
#synth SSet.realizationWeakEquivalences.{u}.IsStableUnderRetracts

example : weakEquivalences SSet.{u} =
    SSet.realizationWeakEquivalences.{u} := rfl

/--
error: failed to synthesize
  CategoryWithCofibrations SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithCofibrations SSet.{u}

/--
error: failed to synthesize
  CategoryWithFibrations SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithFibrations SSet.{u}

/--
error: failed to synthesize
  ModelCategory SSet
-/
#guard_msgs (error, substring := true) in
#synth ModelCategory SSet.{u}

end WeakOnly

section NamedModelOnly

local instance : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory

#synth ModelCategory SSet.{u}
#synth CategoryWithCofibrations SSet.{u}
#synth CategoryWithFibrations SSet.{u}
#synth CategoryWithWeakEquivalences SSet.{u}

example : cofibrations SSet.{u} = monomorphisms SSet.{u} := rfl
example : fibrations SSet.{u} =
    SSet.modelCategoryQuillen.J.{u}.rlp := rfl
example : weakEquivalences SSet.{u} =
    SSet.realizationWeakEquivalences.{u} := rfl

example : (inferInstance : CategoryWithCofibrations SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithCofibrations := rfl
example : (inferInstance : CategoryWithFibrations SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithFibrations := rfl
example : (inferInstance : CategoryWithWeakEquivalences SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences := rfl

end NamedModelOnly

section ExplicitDuplicateParentActivation

attribute [local instance]
  SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences

local instance : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategory

example : (inferInstance : CategoryWithWeakEquivalences SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences := rfl

example : SSet.modelCategoryQuillen.modelCategory.categoryWithWeakEquivalences =
    SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences := rfl

end ExplicitDuplicateParentActivation

section WrongScope

open scoped TopCat.modelCategory

#synth ModelCategory TopCat.{0}

/--
error: failed to synthesize
  CategoryWithCofibrations SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithCofibrations SSet.{u}

/--
error: failed to synthesize
  CategoryWithFibrations SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithFibrations SSet.{u}

/--
error: failed to synthesize
  CategoryWithWeakEquivalences SSet
-/
#guard_msgs (error, substring := true) in
#synth CategoryWithWeakEquivalences SSet.{u}

/--
error: failed to synthesize
  ModelCategory SSet
-/
#guard_msgs (error, substring := true) in
#synth ModelCategory SSet.{u}

end WrongScope

section GenericConstructor

variable (W : MorphismProperty SSet.{u})
  [W.HasTwoOutOfThreeProperty]
  [W.IsStableUnderRetracts]
  (hFactor : HasFunctorialFactorization
    (monomorphisms SSet.{u} ⊓ W)
    SSet.modelCategoryQuillen.J.{u}.rlp)
  (hRec : SSet.modelCategoryQuillen.I.{u}.rlp =
    SSet.modelCategoryQuillen.J.{u}.rlp ⊓ W)

noncomputable example : ModelCategory SSet.{u} :=
  SSet.modelCategoryQuillen.modelCategoryOf W hFactor hRec

end GenericConstructor

section ScopedPackage

open scoped SSet.modelCategoryQuillen

#synth CategoryWithCofibrations SSet.{u}
#synth CategoryWithFibrations SSet.{u}
#synth CategoryWithWeakEquivalences SSet.{u}
#synth ModelCategory SSet.{u}

example : (inferInstance : ModelCategory SSet.{u}) =
    SSet.modelCategoryQuillen.modelCategory := rfl

example : cofibrations SSet.{u} = monomorphisms SSet.{u} := rfl
example : fibrations SSet.{u} =
    SSet.modelCategoryQuillen.J.{u}.rlp := rfl
example : weakEquivalences SSet.{u} =
    SSet.realizationWeakEquivalences.{u} := rfl

example : SSet.modelCategoryQuillen.modelCategory.categoryWithCofibrations =
    SSet.modelCategoryQuillen.instCategoryWithCofibrations := rfl
example : SSet.modelCategoryQuillen.modelCategory.categoryWithFibrations =
    SSet.modelCategoryQuillen.instCategoryWithFibrations := rfl
example :
    SSet.modelCategoryQuillen.modelCategory.categoryWithWeakEquivalences =
      SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences := rfl

example : (inferInstance : CategoryWithCofibrations SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithCofibrations := rfl
example : (inferInstance : CategoryWithFibrations SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithFibrations := rfl
example : (inferInstance : CategoryWithWeakEquivalences SSet.{u}) =
    SSet.modelCategoryQuillen.instCategoryWithWeakEquivalences := rfl

#synth (weakEquivalences SSet.{u}).ContainsIdentities
#synth (weakEquivalences SSet.{u}).HasTwoOutOfThreeProperty
#synth (weakEquivalences SSet.{u}).IsStableUnderRetracts

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    Cofibration f ↔ Mono f :=
  SSet.modelCategoryQuillen.cofibration_iff f

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    Fibration f ↔ SSet.modelCategoryQuillen.J.{u}.rlp f :=
  SSet.modelCategoryQuillen.fibration_iff f

example {X Y : SSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ SSet.realizationWeakEquivalences f := by
  rw [weakEquivalence_iff]
  rfl

section IdentityAndIso

variable (X : SSet.{u})

example : Cofibration (𝟙 X) := by infer_instance
example : Fibration (𝟙 X) := by infer_instance
example : WeakEquivalence (𝟙 X) := by infer_instance

variable {X Y : SSet.{u}} (e : X ⟶ Y) [IsIso e]

example : Cofibration e := by infer_instance
example : Fibration e := by infer_instance
example : WeakEquivalence e := by infer_instance

end IdentityAndIso

section WeakFactorizationSystems

#synth IsWeakFactorizationSystem
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})

#synth IsWeakFactorizationSystem
  (cofibrations SSet.{u}) (trivialFibrations SSet.{u})

end WeakFactorizationSystems

section Factorizations

#synth HasFactorization
  (trivialCofibrations SSet.{u}) (fibrations SSet.{u})
#synth HasFactorization
  (cofibrations SSet.{u}) (trivialFibrations SSet.{u})

noncomputable example {X Y : SSet.{u}} (f : X ⟶ Y) :
    let d := factorizationData
      (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) f
    d.i ≫ d.p = f := by
  exact (factorizationData
    (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) f).fac

noncomputable example {X Y : SSet.{u}} (f : X ⟶ Y) :
    let d := factorizationData
      (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) f
    Cofibration d.i ∧ WeakEquivalence d.i ∧ Fibration d.p := by
  dsimp only
  let d := factorizationData
    (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) f
  have hi : Cofibration d.i ∧ WeakEquivalence d.i :=
    (mem_trivialCofibrations_iff d.i).mp d.hi
  have hp : Fibration d.p := (fibration_iff d.p).mpr d.hp
  exact ⟨hi.1, hi.2, hp⟩

noncomputable example {X Y : SSet.{u}} (f : X ⟶ Y) :
    let d := factorizationData
      (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) f
    d.i ≫ d.p = f := by
  exact (factorizationData
    (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) f).fac

noncomputable example {X Y : SSet.{u}} (f : X ⟶ Y) :
    let d := factorizationData
      (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) f
    Cofibration d.i ∧ Fibration d.p ∧ WeakEquivalence d.p := by
  dsimp only
  let d := factorizationData
    (cofibrations SSet.{u}) (trivialFibrations SSet.{u}) f
  have hi : Cofibration d.i := (cofibration_iff d.i).mpr d.hi
  have hp : Fibration d.p ∧ WeakEquivalence d.p :=
    (mem_trivialFibrations_iff d.p).mp d.hp
  exact ⟨hi, hp.1, hp.2⟩

end Factorizations

section Lifting

variable {A B X Y : SSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)

example [Cofibration i] [WeakEquivalence i] [Fibration p] :
    HasLiftingProperty i p := by infer_instance

example [Cofibration i] [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty i p := by infer_instance

end Lifting

section Generators

example : SSet.modelCategoryQuillen.I.{u}.rlp =
    trivialFibrations SSet.{u} := by
  rw [← SSet.rlp_monomorphisms,
    ← SSet.modelCategoryQuillen.cofibrations_eq,
    cofibrations_rlp]

example : SSet.modelCategoryQuillen.J.{u}.rlp.llp =
    trivialCofibrations SSet.{u} := by
  rw [← SSet.modelCategoryQuillen.fibrations_eq, fibrations_llp]

example (n : ℕ) :
    SSet.modelCategoryQuillen.I.{u} (SSet.boundary.{u} n).ι :=
  SSet.modelCategoryQuillen.boundary_ι_mem_I n

example (n : ℕ) :
    Cofibration (SSet.boundary.{u} n).ι :=
  SSet.modelCategoryQuillen.cofibration_of_mono _

example (n : ℕ) (i : Fin (n + 2)) :
    SSet.modelCategoryQuillen.J.{u} (SSet.horn.{u} (n + 1) i).ι := by
  let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  exact SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) i

example (n : ℕ) (i : Fin (n + 2)) :
    trivialCofibrations SSet.{u} (SSet.horn.{u} (n + 1) i).ι := by
  let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
  have h : SSet.modelCategoryQuillen.J.{u}.rlp.llp
      (SSet.horn.{u} (n + 1) i).ι :=
    le_llp_rlp (T := SSet.modelCategoryQuillen.J.{u}) _
      (SSet.modelCategoryQuillen.horn_ι_mem_J (n + 1) i)
  rw [← SSet.modelCategoryQuillen.fibrations_eq,
    fibrations_llp] at h
  exact h

example (n : ℕ) {X Y : SSet.{u}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty (SSet.boundary.{u} n).ι p := by
  let _ : Cofibration (SSet.boundary.{u} n).ι :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  infer_instance

example {X Y : SSet.{u}} (p : X ⟶ Y)
    [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty (SSet.boundary.{u} 0).ι p := by
  let _ : Cofibration (SSet.boundary.{u} 0).ι :=
    SSet.modelCategoryQuillen.cofibration_of_mono _
  infer_instance

example : trivialCofibrations SSet.{u}
    (SSet.horn.{u} 1 (0 : Fin 2)).ι := by
  have h : SSet.modelCategoryQuillen.J.{u}.rlp.llp
      (SSet.horn.{u} 1 (0 : Fin 2)).ι :=
    le_llp_rlp (T := SSet.modelCategoryQuillen.J.{u}) _
      (SSet.modelCategoryQuillen.horn_ι_mem_J 1 (0 : Fin 2))
  rw [← SSet.modelCategoryQuillen.fibrations_eq, fibrations_llp] at h
  exact h

example : trivialCofibrations SSet.{u}
    (SSet.horn.{u} 1 (1 : Fin 2)).ι := by
  have h : SSet.modelCategoryQuillen.J.{u}.rlp.llp
      (SSet.horn.{u} 1 (1 : Fin 2)).ι :=
    le_llp_rlp (T := SSet.modelCategoryQuillen.J.{u}) _
      (SSet.modelCategoryQuillen.horn_ι_mem_J 1 (1 : Fin 2))
  rw [← SSet.modelCategoryQuillen.fibrations_eq, fibrations_llp] at h
  exact h

end Generators

end ScopedPackage

section UniverseSpecializations

open scoped SSet.modelCategoryQuillen

#synth CategoryWithCofibrations SSet.{1}
#synth CategoryWithFibrations SSet.{1}
#synth CategoryWithWeakEquivalences SSet.{1}
#synth ModelCategory SSet.{1}
#synth CategoryWithCofibrations SSet.{0}
#synth CategoryWithFibrations SSet.{0}
#synth CategoryWithWeakEquivalences SSet.{0}
#synth ModelCategory SSet.{0}

noncomputable example : ModelCategory SSet.{1} :=
  SSet.modelCategoryQuillen.modelCategory

noncomputable example : ModelCategory SSet.{0} :=
  SSet.modelCategoryQuillen.modelCategory

example : weakEquivalences SSet.{1} =
    SSet.realizationWeakEquivalences.{1} := rfl

example : weakEquivalences SSet.{0} =
    SSet.realizationWeakEquivalences.{0} := rfl

end UniverseSpecializations

section PrivateAndAPIBoundaries

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.realizationFunctorialFactorizationData

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.I_rlp_eq_J_rlp_inf_realizationWeakEquivalences

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.modelCategoryFromRecognition

#guard_msgs (error, substring := true) in
#check SSet.realizationCounitIsIso

#guard_msgs (error, substring := true) in
#check SSet.realizationCoreflectionIso

#guard_msgs (error, substring := true) in
#check SSet.deltaRealizationAdjunction

#guard_msgs (error, substring := true) in
#check SSet.realSingCoreflectionIso

#guard_msgs (error, substring := true) in
#check SSet.deltaRealSingArrowIso

#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalence_of_fibration_of_isPullback

#guard_msgs (error, substring := true) in
#check SSet.minimal_I_rlp_of_realizationWeakEquivalence

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.realizationIsQuillenAdjunction

#guard_msgs (error, substring := true) in
#check SSet.modelCategoryQuillen.realizationIsQuillenEquivalence

end PrivateAndAPIBoundaries

section PullRequest4615Boundaries

#guard_msgs (error, substring := true) in
#check SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences_of_inner_rows

#guard_msgs (error, substring := true) in
#check SSet.bkHocolimMap_mem_realizationWeakEquivalences

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.weakEquivalence_map_of_isPushouts_of_cofibrant

#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isPushout_mono

#guard_msgs (error, substring := true) in
#check SSet.realizationWeakEquivalences.of_isColimit_nat_mono

end PullRequest4615Boundaries

#print axioms SSet.modelCategoryQuillen.modelCategoryOf
#print axioms SSet.modelCategoryQuillen.modelCategory

end MathlibExtTest.AlgebraicTopology.ModelCategory.SSetModelStructureTests
