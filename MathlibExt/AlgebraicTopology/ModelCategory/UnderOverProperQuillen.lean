/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Proper
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction
public import MathlibExt.AlgebraicTopology.ModelCategory.Under
public import Mathlib.CategoryTheory.Comma.Over.Pullback

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Properness and Quillen adjunctions for Under and Over categories

The model structures on `Under S` and `Over S` create their three model
classes through the forgetful functor.  Properness therefore descends from
the base along the corresponding created pushout and pullback squares.

The four standard free/forgetful and base-change adjunctions are Quillen for
the same reason: their relevant adjoint leaves the underlying morphism
unchanged.  The Quillen results are named theorem values, not instances.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open HomotopicalAlgebra CategoryTheory.Limits
open CategoryTheory.MorphismProperty

namespace CategoryTheory.Under

variable {C : Type u} [Category.{v} C]

/-- Left properness descends to an Under category. -/
instance instIsLeftProper (S : C) [ModelCategory C] [IsLeftProper C] :
    IsLeftProper (Under S) where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    constructor
    intro A B i hi
    constructor
    intro X Y j f' f sq hf
    have hi' : cofibrations C i.right := by
      simpa [cofibrations_under_def, MorphismProperty.under_iff] using hi
    have hf' : weakEquivalences C f.right := by
      simpa [weakEquivalences_under_def, MorphismProperty.under_iff] using hf
    let _ : Cofibration ((Under.forget S).map i) := by
      change Cofibration i.right
      exact (cofibration_iff i.right).mpr hi'
    let _ : WeakEquivalence ((Under.forget S).map f) := by
      change WeakEquivalence f.right
      exact (weakEquivalence_iff f.right).mpr hf'
    have h : WeakEquivalence ((Under.forget S).map f') :=
      IsLeftProper.weakEquivalence_of_isPushout (sq.map (Under.forget S))
    change WeakEquivalence f'.right at h
    rw [weakEquivalences_under_def, MorphismProperty.under_iff]
    exact (weakEquivalence_iff f'.right).mp h

/-- Right properness descends to an Under category. -/
instance instIsRightProper (S : C) [ModelCategory C] [IsRightProper C] :
    IsRightProper (Under S) where
  weakEquivalences_isStableUnderBaseChangeAgainst_fibrations := by
    constructor
    intro X Y p hp
    constructor
    intro Z W f' g' g sq hg
    have hp' : fibrations C p.right := by
      simpa [fibrations_under_def, MorphismProperty.under_iff] using hp
    have hg' : weakEquivalences C g.right := by
      simpa [weakEquivalences_under_def, MorphismProperty.under_iff] using hg
    let _ : Fibration ((Under.forget S).map p) := by
      change Fibration p.right
      exact (fibration_iff p.right).mpr hp'
    let _ : WeakEquivalence ((Under.forget S).map g) := by
      change WeakEquivalence g.right
      exact (weakEquivalence_iff g.right).mpr hg'
    have h : WeakEquivalence ((Under.forget S).map g') :=
      IsRightProper.weakEquivalence_of_isPullback (sq.map (Under.forget S))
    change WeakEquivalence g'.right at h
    rw [weakEquivalences_under_def, MorphismProperty.under_iff]
    exact (weakEquivalence_iff g'.right).mp h

/-- The free-under-object/forgetful adjunction is Quillen. -/
theorem costarAdjForget_isQuillenAdjunction (S : C) [ModelCategory C] :
    Adjunction.IsQuillenAdjunction (Under.costarAdjForget S) :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (by
      intro X Y p hp
      change fibrations C p.right
      simpa [fibrations_under_def, MorphismProperty.under_iff] using hp)
    (by
      intro X Y p hp
      change trivialFibrations C p.right
      simpa [trivialFibrations_under_eq, MorphismProperty.under_iff] using hp)

/-- Pushout along a base map is left Quillen to restriction of Under
objects. -/
theorem mapPushoutAdj_isQuillenAdjunction {S T : C} (f : S ⟶ T)
    [ModelCategory C] :
    Adjunction.IsQuillenAdjunction (Under.mapPushoutAdj f) :=
  Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
    (by
      intro X Y p hp
      change fibrations C p.right
      simpa [fibrations_under_def, MorphismProperty.under_iff] using hp)
    (by
      intro X Y p hp
      change trivialFibrations C p.right
      simpa [trivialFibrations_under_eq, MorphismProperty.under_iff] using hp)

end CategoryTheory.Under

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C]

/-- Left properness descends to an Over category. -/
instance instIsLeftProper (S : C) [ModelCategory C] [IsLeftProper C] :
    IsLeftProper (Over S) where
  weakEquivalences_isStableUnderCobaseChangeAgainst_cofibrations := by
    constructor
    intro A B i hi
    constructor
    intro X Y j f' f sq hf
    have hi' : cofibrations C i.left := by
      simpa [cofibrations_over_def, MorphismProperty.over_iff] using hi
    have hf' : weakEquivalences C f.left := by
      simpa [weakEquivalences_over_def, MorphismProperty.over_iff] using hf
    let _ : Cofibration ((Over.forget S).map i) := by
      change Cofibration i.left
      exact (cofibration_iff i.left).mpr hi'
    let _ : WeakEquivalence ((Over.forget S).map f) := by
      change WeakEquivalence f.left
      exact (weakEquivalence_iff f.left).mpr hf'
    have h : WeakEquivalence ((Over.forget S).map f') :=
      IsLeftProper.weakEquivalence_of_isPushout (sq.map (Over.forget S))
    change WeakEquivalence f'.left at h
    rw [weakEquivalences_over_def, MorphismProperty.over_iff]
    exact (weakEquivalence_iff f'.left).mp h

/-- Right properness descends to an Over category. -/
instance instIsRightProper (S : C) [ModelCategory C] [IsRightProper C] :
    IsRightProper (Over S) where
  weakEquivalences_isStableUnderBaseChangeAgainst_fibrations := by
    constructor
    intro X Y p hp
    constructor
    intro Z W f' g' g sq hg
    have hp' : fibrations C p.left := by
      simpa [fibrations_over_def, MorphismProperty.over_iff] using hp
    have hg' : weakEquivalences C g.left := by
      simpa [weakEquivalences_over_def, MorphismProperty.over_iff] using hg
    let _ : Fibration ((Over.forget S).map p) := by
      change Fibration p.left
      exact (fibration_iff p.left).mpr hp'
    let _ : WeakEquivalence ((Over.forget S).map g) := by
      change WeakEquivalence g.left
      exact (weakEquivalence_iff g.left).mpr hg'
    have h : WeakEquivalence ((Over.forget S).map g') :=
      IsRightProper.weakEquivalence_of_isPullback (sq.map (Over.forget S))
    change WeakEquivalence g'.left at h
    rw [weakEquivalences_over_def, MorphismProperty.over_iff]
    exact (weakEquivalence_iff g'.left).mp h

/-- The forgetful/cofree-over-object adjunction is Quillen. -/
theorem forgetAdjStar_isQuillenAdjunction (S : C) [ModelCategory C] :
    Adjunction.IsQuillenAdjunction (Over.forgetAdjStar S) where
  preservesCofibrations := by
    intro X Y i hi
    change cofibrations C i.left
    simpa [cofibrations_over_def, MorphismProperty.over_iff] using hi
  preservesTrivialCofibrations := by
    intro X Y i hi
    change trivialCofibrations C i.left
    simpa [trivialCofibrations_over_eq, MorphismProperty.over_iff] using hi

/-- Postcomposition along a base map is left Quillen to pullback of Over
objects. -/
theorem mapPullbackAdj_isQuillenAdjunction {S T : C} (f : S ⟶ T)
    [ModelCategory C] :
    Adjunction.IsQuillenAdjunction (Over.mapPullbackAdj f) where
  preservesCofibrations := by
    intro X Y i hi
    change cofibrations C i.left
    simpa [cofibrations_over_def, MorphismProperty.over_iff] using hi
  preservesTrivialCofibrations := by
    intro X Y i hi
    change trivialCofibrations C i.left
    simpa [trivialCofibrations_over_eq, MorphismProperty.over_iff] using hi

end CategoryTheory.Over
