/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.RectangularPartial
public import MathlibExt.Analysis.CStarAlgebra.Module.Right
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The actual adjoint of a dense rectangular right-module operator

The adjoint domain is the full set of vectors admitting a coefficient-valued
pairing witness. Density makes that witness unique, and the chosen value
defines the actual complex-linear partial adjoint and right-module action.
The graph is precisely the intersection of its closed pairing equations.
No density of the adjoint domain, closedness of the original operator,
regularity or orthogonal complement is assumed.

The compatible `StarOrderedRing` dictionary is the one used by the existing
right-inner-product continuity API. The canonical spectral order supplies
it for the original C-star coefficient algebra; no unit is required.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped RightActions

namespace CStarModule.DenselyDefinedRightPartialOperator

universe uB uE uF

variable {B : Type uB} {E : Type uE} {F : Type uF}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F] [CStarModule Bᵐᵒᵖ F]

/-- The literal coefficient pairing equation defining an adjoint witness. -/
def IsAdjointWitness (T : DenselyDefinedRightPartialOperator B E F) (y : F) (z : E) :
    Prop :=
  ∀ x : T.toPartial.domain,
    rightInner (B := B) (T.toPartial x) y = rightInner (B := B) (x : E) z

/-- Every vector admitting an actual adjoint witness belongs to the full adjoint domain. -/
def adjointDomain (T : DenselyDefinedRightPartialOperator B E F) : Submodule ℂ F where
  carrier := {y | ∃ z : E, IsAdjointWitness T y z}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro x
    rw [rightInner_zero_right, rightInner_zero_right]
  add_mem' := by
    rintro y y' ⟨z, hz⟩ ⟨z', hz'⟩
    refine ⟨z + z', ?_⟩
    intro x
    rw [rightInner_add_right, rightInner_add_right, hz x, hz' x]
  smul_mem' := by
    rintro c y ⟨z, hz⟩
    refine ⟨c • z, ?_⟩
    intro x
    rw [rightInner_smul_right, rightInner_smul_right, hz x]

/-- The domain is exactly the original full witness set. -/
@[simp]
theorem mem_adjointDomain_iff (T : DenselyDefinedRightPartialOperator B E F) (y : F) :
    y ∈ adjointDomain T ↔ ∃ z : E, IsAdjointWitness T y z := Iff.rfl

/-- The full adjoint domain is stable under right multiplication by the coefficient algebra. -/
theorem adjointDomain_right_smul (T : DenselyDefinedRightPartialOperator B E F)
    {y : F} (hy : y ∈ adjointDomain T) (b : B) : y <• b ∈ adjointDomain T := by
  rcases hy with ⟨z, hz⟩
  refine ⟨z <• b, ?_⟩
  intro x
  rw [rightInner_right_smul, rightInner_right_smul, hz x]

variable [StarOrderedRing Bᵐᵒᵖ]

/-- Density of the original domain makes each adjoint witness unique. -/
theorem adjointWitness_unique (T : DenselyDefinedRightPartialOperator B E F)
    {y : F} {z z' : E} (hz : IsAdjointWitness T y z) (hz' : IsAdjointWitness T y z') :
    z = z' := by
  apply ext_rightInner (B := B)
  intro x
  have h := Continuous.ext_on T.dense_domain
    (continuous_rightInner_left (B := B) z)
    (continuous_rightInner_left (B := B) z')
    (by
      intro u hu
      exact (hz ⟨u, hu⟩).symm.trans (hz' ⟨u, hu⟩))
  exact congrFun h x

/-- The full domain supplies a proved unique witness for every one of its vectors. -/
theorem existsUnique_adjointWitness (T : DenselyDefinedRightPartialOperator B E F)
    (y : adjointDomain T) : ∃! z : E, IsAdjointWitness T (y : F) z := by
  rcases y.property with ⟨z, hz⟩
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  exact adjointWitness_unique T hz' hz

/-- The actual adjoint value is the unique witness already proved to exist in its domain. -/
def adjointValue (T : DenselyDefinedRightPartialOperator B E F) (y : adjointDomain T) : E :=
  Classical.choose (existsUnique_adjointWitness T y)

/-- The constructed value satisfies the full original pairing equation. -/
theorem adjointValue_spec (T : DenselyDefinedRightPartialOperator B E F)
    (y : adjointDomain T) : IsAdjointWitness T (y : F) (adjointValue T y) :=
  (Classical.choose_spec (existsUnique_adjointWitness T y)).1

@[simp]
theorem adjointValue_zero (T : DenselyDefinedRightPartialOperator B E F) :
    adjointValue T 0 = 0 := by
  apply adjointWitness_unique T (adjointValue_spec T 0)
  intro x
  change rightInner (B := B) (T.toPartial x) (0 : F) =
    rightInner (B := B) (x : E) (0 : E)
  rw [rightInner_zero_right, rightInner_zero_right]

@[simp]
theorem adjointValue_add (T : DenselyDefinedRightPartialOperator B E F)
    (y y' : adjointDomain T) :
    adjointValue T (y + y') = adjointValue T y + adjointValue T y' := by
  apply adjointWitness_unique T (adjointValue_spec T (y + y'))
  intro x
  change rightInner (B := B) (T.toPartial x) ((y : F) + (y' : F)) =
    rightInner (B := B) (x : E) (adjointValue T y + adjointValue T y')
  rw [rightInner_add_right, rightInner_add_right,
    adjointValue_spec T y x, adjointValue_spec T y' x]

@[simp]
theorem adjointValue_smul (T : DenselyDefinedRightPartialOperator B E F)
    (c : ℂ) (y : adjointDomain T) :
    adjointValue T (c • y) = c • adjointValue T y := by
  apply adjointWitness_unique T (adjointValue_spec T (c • y))
  intro x
  change rightInner (B := B) (T.toPartial x) (c • (y : F)) =
    rightInner (B := B) (x : E) (c • adjointValue T y)
  rw [rightInner_smul_right, rightInner_smul_right, adjointValue_spec T y x]

/-- The selected adjoint witness preserves the original right coefficient multiplication. -/
theorem adjointValue_right_smul (T : DenselyDefinedRightPartialOperator B E F)
    (y : adjointDomain T) (b : B) :
    adjointValue T ⟨(y : F) <• b, adjointDomain_right_smul T y.property b⟩ =
      adjointValue T y <• b := by
  apply adjointWitness_unique T (adjointValue_spec T
    ⟨(y : F) <• b, adjointDomain_right_smul T y.property b⟩)
  intro x
  rw [rightInner_right_smul, rightInner_right_smul, adjointValue_spec T y x]

/-- The genuine rectangular complex-linear partial adjoint on its full witness domain. -/
def adjoint (T : DenselyDefinedRightPartialOperator B E F) : F →ₗ.[ℂ] E where
  domain := adjointDomain T
  toFun :=
    { toFun := adjointValue T
      map_add' := adjointValue_add T
      map_smul' := fun c y => by
        simpa only [RingHom.id_apply] using adjointValue_smul T c y }

@[simp]
theorem adjoint_domain (T : DenselyDefinedRightPartialOperator B E F) :
    (adjoint T).domain = adjointDomain T := rfl

@[simp]
theorem adjoint_apply (T : DenselyDefinedRightPartialOperator B E F)
    (y : adjointDomain T) : (adjoint T) y = adjointValue T y := rfl

/-- The partial adjoint satisfies the original coefficient-valued pairing on both domains. -/
theorem adjoint_pairing (T : DenselyDefinedRightPartialOperator B E F)
    (x : T.toPartial.domain) (y : adjointDomain T) :
    rightInner (B := B) (T.toPartial x) (y : F) =
      rightInner (B := B) (x : E) ((adjoint T) y) :=
  adjointValue_spec T y x

/-- The partial adjoint is right-linear on its actual source domain. -/
theorem adjoint_right_smul (T : DenselyDefinedRightPartialOperator B E F)
    (y : adjointDomain T) (b : B) :
    (adjoint T) ⟨(y : F) <• b, adjointDomain_right_smul T y.property b⟩ =
      (adjoint T) y <• b :=
  adjointValue_right_smul T y b

/-- The actual graph consists of all pairs satisfying the original full pairing equations. -/
theorem adjoint_graph_eq (T : DenselyDefinedRightPartialOperator B E F) :
    ((adjoint T).graph : Set (F × E)) =
      {p | IsAdjointWitness T p.1 p.2} := by
  ext p
  constructor
  · intro hp
    rcases (LinearPMap.mem_graph_iff (adjoint T)).1 hp with ⟨y, hy, hz⟩
    have h := adjointValue_spec T y
    change IsAdjointWitness T (y : F) ((adjoint T) y) at h
    rw [hy, hz] at h
    exact h
  · intro hp
    have hy : p.1 ∈ adjointDomain T := ⟨p.2, hp⟩
    apply (LinearPMap.mem_graph_iff (adjoint T)).2
    refine ⟨⟨p.1, hy⟩, rfl, ?_⟩
    exact adjointWitness_unique T (adjointValue_spec T ⟨p.1, hy⟩) hp

/-- The full witness graph is closed in the original product norm topology. -/
theorem isClosed_adjoint_graph (T : DenselyDefinedRightPartialOperator B E F) :
    IsClosed ((adjoint T).graph : Set (F × E)) := by
  have hs : {p : F × E | IsAdjointWitness T p.1 p.2} =
      ⋂ x : T.toPartial.domain,
        {p | rightInner (B := B) (T.toPartial x) p.1 = rightInner (B := B) (x : E) p.2} := by
    ext p
    simp only [IsAdjointWitness, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [adjoint_graph_eq, hs]
  apply isClosed_iInter
  intro x
  exact isClosed_eq
    ((continuous_rightInner_right (B := B) (T.toPartial x)).comp continuous_fst)
    ((continuous_rightInner_right (B := B) (x : E)).comp continuous_snd)

end CStarModule.DenselyDefinedRightPartialOperator
