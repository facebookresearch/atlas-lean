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
# Adjoint domains of densely defined right-module operators

Let `T : E → F` be a densely defined right-linear partial operator between right C-star modules
over a nonunital algebra `B` with star-compatible coefficient order. Its adjoint domain is `{y ∈
F | ∃ z ∈ E, ∀ x ∈ dom T, ⟨T x, y⟩_B = ⟨x, z⟩_B}`. Density of `dom T` makes `z` unique, and `T*
y = z` defines a complex-linear partial map whose domain is stable under right coefficients.

The graph of `T*` is the set of pairs satisfying all these pairing equations, hence is closed in
the product norm topology. The construction applies to pre-Hilbert modules; density of the
adjoint domain is a separate condition.
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

/-- **Adjoint pairing witness.** For a dense right-module partial operator `T`, `z : E` is a
witness for `y : F` when `⟨T x, y⟩_B = ⟨x, z⟩_B` for every `x ∈ dom T`. -/
def IsAdjointWitness (T : DenselyDefinedRightPartialOperator B E F) (y : F) (z : E) :
    Prop :=
  ∀ x : T.toPartial.domain,
    rightInner (B := B) (T.toPartial x) y = rightInner (B := B) (x : E) z

/-- **Full adjoint domain.** For a dense right-module partial operator `T : E → F`, this complex
submodule is the set of `y : F` admitting a witness `z : E` for `⟨T x, y⟩_B = ⟨x, z⟩_B` on
`dom T`. -/
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

/-- **Membership in the adjoint domain.** `y ∈ adjointDomain T` exactly when some `z : E`
satisfies `IsAdjointWitness T y z`. -/
@[simp]
theorem mem_adjointDomain_iff (T : DenselyDefinedRightPartialOperator B E F) (y : F) :
    y ∈ adjointDomain T ↔ ∃ z : E, IsAdjointWitness T y z := Iff.rfl

/-- **Right invariance of the adjoint domain.** For a dense right-module operator, `y ∈ dom T*`
implies `y <• b ∈ dom T*` for every coefficient `b : B`. -/
theorem adjointDomain_right_smul (T : DenselyDefinedRightPartialOperator B E F)
    {y : F} (hy : y ∈ adjointDomain T) (b : B) : y <• b ∈ adjointDomain T := by
  rcases hy with ⟨z, hz⟩
  refine ⟨z <• b, ?_⟩
  intro x
  rw [rightInner_right_smul, rightInner_right_smul, hz x]

variable [StarOrderedRing Bᵐᵒᵖ]

/-- **Uniqueness of adjoint witnesses.** If `z,z'` both satisfy `⟨T x, y⟩_B = ⟨x, z⟩_B` on the
dense domain of `T`, then `z = z'`. -/
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

/-- **Unique witness on the adjoint domain.** Every `y : adjointDomain T` has exactly one `z : E`
satisfying the adjoint pairing equation on `dom T`. -/
theorem existsUnique_adjointWitness (T : DenselyDefinedRightPartialOperator B E F)
    (y : adjointDomain T) : ∃! z : E, IsAdjointWitness T (y : F) z := by
  rcases y.property with ⟨z, hz⟩
  refine ⟨z, hz, ?_⟩
  intro z' hz'
  exact adjointWitness_unique T hz' hz

/-- **Value of the partial adjoint.** For `y ∈ dom T*`, `adjointValue T y` is the unique `z : E`
satisfying `⟨T x, y⟩_B = ⟨x, z⟩_B` for all `x ∈ dom T`. -/
def adjointValue (T : DenselyDefinedRightPartialOperator B E F) (y : adjointDomain T) : E :=
  Classical.choose (existsUnique_adjointWitness T y)

/-- **Pairing characterization of the adjoint value.** `IsAdjointWitness T y (adjointValue T y)`
holds for every `y : adjointDomain T`. -/
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

/-- **Right linearity of the adjoint value.** For `y ∈ dom T*` and `b : B`, the adjoint value of
`y <• b` is `adjointValue T y <• b`. -/
theorem adjointValue_right_smul (T : DenselyDefinedRightPartialOperator B E F)
    (y : adjointDomain T) (b : B) :
    adjointValue T ⟨(y : F) <• b, adjointDomain_right_smul T y.property b⟩ =
      adjointValue T y <• b := by
  apply adjointWitness_unique T (adjointValue_spec T
    ⟨(y : F) <• b, adjointDomain_right_smul T y.property b⟩)
  intro x
  rw [rightInner_right_smul, rightInner_right_smul, adjointValue_spec T y x]

/-- **Complex-linear partial adjoint.** For a densely defined right-module map `T : E → F`,
`adjoint T : F →ₗ.[ℂ] E` has the full witness domain and evaluates each vector at its unique
adjoint witness. -/
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

/-- **Pairing identity for the partial adjoint.** For `x ∈ dom T` and `y ∈ dom T*`, `⟨T x, y⟩_B =
⟨x, T* y⟩_B`. -/
theorem adjoint_pairing (T : DenselyDefinedRightPartialOperator B E F)
    (x : T.toPartial.domain) (y : adjointDomain T) :
    rightInner (B := B) (T.toPartial x) (y : F) =
      rightInner (B := B) (x : E) ((adjoint T) y) :=
  adjointValue_spec T y x

/-- **Right linearity of the partial adjoint.** On the full adjoint domain, `T* (y <• b) = T* y <•
b` for every `b : B`. -/
theorem adjoint_right_smul (T : DenselyDefinedRightPartialOperator B E F)
    (y : adjointDomain T) (b : B) :
    (adjoint T) ⟨(y : F) <• b, adjointDomain_right_smul T y.property b⟩ =
      (adjoint T) y <• b :=
  adjointValue_right_smul T y b

/-- **Graph of the partial adjoint.** The graph is exactly `{(y,z) ∈ F × E | ∀ x ∈ dom T, ⟨T x,
y⟩_B = ⟨x, z⟩_B}`. -/
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

/-- **Closed graph of the partial adjoint.** For a densely defined right-module operator, the full
adjoint graph is closed in the product norm topology on `F × E`. -/
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
