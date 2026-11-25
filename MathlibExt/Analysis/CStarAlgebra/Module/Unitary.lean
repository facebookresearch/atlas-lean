/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable

/-!
# Unitary equivalences of right C-star modules

This file bundles an adjointable operator whose adjoint is a two-sided
inverse.  The coefficient, source, and target universes are independent, and
no completeness or fullness hypothesis is imposed.
-/

@[expose] public section

namespace CStarModule

universe uB uE uF uG

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. A unitary equivalence is an adjointable map between E and F whose adjoint is
its two-sided inverse. -/
structure UnitaryEquiv
    (B : Type uB) (E : Type uE) (F : Type uF)
    [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
    [CStarModule Bᵐᵒᵖ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
    [CStarModule Bᵐᵒᵖ F] where
  /-- Let B be a possibly nonunital complex C-star algebra and E and F normed right C-star modules
over B. A unitary module equivalence is an adjointable map whose adjoint is its two-sided
inverse. The forward map of the equivalence is an adjointable operator from E to F. -/
  toAdjointable : AdjointableOperator B E F
  /-- Let B be a possibly nonunital complex C-star algebra and E and F normed right C-star modules
over B. A unitary module equivalence is an adjointable map whose adjoint is its two-sided
inverse. The adjoint of the forward map followed by that map is the identity of E. -/
  adjoint_comp_self :
    toAdjointable.adjointOperator.comp toAdjointable =
      AdjointableOperator.id
  /-- Let B be a possibly nonunital complex C-star algebra and E and F normed right C-star modules
over B. A unitary module equivalence is an adjointable map whose adjoint is its two-sided
inverse. The forward map followed by its adjoint is the identity of F. -/
  comp_adjoint_self :
    toAdjointable.comp toAdjointable.adjointOperator =
      AdjointableOperator.id

namespace UnitaryEquiv

variable {B : Type uB} {E : Type uE} {F : Type uF} {G : Type uG}
variable [NonUnitalCStarAlgebra B] [PartialOrder Bᵐᵒᵖ]
variable [NormedAddCommGroup E] [NormedSpace ℂ E] [SMul Bᵐᵒᵖ E]
  [CStarModule Bᵐᵒᵖ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [SMul Bᵐᵒᵖ F]
  [CStarModule Bᵐᵒᵖ F]
variable [NormedAddCommGroup G] [NormedSpace ℂ G] [SMul Bᵐᵒᵖ G]
  [CStarModule Bᵐᵒᵖ G]

instance : FunLike (UnitaryEquiv B E F) E F where
  coe U := U.toAdjointable
  coe_injective U V h := by
    cases U
    cases V
    simp_all

instance : ContinuousLinearMapClass (UnitaryEquiv B E F) ℂ E F where
  map_add U := U.toAdjointable.toContinuousLinearMap.map_add
  map_smulₛₗ U := U.toAdjointable.toContinuousLinearMap.map_smul
  map_continuous U := U.toAdjointable.toContinuousLinearMap.continuous

@[simp]
theorem coe_toAdjointable (U : UnitaryEquiv B E F) :
    (U.toAdjointable : E → F) = U :=
  rfl

@[ext]
theorem ext {U V : UnitaryEquiv B E F} (h : ∀ x, U x = V x) : U = V := by
  apply DFunLike.coe_injective
  funext x
  exact h x

@[simp]
theorem adjoint_apply_apply (U : UnitaryEquiv B E F) (x : E) :
    U.toAdjointable.adjoint (U x) = x := by
  have h := congrArg (fun T : AdjointableOperator B E E ↦ T x)
    U.adjoint_comp_self
  simpa using h

@[simp]
theorem apply_adjoint_apply (U : UnitaryEquiv B E F) (y : F) :
    U (U.toAdjointable.adjoint y) = y := by
  have h := congrArg (fun T : AdjointableOperator B F F ↦ T y)
    U.comp_adjoint_self
  simpa using h

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. A unitary module equivalence preserves the B-valued inner product of every pair
of vectors. -/
theorem rightInner_map_map (U : UnitaryEquiv B E F) (x y : E) :
    rightInner (B := B) (U x) (U y) = rightInner (B := B) x y := by
  change rightInner (B := B) (U.toAdjointable x) (U.toAdjointable y) = _
  rw [U.toAdjointable.adjoint_inner]
  have hy : U.toAdjointable.adjoint (U.toAdjointable y) = y := by
    simpa only [coe_toAdjointable] using U.adjoint_apply_apply y
  rw [hy]

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. A unitary module equivalence preserves the norm of every vector. -/
@[simp]
theorem norm_map (U : UnitaryEquiv B E F) (x : E) :
    ‖U x‖ = ‖x‖ :=
  norm_map_of_map_rightInner id U (fun _ ↦ rfl) U.rightInner_map_map x

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. The map of a unitary module equivalence is an isometry. -/
theorem isometry (U : UnitaryEquiv B E F) : Isometry U := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, U.norm_map]

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. The identity map is a unitary equivalence of a module with itself. -/
def refl : UnitaryEquiv B E E where
  toAdjointable := AdjointableOperator.id
  adjoint_comp_self := by
    ext x
    rfl
  comp_adjoint_self := by
    ext x
    rfl

@[simp]
theorem refl_apply (x : E) : refl (B := B) (E := E) x = x :=
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. The adjoint reverses a unitary module equivalence. -/
def symm (U : UnitaryEquiv B E F) : UnitaryEquiv B F E where
  toAdjointable := U.toAdjointable.adjointOperator
  adjoint_comp_self := by
    simpa using U.comp_adjoint_self
  comp_adjoint_self := by
    simpa using U.adjoint_comp_self

theorem symm_apply (U : UnitaryEquiv B E F) (y : F) :
    U.symm y = U.toAdjointable.adjointOperator y :=
  rfl

@[simp]
theorem symm_apply_apply (U : UnitaryEquiv B E F) (x : E) :
    U.symm (U x) = x := by
  simpa only [symm_apply, AdjointableOperator.adjointOperator_apply] using
    U.adjoint_apply_apply x

@[simp]
theorem apply_symm_apply (U : UnitaryEquiv B E F) (y : F) :
    U (U.symm y) = y := by
  simpa only [symm_apply, AdjointableOperator.adjointOperator_apply] using
    U.apply_adjoint_apply y

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. A unitary module equivalence defines a complex-linear isometric equivalence of
the underlying normed spaces. -/
noncomputable def toLinearIsometryEquiv (U : UnitaryEquiv B E F) :
    E ≃ₗᵢ[ℂ] F where
  toFun := U
  invFun := U.symm
  left_inv := U.symm_apply_apply
  right_inv := U.apply_symm_apply
  map_add' := map_add U
  map_smul' := map_smul U
  norm_map' := U.norm_map

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. A complex-linear isometric equivalence that also preserves the B-valued module
inner product defines a unitary module equivalence. -/
noncomputable def ofLinearIsometryEquiv
    (e : E ≃ₗᵢ[ℂ] F)
    (hinner : ∀ x y,
      rightInner (B := B) (e x) (e y) =
        rightInner (B := B) x y) :
    UnitaryEquiv B E F where
  toAdjointable :=
    { toContinuousLinearMap :=
        e.toContinuousLinearEquiv.toContinuousLinearMap
      adjoint :=
        e.symm.toContinuousLinearEquiv.toContinuousLinearMap
      isAdjointPair' :=
        (AdjointableOperator.isAdjointPair_iff_adjoint_inner
          e.toContinuousLinearEquiv.toContinuousLinearMap
          e.symm.toContinuousLinearEquiv.toContinuousLinearMap).2 <| by
          intro x y
          simpa using hinner x (e.symm y) }
  adjoint_comp_self := by
    ext x
    exact e.symm_apply_apply x
  comp_adjoint_self := by
    ext y
    exact e.apply_symm_apply y

@[simp]
theorem ofLinearIsometryEquiv_apply
    (e : E ≃ₗᵢ[ℂ] F)
    (hinner : ∀ x y,
      rightInner (B := B) (e x) (e y) =
        rightInner (B := B) x y)
    (x : E) :
    ofLinearIsometryEquiv e hinner x = e x :=
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. Composition of unitary module equivalences is a unitary module equivalence. -/
def trans (U : UnitaryEquiv B E F) (V : UnitaryEquiv B F G) :
    UnitaryEquiv B E G where
  toAdjointable := V.toAdjointable.comp U.toAdjointable
  adjoint_comp_self := by
    ext x
    change U.toAdjointable.adjointOperator
      (V.toAdjointable.adjointOperator (V (U x))) = x
    rw [AdjointableOperator.adjointOperator_apply,
      AdjointableOperator.adjointOperator_apply,
      V.adjoint_apply_apply, U.adjoint_apply_apply]
  comp_adjoint_self := by
    ext x
    change V (U (U.toAdjointable.adjointOperator
      (V.toAdjointable.adjointOperator x))) = x
    rw [AdjointableOperator.adjointOperator_apply,
      AdjointableOperator.adjointOperator_apply,
      U.apply_adjoint_apply, V.apply_adjoint_apply]

@[simp]
theorem trans_apply (U : UnitaryEquiv B E F)
    (V : UnitaryEquiv B F G) (x : E) :
    U.trans V x = V (U x) :=
  rfl

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. Conjugation by a unitary module equivalence is a unital complex star algebra
homomorphism between the adjointable endomorphism algebras. -/
@[no_expose]
def conjStarAlgHom (U : UnitaryEquiv B E F) :
    AdjointableOperator.End B E →⋆ₐ[ℂ] AdjointableOperator.End B F where
  toFun T := U.toAdjointable.comp (T.comp U.toAdjointable.adjointOperator)
  map_one' := by
    ext y
    change U (U.symm y) = y
    exact U.apply_symm_apply y
  map_mul' := by
    intro T S
    ext y
    change U (T (S (U.symm y))) =
      U (T (U.symm (U (S (U.symm y)))))
    rw [U.symm_apply_apply]
  map_zero' := by
    ext y
    change U (0 : E) = 0
    exact map_zero U
  map_add' := by
    intro T S
    ext y
    change U (T (U.symm y) + S (U.symm y)) =
      U (T (U.symm y)) + U (S (U.symm y))
    exact map_add U _ _
  commutes' := by
    intro c
    ext y
    change U (c • U.symm y) = c • y
    rw [map_smul, U.apply_symm_apply]
  map_star' := by
    intro T
    change U.toAdjointable.comp
        (T.adjointOperator.comp U.toAdjointable.adjointOperator) =
      (U.toAdjointable.comp (T.comp U.toAdjointable.adjointOperator)).adjointOperator
    rw [AdjointableOperator.comp_adjointOperator,
      AdjointableOperator.comp_adjointOperator,
      AdjointableOperator.adjointOperator_adjointOperator]
    ext y
    rfl

/-- Let B be a possibly nonunital complex C-star algebra and E, F and G normed right C-star
modules over B. A unitary module equivalence is an adjointable map whose adjoint is its two-
sided inverse. Conjugation sends an endomorphism T of E to the composite of the unitary, T and
the unitary adjoint. -/
@[simp]
theorem conjStarAlgHom_apply (U : UnitaryEquiv B E F)
    (T : AdjointableOperator.End B E) (y : F) :
    U.conjStarAlgHom T y = U (T (U.symm y)) := by
  rfl

end UnitaryEquiv

end CStarModule
