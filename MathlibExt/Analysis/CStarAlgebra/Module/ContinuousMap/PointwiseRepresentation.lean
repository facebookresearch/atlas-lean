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

public import MathlibExt.Analysis.CStarAlgebra.Module.ContinuousMap.Operators
public import MathlibExt.Analysis.CStarAlgebra.Module.ContinuousMap.ConstantOperators
public import MathlibExt.Analysis.CStarAlgebra.ContinuousMap.Hom

/-!
# Continuous coefficient paths acting on the original section module

For an actual coefficient representation on E, a continuous D-valued path
acts pointwise on C(X,E). The left algebra is C(X,D) and the right algebra
is C(X,B). The original supremum norm and coefficient inner product are
used. Contractivity of the given representation proves the vector orbit
continuity required by the existing strong-adjoint section constructor.

This is the representation required by Blackadar's interval amplification
in the proof of18.4.4. It is distinct from extending only the right algebra
while retaining D as the left algebra. No cycle compactness, product,
homotopy, output norm or module dictionary is supplied by the caller.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra RightActions

namespace CStarModule.AdjointableOperator

universe uX uD uB uE

variable {D : Type uD} [NonUnitalCStarAlgebra D]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E]

/--
Let D and B be possibly nonunital complex C*-algebras, with a star-compatible partial order on
Bᵐᵒᵖ. Let E be a normed right inner-product B-module with a compatible complex normed-space
structure, and let ρ be a nonunital complex star representation of D by adjointable
endomorphisms of E.

For x ∈ E, the map a ↦ ρ(a)x is bounded and complex-linear from D to E.
-/
def coefficientVectorCLM (rho : D →⋆ₙₐ[ℂ] End B E) (x : E) : D →L[ℂ] E := by
  let L : D →ₗ[ℂ] E :=
    { toFun := fun a => rho a x
      map_add' := by
        intro a b
        simp only [map_add, add_apply]
      map_smul' := by
        intro c a
        simp only [map_smul, smul_apply, RingHom.id_apply] }
  exact L.mkContinuous ‖x‖ fun a => by
    change ‖rho a x‖ ≤ ‖x‖ * ‖a‖
    calc
      ‖rho a x‖ ≤ ‖rho a‖ * ‖x‖ := (rho a).toContinuousLinearMap.le_opNorm x
      _ ≤ ‖a‖ * ‖x‖ := mul_le_mul_of_nonneg_right
        (norm_nonUnitalStarAlgHom_apply_le rho a) (norm_nonneg x)
      _ = ‖x‖ * ‖a‖ := mul_comm _ _

/--
Let D and B be possibly nonunital complex C*-algebras, with a star-compatible partial order on
Bᵐᵒᵖ. Let E be a normed right inner-product B-module with a compatible complex normed-space
structure, and let ρ be a nonunital complex star representation of D by adjointable
endomorphisms of E.

For x ∈ E and a ∈ D, the bounded vector map associated to x evaluates to ρ(a)x.
-/
@[simp]
theorem coefficientVectorCLM_apply (rho : D →⋆ₙₐ[ℂ] End B E) (x : E) (a : D) :
    coefficientVectorCLM rho x a = rho a x := rfl

/--
Let D and B be possibly nonunital complex C*-algebras, with a star-compatible partial order on
Bᵐᵒᵖ. Let E be a normed right inner-product B-module with a compatible complex normed-space
structure, and let ρ be a nonunital complex star representation of D by adjointable
endomorphisms of E. Let X be a compact topological space and equip C(X, B)ᵐᵒᵖ with a
star-compatible partial order.

Pointwise evaluation defines a nonunital complex star representation of C(X, D) on the right
C(X, B)-module C(X, E).
-/
def continuousCoefficientRepresentation
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (rho : D →⋆ₙₐ[ℂ] End B E) :
    letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
      CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
    letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
      CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
    C(X, D) →⋆ₙₐ[ℂ] End C(X, B) C(X, E) := by
  letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
  letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
  exact continuousMapRepresentation X
    (fun t => rho.comp (_root_.ContinuousMap.evalNonUnitalStarAlgHom t))
    (fun a x => (coefficientVectorCLM rho x).continuous.comp a.continuous)

/--
Let D and B be possibly nonunital complex C*-algebras, with a star-compatible partial order on
Bᵐᵒᵖ. Let E be a normed right inner-product B-module with a compatible complex normed-space
structure, and let ρ be a nonunital complex star representation of D by adjointable
endomorphisms of E. Let X be a compact topological space and equip C(X, B)ᵐᵒᵖ with a
star-compatible partial order.

For a ∈ C(X, D), f ∈ C(X, E) and t ∈ X, the induced representation satisfies (ρ_X(a)f)(t) =
ρ(a(t))(f(t)).
-/
@[simp]
theorem continuousCoefficientRepresentation_apply
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    (rho : D →⋆ₙₐ[ℂ] End B E) (a : C(X, D)) (f : C(X, E)) (t : X) :
    letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
      CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
    letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
      CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
    continuousCoefficientRepresentation X rho a f t = rho (a t) (f t) := by
  let : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
  exact continuousMapRepresentation_apply X
    (fun s => rho.comp (_root_.ContinuousMap.evalNonUnitalStarAlgHom s))
    (fun b x => (coefficientVectorCLM rho x).continuous.comp b.continuous) a f t

/--
Let D and B be possibly nonunital complex C*-algebras, with a star-compatible partial order on
Bᵐᵒᵖ. Let E be a normed right inner-product B-module with a compatible complex normed-space
structure, and let ρ be a nonunital complex star representation of D by adjointable
endomorphisms of E. Let X be a compact topological space and equip C(X, B)ᵐᵒᵖ with a
star-compatible partial order.

If E is complete, the action of a constant coefficient a ∈ D is the constant extension of the
adjointable endomorphism ρ(a).
-/
theorem continuousCoefficientRepresentation_const
    (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
    [CompleteSpace E] (rho : D →⋆ₙₐ[ℂ] End B E) (a : D) :
    letI : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
      CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
    letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
      CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
    continuousCoefficientRepresentation X rho (_root_.ContinuousMap.const X a) =
      CStarModule.ContinuousMap.constantEndomorphismMap (B := B) X (rho a) := by
  let : SMul (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.rightAction (B := B) (E := E) X
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, E) :=
    CStarModule.ContinuousMap.cstarModule (B := B) (E := E) X
  apply AdjointableOperator.ext
  intro f
  apply _root_.ContinuousMap.ext
  intro t
  simp only [continuousCoefficientRepresentation_apply, _root_.ContinuousMap.const_apply,
    CStarModule.ContinuousMap.constantEndomorphismMap_apply]

end CStarModule.AdjointableOperator
