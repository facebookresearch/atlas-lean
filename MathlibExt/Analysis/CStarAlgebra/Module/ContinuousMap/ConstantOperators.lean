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

public import MathlibExt.Analysis.CStarAlgebra.Module.ContinuousMap.TensorModel
public import MathlibExt.Analysis.CStarAlgebra.Module.InternalTensorProduct.CanonicalBaseChange

/-!
# Constant adjointable operators on the original continuous-section module

The existing full constant-coefficient tensor model supplies a unital
endomorphism homomorphism and countable generation. Its dense pure span
identifies the operator with literal pointwise composition. The canonical
vector map is the actual constant section, giving the constant rank-one
formula and preservation of genuine Hilbert-module compacts.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped CStarAlgebra CStarModule.Right RightActions

namespace CStarModule.ContinuousMap

universe uX uB uE

variable (X : Type uX) [TopologicalSpace X] [CompactSpace X]
variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
  [PartialOrder (C(X, B))ᵐᵒᵖ] [StarOrderedRing (C(X, B))ᵐᵒᵖ]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

attribute [local instance] CStarModule.ContinuousMap.rightAction
  CStarModule.ContinuousMap.cstarModule

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures. Let X be a compact topological space, and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

Applying a fixed adjointable endomorphism of E pointwise defines a unital complex star
homomorphism into the adjointable endomorphisms of C(X, E) over C(X, B).
-/
def constantEndomorphismMap : AdjointableOperator.End B E →⋆ₐ[ℂ]
    AdjointableOperator.End C(X, B) C(X, E) := by
  letI : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) := CStarModule.Right.selfModule
  exact InternalTensorProduct.IsModel.mapLeftStarAlgHom
    (InternalTensorProduct.continuousMap_isModel (B := B) (E := E) X)

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures. Let X be a compact topological space, and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

For an adjointable endomorphism T of E, the forward bounded map of its constant extension sends
f ∈ C(X, E) to the function t ↦ T(f(t)).
-/
theorem constantEndomorphismMap_toContinuousLinearMap (T : AdjointableOperator.End B E) :
    (constantEndomorphismMap (B := B) (E := E) X T).toContinuousLinearMap =
      T.toContinuousLinearMap.compLeftContinuous ℂ X := by
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) := CStarModule.Right.selfModule
  apply ContinuousLinearMap.ext_on
    (InternalTensorProduct.continuousMap_isModel (B := B) (E := E) X).2.2.2.2.2.2.2
  rintro _ ⟨⟨e, b⟩, rfl⟩
  change constantEndomorphismMap (B := B) (E := E) X T
      (InternalTensorProduct.continuousMapPure (B := B) X e b) =
    T.toContinuousLinearMap.compLeftContinuous ℂ X
      (InternalTensorProduct.continuousMapPure (B := B) X e b)
  rw [constantEndomorphismMap, InternalTensorProduct.IsModel.mapLeftStarAlgHom_pure]
  apply _root_.ContinuousMap.ext
  intro t
  change T e <• b t = T (e <• b t)
  exact (T.map_right_smul e (b t)).symm

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures. Let X be a compact topological space, and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

For an adjointable endomorphism T of E, f ∈ C(X, E) and t ∈ X, the constant extension satisfies
(T_X f)(t) = T(f(t)).
-/
@[simp]
theorem constantEndomorphismMap_apply (T : AdjointableOperator.End B E)
    (f : C(X, E)) (t : X) :
    constantEndomorphismMap (B := B) (E := E) X T f t = T (f t) :=
  congrArg (fun L : C(X, E) →L[ℂ] C(X, E) => L f t)
    (constantEndomorphismMap_toContinuousLinearMap (B := B) (E := E) X T)

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures. Let X be a compact topological space, and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

For coefficient change B → C(X, B) by constant functions, the canonical vector map sends x ∈ E
to the constant E-valued function with value x.
-/
theorem canonicalBaseChangeMap_eq_const (x : E) :
    InternalTensorProduct.IsModel.canonicalBaseChangeMap
        (InternalTensorProduct.continuousMap_isModel (B := B) (E := E) X) x =
      _root_.ContinuousMap.const X x := by
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) := CStarModule.Right.selfModule
  obtain ⟨y, b, h⟩ := CStarModule.exists_right_factor_of_starOrderedRing (B := B) x
  rw [InternalTensorProduct.IsModel.canonicalBaseChangeMap_factor
    (InternalTensorProduct.continuousMap_isModel (B := B) (E := E) X) x y b h]
  apply _root_.ContinuousMap.ext
  intro t
  change y <• b = x
  exact h.symm

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures. Let X be a compact topological space, and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

The constant extension of the rank-one module operator determined by x, y ∈ E is the rank-one
operator determined by their constant sections in C(X, E).
-/
theorem constantEndomorphismMap_rankOne (x y : E) :
    constantEndomorphismMap (B := B) (E := E) X (AdjointableOperator.rankOne (B := B) x y) =
      AdjointableOperator.rankOne (B := C(X, B))
        (_root_.ContinuousMap.const X x) (_root_.ContinuousMap.const X y) := by
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) := CStarModule.Right.selfModule
  have h := InternalTensorProduct.IsModel.mapLeftStarAlgHom_rankOne_baseChange
    (InternalTensorProduct.continuousMap_isModel (B := B) (E := E) X) x y
  rw [canonicalBaseChangeMap_eq_const (B := B) X x,
    canonicalBaseChangeMap_eq_const (B := B) X y] at h
  exact h

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures. Let X be a compact topological space, and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

If T is a compact module endomorphism of E, its constant extension is a compact module
endomorphism of C(X, E).
-/
theorem constantEndomorphismMap_mem_compact {T : AdjointableOperator.End B E}
    (hT : T ∈ AdjointableOperator.compactSubmodule (B := B) (E := E) (F := E)) :
    constantEndomorphismMap (B := B) (E := E) X T ∈
      AdjointableOperator.compactSubmodule (B := C(X, B)) (E := C(X, E)) (F := C(X, E)) := by
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) := CStarModule.Right.selfModule
  exact InternalTensorProduct.IsModel.mapLeftStarAlgHom_mem_compact_baseChange
    (InternalTensorProduct.continuousMap_isModel (B := B) (E := E) X) hT

/--
Let B be a possibly nonunital complex C*-algebra whose opposite algebra Bᵐᵒᵖ has a
star-compatible partial order. Let E be a complete normed right inner-product module over B,
with compatible complex normed-space structures. Let X be a compact topological space, and equip
C(X, B)ᵐᵒᵖ with a star-compatible partial order.

If E is countably generated over B, then C(X, E) is countably generated over C(X, B).
-/
theorem countablyGenerated
    (hE : CStarModule.IsCountablyGenerated (B := B) (E := E)) :
    CStarModule.IsCountablyGenerated (B := C(X, B)) (E := C(X, E)) := by
  let : CStarModule (C(X, B))ᵐᵒᵖ C(X, B) := CStarModule.Right.selfModule
  exact InternalTensorProduct.IsModel.countablyGenerated_baseChange
    (InternalTensorProduct.continuousMap_isModel (B := B) (E := E) X) hE

end CStarModule.ContinuousMap
