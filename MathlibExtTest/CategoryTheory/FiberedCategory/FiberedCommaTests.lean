/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.FiberedCategory.FiberedCommaRealization

/-!
# Full original fibered-comma and realized-adjunction clients

The categorical clients keep four independent total/base object and Hom
levels. They observe actual Cartesian factors, complete hom-set roundtrips,
and the right-adjoint map with both adjunction triangle laws. The realization
client uses the owner's actual native common-value profile and its original
forward inclusion and inverse chosen pullback, with both unit/counit homotopies.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe uS vS uX vX uNative vNative

namespace MathlibExtTest.FiberedComma

open CategoryTheory.Functor.IsPreFibered

section FullHom

variable {S : Type uS} [Category.{vS} S]
  {X : Type uX} [Category.{vX} X] {p : X ⥤ S} [p.IsPreFibered]

/-- Every actual comma arrow has its original factor and both full Hom roundtrips. -/
theorem full_original_hom_factor_and_roundtrips (s : S) (b : p.Fiber s)
    (a : StructuredArrow s p)
    (g : (Functor.fiberToStructuredArrow (p := p) s).obj b ⟶ a)
    (f : b ⟶ structuredPullbackObject a) :
    ((structuredFiberHomEquiv s b a) g).val ≫ structuredPullbackLift a = g.right ∧
      (structuredFiberHomEquiv s b a).symm ((structuredFiberHomEquiv s b a) g) = g ∧
      (structuredFiberHomEquiv s b a) ((structuredFiberHomEquiv s b a).symm f) = f := by
  refine ⟨?_, (structuredFiberHomEquiv s b a).symm_apply_apply g,
    (structuredFiberHomEquiv s b a).apply_symm_apply f⟩
  change (structuredFiberHomForward s b a g).val ≫ structuredPullbackLift a = g.right
  exact structuredFiberHomForward_fac s b a g

/-- The actual chosen-pullback map and both original adjunction triangles retain all arrows. -/
theorem original_right_adjoint_map_and_triangle_laws (s : S)
    (b : p.Fiber s) {a a' : StructuredArrow s p} (q : a ⟶ a') :
    ((structuredToFiber (p := p) s).map q).val ≫ structuredPullbackLift a' =
        structuredPullbackLift a ≫ q.right ∧
      (Functor.fiberToStructuredArrow (p := p) s).map
          ((fiberToStructuredArrowAdjunction (p := p) s).unit.app b) ≫
        (fiberToStructuredArrowAdjunction (p := p) s).counit.app
          ((Functor.fiberToStructuredArrow (p := p) s).obj b) =
        𝟙 ((Functor.fiberToStructuredArrow (p := p) s).obj b) ∧
      (fiberToStructuredArrowAdjunction (p := p) s).unit.app
          ((structuredToFiber (p := p) s).obj a) ≫
        (structuredToFiber (p := p) s).map
          ((fiberToStructuredArrowAdjunction (p := p) s).counit.app a) =
        𝟙 ((structuredToFiber (p := p) s).obj a) := by
  exact ⟨structuredToFiber_map_fac s q,
    (fiberToStructuredArrowAdjunction (p := p) s).left_triangle_components b,
    (fiberToStructuredArrowAdjunction (p := p) s).right_triangle_components a⟩

end FullHom

section NativeRealization

variable {S : Type uNative} [Category.{vNative} S]
  {X : Type (max uNative vNative)} [Category.{vNative} X]
  {p : X ⥤ S} [p.IsPreFibered]

/-- The realized equivalence uses the actual maps and complete unit/counit homotopies. -/
theorem original_realized_inclusion_inverse_and_homotopies (s : S) :
    (fiberCommaRealizedEquiv (p := p) s).toFun =
        (SSet.toTop.map (nerveMap (Functor.fiberToStructuredArrow (p := p) s))).hom ∧
      (fiberCommaRealizedEquiv (p := p) s).invFun =
        (SSet.toTop.map (nerveMap (structuredToFiber (p := p) s))).hom ∧
      Nonempty (SSet.Homotopy
        (𝟙 (nerve (Functor.Fiber p s) : SSet.{max uNative vNative}))
        (nerveMap (Functor.fiberToStructuredArrow (p := p) s ⋙ structuredToFiber (p := p) s))) ∧
      Nonempty (SSet.Homotopy
        (nerveMap (structuredToFiber (p := p) s ⋙ Functor.fiberToStructuredArrow (p := p) s))
        (𝟙 (nerve (StructuredArrow s p) : SSet.{max uNative vNative}))) ∧
      SSet.realizationWeakEquivalences
        (nerveMap (Functor.fiberToStructuredArrow (p := p) s)) := by
  refine ⟨fiberCommaRealizedEquiv_toFun s, fiberCommaRealizedEquiv_invFun s, ⟨?_⟩,
    ⟨?_⟩, fiberToStructuredArrow_mem_realizationWeakEquivalences s⟩
  · simpa only [nerveMap_id] using
      NatTrans.nerveHomotopy (fiberToStructuredArrowAdjunction (p := p) s).unit
  · simpa only [nerveMap_id] using
      NatTrans.nerveHomotopy (fiberToStructuredArrowAdjunction (p := p) s).counit

end NativeRealization

end MathlibExtTest.FiberedComma

namespace CategoryTheory.Functor.IsPreFibered

#print axioms _root_.CategoryTheory.Functor.fiberToStructuredArrow
#print axioms structuredFiberHomEquiv
#print axioms structuredToFiber
#print axioms fiberToStructuredArrowAdjunction
#print axioms structuredToFiber_map_fac
#print axioms fiberCommaRealizedEquiv
#print axioms fiberCommaRealizedEquiv_toFun
#print axioms fiberCommaRealizedEquiv_invFun
#print axioms fiberToStructuredArrow_mem_realizationWeakEquivalences

end CategoryTheory.Functor.IsPreFibered

namespace MathlibExtTest.FiberedComma

#print axioms full_original_hom_factor_and_roundtrips
#print axioms original_right_adjoint_map_and_triangle_laws
#print axioms original_realized_inclusion_inverse_and_homotopies

end MathlibExtTest.FiberedComma

end
