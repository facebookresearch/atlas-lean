/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerEnrichment
public import Mathlib.CategoryTheory.Elements
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Basic.Countable.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# Cardinal bounds for inner tensors and cylinders

The total point count of an inner tensor is bounded by the product of the total point counts of
its simplicial-space and simplicial-set factors. The standard one-simplex has countably
infinitely many total simplices, so its inner cylinder preserves any total-point bound γ with ℵ₀
≤ γ.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite Cardinal
namespace SimplicialSpace

-- Local proof notation only; no new public point record or tensor.
private abbrev rawTotal (X : SimplicialSpace.{u}) :=
  Σ m : SimplexCategoryᵒᵖ, Σ n : SimplexCategoryᵒᵖ, (X.diagram.obj m).obj n

private def rawTotalElementsEquiv (X : SimplicialSpace.{u}) :
    rawTotal X ≃ (Functor.uncurry.obj X.diagram).Elements where
  toFun q := Functor.elementsMk _ (q.1, q.2.1) q.2.2
  invFun q := ⟨q.obj.1, q.obj.2, q.val⟩
  left_inv q := by rcases q with ⟨m, n, x⟩; rfl
  right_inv q := by cases q; rfl

private def tensorTotalInjection (K : SSet.{u}) (X : SimplicialSpace.{u}) :
    rawTotal ((innerTensor K).obj X) → rawTotal X × K.Elements :=
  fun q => (⟨q.1, q.2.1, q.2.2.1⟩, Functor.elementsMk K q.2.1 q.2.2.2)

private theorem tensorTotalInjection_injective (K : SSet.{u}) (X : SimplicialSpace.{u}) :
    Function.Injective (tensorTotalInjection K X) := by
  rintro ⟨m, n, x, k⟩ ⟨m', n', x', k'⟩ h
  have hfirst := congrArg Prod.fst h
  change (⟨m, n, x⟩ : rawTotal X) = ⟨m', n', x'⟩ at hfirst
  cases hfirst
  have hsecond := congrArg Prod.snd h
  have hval : ∀ {e₁ e₂ : K.Elements}, e₁ = e₂ → HEq e₁.val e₂.val := by
    intro e₁ e₂ he
    cases he
    rfl
  have hk : k = k' := eq_of_heq (hval hsecond)
  cases hk
  rfl

/-- Total points of the actual inner tensor have the original product bound. -/
theorem mk_innerTensor_elements_le (K : SSet.{u}) (X : SimplicialSpace.{u}) :
    Cardinal.mk (Functor.uncurry.obj ((innerTensor K).obj X).diagram).Elements ≤
      Cardinal.mk (Functor.uncurry.obj X.diagram).Elements * Cardinal.mk K.Elements := by
  rw [← Cardinal.mk_congr (rawTotalElementsEquiv ((innerTensor K).obj X)),
    ← Cardinal.mk_congr (rawTotalElementsEquiv X)]
  exact (Cardinal.mk_le_of_injective (tensorTotalInjection_injective K X)).trans_eq
    (by rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id])

open scoped Simplicial

private theorem oneSimplex_elements_countable :
    Countable (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements := by
  let _ : Countable SimplexCategory :=
    (show Function.Injective SimplexCategory.len from by
      intro a b h
      rw [← SimplexCategory.mk_len a, ← SimplexCategory.mk_len b, h]).countable
  let _ : Countable SimplexCategoryᵒᵖ :=
    (Opposite.unop_injective :
      Function.Injective (unop : SimplexCategoryᵒᵖ → SimplexCategory)).countable
  let _ : ∀ n : SimplexCategoryᵒᵖ,
      Countable ((SSet.stdSimplex.{u}.obj ⦋1⦌).obj n) := fun _ => inferInstance
  let e : (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements ≃
      Σ n : SimplexCategoryᵒᵖ, (SSet.stdSimplex.{u}.obj ⦋1⦌).obj n :=
    { toFun x := ⟨x.obj, x.val⟩
      invFun x := Functor.elementsMk _ x.1 x.2
      left_inv x := by cases x; rfl
      right_inv x := by cases x; rfl }
  exact e.injective.countable

private def constantPointAtDegree (n : ℕ) : (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements :=
  Functor.elementsMk _ (op ⦋n⦌)
    (SSet.stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.const (Fin (n + 1)) (0 : Fin 2))))

/-- The original degree distinguishes constant scalar simplices, proving infinite total points. -/
theorem constant_points_degree_injective :
    Function.Injective (fun n : ℕ =>
      Functor.elementsMk (SSet.stdSimplex.{u}.obj ⦋1⦌) (op ⦋n⦌)
        (SSet.stdSimplex.objEquiv.symm
          (SimplexCategory.Hom.mk (OrderHom.const (Fin (n + 1)) (0 : Fin 2))))) := by
  change Function.Injective (constantPointAtDegree.{u})
  intro n m h
  exact congrArg (fun e : (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements => e.obj.unop.len) h

/-- The full scalar total-point type is countably infinite, retaining every original degree. -/
theorem mk_oneSimplex_elements :
    Cardinal.mk (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements = ℵ₀ := by
  let _ : Countable (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements := oneSimplex_elements_countable
  let _ : Infinite (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements :=
    Infinite.of_injective (constantPointAtDegree.{u}) constant_points_degree_injective
  exact Cardinal.mk_eq_aleph0 _

/-- The true scalar cylinder count is absorbed by the same infinite γ. -/
theorem actual_oneSimplex_cylinder_bound (X : SimplicialSpace.{u}) (γ : Cardinal.{u})
    (hγ : ℵ₀ ≤ γ) (hX : Cardinal.mk (Functor.uncurry.obj X.diagram).Elements ≤ γ) :
    Cardinal.mk (Functor.uncurry.obj
      ((innerTensor (SSet.stdSimplex.{u}.obj ⦋1⦌)).obj X).diagram).Elements ≤ γ := by
  calc
    _ ≤ Cardinal.mk (Functor.uncurry.obj X.diagram).Elements *
        Cardinal.mk (SSet.stdSimplex.{u}.obj ⦋1⦌).Elements := mk_innerTensor_elements_le _ X
    _ ≤ γ * γ := mul_le_mul' hX (mk_oneSimplex_elements.le.trans hγ)
    _ = γ := Cardinal.mul_eq_self hγ

end SimplicialSpace
