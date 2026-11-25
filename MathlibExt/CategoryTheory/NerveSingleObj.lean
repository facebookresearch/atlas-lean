/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
/-
Author: @toskua, Avocado
-/
module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.SingleObj

/-!
# Tuples in the nerve of a one-object category

The degree-`n` simplices in the nerve of `SingleObj M` are identified with
`n`-tuples in the monoid `M`.  We provide both the direct one-object category
and the opposite category used by bar constructions.

The two readers have different middle-face multiplication orders.  Since
composition in `SingleObj M` is reverse multiplication, the direct reader
composes adjacent entries as `second * first`.  Passing to `Mᵐᵒᵖ` reverses the
order again, so the opposite reader composes them as `first * second`.
-/

@[expose] public section

open scoped Simplicial

universe u

namespace CategoryTheory
namespace nerve

variable (M : Type u) [Monoid M]

/-- Consecutive arrows identify an `n`-simplex in the nerve of `SingleObj M`
with an `n`-tuple in `M`. -/
noncomputable def singleObjEquiv (n : ℕ) :
    ComposableArrows (SingleObj M) n ≃ (Fin n → M) where
  toFun F := fun i => F.map' i.val (i.val + 1)
  invFun t :=
    ComposableArrows.mkOfObjOfMapSucc
      (fun _ => SingleObj.star M) (fun i => t i)
  left_inv F := by
    refine ComposableArrows.ext ?_ ?_
    · intro i
      exact Subsingleton.elim _ _
    · intro i hi
      simp only [ComposableArrows.mkOfObjOfMapSucc_map_succ]
      apply eq_of_heq
      simp
  right_inv t := by
    funext i
    simp [ComposableArrows.mkOfObjOfMapSucc_map_succ]

/-- The direct tuple reader evaluates to the corresponding consecutive
arrow. -/
@[simp]
theorem singleObjEquiv_apply (n : ℕ) (F : ComposableArrows (SingleObj M) n)
    (i : Fin n) :
    singleObjEquiv M n F i = F.map' i.val (i.val + 1) :=
  rfl

/-- Rebuilding a direct tuple puts its `i`th entry on the `i`th consecutive
arrow. -/
@[simp]
theorem singleObjEquiv_symm_map_succ (n : ℕ) (t : Fin n → M) (i : Fin n) :
    ((singleObjEquiv M n).symm t).map' i.val (i.val + 1) = t i := by
  simp [singleObjEquiv, ComposableArrows.mkOfObjOfMapSucc_map_succ]

/-- The opposite one-object nerve reader used by bar constructions.  It reads
consecutive arrows with `unop` and rebuilds them with `op`; this is the direct,
cast-free form of the legacy classifying-nerve tuple equivalence. -/
noncomputable def singleObjOppEquiv (n : ℕ) :
    ComposableArrows (SingleObj Mᵐᵒᵖ) n ≃ (Fin n → M) where
  toFun F := fun i => MulOpposite.unop (F.map' i.val (i.val + 1))
  invFun t :=
    ComposableArrows.mkOfObjOfMapSucc
      (fun _ => SingleObj.star Mᵐᵒᵖ)
      (fun i => MulOpposite.op (t i))
  left_inv F := by
    refine ComposableArrows.ext ?_ ?_
    · intro i
      exact Subsingleton.elim _ _
    · intro i hi
      simp only [ComposableArrows.mkOfObjOfMapSucc_map_succ, MulOpposite.op_unop]
      apply eq_of_heq
      simp
  right_inv t := by
    funext i
    simp [ComposableArrows.mkOfObjOfMapSucc_map_succ]

/-- The opposite tuple reader evaluates by removing `op` from the
corresponding consecutive arrow. -/
@[simp]
theorem singleObjOppEquiv_apply (n : ℕ)
    (F : ComposableArrows (SingleObj Mᵐᵒᵖ) n) (i : Fin n) :
    singleObjOppEquiv M n F i =
      MulOpposite.unop (F.map' i.val (i.val + 1)) :=
  rfl

/-- Rebuilding an opposite tuple puts `op (t i)` on the `i`th consecutive
arrow. -/
@[simp]
theorem singleObjOppEquiv_symm_map_succ (n : ℕ) (t : Fin n → M)
    (i : Fin n) :
    ((singleObjOppEquiv M n).symm t).map' i.val (i.val + 1) =
      MulOpposite.op (t i) := by
  simp [singleObjOppEquiv, ComposableArrows.mkOfObjOfMapSucc_map_succ]

/-- The opposite tuple dictionary retains the ORIGINAL monoid map on
EVERY consecutive-arrow coordinate. -/
theorem singleObjOppEquiv_nerveMap {N : Type u} [Monoid N]
    (f : M →* N) (n : ℕ) (F : ComposableArrows (SingleObj Mᵐᵒᵖ) n) :
    singleObjOppEquiv N n
        ((nerveMap (SingleObj.mapHom _ _ (MonoidHom.op f))).app (Opposite.op ⦋n⦌) F) =
      fun i => f (singleObjOppEquiv M n F i) := by
  funext i
  rfl

private theorem singleObjEquiv_symm_two (t : Fin 2 → M) :
    (singleObjEquiv M 2).symm t =
      ComposableArrows.mk₂ (X₀ := SingleObj.star M) (X₁ := SingleObj.star M)
        (X₂ := SingleObj.star M) (t 0) (t 1) := by
  apply (singleObjEquiv M 2).injective
  rw [Equiv.apply_symm_apply]
  funext i
  fin_cases i <;> rfl

private theorem singleObjOppEquiv_symm_two (t : Fin 2 → M) :
    (singleObjOppEquiv M 2).symm t =
      ComposableArrows.mk₂ (X₀ := SingleObj.star Mᵐᵒᵖ)
        (X₁ := SingleObj.star Mᵐᵒᵖ) (X₂ := SingleObj.star Mᵐᵒᵖ)
        (MulOpposite.op (t 0)) (MulOpposite.op (t 1)) := by
  apply (singleObjOppEquiv M 2).injective
  rw [Equiv.apply_symm_apply]
  funext i
  fin_cases i <;> rfl

/-- In the direct one-object nerve, the middle face of `(first, second)` is
`second * first`, because categorical composition in `SingleObj M` reverses
monoid multiplication. -/
@[simp]
theorem singleObjEquiv_middle_face (t : Fin 2 → M) :
    singleObjEquiv M 1
        ((nerve (SingleObj M)).δ (1 : Fin 3) ((singleObjEquiv M 2).symm t)) 0 =
      t 1 * t 0 := by
  rw [singleObjEquiv_symm_two, δ₁_mk₂_eq]
  rfl

/-- In the opposite one-object nerve used by bar constructions, the middle
face of `(first, second)` is `first * second`. -/
@[simp]
theorem singleObjOppEquiv_middle_face (t : Fin 2 → M) :
    singleObjOppEquiv M 1
        ((nerve (SingleObj Mᵐᵒᵖ)).δ (1 : Fin 3)
          ((singleObjOppEquiv M 2).symm t)) 0 =
      t 0 * t 1 := by
  rw [singleObjOppEquiv_symm_two, δ₁_mk₂_eq]
  rfl

section Group

variable (G : Type u) [Group G]

/-- Inverting the original one-object arrows gives a strict simplicial
isomorphism from the opposite group nerve to the direct group nerve. -/
noncomputable def inversionIso : nerve (SingleObj Gᵐᵒᵖ) ≅ nerve (SingleObj G) where
  hom := nerveMap (SingleObj.mapHom _ _ (MulEquiv.inv' G).symm.toMonoidHom)
  inv := nerveMap (SingleObj.mapHom _ _ (MulEquiv.inv' G).toMonoidHom)
  hom_inv_id := by
    let F := SingleObj.mapHom _ _ (MulEquiv.inv' G).symm.toMonoidHom
    let H := SingleObj.mapHom _ _ (MulEquiv.inv' G).toMonoidHom
    have h : (MulEquiv.inv' G).toMonoidHom.comp
        (MulEquiv.inv' G).symm.toMonoidHom = MonoidHom.id Gᵐᵒᵖ := by
      ext g
      exact (MulEquiv.inv' G).apply_symm_apply g
    have hFH : F ⋙ H = 𝟭 (SingleObj Gᵐᵒᵖ) := by
      rw [← SingleObj.mapHom_comp, h, SingleObj.mapHom_id]
    calc
      nerveMap F ≫ nerveMap H = nerveMap (F ⋙ H) :=
        (nerveFunctor.map_comp F.toCatHom H.toCatHom).symm
      _ = nerveMap (𝟭 (SingleObj Gᵐᵒᵖ)) := congrArg nerveMap hFH
      _ = 𝟙 (nerve (SingleObj Gᵐᵒᵖ)) := nerveFunctor.map_id (Cat.of (SingleObj Gᵐᵒᵖ))
  inv_hom_id := by
    let F := SingleObj.mapHom _ _ (MulEquiv.inv' G).toMonoidHom
    let H := SingleObj.mapHom _ _ (MulEquiv.inv' G).symm.toMonoidHom
    have h : (MulEquiv.inv' G).symm.toMonoidHom.comp
        (MulEquiv.inv' G).toMonoidHom = MonoidHom.id G := by
      ext g
      exact (MulEquiv.inv' G).symm_apply_apply g
    have hFH : F ⋙ H = 𝟭 (SingleObj G) := by
      rw [← SingleObj.mapHom_comp, h, SingleObj.mapHom_id]
    calc
      nerveMap F ≫ nerveMap H = nerveMap (F ⋙ H) :=
        (nerveFunctor.map_comp F.toCatHom H.toCatHom).symm
      _ = nerveMap (𝟭 (SingleObj G)) := congrArg nerveMap hFH
      _ = 𝟙 (nerve (SingleObj G)) := nerveFunctor.map_id (Cat.of (SingleObj G))

/-- The inversion map reads every original opposite tuple as the direct
tuple of inverse arrows. -/
theorem inversionIso_simplex (n : ℕ) (g : Fin n → G) :
    (inversionIso G).hom.app (Opposite.op ⦋n⦌)
        ((singleObjOppEquiv G n).symm g) =
      (singleObjEquiv G n).symm (fun i => (g i)⁻¹) := by
  apply (singleObjEquiv G n).injective
  rw [Equiv.apply_symm_apply]
  funext i
  change (MulEquiv.inv' G).symm
      (((singleObjOppEquiv G n).symm g).map' i.val (i.val + 1)) = (g i)⁻¹
  rw [singleObjOppEquiv_symm_map_succ]
  rfl

/-- The inverse inversion map reads every original direct tuple as the
opposite tuple of inverse arrows. -/
theorem inversionIso_inv_simplex (n : ℕ) (g : Fin n → G) :
    (inversionIso G).inv.app (Opposite.op ⦋n⦌)
        ((singleObjEquiv G n).symm g) =
      (singleObjOppEquiv G n).symm (fun i => (g i)⁻¹) := by
  apply injective_of_mono ((inversionIso G).hom.app (Opposite.op ⦋n⦌))
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (inversionIso G).inv_hom_id (Opposite.op ⦋n⦌))
    ((singleObjEquiv G n).symm g)
  change (inversionIso G).hom.app (Opposite.op ⦋n⦌)
      ((inversionIso G).inv.app (Opposite.op ⦋n⦌) ((singleObjEquiv G n).symm g)) =
    (singleObjEquiv G n).symm g at h
  rw [h, inversionIso_simplex]
  simp only [inv_inv]
  rfl

end Group

end nerve
end CategoryTheory
