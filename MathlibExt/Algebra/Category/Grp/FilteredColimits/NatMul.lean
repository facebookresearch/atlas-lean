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

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Multiplication cofinality for `ℕ`-indexed filtered colimits in `GrpCat`

For a positive `k : ℕ`, multiplication by `k` is cofinal in `ℕ`.
The monotone functor `n ↦ n * k` is final, so for any `F : ℕ ⥤ GrpCat`
the colimit after precomposing with this functor is canonically isomorphic
to the original colimit. We provide the comparison isomorphism

`colimit ((natMulFunctor k).comp F) ≅ colimit F`

with its explicit `G.mk` formulas. The positivity hypothesis `0 < k`
is essential to obtain `n ≤ n * k`.
-/

@[expose] public section

open CategoryTheory Limits

universe u

noncomputable section

namespace GrpCat.FilteredColimits

/-- Multiplication `n ↦ n * k` is monotone on `ℕ`. -/
theorem natMulMonotone (k : ℕ) : Monotone (fun n : ℕ => n * k) :=
  fun _ _ h => Nat.mul_le_mul_right k h

/-- Functor `ℕ ⥤ ℕ` sending `n` to `n * k` and `m ≤ n` to `m * k ≤ n * k`. -/
def natMulFunctor (k : ℕ) : ℕ ⥤ ℕ :=
  (natMulMonotone k).functor

/-- Object part of `natMulFunctor k` is definitionally `n * k`. -/
@[simp]
theorem natMulFunctor_obj (k n : ℕ) : (natMulFunctor k).obj n = n * k :=
  rfl

/-- The functor `n ↦ n * k` is final when `0 < k`.

The positivity hypothesis `hk : 0 < k` gives `∀ n, n ≤ n * k` via
`Nat.le_mul_of_pos_right`, which is exactly the finality criterion for
monotone maps `ℕ → ℕ` through `Monotone.final_functor_iff`. -/
theorem natMulFunctor_final {k : ℕ} (hk : 0 < k) : (natMulFunctor k).Final := by
  have hf : (natMulMonotone k).functor.Final := by
    rw [Monotone.final_functor_iff]
    intro n₂
    exact ⟨n₂, Nat.le_mul_of_pos_right n₂ hk⟩
  exact hf

variable {F : ℕ ⥤ GrpCat.{u}}

/-- Forward comparison cocone from the multiplied diagram to the original colimit.

Direction: cocone over `(natMulFunctor k).comp F` with point `colimit F`;
its `n`-th leg is the `(n * k)`-th injection of `F`. -/
noncomputable abbrev natMulForwardCocone (k : ℕ) (F : ℕ ⥤ GrpCat.{u}) :
    Cocone ((natMulFunctor k).comp F) where
  pt := (colimitCocone (F := F)).pt
  ι :=
    { app := fun n => (colimitCocone (F := F)).ι.app (n * k)
      naturality := fun m n f => by
        have h_le : m * k ≤ n * k := by
          have h : m ≤ n := leOfHom f
          exact Nat.mul_le_mul_right k h
        have h_eq : (natMulFunctor k).map f = homOfLE h_le := Subsingleton.elim _ _
        have h_comp : ((natMulFunctor k).comp F).map f =
            F.map ((natMulFunctor k).map f) := rfl
        have h_map : ((natMulFunctor k).comp F).map f =
            F.map (homOfLE h_le) := h_comp.trans (congrArg (F.map) h_eq)
        rw [h_map]
        exact (colimitCocone (F := F)).ι.naturality (homOfLE h_le)
    }

/-- The `n`-th leg of `natMulForwardCocone` is definitionally `ι (n * k)`. -/
@[simp]
theorem natMulForwardCocone_ι_app (k : ℕ) (F : ℕ ⥤ GrpCat.{u}) (n : ℕ) :
    (natMulForwardCocone k F).ι.app n = (colimitCocone (F := F)).ι.app (n * k) :=
  rfl

/-- The point of `natMulForwardCocone` is `colimit F`. -/
@[simp]
theorem natMulForwardCocone_pt (k : ℕ) (F : ℕ ⥤ GrpCat.{u}) :
    (natMulForwardCocone k F).pt = (colimitCocone (F := F)).pt :=
  rfl

/-- The forward comparison cocone is a colimit when `0 < k`.

Uses finality of `n ↦ n * k` via `Functor.Final.isColimitWhiskerEquiv`. -/
noncomputable def natMulForwardIsColimit (k : ℕ) (hk : 0 < k)
    (F : ℕ ⥤ GrpCat.{u}) :
    IsColimit (natMulForwardCocone k F) := by
  haveI : (natMulFunctor k).Final := natMulFunctor_final hk
  exact (Functor.Final.isColimitWhiskerEquiv (natMulFunctor k)
    (colimitCocone (F := F))).symm (colimitCoconeIsColimit F)

/-- Forward comparison map `colimit ((natMulFunctor k).comp F) ⟶ colimit F`
induced by `natMulForwardCocone`. -/
noncomputable def natMulForwardHom (k : ℕ) (F : ℕ ⥤ GrpCat.{u}) :
    (colimitCocone (F := (natMulFunctor k).comp F)).pt ⟶
      (colimitCocone (F := F)).pt :=
  (colimitCoconeIsColimit (F := (natMulFunctor k).comp F)).desc
    (natMulForwardCocone k F)

/-- Leg-wise formula for `natMulForwardHom`: `ι n ≫ forward = ι (n * k)`. -/
@[simp]
theorem natMulForwardHom_ι (k : ℕ) (F : ℕ ⥤ GrpCat.{u}) (n : ℕ) :
    (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n ≫
      natMulForwardHom k F =
      (colimitCocone (F := F)).ι.app (n * k) :=
  (colimitCoconeIsColimit (F := (natMulFunctor k).comp F)).fac
    (natMulForwardCocone k F) n

/-- `G.mk` formula for the forward map: `⟨n, x⟩ ↦ ⟨n * k, x⟩` with
`x : F.obj (n * k)`, viewed from the multiplied colimit to the original. -/
theorem natMulForwardHom_mk (k : ℕ) (F : ℕ ⥤ GrpCat.{u}) (n : ℕ)
    (x : F.obj (n * k)) :
    (natMulForwardHom k F) (G.mk (F := (natMulFunctor k).comp F) ⟨n, x⟩) =
      G.mk (F := F) ⟨n * k, x⟩ := by
  have h := ConcreteCategory.congr_hom (natMulForwardHom_ι k F (n := n)) x
  exact h

/-- Backward comparison map `colimit F ⟶ colimit ((natMulFunctor k).comp F)`
induced by the colimit property of `natMulForwardCocone` when `0 < k`. -/
noncomputable def natMulBackwardHom (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u}) :
    (natMulForwardCocone k F).pt ⟶
      (colimitCocone (F := (natMulFunctor k).comp F)).pt :=
  (natMulForwardIsColimit k hk F).desc (colimitCocone (F := (natMulFunctor k).comp F))

/-- Leg-wise formula for the backward map: the leg of the forward cocone
followed by the backward map equals the original injection of the multiplied
diagram. -/
theorem natMulBackwardHom_ι_mul (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u})
    (n : ℕ) :
    (natMulForwardCocone k F).ι.app n ≫ natMulBackwardHom k hk F =
      (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n :=
  (natMulForwardIsColimit k hk F).fac
    (colimitCocone (F := (natMulFunctor k).comp F)) n

/-- Rewriting of `natMulBackwardHom_ι_mul` with the definitional form
`colimitCocone.ι (n * k)` on the left. -/
theorem natMulBackwardHom_ι_mul_of_rfl (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u})
    (n : ℕ) :
    (colimitCocone (F := F)).ι.app (n * k) ≫ natMulBackwardHom k hk F =
      (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n := by
  have h := natMulBackwardHom_ι_mul k hk F (n := n)
  rwa [natMulForwardCocone_ι_app] at h

/-- Forward then backward is identity on `colimit ((natMulFunctor k).comp F)`. -/
theorem natMulForwardBackward_id (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u}) :
    natMulForwardHom k F ≫ natMulBackwardHom k hk F =
      𝟙 ((colimitCocone (F := (natMulFunctor k).comp F)).pt) := by
  apply (colimitCoconeIsColimit (F := (natMulFunctor k).comp F)).hom_ext
  intro n
  have h_main : (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n ≫
      (natMulForwardHom k F ≫ natMulBackwardHom k hk F) =
      (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n := by
    have h_assoc : (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n ≫
        (natMulForwardHom k F ≫ natMulBackwardHom k hk F) =
        ((colimitCocone (F := (natMulFunctor k).comp F)).ι.app n ≫
          natMulForwardHom k F) ≫ natMulBackwardHom k hk F :=
      (Category.assoc _ _ _).symm
    have h_forward : ((colimitCocone (F := (natMulFunctor k).comp F)).ι.app n ≫
          natMulForwardHom k F) ≫ natMulBackwardHom k hk F =
        (colimitCocone (F := F)).ι.app (n * k) ≫ natMulBackwardHom k hk F :=
      congrArg (· ≫ natMulBackwardHom k hk F) (natMulForwardHom_ι k F n)
    exact h_assoc.trans (h_forward.trans (natMulBackwardHom_ι_mul_of_rfl k hk F n))
  exact h_main.trans (Category.comp_id _).symm

/-- Backward then forward is identity on `colimit F`. -/
theorem natMulBackwardForward_id (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u}) :
    natMulBackwardHom k hk F ≫ natMulForwardHom k F =
      𝟙 ((colimitCocone (F := F)).pt) := by
  apply (natMulForwardIsColimit k hk F).hom_ext
  intro n
  have h_main : (natMulForwardCocone k F).ι.app n ≫
      (natMulBackwardHom k hk F ≫ natMulForwardHom k F) =
      (natMulForwardCocone k F).ι.app n := by
    have h_assoc : (natMulForwardCocone k F).ι.app n ≫
        (natMulBackwardHom k hk F ≫ natMulForwardHom k F) =
        ((natMulForwardCocone k F).ι.app n ≫ natMulBackwardHom k hk F) ≫
          natMulForwardHom k F :=
      (Category.assoc _ _ _).symm
    have h_back : ((natMulForwardCocone k F).ι.app n ≫ natMulBackwardHom k hk F) ≫
          natMulForwardHom k F =
        (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n ≫
          natMulForwardHom k F :=
      congrArg (· ≫ natMulForwardHom k F) (natMulBackwardHom_ι_mul k hk F n)
    have h_forw : (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n ≫
          natMulForwardHom k F =
        (natMulForwardCocone k F).ι.app n :=
      (natMulForwardHom_ι k F n).trans (natMulForwardCocone_ι_app k F n).symm
    exact h_assoc.trans (h_back.trans h_forw)
  exact h_main.trans (Category.comp_id _).symm

/-- Comparison isomorphism from the multiplied colimit to the original.

Direction `colimit ((natMulFunctor k).comp F) ≅ colimit F` for `0 < k`,
built from the explicit forward and backward maps. -/
noncomputable def natMulColimitIso (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u}) :
    colimit ((natMulFunctor k).comp F) ≅ colimit F where
  hom := natMulForwardHom k F
  inv := natMulBackwardHom k hk F
  hom_inv_id := natMulForwardBackward_id k hk F
  inv_hom_id := natMulBackwardForward_id k hk F

/-- Forward leg formula for `natMulColimitIso`: `ι n ≫ hom = ι (n * k)`. -/
@[simp]
theorem natMulColimitIso_hom_ι (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u})
    (n : ℕ) :
    (colimitCocone (F := (natMulFunctor k).comp F)).ι.app n ≫
      (natMulColimitIso k hk F).hom =
      (colimitCocone (F := F)).ι.app (n * k) :=
  natMulForwardHom_ι k F n

/-- `G.mk` formula for the forward direction of `natMulColimitIso`:
`G.mk ⟨n, x⟩` with `x : F.obj (n * k)` maps to `G.mk ⟨n * k, x⟩`. -/
theorem natMulColimitIso_hom_mk (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u})
    (n : ℕ) (x : F.obj (n * k)) :
    (natMulColimitIso k hk F).hom (G.mk (F := (natMulFunctor k).comp F) ⟨n, x⟩) =
      G.mk (F := F) ⟨n * k, x⟩ :=
  natMulForwardHom_mk k F n x

/-- Cofinal representative: any `G.mk ⟨n, x⟩` equals the class obtained by
pushing `x` forward along `n ≤ n * k`. Requires `0 < k`. -/
theorem natMul_cofinal_rep (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u})
    (n : ℕ) (x : F.obj n) :
    G.mk (F := F) ⟨n, x⟩ =
      G.mk (F := F) ⟨n * k, F.map (homOfLE (Nat.le_mul_of_pos_right n hk)) x⟩ := by
  apply G.mk_eq
  exact ⟨n * k, homOfLE (Nat.le_mul_of_pos_right n hk), 𝟙 _, by simp⟩

/-- `G.mk` formula for the inverse of `natMulColimitIso`.

For `0 < k`, `G.mk ⟨n, x⟩` with `x : F.obj n` maps to
`G.mk ⟨n, F.map (n ≤ n * k) x⟩` in the multiplied colimit. -/
theorem natMulColimitIso_inv_mk (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u})
    (n : ℕ) (x : F.obj n) :
    (natMulColimitIso k hk F).inv (G.mk (F := F) ⟨n, x⟩) =
      G.mk (F := (natMulFunctor k).comp F)
        ⟨n, F.map (homOfLE (Nat.le_mul_of_pos_right n hk)) x⟩ := by
  set iso := natMulColimitIso k hk F
  set cand : colimit ((natMulFunctor k).comp F) :=
    G.mk (F := (natMulFunctor k).comp F)
      ⟨n, F.map (homOfLE (Nat.le_mul_of_pos_right n hk)) x⟩
  have h_mk : iso.hom cand =
      G.mk (F := F) ⟨n * k, F.map (homOfLE (Nat.le_mul_of_pos_right n hk)) x⟩ :=
    natMulColimitIso_hom_mk k hk F n (F.map (homOfLE (Nat.le_mul_of_pos_right n hk)) x)
  have h_cof : (G.mk (F := F) ⟨n * k, F.map (homOfLE (Nat.le_mul_of_pos_right n hk)) x⟩ :
      colimit F) = G.mk (F := F) ⟨n, x⟩ :=
    (natMul_cofinal_rep k hk F n x).symm
  have h_hom_cand : iso.hom cand = G.mk (F := F) ⟨n, x⟩ := h_mk.trans h_cof
  have h_hom_inv : iso.hom (iso.inv (G.mk (F := F) ⟨n, x⟩)) =
      G.mk (F := F) ⟨n, x⟩ :=
    ConcreteCategory.congr_hom iso.inv_hom_id (G.mk (F := F) ⟨n, x⟩)
  have h_eq : iso.hom cand = iso.hom (iso.inv (G.mk (F := F) ⟨n, x⟩)) :=
    h_hom_cand.trans h_hom_inv.symm
  have h_left : iso.inv (iso.hom cand) = cand :=
    ConcreteCategory.congr_hom iso.hom_inv_id cand
  have h_right : iso.inv (iso.hom (iso.inv (G.mk (F := F) ⟨n, x⟩))) =
      iso.inv (G.mk (F := F) ⟨n, x⟩) :=
    ConcreteCategory.congr_hom iso.hom_inv_id (iso.inv (G.mk (F := F) ⟨n, x⟩))
  have h_final : cand = iso.inv (G.mk (F := F) ⟨n, x⟩) :=
    (h_left.symm.trans (congrArg iso.inv h_eq)).trans h_right
  exact h_final.symm

/-- Multiplicative group equivalence `colimit ((natMulFunctor k).comp F) ≃* colimit F`
for `0 < k`, from `natMulColimitIso`. -/
noncomputable def natMulColimitMulEquiv (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u}) :
    colimit ((natMulFunctor k).comp F) ≃* colimit F :=
  (natMulColimitIso k hk F).groupIsoToMulEquiv

/-- Forward `G.mk` formula for the `MulEquiv`: `⟨n, x⟩ ↦ ⟨n * k, x⟩`. -/
@[simp]
theorem natMulColimitMulEquiv_apply_mk (k : ℕ) (hk : 0 < k) (F : ℕ ⥤ GrpCat.{u})
    (n : ℕ) (x : F.obj (n * k)) :
    natMulColimitMulEquiv k hk F (G.mk (F := (natMulFunctor k).comp F) ⟨n, x⟩) =
      G.mk (F := F) ⟨n * k, x⟩ :=
  natMulColimitIso_hom_mk k hk F n x

/-- Inverse `G.mk` formula for the `MulEquiv`: pushes `x` forward along
`n ≤ n * k` before re-embedding, for `0 < k`. -/
theorem natMulColimitMulEquiv_symm_apply_mk (k : ℕ) (hk : 0 < k)
    (F : ℕ ⥤ GrpCat.{u}) (n : ℕ) (x : F.obj n) :
    (natMulColimitMulEquiv k hk F).symm (G.mk (F := F) ⟨n, x⟩) =
      G.mk (F := (natMulFunctor k).comp F)
        ⟨n, F.map (homOfLE (Nat.le_mul_of_pos_right n hk)) x⟩ := by
  have h_inv := natMulColimitIso_inv_mk k hk F n x
  have h_symm_eq_inv : (natMulColimitMulEquiv k hk F).symm (G.mk (F := F) ⟨n, x⟩) =
      (natMulColimitIso k hk F).inv (G.mk (F := F) ⟨n, x⟩) := by
    simp [natMulColimitMulEquiv, CategoryTheory.Iso.groupIsoToMulEquiv]
  rw [h_symm_eq_inv, h_inv]

end GrpCat.FilteredColimits

end
