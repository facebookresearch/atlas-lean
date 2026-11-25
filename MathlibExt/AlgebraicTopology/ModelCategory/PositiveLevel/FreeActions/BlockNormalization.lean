/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.BlockGeometry
public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Components

/-!
# Original finite-block coefficient normalization

The full complement and input automorphism action groupoid maps to the actual
costructured block index. Its arrows retain both original finite maps, through
the existing usual-permutation equivalence.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.Prod

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual pair of complement and input automorphism groups. -/
abbrev pairedBlockGroup (n m : ℕ) := Aut (card (m - n)) × Aut (card n)

/-- The original complement-first block bijections. -/
abbrev pairedBlockAlphabet (n m : ℕ) := card (m - n) ⊗ card n ≅ card m

/-- The original free paired-block action, selected locally. -/
@[instance_reducible]
def pairedBlockAction (n m : ℕ) : MulAction (pairedBlockGroup n m) (pairedBlockAlphabet n m) :=
  pairedBlockMulAction (card (m - n)) (card n) (card m)

/-- The original paired scalar and input action on the block alphabet. -/
local instance selectedPairedBlockAction (n m : ℕ) :
    MulAction (pairedBlockGroup n m) (pairedBlockAlphabet n m) := pairedBlockAction n m

/-- The actual index tensor map retains both paired finite-block automorphisms. -/
theorem pairedBlockIndex_map (n m : ℕ) (a : pairedBlockGroup n m) :
    (actionTensorIndex n).map
      (show (card (m - n), SingleObj.star (Equiv.Perm (Fin n))) ⟶
          (card (m - n), SingleObj.star (Equiv.Perm (Fin n))) from
        ⟨a.1.asIso.hom, finAutEquiv (card n) a.2⟩) =
      (pairedBlockAut (card (m - n)) (card n) a).asIso.hom := by
  change a.1.asIso.hom ⊗ₘ ((finAutEquiv (card n)).symm (finAutEquiv (card n) a.2)).asIso.hom =
    a.1.asIso.hom ⊗ₘ a.2.asIso.hom
  rw [MulEquiv.symm_apply_apply]

/-- Every original action arrow retains its actual block triangle. -/
theorem pairedBlockTriangle (n m : ℕ)
    {x y : ActionCategory (pairedBlockGroup n m) (pairedBlockAlphabet n m)} (f : x ⟶ y) :
    (pairedBlockAut (card (m - n)) (card n) f.hom).asIso.hom ≫ y.back.hom = x.back.hom := by
  have hw := congrArg Iso.hom f.map_val
  change (pairedBlockAut (card (m - n)) (card n) f.hom).asIso.inv ≫ x.back.hom = y.back.hom at hw
  rw [← hw, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The full paired action groupoid maps to the original free-module coefficient index. -/
def pairedBlockInclusion (n m : ℕ) :
    ActionCategory (pairedBlockGroup n m) (pairedBlockAlphabet n m) ⥤
      CostructuredArrow (actionTensorIndex n) (card m) where
  obj x := CostructuredArrow.mk
    (Y := (card (m - n), SingleObj.star (Equiv.Perm (Fin n)))) x.back.hom
  map f := CostructuredArrow.homMk
    (show (card (m - n), SingleObj.star (Equiv.Perm (Fin n))) ⟶
        (card (m - n), SingleObj.star (Equiv.Perm (Fin n))) from
      ⟨f.hom.1.asIso.hom, finAutEquiv (card n) f.hom.2⟩)
    (by rw [pairedBlockIndex_map]; exact pairedBlockTriangle n m f)
  map_id x := by
    apply CostructuredArrow.ext
    apply Prod.ext
    · rfl
    · change finAutEquiv (card n) 1 = 1
      exact map_one _
  map_comp f g := by
    apply CostructuredArrow.ext
    apply Prod.ext
    · rfl
    · change finAutEquiv (card n) (g.hom.2 * f.hom.2) =
        finAutEquiv (card n) g.hom.2 * finAutEquiv (card n) f.hom.2
      exact map_mul _ _ _

/-- The paired normalization keeps both complete original source maps injectively. -/
instance pairedBlockInclusion_faithful (n m : ℕ) : (pairedBlockInclusion n m).Faithful where
  map_injective {x y} f g hfg := by
    have hl := congrArg (fun z => z.left) hfg
    have hR : f.hom.1.asIso.hom = g.hom.1.asIso.hom := congrArg Prod.fst hl
    have hN : finAutEquiv (card n) f.hom.2 = finAutEquiv (card n) g.hom.2 := congrArg Prod.snd hl
    have hR' : f.hom.1 = g.hom.1 := Aut.ext (Iso.ext hR)
    have hN' : f.hom.2 = g.hom.2 := (finAutEquiv (card n)).injective hN
    apply Functor.Elements.Hom.ext
    exact Prod.ext hR' hN'

/-- Every original normalized block arrow is the image of its complete paired action scalar. -/
instance pairedBlockInclusion_full (n m : ℕ) : (pairedBlockInclusion n m).Full where
  map_surjective {x y} f := by
    let k : card (m - n) ⟶ card (m - n) := f.left.1
    let a : pairedBlockGroup n m :=
      ⟨Aut.of (asIso k), (finAutEquiv (card n)).symm f.left.2⟩
    have he :
        (show (card (m - n), SingleObj.star (Equiv.Perm (Fin n))) ⟶
            (card (m - n), SingleObj.star (Equiv.Perm (Fin n))) from
          ⟨a.1.asIso.hom, finAutEquiv (card n) a.2⟩) = f.left := by
      apply Prod.ext
      · rfl
      · exact (finAutEquiv (card n)).apply_symm_apply _
    have ht : (pairedBlockAut (card (m - n)) (card n) a).asIso.hom ≫ y.back.hom = x.back.hom := by
      rw [← pairedBlockIndex_map, he]
      exact f.w
    have ha : a • x.back = y.back := by
      apply Iso.ext
      change (pairedBlockAut (card (m - n)) (card n) a).asIso.inv ≫ x.back.hom = y.back.hom
      rw [← ht, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    refine ⟨(⟨a, ha⟩ : x ⟶ y), ?_⟩
    apply CostructuredArrow.ext
    exact he

end HomotopicalAlgebra.PositiveLevelModel
