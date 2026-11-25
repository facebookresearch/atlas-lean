/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.BlockNormalization

/-!
# The entire original block coefficient equivalence

Every original block coefficient object has its actual residual alphabet
comparison. Together with the full paired-arrow normalization this gives the
complete equivalence used by arbitrary finite-action free R-modules.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.Prod

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The original paired block action used in the full coefficient equivalence. -/
local instance equivalencePairedBlockAction (n m : ℕ) :
    MulAction (pairedBlockGroup n m) (pairedBlockAlphabet n m) := pairedBlockAction n m

/-- Forget only the original input action coordinate of a block coefficient object. -/
def originalBlockDecomposition (n m : ℕ) (c : CostructuredArrow (actionTensorIndex n) (card m)) :
    BlockDecomposition (card n) (card m) := CostructuredArrow.mk (Y := c.left.1) c.hom

/-- Every original coefficient object witnesses the actual input-degree inequality. -/
theorem originalBlockDegree_le (n m : ℕ) (c : CostructuredArrow (actionTensorIndex n) (card m)) : n
    ≤ m := by
  have hObj : (c.left.1 ⊗ card n).of = (card m).of := FintypeCat.Skeleton.is_skeletal ⟨c.hom.iso⟩
  have hLen := congrArg FintypeCat.Skeleton.len hObj
  change c.left.1.of.len + n = m at hLen
  rw [← hLen]
  exact Nat.le_add_left n c.left.1.of.len

/-- The original residual-alphabet comparison uses the existing exact complement normalization. -/
def originalBlockComplementIso (n m : ℕ) (c : CostructuredArrow (actionTensorIndex n) (card m)) :
    card (m - n) ≅ c.left.1 :=
  cardComplementIso (originalBlockDegree_le n m c) (originalBlockDecomposition n m c)

/-- The normalized original block bijection retains the actual original coefficient map. -/
def originalNormalizedBlock (n m : ℕ) (c : CostructuredArrow (actionTensorIndex n) (card m)) :
    pairedBlockAlphabet n m :=
  cardNormalizedBlock (originalBlockDegree_le n m c) (originalBlockDecomposition n m c)

/-- The complete original coefficient object is isomorphic to its actual paired-block normalization.
-/
def originalNormalizedBlockIso (n m : ℕ) (c : CostructuredArrow (actionTensorIndex n) (card m)) :
    (pairedBlockInclusion n m).obj (originalNormalizedBlock n m c :
      ActionCategory (pairedBlockGroup n m) (pairedBlockAlphabet n m)) ≅ c := by
  let k := originalBlockComplementIso n m c
  let e : SingleObj.star (Equiv.Perm (Fin n)) ≅ c.left.2 := eqToIso (Subsingleton.elim _ _)
  have he : (degreeActionInclusion n).map e.hom = 𝟙 (card n) := by
    change (degreeActionInclusion n).map (eqToHom (Subsingleton.elim _ _)) = 𝟙 (card n)
    rw [eqToHom_map]
    rfl
  refine CostructuredArrow.isoMk (k.prod e) ?_
  change (k.hom ⊗ₘ (degreeActionInclusion n).map e.hom) ≫ c.hom = (k.hom ▷ card n) ≫ c.hom
  exact (congrArg (fun f : card n ⟶ card n => (k.hom ⊗ₘ f) ≫ c.hom) he).trans
    (congrArg (fun f : card (m - n) ⊗ card n ⟶ c.left.1 ⊗ card n => f ≫ c.hom)
      (tensorHom_id k.hom (card n)))

/-- All original block coefficient objects lie in the image of the actual paired-action
normalization. -/
instance pairedBlockInclusion_essSurj (n m : ℕ) : (pairedBlockInclusion n m).EssSurj where
  mem_essImage c := ⟨originalNormalizedBlock n m c, ⟨originalNormalizedBlockIso n m c⟩⟩

/-- The full original coefficient index is equivalent to the genuine free paired-block action
groupoid. -/
instance pairedBlockInclusion_isEquivalence (n m : ℕ) : (pairedBlockInclusion n m).IsEquivalence :=
    {}

/-- The actual entire paired coefficient equivalence retains the original inclusion functor. -/
def pairedBlockEquivalence (n m : ℕ) :
    ActionCategory (pairedBlockGroup n m) (pairedBlockAlphabet n m) ≌
      CostructuredArrow (actionTensorIndex n) (card m) :=
  (pairedBlockInclusion n m).asEquivalence

end HomotopicalAlgebra.PositiveLevelModel
