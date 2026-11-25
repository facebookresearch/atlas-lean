/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.PositiveLevel.FreeActions.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-!
# The genuine paired finite-block action in free R-module coefficients

The complement and input permutation groups act by inverse precomposition on
actual block bijections. The action is free because the original block tensor
map is injective on the complete pair of finite-bijection maps.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Operad.SmallFinBijGroupoid
open scoped CategoryTheory.Prod

namespace HomotopicalAlgebra.PositiveLevelModel

local notation "I" => CategoryTheory.Operad.SmallFinBijGroupoid

/-- The actual complete tensor pair on two finite-alphabet automorphism groups. -/
def pairedBlockAut (R N : I) : Aut R × Aut N →* Aut (R ⊗ N) where
  toFun a := .of ((tensor I).mapIso (a.1.asIso.prod a.2.asIso))
  map_one' := by
    apply Aut.ext
    apply Iso.ext
    change 𝟙 R ⊗ₘ 𝟙 N = 𝟙 (R ⊗ N)
    exact id_tensorHom_id R N
  map_mul' a b := by
    apply Aut.ext
    apply Iso.ext
    change (b.1.asIso.hom ≫ a.1.asIso.hom) ⊗ₘ (b.2.asIso.hom ≫ a.2.asIso.hom) =
      (b.1.asIso.hom ⊗ₘ b.2.asIso.hom) ≫ (a.1.asIso.hom ⊗ₘ a.2.asIso.hom)
    exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- The paired automorphism keeps both original finite-block maps. -/
theorem pairedBlockAut_hom (R N : I) (a : Aut R × Aut N) :
    (pairedBlockAut R N a).asIso.hom = a.1.asIso.hom ⊗ₘ a.2.asIso.hom := rfl

/-- The original finite-bijection tensor is injective on the full pair of maps. -/
theorem pairedBlockHom_injective (R N : I) :
    Function.Injective (fun a : (R ⟶ R) × (N ⟶ N) => a.1 ⊗ₘ a.2) := by
  intro a b hab
  change blockSumHom a.1 a.2 = blockSumHom b.1 b.2 at hab
  apply Prod.ext
  · apply Core.hom_ext
    funext x
    have h := congrArg (fun f => f.iso.hom ((blockSumEquiv R N).symm (Sum.inl x))) hab
    simp only [blockSumHom_apply, Equiv.apply_symm_apply, Sum.map_inl] at h
    exact Sum.inl.inj ((blockSumEquiv R N).symm.injective h)
  · apply Core.hom_ext
    funext x
    have h := congrArg (fun f => f.iso.hom ((blockSumEquiv R N).symm (Sum.inr x))) hab
    simp only [blockSumHom_apply, Equiv.apply_symm_apply, Sum.map_inr] at h
    exact Sum.inr.inj ((blockSumEquiv R N).symm.injective h)

/-- The complete paired block subgroup is injective. -/
theorem pairedBlockAut_injective (R N : I) : Function.Injective (pairedBlockAut R N) := by
  intro a b hab
  have h := congrArg (fun z => z.asIso.hom) hab
  change a.1.asIso.hom ⊗ₘ a.2.asIso.hom = b.1.asIso.hom ⊗ₘ b.2.asIso.hom at h
  have hp : (a.1.asIso.hom, a.2.asIso.hom) = (b.1.asIso.hom, b.2.asIso.hom) :=
    @pairedBlockHom_injective R N (a.1.asIso.hom, a.2.asIso.hom) (b.1.asIso.hom, b.2.asIso.hom) h
  have hR : a.1.asIso.hom = b.1.asIso.hom := congrArg (fun z : (R ⟶ R) × (N ⟶ N) => z.1) hp
  have hN : a.2.asIso.hom = b.2.asIso.hom := congrArg (fun z : (R ⟶ R) × (N ⟶ N) => z.2) hp
  have hR' : a.1.asIso = b.1.asIso := Iso.ext hR
  have hN' : a.2.asIso = b.2.asIso := Iso.ext hN
  exact Prod.ext (Aut.ext hR') (Aut.ext hN')

/-- The original paired block action uses inverse precomposition of both blocks. -/
@[instance_reducible]
def pairedBlockMulAction (R N M : I) : MulAction (Aut R × Aut N) (R ⊗ N ≅ M) where
  smul a e := (pairedBlockAut R N a).asIso.symm ≪≫ e
  one_smul e := by
    change (pairedBlockAut R N 1).asIso.symm ≪≫ e = e
    rw [map_one]
    exact Iso.refl_trans e
  mul_smul a b e := by
    change (pairedBlockAut R N (a * b)).asIso.symm ≪≫ e =
      (pairedBlockAut R N a).asIso.symm ≪≫ ((pairedBlockAut R N b).asIso.symm ≪≫ e)
    rw [map_mul]
    change ((pairedBlockAut R N b).asIso ≪≫ (pairedBlockAut R N a).asIso).symm ≪≫ e =
      (pairedBlockAut R N a).asIso.symm ≪≫ ((pairedBlockAut R N b).asIso.symm ≪≫ e)
    rw [Iso.trans_symm, Iso.trans_assoc]

/-- The actual paired finite-block action is free on the original bijections. -/
theorem pairedBlockMulAction_free (R N M : I) (e : R ⊗ N ≅ M) :
    let _ := pairedBlockMulAction R N M
    Function.Injective (fun a : Aut R × Aut N => a • e) := by
  change Function.Injective (fun a : Aut R × Aut N => (pairedBlockAut R N a).asIso.symm ≪≫ e)
  intro a b hab
  have h := congrArg Iso.inv hab
  change e.inv ≫ (pairedBlockAut R N a).asIso.hom = e.inv ≫ (pairedBlockAut R N b).asIso.hom at h
  apply pairedBlockAut_injective R N
  exact Aut.ext (Iso.ext ((cancel_epi e.inv).mp h))

end HomotopicalAlgebra.PositiveLevelModel
