/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.SharpOverWeakBaseChange
import MathlibExt.CategoryTheory.Limits.Shapes.PullbackFibreBaseChange

/-!
# Full original fibre maps over weak base maps between sharp projections

A genuine original square factors through the literal pullback of its
original target projection. Sharpness makes its base comparison weak;
actual total and base weakness make the original over-map weak. Full
base change of that map and native pullback pasting give the SAME
original fibre map weak. All projections and original basepoints remain.
-/

noncomputable section
universe u v
open CategoryTheory Limits MorphismProperty
namespace HomotopicalAlgebra.SharpFibreMapWeak
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsRightProper C]
variable {E E' B B' A : C}

/-- The SAME whole original fibre map is weak from original total/base weakness and both sharp
projections. -/
theorem fibreMap_weak (p : E ⟶ B) (q : E' ⟶ B') (f : E ⟶ E') (g : B ⟶ B')
    (h : f ≫ q = p ≫ g) (a : A ⟶ B)
    (hp : sharpMaps (weakEquivalences C) p) (hq : sharpMaps (weakEquivalences C) q)
    (hf : weakEquivalences C f) (hg : weakEquivalences C g) :
    weakEquivalences C (fibreMap p q f g h a) := by
  let t := toBasePullback p q f g h
  have ht_fst : t ≫ pullback.fst q g = f := pullback.lift_fst _ _ _
  have ht_snd : t ≫ pullback.snd q g = p := pullback.lift_snd _ _ _
  have hfst : weakEquivalences C (pullback.fst q g) := by
    have hs : (weakEquivalences C).IsStableUnderBaseChangeAlong q :=
      (MorphismProperty.universally_le
          (fun _ _ q => (weakEquivalences C).IsStableUnderBaseChangeAlong q)) _ hq
    exact hs.of_isPullback (IsPullback.of_hasPullback q g).flip hg
  have ht : weakEquivalences C t := (weakEquivalences C).of_postcomp t _ hfst (ht_fst.symm ▸ hf)
  let F : Over.mk p ⟶ Over.mk (pullback.snd q g) := Over.homMk t ht_snd
  have hq' : sharpMaps (weakEquivalences C) (pullback.snd q g) :=
    (sharpMaps (weakEquivalences C)).of_isPullback (IsPullback.of_hasPullback q g) hq
  have hchange := SharpOverWeakBaseChange.pullback_map_weak a F ht hp hq'
  let e : pullback (pullback.snd q g) a ≅ pullback q (a ≫ g) := by
    exact (pullbackLeftPullbackSndIso q g a)
  have heq : ((Over.pullback a).map F).left ≫ e.hom = fibreMap p q f g h a := by
    have h₁ : e.hom ≫ pullback.fst q (a ≫ g) = pullback.fst (pullback.snd q g) a ≫ pullback.fst q g
        :=
      pullbackLeftPullbackSndIso_hom_fst q g a
    have h₂ : e.hom ≫ pullback.snd q (a ≫ g) = pullback.snd (pullback.snd q g) a :=
      pullbackLeftPullbackSndIso_hom_snd q g a
    have ht₁ : ((Over.pullback a).map F).left ≫ pullback.fst (pullback.snd q g) a =
        pullback.fst p a ≫ t := pullback.lift_fst _ _ _
    have ht₂ : ((Over.pullback a).map F).left ≫ pullback.snd (pullback.snd q g) a =
        pullback.snd p a := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => ((Over.pullback a).map F).left ≫ k) h₁).trans
          (((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫ pullback.fst q g) ht₁)).trans
            ((Category.assoc _ _ _).trans ((congrArg (fun k => pullback.fst p a ≫ k) ht_fst).trans
              (pullback.lift_fst _ _ _).symm))))
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun k => ((Over.pullback a).map F).left ≫ k) h₂).trans
          (ht₂.trans ((Category.comp_id _).symm.trans (pullback.lift_snd _ _ _).symm)))
  exact heq ▸ (weakEquivalences C).comp_mem _ _ hchange (mem_weakEquivalences _)

end HomotopicalAlgebra.SharpFibreMapWeak
