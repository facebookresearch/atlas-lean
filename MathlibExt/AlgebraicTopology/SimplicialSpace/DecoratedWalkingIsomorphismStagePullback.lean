/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.WalkingIsomorphismStagePushout
import MathlibExt.AlgebraicTopology.SimplicialSpace.EquivalenceMappingComponents
import MathlibExt.AlgebraicTopology.SimplicialSpace.InnerHomColimits

/-!
# Decorated pullbacks for the original alternating stages

The original successor pushout becomes a pullback under the contravariant
inner mapping functor. The actual generated-stage epimorphism covers every
edge, so its component selector lifts this raw pullback to the original
equivalence-decorated mapping spaces, including the nonmonic two-stage map.

Source: Rezk (2001), Section 11.7, equation (11.8) and the decoration after (11.9).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SimplicialSpace.EquivalenceMapping

private theorem rawStageSuccessor_isPullback (W : SimplicialSpace.{u})
    (k : ℕ) (hk : 2 ≤ k) :
    IsPullback
      ((discreteSourceMapping W).map (SSet.coherentIso.stageSimplexMap k).op)
      ((discreteSourceMapping W).map
        (SSet.coherentIso.stageDiagram.map (homOfLE (Nat.sub_le k 1))).op)
      ((discreteSourceMapping W).map (SSet.horn k 0).ι.op)
      ((discreteSourceMapping W).map (SSet.coherentIso.hornAttachment k hk).op) := by
  let H := innerHomFunctor.flip.obj W
  let : PreservesColimitsOfShape WalkingSpan H.rightOp :=
    innerHom_rightOp_preservesColimitsOfShape WalkingSpan W
  have h := ((SSet.coherentIso.innerStageSuccessor_isPushout.{u} k hk).map
    ofSimplicialObject).map H.rightOp
  exact h.unop.flip

private theorem stageSimplexMap_edgeCover (k : ℕ) :
    ∀ γ : (Δ[1] : SSet.{u}) ⟶ (SSet.coherentIso.stage k : SSet.{u}),
      ∃ δ : (Δ[1] : SSet.{u}) ⟶ Δ[k],
        δ ≫ SSet.coherentIso.stageSimplexMap k = γ := by
  let : Epi (SSet.coherentIso.stageSimplexMap.{u} k) := by
    change Epi (SSet.Subcomplex.toOfSimplex (SSet.coherentIso.alternatingSimplex.{u} k))
    infer_instance
  intro γ
  obtain ⟨a, ha⟩ := (epi_iff_surjective _).mp
    (inferInstance : Epi ((SSet.coherentIso.stageSimplexMap.{u} k).app (op ⦋1⦌)))
    (SSet.yonedaEquiv γ)
  refine ⟨SSet.yonedaEquiv.symm a, ?_⟩
  apply SSet.yonedaEquiv.injective
  simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using ha

/-- Every original alternating-stage successor gives the pullback of the four
literal equivalence-decorated restrictions. Its universal lift retains both
prescribed legs, for every scalar source and every stage `k ≥ 2`. -/
theorem stageSuccessor_isPullback (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (k : ℕ) (hk : 2 ≤ k) :
    IsPullback
      (restriction W hW (SSet.coherentIso.stageSimplexMap k))
      (restriction W hW
        (SSet.coherentIso.stageDiagram.map (homOfLE (Nat.sub_le k 1))))
      (restriction W hW (SSet.horn k 0).ι)
      (restriction W hW (SSet.coherentIso.hornAttachment k hk)) := by
  let σ := SSet.coherentIso.stageSimplexMap.{u} k
  let e : (SSet.coherentIso.stage (k - 1) : SSet.{u}) ⟶
      (SSet.coherentIso.stage k : SSet.{u}) :=
    SSet.coherentIso.stageDiagram.{u}.map (homOfLE (Nat.sub_le k 1))
  let iHorn := (SSet.horn.{u} k 0).ι
  let h := SSet.coherentIso.hornAttachment.{u} k hk
  let raw : IsPullback ((discreteSourceMapping W).map σ.op)
      ((discreteSourceMapping W).map e.op)
      ((discreteSourceMapping W).map iHorn.op)
      ((discreteSourceMapping W).map h.op) := rawStageSuccessor_isPullback W k hk
  let selected := restriction_isPullback_of_edgeCover W hW σ
    (stageSimplexMap_edgeCover k)
  have w : restriction W hW σ ≫ restriction W hW iHorn =
      restriction W hW e ≫ restriction W hW h := by
    exact (restriction_comp W hW iHorn σ).symm.trans
      ((congrArg (restriction W hW)
        (SSet.coherentIso.hornAttachment_stageSimplexMap k hk)).trans
          (restriction_comp W hW h e))
  have hlift {K : SSet.{u}}
      (a : K ⟶ (subcomplex W hW Δ[k] : SSet.{u}))
      (b : K ⟶ (subcomplex W hW (SSet.coherentIso.stage (k - 1)) : SSet.{u}))
      (hab : a ≫ restriction W hW iHorn = b ≫ restriction W hW h) :
      ∃ m : K ⟶ (subcomplex W hW (SSet.coherentIso.stage k) : SSet.{u}),
        m ≫ restriction W hW σ = a ∧ m ≫ restriction W hW e = b := by
    have habRaw : (a ≫ (subcomplex W hW Δ[k]).ι) ≫
          (discreteSourceMapping W).map iHorn.op =
        (b ≫ (subcomplex W hW (SSet.coherentIso.stage (k - 1))).ι) ≫
          (discreteSourceMapping W).map h.op := by
      simpa only [Category.assoc, ← restriction_ι] using
        congrArg (fun q => q ≫ (subcomplex W hW (SSet.horn k 0)).ι) hab
    let l := raw.lift (a ≫ (subcomplex W hW Δ[k]).ι)
      (b ≫ (subcomplex W hW (SSet.coherentIso.stage (k - 1))).ι) habRaw
    let m := selected.lift l a (raw.lift_fst _ _ habRaw)
    refine ⟨m, selected.lift_snd _ _ _, ?_⟩
    apply (cancel_mono (subcomplex W hW (SSet.coherentIso.stage (k - 1))).ι).mp
    calc
      m ≫ restriction W hW e ≫
          (subcomplex W hW (SSet.coherentIso.stage (k - 1))).ι =
          (m ≫ (subcomplex W hW (SSet.coherentIso.stage k)).ι) ≫
            (discreteSourceMapping W).map e.op := by rw [restriction_ι, Category.assoc]
      _ = l ≫ (discreteSourceMapping W).map e.op := by rw [selected.lift_fst]
      _ = b ≫ (subcomplex W hW (SSet.coherentIso.stage (k - 1))).ι :=
        raw.lift_snd _ _ habRaw
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk w
    (fun s => (hlift s.fst s.snd s.condition).choose)
    (fun s => (hlift s.fst s.snd s.condition).choose_spec.1)
    (fun s => (hlift s.fst s.snd s.condition).choose_spec.2) ?_)
  intro s m hm₁ hm₂
  apply (cancel_mono (subcomplex W hW (SSet.coherentIso.stage k)).ι).mp
  apply raw.hom_ext
  · simpa only [Category.assoc, ← restriction_ι] using
      congrArg (fun q => q ≫ (subcomplex W hW Δ[k]).ι)
        (hm₁.trans (hlift s.fst s.snd s.condition).choose_spec.1.symm)
  · simpa only [Category.assoc, ← restriction_ι] using
      congrArg (fun q => q ≫ (subcomplex W hW (SSet.coherentIso.stage (k - 1))).ι)
        (hm₂.trans (hlift s.fst s.snd s.condition).choose_spec.2.symm)

end SimplicialSpace.EquivalenceMapping
