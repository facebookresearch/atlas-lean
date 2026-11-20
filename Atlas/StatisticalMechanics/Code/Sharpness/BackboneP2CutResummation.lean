/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Sharpness.BackboneSelectorCompatible

open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def shb_cutEquiv (P : G.edgeFinset → Prop) [DecidablePred P] :
    (G.edgeFinset → ℕ) ≃
      ({e : G.edgeFinset // P e} → ℕ) ×
        ({e : G.edgeFinset // ¬ P e} → ℕ) :=
  Equiv.piEquivPiSubtypeProd P (fun _ => ℕ)


noncomputable def shb_cutLeft (P : G.edgeFinset → Prop) [DecidablePred P]
    (a : {e : G.edgeFinset // P e} → ℕ) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm (a, fun _ => 0)


noncomputable def shb_cutRight (P : G.edgeFinset → Prop) [DecidablePred P]
    (b : {e : G.edgeFinset // ¬ P e} → ℕ) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm (fun _ => 0, b)


noncomputable def shb_cutJoin (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab : ({e : G.edgeFinset // P e} → ℕ) ×
      ({e : G.edgeFinset // ¬ P e} → ℕ)) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm ab

@[simp] theorem shb_cutJoin_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab) (e : G.edgeFinset) :
    shb_cutJoin G P ab e = if h : P e then ab.1 ⟨e, h⟩ else ab.2 ⟨e, h⟩ := by
  simp [shb_cutJoin, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]

@[simp] theorem shb_cutLeft_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (a) (e : G.edgeFinset) :
    shb_cutLeft G P a e = if h : P e then a ⟨e, h⟩ else 0 := by
  simp [shb_cutLeft, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]

@[simp] theorem shb_cutRight_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (b) (e : G.edgeFinset) :
    shb_cutRight G P b e = if h : P e then 0 else b ⟨e, h⟩ := by
  simp [shb_cutRight, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]


theorem shb_ofEdgeFun_cutJoin_add
    (P : G.edgeFinset → Prop) [DecidablePred P] (a b) :
    (fun e => ofEdgeFun G (shb_cutLeft G P a) e +
      ofEdgeFun G (shb_cutRight G P b) e) =
      ofEdgeFun G (shb_cutJoin G P (a, b)) := by
  funext e
  unfold ofEdgeFun
  by_cases he : e ∈ G.edgeFinset
  · rw [dif_pos he, dif_pos he, dif_pos he]
    by_cases hp : P ⟨e, he⟩ <;> simp [shb_cutJoin_apply, hp]
  · rw [dif_neg he, dif_neg he, dif_neg he]


theorem shb_weight_cutJoin_split (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] (a b) :
    weight G β J (ofEdgeFun G (shb_cutJoin G P (a, b))) =
      weight G β J (ofEdgeFun G (shb_cutLeft G P a)) *
        weight G β J (ofEdgeFun G (shb_cutRight G P b)) := by
  rw [← shb_ofEdgeFun_cutJoin_add G P a b]
  unfold weight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun e he => ?_)
  have heSet : e ∈ G.edgeSet := by
    simpa [SimpleGraph.edgeFinset] using he
  unfold ofEdgeFun
  rw [dif_pos he, dif_pos he]
  by_cases hp : P ⟨e, he⟩ <;>
    simp [shb_cutLeft_apply, shb_cutRight_apply, hp, heSet]


theorem shb_cutLeft_injective (P : G.edgeFinset → Prop) [DecidablePred P] :
    Function.Injective (shb_cutLeft G P) := by
  intro a a' h
  have h' := congrArg (shb_cutEquiv G P) h
  simpa [shb_cutLeft] using congrArg Prod.fst h'

theorem shb_cutRight_injective (P : G.edgeFinset → Prop) [DecidablePred P] :
    Function.Injective (shb_cutRight G P) := by
  intro b b' h
  have h' := congrArg (shb_cutEquiv G P) h
  simpa [shb_cutRight] using congrArg Prod.snd h'

noncomputable def shb_cutLeftWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (a : {e : G.edgeFinset // P e} → ℕ) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutLeft G P a))

noncomputable def shb_cutRightWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (b : {e : G.edgeFinset // ¬ P e} → ℕ) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutRight G P b))

noncomputable def shb_cutJoinWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab : ({e : G.edgeFinset // P e} → ℕ) ×
      ({e : G.edgeFinset // ¬ P e} → ℕ)) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutJoin G P ab))

theorem shb_cutJoinWeight_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] (ab) :
    shb_cutJoinWeight G β J P ab =
      shb_cutLeftWeight G β J P ab.1 * shb_cutRightWeight G β J P ab.2 := by
  exact shb_weight_cutJoin_split G β J P ab.1 ab.2



theorem shb_summable_weight_cutLeft (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    Summable (fun a : {e : G.edgeFinset // P e} → ℕ =>
      shb_cutLeftWeight G β J P a) :=
  (shb_summable_weight G β J).comp_injective (shb_cutLeft_injective G P)

theorem shb_summable_weight_cutRight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    Summable (fun b : {e : G.edgeFinset // ¬ P e} → ℕ =>
      shb_cutRightWeight G β J P b) :=
  (shb_summable_weight G β J).comp_injective (shb_cutRight_injective G P)

theorem shb_tsum_prod_factor {A B : Type*} (f : A → ℝ) (g : B → ℝ)
    (hf : Summable f) (hg : Summable g) :
    (∑' ab : A × B, f ab.1 * g ab.2) = (∑' a, f a) * ∑' b, g b := by
  exact (Summable.tsum_mul_tsum hf hg
    (summable_mul_of_summable_norm hf.norm hg.norm)).symm




noncomputable def shb_fullWeightMass (β : ℝ) (J : Sym2 V → ℝ) : ℝ :=
  ∑' m : G.edgeFinset → ℕ, weight G β J (ofEdgeFun G m)

noncomputable def shb_cutLeftMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' a, shb_cutLeftWeight G β J P a

noncomputable def shb_cutRightMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' b, shb_cutRightWeight G β J P b

noncomputable def shb_cutJoinMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' ab, shb_cutJoinWeight G β J P ab

theorem shb_fullWeightMass_eq_cutJoinMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_fullWeightMass G β J = shb_cutJoinMass G β J P := by
  unfold shb_fullWeightMass shb_cutJoinMass shb_cutJoinWeight shb_cutJoin
  rw [← (shb_cutEquiv G P).symm.tsum_eq]

theorem shb_cutJoinMass_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_cutJoinMass G β J P =
      shb_cutLeftMass G β J P * shb_cutRightMass G β J P := by
  unfold shb_cutJoinMass shb_cutLeftMass shb_cutRightMass
  rw [tsum_congr (fun ab => shb_cutJoinWeight_factor G β J P ab)]
  exact shb_tsum_prod_factor
    (shb_cutLeftWeight G β J P) (shb_cutRightWeight G β J P)
    (shb_summable_weight_cutLeft G β J P)
    (shb_summable_weight_cutRight G β J P)



theorem shb_tsum_weight_cut_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_fullWeightMass G β J =
      shb_cutLeftMass G β J P * shb_cutRightMass G β J P :=
  (shb_fullWeightMass_eq_cutJoinMass G β J P).trans
    (shb_cutJoinMass_factor G β J P)

end StatMech.Sharpness
