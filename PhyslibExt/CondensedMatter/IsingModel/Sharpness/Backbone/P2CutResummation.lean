/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.SelectorCompatible

/-!
# Current weights along an edge cut

Splitting the edges of a graph by a predicate `P` identifies currents with pairs of currents on
the two sides; the current weight is multiplicative under this splitting, so the total weight mass
factors as the product of the masses of the two sides.

## i. Overview

`shb_cutEquiv` identifies edge functions on `G` with pairs of edge functions on the edges where
`P` holds and where it fails; `shb_cutLeft`, `shb_cutRight` extend one side by zero and
`shb_cutJoin` glues a pair. The weight of a glued current is the product of the weights of its two
parts (`shb_weight_cutJoin_split`). Summing, with summability of the weight on each side, the total
weight mass factors (`shb_tsum_weight_cut_factor`).

Headline fidelity: `shb_weight_cutJoin_split`, `shb_cutJoinMass_factor` and
`shb_tsum_weight_cut_factor` are unconditional. They concern the unrestricted weight mass; the
restricted versions used for the backbone chain rule are in `ExplorationCutAdmissible`.

## ii. Key results

- `shb_cutEquiv` : edge functions as pairs along a cut
- `shb_weight_cutJoin_split` : the weight is multiplicative along a cut
- `shb_tsum_weight_cut_factor` : the total weight mass factors along a cut

## iii. Table of contents

- A. Splitting edge functions along a cut
- B. Weights along a cut
- C. Weight masses along a cut

## iv. References

None beyond those in the imported modules.

-/

@[expose] public section

open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## A. Splitting edge functions along a cut -/

/-- Edge functions on `G` as pairs of edge functions on the edges where `P` holds and where it
fails. -/
noncomputable def shb_cutEquiv (P : G.edgeFinset → Prop) [DecidablePred P] :
    (G.edgeFinset → ℕ) ≃
      ({e : G.edgeFinset // P e} → ℕ) ×
        ({e : G.edgeFinset // ¬ P e} → ℕ) :=
  Equiv.piEquivPiSubtypeProd P (fun _ => ℕ)

/-- The edge function on `G` equal to `a` on the `P`-side and zero elsewhere. -/
noncomputable def shb_cutLeft (P : G.edgeFinset → Prop) [DecidablePred P]
    (a : {e : G.edgeFinset // P e} → ℕ) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm (a, fun _ => 0)

/-- The edge function on `G` equal to `b` on the non-`P` side and zero elsewhere. -/
noncomputable def shb_cutRight (P : G.edgeFinset → Prop) [DecidablePred P]
    (b : {e : G.edgeFinset // ¬ P e} → ℕ) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm (fun _ => 0, b)

/-- The edge function on `G` glued from a pair of side edge functions. -/
noncomputable def shb_cutJoin (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab : ({e : G.edgeFinset // P e} → ℕ) ×
      ({e : G.edgeFinset // ¬ P e} → ℕ)) : G.edgeFinset → ℕ :=
  (shb_cutEquiv G P).symm ab

omit [DecidableEq V] in
@[simp] lemma shb_cutJoin_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab) (e : G.edgeFinset) :
    shb_cutJoin G P ab e = if h : P e then ab.1 ⟨e, h⟩ else ab.2 ⟨e, h⟩ := by
  simp [shb_cutJoin, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]

omit [DecidableEq V] in
@[simp] lemma shb_cutLeft_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (a) (e : G.edgeFinset) :
    shb_cutLeft G P a e = if h : P e then a ⟨e, h⟩ else 0 := by
  simp [shb_cutLeft, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]

omit [DecidableEq V] in
@[simp] lemma shb_cutRight_apply (P : G.edgeFinset → Prop) [DecidablePred P]
    (b) (e : G.edgeFinset) :
    shb_cutRight G P b e = if h : P e then 0 else b ⟨e, h⟩ := by
  simp [shb_cutRight, shb_cutEquiv, Equiv.piEquivPiSubtypeProd]

/-! ## B. Weights along a cut -/

/-- A glued current is the sum of its two parts extended by zero. -/
lemma shb_ofEdgeFun_cutJoin_add
    (P : G.edgeFinset → Prop) [DecidablePred P] (a b) :
    (fun e => ofEdgeFun G (shb_cutLeft G P a) e +
      ofEdgeFun G (shb_cutRight G P b) e) =
      ofEdgeFun G (shb_cutJoin G P (a, b)) := by
  funext e
  unfold ofEdgeFun
  by_cases he : e ∈ G.edgeFinset
  · rw [dite_eq_left he, dite_eq_left he, dite_eq_left he]
    by_cases hp : P ⟨e, he⟩ <;> simp [shb_cutJoin_apply, hp]
  · rw [dite_eq_right he, dite_eq_right he, dite_eq_right he]

/-- The weight of a glued current is the product of the weights of its two parts. -/
lemma shb_weight_cutJoin_split (β : ℝ) (J : Sym2 V → ℝ)
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
  rw [dite_eq_left he, dite_eq_left he]
  by_cases hp : P ⟨e, he⟩ <;>
    simp [shb_cutLeft_apply, shb_cutRight_apply, hp, heSet]

omit [DecidableEq V] in
lemma shb_cutLeft_injective (P : G.edgeFinset → Prop) [DecidablePred P] :
    Function.Injective (shb_cutLeft G P) := by
  intro a a' h
  have h' := congrArg (shb_cutEquiv G P) h
  simpa [shb_cutLeft] using congrArg Prod.fst h'

omit [DecidableEq V] in
lemma shb_cutRight_injective (P : G.edgeFinset → Prop) [DecidablePred P] :
    Function.Injective (shb_cutRight G P) := by
  intro b b' h
  have h' := congrArg (shb_cutEquiv G P) h
  simpa [shb_cutRight] using congrArg Prod.snd h'

/-- The weight of the `P`-side part extended by zero. -/
noncomputable def shb_cutLeftWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (a : {e : G.edgeFinset // P e} → ℕ) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutLeft G P a))

/-- The weight of the non-`P` side part extended by zero. -/
noncomputable def shb_cutRightWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (b : {e : G.edgeFinset // ¬ P e} → ℕ) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutRight G P b))

/-- The weight of a glued current. -/
noncomputable def shb_cutJoinWeight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P]
    (ab : ({e : G.edgeFinset // P e} → ℕ) ×
      ({e : G.edgeFinset // ¬ P e} → ℕ)) : ℝ :=
  weight G β J (ofEdgeFun G (shb_cutJoin G P ab))

/-- The weight of a glued current factors. -/
lemma shb_cutJoinWeight_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] (ab) :
    shb_cutJoinWeight G β J P ab =
      shb_cutLeftWeight G β J P ab.1 * shb_cutRightWeight G β J P ab.2 := by
  exact shb_weight_cutJoin_split G β J P ab.1 ab.2

lemma shb_summable_weight_cutLeft (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    Summable (fun a : {e : G.edgeFinset // P e} → ℕ =>
      shb_cutLeftWeight G β J P a) :=
  (shb_summable_weight G β J).comp_injective (shb_cutLeft_injective G P)

lemma shb_summable_weight_cutRight (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    Summable (fun b : {e : G.edgeFinset // ¬ P e} → ℕ =>
      shb_cutRightWeight G β J P b) :=
  (shb_summable_weight G β J).comp_injective (shb_cutRight_injective G P)

/-! ## C. Weight masses along a cut -/

/-- The sum over pairs of a product of summable functions is the product of the sums. -/
lemma shb_tsum_prod_factor {A B : Type*} (f : A → ℝ) (g : B → ℝ)
    (hf : Summable f) (hg : Summable g) :
    (∑' ab : A × B, f ab.1 * g ab.2) = (∑' a, f a) * ∑' b, g b := by
  exact (Summable.tsum_mul_tsum hf hg
    (summable_mul_of_summable_norm hf.norm hg.norm)).symm

/-- The total weight mass of currents on `G`. -/
noncomputable def shb_fullWeightMass (β : ℝ) (J : Sym2 V → ℝ) : ℝ :=
  ∑' m : G.edgeFinset → ℕ, weight G β J (ofEdgeFun G m)

/-- The weight mass of `P`-side parts. -/
noncomputable def shb_cutLeftMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' a, shb_cutLeftWeight G β J P a

/-- The weight mass of non-`P` side parts. -/
noncomputable def shb_cutRightMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' b, shb_cutRightWeight G β J P b

/-- The weight mass summed over pairs of parts. -/
noncomputable def shb_cutJoinMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] : ℝ :=
  ∑' ab, shb_cutJoinWeight G β J P ab

/-- The total weight mass equals the mass summed over pairs of parts. -/
lemma shb_fullWeightMass_eq_cutJoinMass (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_fullWeightMass G β J = shb_cutJoinMass G β J P := by
  unfold shb_fullWeightMass shb_cutJoinMass shb_cutJoinWeight shb_cutJoin
  rw [← (shb_cutEquiv G P).symm.tsum_eq]

/-- The mass summed over pairs factors into the masses of the two sides. -/
lemma shb_cutJoinMass_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_cutJoinMass G β J P =
      shb_cutLeftMass G β J P * shb_cutRightMass G β J P := by
  unfold shb_cutJoinMass shb_cutLeftMass shb_cutRightMass
  rw [tsum_congr (fun ab => shb_cutJoinWeight_factor G β J P ab)]
  exact shb_tsum_prod_factor
    (shb_cutLeftWeight G β J P) (shb_cutRightWeight G β J P)
    (shb_summable_weight_cutLeft G β J P)
    (shb_summable_weight_cutRight G β J P)

/-- The total weight mass factors along a cut. -/
theorem shb_tsum_weight_cut_factor (β : ℝ) (J : Sym2 V → ℝ)
    (P : G.edgeFinset → Prop) [DecidablePred P] :
    shb_fullWeightMass G β J =
      shb_cutLeftMass G β J P * shb_cutRightMass G β J P :=
  (shb_fullWeightMass_eq_cutJoinMass G β J P).trans
    (shb_cutJoinMass_factor G β J P)

end StatMech.Sharpness
