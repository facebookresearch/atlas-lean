/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.SumRelFeedback
public import MathlibExt.CategoryTheory.Monoidal.Traced
/-!
# The finite-path symmetric trace on disjoint-union relations

The finite-path feedback operation satisfies all six symmetric trace axioms.
Naturality and superposing act on visible edges. Sliding rotates alternating
hidden paths, and double-feedback vanishing splits and flattens finite paths
across two hidden summands. The empty unit and yanking have their usual effects.

This is Joyal, Street and Verity, Traced monoidal categories (1996), Proposition 6.3,
https://doi.org/10.1017/S0305004100074338. The proof applies to arbitrary relations
on possibly infinite sets, with no determinism or termination assumption.
-/

@[expose] public section
open CategoryTheory MonoidalCategory
namespace CategoryTheory.SumRelCat
universe u
variable {X X' Y Y' U V W Z : SumRelCat.{u}}

/-- Visible pre- and postcomposition commute with finite-path feedback. -/
theorem feedback_naturality (f : X ⊗ U ⟶ Y ⊗ U) (g : X' ⟶ X) (h : Y ⟶ Y') :
    feedback ((g ⊗ₘ 𝟙 U) ≫ f ≫ (h ⊗ₘ 𝟙 U)) = g ≫ feedback f ≫ h := by
  apply Hom.ext
  ext ⟨x, y⟩
  rw [feedback_rel]
  simp only [rel_comp, SetRel.comp, tensor_rel_eq, rel_id, SetRel.id,
    Set.mem_ofPred_eq, feedback_rel]
  aesop

/-- Closing the empty hidden summand removes the unitors. -/
theorem feedback_vanishing_unit (f : X ⊗ 𝟙_ SumRelCat ⟶ Y ⊗ 𝟙_ SumRelCat) :
    feedback f = (ρ_ X).inv ≫ f ≫ (ρ_ Y).hom := by
  apply Hom.ext
  ext ⟨x, y⟩
  rw [feedback_zero]
  simp [rel_comp, SetRel.comp]

/-- Closing the swap relation gives the identity. -/
theorem feedback_yanking (X : SumRelCat.{u}) : feedback (β_ X X).hom = 𝟙 X := by
  apply Hom.ext
  ext ⟨x, y⟩
  rw [feedback_rel]
  simp only [tensorObj_def, braiding_hom_rel_eq, Set.mem_ofPred_eq, Sum.swap_inl,
    reduceCtorEq, Sum.inr.injEq, Sum.swap_inr, Sum.inl.injEq, exists_and_left,
    ↓existsAndEq, and_true, exists_eq_left', false_or, rel_id, SetRel.mem_id]
  rw [Relation.reflTransGen_iff_eq (by simp)]
  exact eq_comm
/-- Feedback commutes with a separate visible relation. -/
theorem feedback_superposing (f : X ⊗ U ⟶ Y ⊗ U) (g : W ⟶ Z) :
    feedback ((α_ W X U).hom ≫ (g ⊗ₘ f) ≫ (α_ Z Y U).inv) = g ⊗ₘ feedback f := by
  apply Hom.ext
  ext ⟨x, y⟩
  rcases x with x | x <;> rcases y with y | y <;>
    rw [feedback_rel] <;>
    simp [rel_comp, SetRel.comp, Sum.exists, feedback_rel]
private theorem rtc_rotate {A B : Type u} (R : A → B → Prop) (S : B → A → Prop)
    (v : B) (b : A) :
    (∃ a, S v a ∧ Relation.ReflTransGen (fun a b => ∃ w, R a w ∧ S w b) a b) ↔
      ∃ w, Relation.ReflTransGen (fun v w => ∃ a, S v a ∧ R a w) v w ∧ S w b := by
  constructor
  · rintro ⟨a, ha, hp⟩
    induction hp with
    | refl => exact ⟨v, .refl, ha⟩
    | @tail b c _ h ih =>
      obtain ⟨w, hw, hwb⟩ := ih
      obtain ⟨z, hbz, hzc⟩ := h
      exact ⟨z, hw.tail ⟨b, hwb, hbz⟩, hzc⟩
  · rintro ⟨w, hp, hb⟩
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨b, hb, .refl⟩
    | @head v w h _ ih =>
      obtain ⟨a, hva, haw⟩ := h
      obtain ⟨c, hwc, hcb⟩ := ih
      exact ⟨a, hva, hcb.head ⟨w, haw, hwc⟩⟩

private theorem comp_right_hidden_rel (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U)
    (s : Sum X U) (t : Sum Y U) :
    (s, t) ∈ (f ≫ (𝟙 Y ⊗ₘ g)).rel ↔ match t with
      | .inl y => (s, Sum.inl y) ∈ f.rel
      | .inr u => ∃ v, (s, Sum.inr v) ∈ f.rel ∧ (v, u) ∈ g.rel := by
  rw [comp_rel]
  cases t <;> simp [Sum.exists]

private theorem comp_left_hidden_rel (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U)
    (s : Sum X V) (t : Sum Y V) :
    (s, t) ∈ ((𝟙 X ⊗ₘ g) ≫ f).rel ↔ match s with
      | .inl x => (Sum.inl x, t) ∈ f.rel
      | .inr v => ∃ u, (v, u) ∈ g.rel ∧ (Sum.inr u, t) ∈ f.rel := by
  rw [comp_rel]
  cases s <;> simp [Sum.exists]

/-- A relation can slide around the feedback loop. -/
theorem feedback_dinaturality (f : X ⊗ U ⟶ Y ⊗ V) (g : V ⟶ U) :
    feedback (f ≫ (𝟙 Y ⊗ₘ g)) = feedback ((𝟙 X ⊗ₘ g) ≫ f) := by
  apply Hom.ext
  ext ⟨x, y⟩
  simp only [feedback_rel, comp_right_hidden_rel, comp_left_hidden_rel]
  constructor
  · rintro (h | ⟨a, b, ⟨v, hx, hva⟩, hab, hy⟩)
    · exact Or.inl h
    · obtain ⟨w, hvw, hwb⟩ := (rtc_rotate
        (fun a v => (Sum.inr a, Sum.inr v) ∈ f.rel)
        (fun v a => (v, a) ∈ g.rel) v b).mp ⟨a, hva, hab⟩
      exact Or.inr ⟨v, w, hx, hvw, b, hwb, hy⟩
  · rintro (h | ⟨v, w, hx, hvw, b, hwb, hy⟩)
    · exact Or.inl h
    · obtain ⟨a, hva, hab⟩ := (rtc_rotate
        (fun a v => (Sum.inr a, Sum.inr v) ∈ f.rel)
        (fun v a => (v, a) ∈ g.rel) v b).mpr ⟨w, hvw, hwb⟩
      exact Or.inr ⟨a, b, ⟨v, hx, hva⟩, hab, hy⟩


private def reassoc (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :=
  (α_ X U V).hom ≫ f ≫ (α_ Y U V).inv
private theorem reassoc_rel (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V))
    (s : Sum (Sum X U) V) (t : Sum (Sum Y U) V) :
    (s, t) ∈ (reassoc f).rel ↔
      (Equiv.sumAssoc X U V s, Equiv.sumAssoc Y U V t) ∈ f.rel := by
  rcases t with (y | u) | v <;> simp [reassoc, rel_comp, SetRel.comp]

private def exitOrContinue (P : U → Prop) (y : Y) : Sum Y U → Prop
  | .inl y' => y' = y
  | .inr u => P u

private theorem flatten_chunk (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V))
    {s : Sum (Sum X U) V} {z : Sum Y U} {y : Y}
    (hp : FeedbackPath (reassoc f) s z)
    (hz : exitOrContinue (fun u => FeedbackPath f (Sum.inr (Sum.inl u)) y) y z) :
    FeedbackPath f (Equiv.sumAssoc X U V s) y := by
  induction hp with
  | @output s z h =>
    rw [reassoc_rel] at h
    cases z with
    | inl y' => cases hz; exact .output h
    | inr u => exact .step h hz
  | step h _ ih =>
    rw [reassoc_rel] at h
    exact .step h (ih hz)

private theorem nested_to_flat (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V))
    {s : Sum X U} {y : Y} (hp : FeedbackPath (feedback (reassoc f)) s y) :
    FeedbackPath f (Equiv.sumAssoc X U V (Sum.inl s)) y := by
  induction hp with
  | output h => exact flatten_chunk f h rfl
  | step h _ ih => exact flatten_chunk f h ih

private theorem finish_chunk (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V))
    {s : Sum X U} {z : Sum Y U} {y : Y}
    (hp : FeedbackPath (reassoc f) (Sum.inl s) z)
    (hz : exitOrContinue (fun u => FeedbackPath (feedback (reassoc f)) (Sum.inr u) y) y z) :
    FeedbackPath (feedback (reassoc f)) s y := by
  cases z with
  | inl y' => cases hz; exact .output hp
  | inr u => exact .step hp hz

private theorem flat_to_chunks (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V))
    {s : Sum X (Sum U V)} {y : Y} (hp : FeedbackPath f s y) :
    ∃ z : Sum Y U, FeedbackPath (reassoc f) ((Equiv.sumAssoc X U V).symm s) z ∧
      exitOrContinue (fun u => FeedbackPath (feedback (reassoc f)) (Sum.inr u) y) y z := by
  induction hp with
  | output h =>
    refine ⟨Sum.inl _, .output ?_, rfl⟩
    rw [reassoc_rel]
    simpa using h
  | @step s v y h _ ih =>
    obtain ⟨z, hz, hfinish⟩ := ih
    cases v with
    | inl u =>
      refine ⟨Sum.inr u, .output ?_, finish_chunk f hz hfinish⟩
      rw [reassoc_rel]
      simpa using h
    | inr v =>
      refine ⟨z, .step ?_ hz, hfinish⟩
      rw [reassoc_rel]
      simpa using h

/-- Closing the hidden summand `U ⊗ V` at once equals closing `V` first and then `U`:
reassociate `f` to `(α_ X U V).hom ≫ f ≫ (α_ Y U V).inv : (X ⊗ U) ⊗ V ⟶ (Y ⊗ U) ⊗ V`, take
its feedback over `V`, and then the feedback of the result over `U`. -/
theorem feedback_vanishing_tensor (f : X ⊗ (U ⊗ V) ⟶ Y ⊗ (U ⊗ V)) :
    feedback f = feedback (feedback ((α_ X U V).hom ≫ f ≫ (α_ Y U V).inv)) := by
  apply Hom.ext
  ext ⟨x, y⟩
  constructor
  · intro h
    obtain ⟨z, hz, hfinish⟩ := flat_to_chunks f h
    exact finish_chunk f hz hfinish
  · exact nested_to_flat f


/-- The Joyal–Street–Verity finite-path trace for relations under disjoint union. -/
def symmetricTrace : SymmetricTrace SumRelCat.{u} where
  trace := feedback
  naturality := feedback_naturality
  dinaturality := feedback_dinaturality
  vanishing_unit := feedback_vanishing_unit
  vanishing_tensor := feedback_vanishing_tensor
  superposing := feedback_superposing
  yanking := feedback_yanking

/-- The supplied symmetric trace is exactly finite-path feedback. -/
@[simp] theorem trace_eq_feedback (f : X ⊗ U ⟶ Y ⊗ U) :
    symmetricTrace.trace f = feedback f := rfl

end CategoryTheory.SumRelCat
