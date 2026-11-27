/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Order.Sigma
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Limit
public import Mathlib.Logic.Equiv.Defs

/-!
# Original dependent lexicographic cellular orders

The actual outer and inner well-founded orders retain their original cover,
greatest-stage join, strict-prefix inclusion and successor-limit laws.
-/

@[expose] public section

set_option autoImplicit false

universe w w'

namespace CategoryTheory.SmallObject.CellularNormalization

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {K : J → Type w'} [∀ j, LinearOrder (K j)] [∀ j, SuccOrder (K j)]
  [∀ j, OrderBot (K j)] [∀ j, WellFoundedLT (K j)]

omit [SuccOrder J] [OrderBot J] [∀ j, SuccOrder (K j)] [∀ j, OrderBot (K j)] in
/-- The dependent lexicographic sum of the actual occurring inner shapes is well founded. -/
theorem lexWellFounded : WellFounded ((· < ·) : Lex (Sigma K) → Lex (Sigma K) → Prop) := by
  let e : Lex (Sigma K) → PSigma K := fun a => ⟨(ofLex a).1, (ofLex a).2⟩
  have h := WellFounded.psigma_lex (r := (· < ·))
    (s := fun j : J => ((· < ·) : K j → K j → Prop))
    (wellFounded_lt : WellFounded ((· < ·) : J → J → Prop))
    (fun j => (wellFounded_lt : WellFounded ((· < ·) : K j → K j → Prop)))
  apply (h.onFun (f := e)).mono
  intro a b hab
  cases hab with
  | left k l hij => exact PSigma.Lex.left _ _ hij
  | right k l hkl => exact PSigma.Lex.right _ hkl

omit [SuccOrder J] [OrderBot J] [WellFoundedLT J] [∀ j, OrderBot (K j)]
  [∀ j, WellFoundedLT (K j)] in
/-- A genuine inner successor is a genuine successor of the flattened order. -/
theorem inner_covBy {j : J} {k : K j} (hk : ¬ IsMax k) :
    ((toLex ⟨j, k⟩) : Lex (Sigma K)) ⋖ (toLex ⟨j, Order.succ k⟩) := by
  refine ⟨Sigma.Lex.right _ _ (Order.lt_succ_iff_not_isMax.mpr hk), ?_⟩
  intro b hb hb'
  rcases b with ⟨i, l⟩
  cases hb with
  | left k l hji =>
    cases hb' with
    | left l k' hij => exact (hji.not_gt hij).elim
    | right l k' hl => exact (lt_irrefl _ hji).elim
  | right k l hkl =>
    cases hb' with
    | left l k' hji => exact (lt_irrefl _ hji).elim
    | right l k' hl => exact (Order.covBy_succ_of_not_isMax hk).2 hkl hl

omit [OrderBot J] [WellFoundedLT J] [∀ j, SuccOrder (K j)]
  [∀ j, WellFoundedLT (K j)] in
/-- Greatest-inner joins cover the next original outer bottom. -/
theorem join_covBy {j : J} (hj : ¬ IsMax j) {k : K j} (hk : IsMax k) :
    ((toLex ⟨j, k⟩) : Lex (Sigma K)) ⋖ (toLex ⟨Order.succ j, ⊥⟩) := by
  refine ⟨Sigma.Lex.left _ _ (Order.lt_succ_iff_not_isMax.mpr hj), ?_⟩
  intro b hb hb'
  rcases b with ⟨i, l⟩
  cases hb with
  | left k l hji =>
    cases hb' with
    | left l k' hij => exact (Order.covBy_succ_of_not_isMax hj).2 hji hij
    | right l k' hl => exact (not_lt_of_ge bot_le hl).elim
  | right k l hkl => exact (hk.not_lt hkl).elim

omit [SuccOrder J] [OrderBot J] [WellFoundedLT J] [∀ j, SuccOrder (K j)]
  [∀ j, WellFoundedLT (K j)] in
/-- A nonbottom flat limit is an actual limit in its original inner order. -/
theorem inner_limit_of_flat_limit {j : J} {k : K j}
    (h : Order.IsSuccLimit ((toLex ⟨j, k⟩) : Lex (Sigma K))) (hk : k ≠ ⊥) :
    Order.IsSuccLimit k := by
  refine ⟨?_, ?_⟩
  · simpa only [isMin_iff_eq_bot] using hk
  · intro l hl
    apply h.isSuccPrelimit (toLex ⟨j, l⟩)
    refine ⟨Sigma.Lex.right _ _ hl.lt, ?_⟩
    intro b hb hb'
    rcases b with ⟨i, n⟩
    cases hb with
    | left l n hji =>
      cases hb' with
      | left n k hij => exact (hji.not_gt hij).elim
      | right n k hn => exact (lt_irrefl _ hji).elim
    | right l n hln =>
      cases hb' with
      | left n k hji => exact (lt_irrefl _ hji).elim
      | right n k hnk => exact hl.2 hln hnk

/-- The inclusion of an original inner strict prefix into the corresponding flat strict prefix. -/
def innerStrictPrefix (j : J) (k : K j) : Set.Iio k → Set.Iio ((toLex ⟨j, k⟩) : Lex (Sigma K)) :=
  fun l => ⟨(toLex ⟨j, l.1⟩), Sigma.Lex.right _ _ l.2⟩

omit [SuccOrder J] [OrderBot J] [WellFoundedLT J] [∀ j, SuccOrder (K j)]
  [∀ j, WellFoundedLT (K j)] in
/-- Every flattened maximum has both an original maximal outer and inner vertex. -/
theorem flat_isMax_iff (j : J) (k : K j) :
    IsMax ((toLex ⟨j, k⟩) : Lex (Sigma K)) ↔ IsMax j ∧ IsMax k := by
  constructor
  · intro h
    constructor
    · intro i hji
      obtain rfl | hji := hji.eq_or_lt
      · exact le_rfl
      · exact (h.not_lt (Sigma.Lex.left k (⊥ : K i) hji)).elim
    · intro l hkl
      have hf := h (Sigma.Lex.right k l hkl)
      exact (Sigma.Lex.le_def.mp hf).resolve_left (lt_irrefl _) |>.choose_spec
  · rintro ⟨hj, hk⟩ b hb
    rcases b with ⟨i, l⟩
    cases hb with
    | left k l hji => exact (hj.not_lt hji).elim
    | right k l hkl => exact Sigma.Lex.right _ _ (hk hkl)

end CategoryTheory.SmallObject.CellularNormalization
