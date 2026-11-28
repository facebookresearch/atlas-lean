/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.ClassicalProcesses.TopLevelCutElimination

/-!
# Tests for Classical Processes top-level cut elimination

A typed three-party chain that reduces to a process that is not a cut, both
by explicit steps and through the main theorem; typed progress witnesses for
the corners of the case analysis (`⊤` against a channel of type `0`, a link
with the cut channel as its first endpoint, a choice against a selection, a
tensor commuting conversion whose cut channel is held only by `⊤`, and cuts
at an exponential proposition held through absorption and through a link);
and a typed `&` commuting conversion on which summing both branches of a
choice increases, while the measure decreases.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.ClassicalProcesses

namespace TopLevelCutEliminationTests

/-- Atoms used in the tests. -/
inductive TestAtom where
  | left : TestAtom
  | right : TestAtom
deriving DecidableEq, Repr

/-- The three-party chain `νx:1.(x[].0 | νy:1.(x().y[].0 | y().z[].0))`, with
`z` the free channel `const 0`: the middle party waits on `x` and then signals
on `y`, and the last party waits on `y` and then signals on `z`. -/
def chain : Proc TestAtom :=
  .cut .one (.emptyOutput (.var 0))
    (.cut .one (.emptyInput (.var 1) (.emptyOutput (.var 0)))
      (.emptyInput (.var 0) (.emptyOutput (.const 0))))

/-- The chain is typed with `z : 1`. -/
theorem chain_typed : HasType ((∅ : Context TestAtom).insert (.const 0) .one) chain := by
  rw [← Finmap.empty_union (s₁ := (∅ : Context TestAtom).insert (.const 0) .one)]
  refine HasType.cut ?_ ?_ (Finmap.disjoint_empty _)
  · convert HasType.one (Atom := TestAtom) (x := .var 0) using 1
    decide
  · -- the inner cut splits the outer channel `x` (to the middle party) from `z`
    have hmid : HasType
        ((Context.lift ((∅ : Context TestAtom).insert (.var 0) .bot)).insert (.var 0) .one)
        (.emptyInput (.var 1) (.emptyOutput (.var 0))) := by
      convert HasType.bot (x := .var 1) (HasType.one (Atom := TestAtom) (x := .var 0))
        (by decide) using 1
      decide
    have hlast : HasType
        ((Context.lift ((∅ : Context TestAtom).insert (.const 0) .one)).insert (.var 0)
          (Logic.CLL.Proposition.one).dual)
        (.emptyInput (.var 0) (.emptyOutput (.const 0))) := by
      convert HasType.bot (x := .var 0) (HasType.one (Atom := TestAtom) (x := .const 0))
        (by decide) using 1
      decide
    convert HasType.cut hmid hlast (by decide) using 1
    decide

/-- The chain reduces to `z[].0`: a `⊥` commuting conversion under the outer
cut, then two `1`/`⊥` principal steps. -/
theorem chain_steps : Steps chain (.emptyOutput (.const 0)) := by
  have first : Step chain (.cut .one (.emptyOutput (.var 0)) (.emptyInput (.var 0)
      (.cut .one (.emptyOutput (.var 0)) (.emptyInput (.var 0) (.emptyOutput (.const 0)))))) :=
    Step.cutRight _ _ (Step.commBot .one (.var 0) _ _)
  exact .tail (.tail (.single first) (Step.oneBot (.cut .one (.emptyOutput (.var 0))
    (.emptyInput (.var 0) (.emptyOutput (.const 0)))))) (Step.oneBot (.emptyOutput (.const 0)))

/-- The result of the chain is not a cut. -/
theorem chain_result_not_cut : ¬ (Proc.emptyOutput (.const 0) : Proc TestAtom).IsCut := by
  rintro ⟨a, q₁, q₂, he⟩
  cases he

/-- The result of the chain is a normal form of one-step reduction. -/
theorem chain_result_normal :
    Relation.Normal Step (Proc.emptyOutput (.const 0) : Proc TestAtom) := by
  exact (HasType.one (Atom := TestAtom) (x := .const 0)).normal_iff_not_isCut.mpr
    chain_result_not_cut

/-- The chain, a typed cut, takes a step. -/
theorem chain_reducible : Relation.Reducible Step chain := by
  exact chain_typed.reducible_of_isCut ⟨_, _, _, rfl⟩

/-- The chain reduces to a process that is not a cut, by top-level cut
elimination. -/
theorem chain_reduces_to_non_cut : ∃ q, Steps chain q ∧ ¬ ∃ a q₁ q₂, q = .cut a q₁ q₂ := by
  exact chain_typed.exists_steps_not_cut

/-- `⊤` on the cut channel against a `⊤` on another channel that absorbs the
cut channel at type `0`: no principal reduction exists for `⊤`/`0`, and after
cut symmetry the cut commutes past the second `⊤`. -/
theorem top_zero_cut_typed_step :
    HasType ((∅ : Context TestAtom).insert (.const 1) .top)
        (.cut .top (.emptyChoice (.var 0)) (.emptyChoice (.const 1))) ∧
      Step (.cut .top (.emptyChoice (.var 0)) (.emptyChoice (.const 1)) : Proc TestAtom)
        (.emptyChoice (.const 1)) := by
  constructor
  · rw [← Finmap.empty_union (s₁ := (∅ : Context TestAtom).insert (.const 1) .top)]
    refine HasType.cut (HasType.top (var_zero_not_mem_lift _)) ?_ (Finmap.disjoint_empty _)
    convert HasType.top (Γ := (∅ : Context TestAtom).insert (.var 0) .zero) (x := .const 1)
      (by decide) using 1
    decide
  · exact Step.cong (Cong.swap _ _ _) (Step.commTop _ (.const 1) _) (Cong.refl _)

/-- A link in the right component with the cut channel as its first endpoint:
reached through cut symmetry and the symmetric axiom-cut step. -/
theorem link_right_cut_typed_step :
    HasType ((∅ : Context TestAtom).insert (.const 0) .one)
        (.cut .one (.emptyOutput (.var 0)) (.link (.var 0) (.const 0))) ∧
      Step (.cut .one (.emptyOutput (.var 0)) (.link (.var 0) (.const 0)) : Proc TestAtom)
        (.emptyOutput (.const 0)) := by
  constructor
  · rw [← Finmap.empty_union (s₁ := (∅ : Context TestAtom).insert (.const 0) .one)]
    refine HasType.cut ?_ ?_ (Finmap.disjoint_empty _)
    · convert HasType.one (Atom := TestAtom) (x := .var 0) using 1
      decide
    · convert HasType.ax (Atom := TestAtom) (w := .var 0) (x := .const 0) (a := .one)
        (by decide) using 1
      decide
  · exact Step.cong (Cong.swap _ _ _) (Step.axCutSymm _ (.const 0) _) (Cong.refl _)

/-- A choice on the cut channel against a right selection: a principal step
after cut symmetry, since the dual of `&` is `⊕`. -/
theorem choice_select_cut_typed_step :
    HasType ((∅ : Context TestAtom).insert (.const 0) .one)
        (.cut (.with .one .one)
          (.choice (.var 0) (.emptyOutput (.var 0)) (.emptyOutput (.var 0)))
          (.selectRight (.var 0) (.emptyInput (.var 0) (.emptyOutput (.const 0))))) ∧
      Step
        (.cut (.with .one .one)
          (.choice (.var 0) (.emptyOutput (.var 0)) (.emptyOutput (.var 0)))
          (.selectRight (.var 0) (.emptyInput (.var 0) (.emptyOutput (.const 0)))) :
          Proc TestAtom)
        (.cut .bot (.emptyInput (.var 0) (.emptyOutput (.const 0))) (.emptyOutput (.var 0))) := by
  constructor
  · rw [← Finmap.empty_union (s₁ := (∅ : Context TestAtom).insert (.const 0) .one)]
    refine HasType.cut ?_ ?_ (Finmap.disjoint_empty _)
    · convert HasType.with (Γ := (∅ : Context TestAtom)) (x := .var 0) HasType.one HasType.one
        Finmap.notMem_empty using 1
      decide
    · have hcont : HasType (((∅ : Context TestAtom).insert (.const 0) .one).insert (.var 0) .bot)
          (.emptyInput (.var 0) (.emptyOutput (.const 0))) :=
        HasType.bot HasType.one (by decide)
      convert HasType.oplusRight (a := .bot) hcont (by decide) using 1
      decide
  · exact Step.cong (Cong.swap _ _ _) (Step.oplusWithRight _ _ _ _ _) (Cong.refl _)

/-- A typed redex for the `&` commuting conversion: a choice on the free
channel `const 1`, both of whose branches use the cut channel. -/
def choiceCommuteRedex : Proc TestAtom :=
  .cut .bot
    (.choice (.const 1) (.emptyInput (.var 0) (.emptyOutput (.const 1)))
      (.emptyInput (.var 0) (.emptyOutput (.const 1))))
    (.emptyOutput (.var 0))

/-- The `&` commuting reduct of `choiceCommuteRedex`: the cut is copied into
both branches of the choice. -/
def choiceCommuteReduct : Proc TestAtom :=
  .choice (.const 1)
    (.cut .bot (.emptyInput (.var 0) (.emptyOutput (.const 1))) (.emptyOutput (.var 0)))
    (.cut .bot (.emptyInput (.var 0) (.emptyOutput (.const 1))) (.emptyOutput (.var 0)))

/-- A variant of the cut weight that sums both branches of a choice instead of
taking the heavier one. -/
noncomputable def sumWeight : Proc TestAtom → ℕ
  | .link _ _ => 0
  | .cut a p q => sizeOf a + sumWeight p + sumWeight q
  | .output _ p q => sumWeight p + sumWeight q
  | .input _ p => sumWeight p
  | .selectLeft _ p => sumWeight p
  | .selectRight _ p => sumWeight p
  | .choice _ p q => sumWeight p + sumWeight q
  | .emptyOutput _ => 0
  | .emptyInput _ p => sumWeight p
  | .emptyChoice _ => 0

/-- On a typed `&` commuting conversion, the summed weight increases: summing
both branches is not a reduction measure, which is why the cut weight takes
the heavier branch. -/
theorem choice_commute_sum_weight_grows :
    HasType ((∅ : Context TestAtom).insert (.const 1) (.with .one .one)) choiceCommuteRedex ∧
      Step choiceCommuteRedex choiceCommuteReduct ∧
      sumWeight choiceCommuteRedex < sumWeight choiceCommuteReduct := by
  refine ⟨?_, Step.commChoice .bot (.const 1) _ _ _, ?_⟩
  · have hbranch : HasType (((∅ : Context TestAtom).insert (.var 0) .bot).insert (.const 1) .one)
        (.emptyInput (.var 0) (.emptyOutput (.const 1))) := by
      convert HasType.bot (x := .var 0) (HasType.one (Atom := TestAtom) (x := .const 1))
        (by decide) using 1
      decide
    rw [← Finmap.union_empty (s₁ := (∅ : Context TestAtom).insert (.const 1) (.with .one .one))]
    refine HasType.cut ?_ ?_ (Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty _))
    · convert HasType.with (x := .const 1) hbranch hbranch (by decide) using 1
      decide
    · convert HasType.one (Atom := TestAtom) (x := .var 0) using 1
      decide
  · simp [sumWeight, choiceCommuteRedex, choiceCommuteReduct]

/-- On the same step, the measure decreases. -/
theorem choice_commute_measure_lt : choiceCommuteReduct.measure < choiceCommuteRedex.measure := by
  exact Step.measure_lt (Step.commChoice .bot (.const 1) _ _ _)

/-- A typed cut against an output on a free channel whose cut channel is held
only by the `⊤` in the first output component, being free in neither
component: the tensor commuting conversion still applies. -/
theorem top_absorbed_tensor_cut_typed_step :
    HasType ((((∅ : Context TestAtom).insert (.const 1) .top).insert (.const 2) .top).insert
          (.const 0) (.tensor .one .one))
        (.cut .bot (.output (.const 0) (.emptyChoice (.const 1)) (.emptyChoice (.const 2)))
          (.emptyOutput (.var 0))) ∧
      Step
        (.cut .bot (.output (.const 0) (.emptyChoice (.const 1)) (.emptyChoice (.const 2)))
          (.emptyOutput (.var 0)) : Proc TestAtom)
        (.output (.const 0) (.cut .bot (.emptyChoice (.const 1)) (.emptyOutput (.var 0)))
          (.emptyChoice (.const 2))) := by
  refine ⟨?_, Step.commTensorLeft .bot (.const 0) (.emptyChoice (.const 1))
    (.emptyChoice (.const 2)) (.emptyOutput (.var 0)) (Or.inr rfl)⟩
  rw [← Finmap.union_empty (s₁ := (((∅ : Context TestAtom).insert (.const 1) .top).insert
    (.const 2) .top).insert (.const 0) (.tensor .one .one))]
  refine HasType.cut ?_ ?_ (Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty _))
  · -- the first output component holds `const 1 : ⊤` and absorbs the cut channel
    have hfirst : HasType
        ((Context.lift (((∅ : Context TestAtom).insert (.const 1) .top).insert (.var 0)
          .bot)).insert (.var 0) .one) (.emptyChoice (.const 1)) := by
      convert HasType.top
        (Γ := ((∅ : Context TestAtom).insert (.var 1) .bot).insert (.var 0) .one)
        (x := .const 1) (by decide) using 1
      decide
    have hsecond : HasType (((∅ : Context TestAtom).insert (.const 2) .top).insert (.const 0) .one)
        (.emptyChoice (.const 2)) := by
      convert HasType.top (Γ := (∅ : Context TestAtom).insert (.const 0) .one) (x := .const 2)
        (by decide) using 1
      decide
    convert HasType.tensor (x := .const 0) hfirst hsecond (by decide) (by decide) (by decide)
      using 1
    decide
  · convert HasType.one (Atom := TestAtom) (x := .var 0) using 1
    decide

/-- A cut at an exponential proposition whose channel is absorbed by `⊤` on
both sides, with no link: no process acts on an exponential channel, and the
cut commutes past the `⊤`. -/
theorem exponential_absorbed_cut_typed_step :
    HasType (((∅ : Context TestAtom).insert (.const 1) .top).insert (.const 2) .top)
        (.cut (.bang .one) (.emptyChoice (.const 1)) (.emptyChoice (.const 2))) ∧
      Step (.cut (.bang .one) (.emptyChoice (.const 1)) (.emptyChoice (.const 2)) :
          Proc TestAtom)
        (.emptyChoice (.const 1)) := by
  refine ⟨?_, Step.commTop _ (.const 1) _⟩
  rw [show (((∅ : Context TestAtom).insert (.const 1) .top).insert (.const 2) .top) =
      (∅ : Context TestAtom).insert (.const 1) .top ∪ (∅ : Context TestAtom).insert (.const 2) .top
    from by decide]
  refine HasType.cut ?_ ?_ (by decide)
  · -- `const 1 : ⊤` absorbs the cut channel at `!1`
    convert HasType.top (Γ := (∅ : Context TestAtom).insert (.var 0) (.bang .one))
      (x := .const 1) (by decide) using 1
    decide
  · -- `const 2 : ⊤` absorbs it at the dual `?⊥`
    convert HasType.top (x := .const 2)
      (Γ := (∅ : Context TestAtom).insert (.var 0) (Logic.CLL.Proposition.bang .one).dual)
      (by decide) using 1
    decide

/-- A cut at an exponential proposition held by a link on one side and absorbed
by `⊤` on the other: the axiom-cut step applies. -/
theorem exponential_link_cut_typed_step :
    HasType (((∅ : Context TestAtom).insert (.const 0) (.quest (.atomDual .left))).insert
          (.const 1) .top)
        (.cut (.bang (.atom .left)) (.link (.const 0) (.var 0)) (.emptyChoice (.const 1))) ∧
      Step (.cut (.bang (.atom .left)) (.link (.const 0) (.var 0)) (.emptyChoice (.const 1)) :
          Proc TestAtom)
        (.emptyChoice (.const 1)) := by
  refine ⟨?_, Step.axCut _ (.const 0) _⟩
  rw [show (((∅ : Context TestAtom).insert (.const 0) (.quest (.atomDual .left))).insert
        (.const 1) .top) =
      (∅ : Context TestAtom).insert (.const 0) (.quest (.atomDual .left)) ∪
        (∅ : Context TestAtom).insert (.const 1) .top
    from by decide]
  refine HasType.cut ?_ ?_ (by decide)
  · -- the link carries the cut channel at `!A` to `const 0 : ?A⊥`
    convert HasType.ax (Atom := TestAtom) (a := .bang (.atom .left)) (w := .const 0)
      (x := .var 0) (by decide) using 1
    decide
  · -- `const 1 : ⊤` absorbs the cut channel at the dual
    convert HasType.top (x := .const 1)
      (Γ := (∅ : Context TestAtom).insert (.var 0)
        (Logic.CLL.Proposition.bang (.atom .left)).dual)
      (by decide) using 1
    decide

end TopLevelCutEliminationTests

end Cslib.ClassicalProcesses
