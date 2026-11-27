/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Languages.ClassicalProcesses.Reduction

/-!
# Tests for Classical Processes reduction

Concrete principal, commuting-conversion and structural-equivalence
steps on small fixtures, typing of their reducts (including a typed
commuting conversion that exchanges bound variables), negative boundary
checks for guarded redexes and for the `κ⊗` side condition, and the
counterexample showing that cut associativity needs its free-name side
conditions in the presence of the `⊤` rule.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.ClassicalProcesses

namespace ReductionTests

/-- Atoms used in the tests. -/
inductive TestAtom where
  | left : TestAtom
  | right : TestAtom
deriving DecidableEq, Repr

/-- The proposition `A` used in the tests. -/
def propA : Logic.CLL.Proposition TestAtom := .atom .left

/-- The proposition `B` used in the tests. -/
def propB : Logic.CLL.Proposition TestAtom := .atom .right

/-- A cut of a tensor output against a par input. The cut proposition is
`A ⊗ A⊥`; the remaining channels are constants `0` and `1`. -/
def tensorParrRedex : Proc TestAtom :=
  .cut (.tensor propA propA.dual)
    (.output (.var 0)
      (.link (.const 0) (.var 0))
      (.link (.const 1) (.var 0)))
    (.input (.var 0) (.link (.var 0) (.var 1)))

/-- A cut of empty output against empty input, with a link as the body of
the empty input. -/
def unitCut : Proc TestAtom :=
  .cut .one (.emptyOutput (.var 0))
    (.emptyInput (.var 0) (.link (.const 0) (.const 1)))

/-- The tensor/par redex steps by the principal tensor-par rule. -/
theorem tensor_parr_step :
    Step tensorParrRedex
      (.cut propA.dual (.link (.const 1) (.var 0))
        (.cut propA (.link (.const 0) (.var 0)) (.link (.var 0) (.var 1)))) :=
  Step.tensorParr _ _ _ _ _

/-- The tensor/par reduct is typed in the redex's context. -/
theorem tensor_parr_reduct_typed :
    HasType
      (((∅ : Context TestAtom).insert (.const 0) propA.dual).insert
        (.const 1) propA)
      (.cut propA.dual (.link (.const 1) (.var 0))
        (.cut propA (.link (.const 0) (.var 0)) (.link (.var 0) (.var 1)))) := by
  have hl : HasType ((Context.lift ((∅ : Context TestAtom).insert (PiCalculus.Name.const 1)
      propA)).insert (.var 0) propA.dual) (.link (.const 1) (.var 0)) := by
    convert HasType.ax (w := .const 1) (x := .var 0) (a := propA.dual) (by decide) using 1
    decide
  have hi₁ : HasType ((Context.lift ((∅ : Context TestAtom).insert (PiCalculus.Name.const 0)
      propA.dual)).insert (.var 0) propA) (.link (.const 0) (.var 0)) := by
    convert HasType.ax (w := .const 0) (x := .var 0) (a := propA) (by decide) using 1
    decide
  have hi₂ : HasType ((Context.lift ((∅ : Context TestAtom).insert (PiCalculus.Name.var 0)
      propA)).insert (.var 0) propA.dual) (.link (.var 0) (.var 1)) := by
    convert HasType.ax (w := .var 0) (x := .var 1) (a := propA) (by decide) using 1
    decide
  have hin := HasType.cut hi₁ hi₂ (by decide)
  have hr : HasType ((Context.lift ((∅ : Context TestAtom).insert (PiCalculus.Name.const 0)
      propA.dual)).insert (.var 0) propA.dual.dual)
      (.cut propA (.link (.const 0) (.var 0)) (.link (.var 0) (.var 1))) := by
    convert hin using 1
    decide
  have h := HasType.cut hl hr (by decide)
  convert h using 1
  decide

/-- Two axiom-cut steps reduce the tensor/par reduct to a single link. -/
theorem tensor_parr_steps_to_link :
    Steps tensorParrRedex (.link (.const 0) (.const 1)) :=
  Relation.ReflTransGen.head (Step.tensorParr _ _ _ _ _)
    (Relation.ReflTransGen.head (Step.axCut _ (.const 1) _)
      (Relation.ReflTransGen.head (Step.axCut _ (.const 0) _) Relation.ReflTransGen.refl))

/-- The unit cut reduces by the `1`/`⊥` rule to its body, a link. -/
theorem unit_cut_step :
    Step unitCut (.link (.const 0) (.const 1)) :=
  Step.oneBot (.link (.const 0) (.const 1))

/-- A cut choosing the left additive branch steps by `oplusWithLeft`. -/
theorem oplus_left_step :
    Step (.cut (.oplus propA propB) (.selectLeft (.var 0) (.emptyChoice (.var 0)))
        (.choice (.var 0) (.emptyChoice (.var 0)) (.emptyChoice (.var 0))))
      (.cut propA (.emptyChoice (.var 0)) (.emptyChoice (.var 0))) :=
  Step.oplusWithLeft _ _ _ _ _

/-- A cut choosing the right additive branch steps by `oplusWithRight`. -/
theorem oplus_right_step :
    Step (.cut (.oplus propA propB) (.selectRight (.var 0) (.emptyChoice (.var 0)))
        (.choice (.var 0) (.emptyChoice (.var 0)) (.emptyChoice (.var 0))))
      (.cut propB (.emptyChoice (.var 0)) (.emptyChoice (.var 0))) :=
  Step.oplusWithRight _ _ _ _ _

/-- A par input on a free channel commutes past the cut, exchanging the
two bound variables in its continuation. -/
theorem comm_parr_step :
    Step (.cut .one (.input (PiCalculus.liftName 0 (.const 0))
        (.link (.var 1) (.var 0))) (.emptyOutput (.var 0)))
      (.input (.const 0)
        (.cut .one (.link (.var 0) (.var 1))
          ((.emptyOutput (.var 0) : Proc TestAtom).liftAt 1))) :=
  Step.commParr _ _ _ _

/-- A typed par-commutation redex: the input on free channel `const 0`
sits under a cut at `⊥` whose left component closes the cut channel with
an empty input and links the input's bound variable to `const 0`. -/
def commParrRedex : Proc TestAtom :=
  .cut .bot
    (.input (PiCalculus.liftName 0 (.const 0))
      (.emptyInput (.var 1) (.link (.var 0) (.const 0))))
    (.emptyOutput (.var 0))

/-- The `κ⅋` reduct of `commParrRedex`: the input moves outside the cut
and the two bound variables are exchanged in the continuation. -/
def commParrReduct : Proc TestAtom :=
  .input (.const 0)
    (.cut .bot (.emptyInput (.var 0) (.link (.var 1) (.const 0)))
      (.emptyOutput (.var 0)))

/-- The typed par-commutation redex steps by `commParr` to its reduct. -/
theorem comm_parr_typed_step : Step commParrRedex commParrReduct :=
  Step.commParr _ _ _ _

/-- The par-commutation redex is typed with `const 0 : A⊥ ⅋ A`. -/
theorem comm_parr_redex_typed :
    HasType ((∅ : Context TestAtom).insert (.const 0) (.parr propA.dual propA))
      commParrRedex := by
  have hbody : HasType
      (((Context.lift ((∅ : Context TestAtom).insert (PiCalculus.Name.var 0)
        Logic.CLL.Proposition.bot)).insert (.var 0) propA.dual).insert
        (PiCalculus.liftName 0 (.const 0)) propA)
      (.emptyInput (.var 1) (.link (.var 0) (.const 0))) := by
    convert HasType.bot (x := .var 1)
      (HasType.ax (w := .var 0) (x := .const 0) (a := propA) (by decide)) (by decide) using 1
    decide
  have hl : HasType ((Context.lift ((∅ : Context TestAtom).insert (PiCalculus.Name.const 0)
      (Logic.CLL.Proposition.parr propA.dual propA))).insert (.var 0) .bot)
      (.input (PiCalculus.liftName 0 (.const 0))
        (.emptyInput (.var 1) (.link (.var 0) (.const 0)))) := by
    convert HasType.parr (x := .const 0) hbody (by decide) using 1
    all_goals first | rfl | decide
  have h := HasType.cut (Δ := ∅) hl
    (by convert (HasType.one (Atom := TestAtom) (x := .var 0)) using 1; decide)
    (Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty _))
  rw [Finmap.union_empty] at h
  exact h

/-- The par-commutation reduct is typed in the same context. -/
theorem comm_parr_reduct_typed :
    HasType ((∅ : Context TestAtom).insert (.const 0) (.parr propA.dual propA))
      commParrReduct :=
  comm_parr_redex_typed.preservation comm_parr_typed_step

/-- Cut symmetry relates the tensor/par redex to its swapped form. -/
theorem cong_swap_redex :
    Cong tensorParrRedex
      (.cut (Logic.CLL.Proposition.tensor propA propA.dual).dual
        (.input (.var 0) (.link (.var 0) (.var 1)))
        (.output (.var 0) (.link (.const 0) (.var 0))
          (.link (.const 1) (.var 0)))) :=
  Cong.swap _ _ _

/-- Cut associativity relates the two associations of a chain of links
`const 0 ↔ x ↔ y ↔ const 1`; the middle link uses both cut channels. -/
theorem cong_assoc_links :
    Cong
      (.cut propA
        (.cut propA ((.link (.const 0) (.var 0) : Proc TestAtom).liftAt 1)
          (.link (.var 0) (.var 1)))
        (.link (.var 0) (.const 1)))
      (.cut propA (.link (.const 0) (.var 0))
        (.cut propA ((.link (.var 0) (.var 1) : Proc TestAtom).rename
            (PiCalculus.swapNameAt 0))
          ((.link (.var 0) (.const 1) : Proc TestAtom).liftAt 1))) :=
  Cong.assoc _ _ _ _ _ (by decide) (by decide)

/-- The symmetric axiom cut fires with the link in the mirrored
orientation. -/
theorem ax_cut_symm_step :
    Step (Atom := TestAtom) (.cut .bot (.link (.var 0) (PiCalculus.liftName 0 (.const 0)))
        (.emptyOutput (.var 0)))
      (.emptyOutput (PiCalculus.Name.const 0)) :=
  Step.axCutSymm _ _ _

/-- A reduction under structural equivalence on both sides: the unit
cut with its components swapped still reduces. -/
theorem cong_closure_step :
    Step (Atom := TestAtom)
      (.cut .bot
        (.emptyInput (.var 0) ((.link (.const 0) (.const 1) : Proc TestAtom).liftAt 0))
        (.emptyOutput (.var 0)))
      (.link (.const 0) (.const 1)) :=
  Step.cong (Cong.swap _ _ _) (Step.oneBot (.link (.const 0) (.const 1))) (Cong.refl _)

/-- The tensor commutation: a cut whose output acts on a free channel
and whose continued output uses the cut variable commutes the output
out of the cut. -/
theorem comm_tensor_right_step :
    Step (Atom := TestAtom) (.cut .one
        (.output (PiCalculus.liftName 0 (.const 0))
          ((.emptyOutput (.var 0) : Proc TestAtom).liftAt 1)
          (.emptyOutput (.var 0)))
        (.emptyInput (.var 0) ((.link (.const 0) (.const 1) : Proc TestAtom).liftAt 0)))
      (.output (.const 0) (.emptyOutput (.var 0))
        (.cut .one (.emptyOutput (.var 0))
          (.emptyInput (.var 0) ((.link (.const 0) (.const 1) : Proc TestAtom).liftAt 0)))) :=
  Step.commTensorRight _ _ _ _ _ (by decide)

/-- The two halves of the tensor-commutation side conditions on a
constant-only `⊤` continuation: the cut variable is free in it in neither
position, but it absorbs, so it can still receive the cut. -/
theorem comm_tensor_top_branch_guards :
    PiCalculus.Name.var 1 ∉
      (Proc.emptyChoice (.const 0) : Proc TestAtom).freeNames ∧
    PiCalculus.Name.var 0 ∉
      (Proc.emptyChoice (.const 0) : Proc TestAtom).freeNames ∧
    (Proc.emptyChoice (.const 0) : Proc TestAtom).absorbs = true := by
  decide

/-- A typed tensor-commutation redex whose cut channel is held by the
`⊤` continuation through its context: the channel is free in neither
output branch, and the right commuting conversion pushes the cut into the
absorbing `⊤` branch, exposing the outer `output` as the derivation-level
`κ⊗` does. -/
theorem top_owned_tensor_redex_steps :
    HasType
      ((((∅ : Context TestAtom).insert (.const 2) propA.dual).insert (.const 0) .top).insert
        (.const 1) (.tensor propA .one))
      (.cut .bot
        (.output (PiCalculus.liftName 0 (.const 1)) (.link (.var 0) (.const 2))
          (.emptyChoice (.const 0)))
        (.emptyOutput (.var 0))) ∧
    PiCalculus.Name.var 1 ∉
      (Proc.link (.var 0) (.const 2) : Proc TestAtom).freeNames ∧
    PiCalculus.Name.var 0 ∉
      (Proc.emptyChoice (.const 0) : Proc TestAtom).freeNames ∧
    Step (Atom := TestAtom) (.cut .bot
        (.output (PiCalculus.liftName 0 (.const 1)) (.link (.var 0) (.const 2))
          (.emptyChoice (.const 0)))
        (.emptyOutput (.var 0)))
      (.output (.const 1) (.link (.var 0) (.const 2))
        (.cut .bot (.emptyChoice (.const 0)) (.emptyOutput (.var 0)))) := by
  refine ⟨?_, by decide, by decide,
    Step.commTensorRight .bot (.const 1) (.link (.var 0) (.const 2)) _ _ (Or.inr rfl)⟩
  have hp : HasType ((Context.lift ((∅ : Context TestAtom).insert (PiCalculus.Name.const 2)
      propA.dual)).insert (.var 0) propA) (.link (.var 0) (.const 2)) := by
    convert HasType.ax (w := .var 0) (x := .const 2) (a := propA.dual) (by decide) using 1
    decide
  have hq : HasType ((((∅ : Context TestAtom).insert (PiCalculus.Name.var 0) .bot).insert
      (.const 0) .top).insert (.const 1) .one) (.emptyChoice (.const 0)) := by
    convert HasType.top (Γ := ((∅ : Context TestAtom).insert (.var 0) .bot).insert (.const 1) .one)
      (x := .const 0) (by decide) using 1
    decide
  have ho := HasType.tensor hp hq (by decide) (by decide) (by decide)
  have h := HasType.cut (Δ := ∅) (a := .bot)
    (Γ := (((∅ : Context TestAtom).insert (.const 2) propA.dual).insert (.const 0) .top).insert
      (.const 1) (.tensor propA .one))
    (by convert ho using 1; decide)
    (by convert (HasType.one (Atom := TestAtom) (x := .var 0)) using 1; decide)
    (Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty _))
  rw [Finmap.union_empty] at h
  exact h

/-- A redex guarded by an input prefix does not step: only cuts reduce. -/
theorem input_guarded_no_step {q : Proc TestAtom} :
    ¬ Step (.input (.const 0) tensorParrRedex) q := by
  intro h
  obtain ⟨a, p₁, p₂, he⟩ := h.isCut
  cases he

/-- Unconditioned cut associativity, as a literal reading of the
source's term equation would state it; only used by the counterexample
below. -/
inductive CongBare : Proc TestAtom → Proc TestAtom → Prop where
  | assocBare (a b : Logic.CLL.Proposition TestAtom)
      (p q r : Proc TestAtom) :
      CongBare (.cut b (.cut a (p.liftAt 1) q) r)
        (.cut a p (.cut b (q.rename (PiCalculus.swapNameAt 0)) (r.liftAt 1)))

/-- The associativity counterexample process: a cut whose inner-left
component holds the outer cut channel only through a `⊤` process. -/
def assocCounterexample : Proc TestAtom :=
  .cut .bot
    (.cut (.oplus .bot .bot)
      (.selectLeft (.var 0) (.emptyChoice (.const 0)))
      (.choice (.var 0) (.emptyOutput (.var 0)) (.emptyOutput (.var 0))))
    (.emptyOutput (.var 0))

/-- The counterexample is typed with only the `⊤` channel free. -/
theorem assoc_counterexample_typed :
    HasType ((∅ : Context TestAtom).insert (.const 0) .top)
      assocCounterexample := by
  have hsel : HasType
      ((((∅ : Context TestAtom).insert (.const 0) .top).insert (.var 1) .bot).insert (.var 0)
        (.oplus .bot .bot))
      (.selectLeft (.var 0) (.emptyChoice (.const 0))) := by
    refine HasType.oplusLeft ?_ (by decide)
    convert HasType.top (Γ := ((∅ : Context TestAtom).insert (.var 1) .bot).insert (.var 0) .bot)
      (x := .const 0) (by decide) using 1
    decide
  have hch : HasType (((∅ : Context TestAtom).lift).insert (.var 0)
      (Logic.CLL.Proposition.oplus .bot .bot).dual)
      (.choice (.var 0) (.emptyOutput (.var 0)) (.emptyOutput (.var 0))) := by
    convert HasType.with (Γ := (∅ : Context TestAtom)) (x := .var 0) (a := .one) (b := .one)
      HasType.one HasType.one (by decide) using 1
    decide
  have hinner := HasType.cut
    (Γ := ((∅ : Context TestAtom).insert (.const 0) .top).insert (.var 0) .bot) (Δ := ∅)
    (a := .oplus .bot .bot) (by convert hsel using 1; decide) hch
    (Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty _))
  rw [Finmap.union_empty] at hinner
  have houter := HasType.cut
    (Γ := (∅ : Context TestAtom).insert (.const 0) .top) (Δ := ∅) (a := .bot)
    (by convert hinner using 1; decide)
    (by convert (HasType.one (Atom := TestAtom) (x := .var 0)) using 1; decide)
    (Finmap.Disjoint.symm _ _ (Finmap.disjoint_empty _))
  rw [Finmap.union_empty] at houter
  exact houter

/-- The bare-assoc image of the counterexample reduces by `κ&` under the
cut. -/
theorem assoc_counterexample_steps :
    Step (Atom := TestAtom) (.cut (.oplus .bot .bot)
        (.selectLeft (.var 0) (.emptyChoice (.const 0)))
        (.cut .bot (.choice (.var 1) (.emptyOutput (.var 1)) (.emptyOutput (.var 1)))
          (.emptyOutput (.var 0))))
      (.cut (.oplus .bot .bot)
        (.selectLeft (.var 0) (.emptyChoice (.const 0)))
        (.choice (.var 0)
          (.cut .bot (.emptyOutput (.var 1)) (.emptyOutput (.var 0)))
          (.cut .bot (.emptyOutput (.var 1)) (.emptyOutput (.var 0))))) :=
  Step.cutRight _ _ (Step.commChoice .bot (.var 0) _ _ _)

/-- Unconditioned associativity relates the counterexample to its
reassociated form (this is the step the guarded `Cong.assoc` refuses). -/
theorem assoc_counterexample_bare :
    CongBare assocCounterexample
      (.cut (.oplus .bot .bot)
        (.selectLeft (.var 0) (.emptyChoice (.const 0)))
        (.cut .bot (.choice (.var 1) (.emptyOutput (.var 1)) (.emptyOutput (.var 1)))
          (.emptyOutput (.var 0)))) :=
  CongBare.assocBare (.oplus .bot .bot) .bot (.selectLeft (.var 0) (.emptyChoice (.const 0)))
    (.choice (.var 0) (.emptyOutput (.var 0)) (.emptyOutput (.var 0))) (.emptyOutput (.var 0))

/-- The untypable core of the counterexample's reduct: an empty output on an
outer channel cut at `⊥` against an empty output is typable in no context. -/
private theorem bot_cut_outer_core_not_typed (C : Context TestAtom) :
    ¬ HasType C (.cut .bot (.emptyOutput (.var 1)) (.emptyOutput (.var 0))) := by
  intro h
  cases h with
  | @cut G D a p q hp hq hdisj =>
    generalize hc : (G.lift).insert (PiCalculus.Name.var 0) Logic.CLL.Proposition.bot = c at hp
    cases hp with
    | one =>
      have hm : PiCalculus.Name.var 0 ∈ (G.lift).insert (PiCalculus.Name.var 0)
          (Logic.CLL.Proposition.bot : Logic.CLL.Proposition TestAtom) :=
        Finmap.mem_insert.mpr (Or.inl rfl)
      rw [hc] at hm
      revert hm
      decide

/-- The `κ&` reduct of the counterexample is not typable: with the typed
counterexample and its `κ&` step, preservation would fail for the
relation closed under unconditioned associativity. -/
theorem assoc_counterexample_reduct_not_typed (Γ : Context TestAtom) :
    ¬ HasType Γ (.cut (.oplus .bot .bot)
        (.selectLeft (.var 0) (.emptyChoice (.const 0)))
        (.choice (.var 0)
          (.cut .bot (.emptyOutput (.var 1)) (.emptyOutput (.var 0)))
          (.cut .bot (.emptyOutput (.var 1)) (.emptyOutput (.var 0))))) := by
  intro h
  cases h with
  | @cut G D a p q hp hq hdisj =>
    generalize hc : (D.lift).insert (PiCalculus.Name.var 0)
      (Logic.CLL.Proposition.oplus Logic.CLL.Proposition.bot Logic.CLL.Proposition.bot).dual = c
      at hq
    cases hq with
    | «with» hb _ _ => exact bot_cut_outer_core_not_typed _ hb

/-- Guarded associativity still excludes the counterexample: its middle
component neither uses the outer cut channel nor absorbs, and no
structural equivalence relates the typed counterexample to its bare
image, which steps to an untypable process. -/
theorem assoc_counterexample_excluded :
    ¬ (PiCalculus.Name.var 1 ∈
        (Proc.choice (.var 0) (.emptyOutput (.var 0)) (.emptyOutput (.var 0)) :
          Proc TestAtom).freeNames ∨
      (Proc.choice (.var 0) (.emptyOutput (.var 0)) (.emptyOutput (.var 0)) :
          Proc TestAtom).absorbs = true) ∧
    ¬ Cong assocCounterexample
        (.cut (.oplus .bot .bot)
          (.selectLeft (.var 0) (.emptyChoice (.const 0)))
          (.cut .bot (.choice (.var 1) (.emptyOutput (.var 1)) (.emptyOutput (.var 1)))
            (.emptyOutput (.var 0)))) := by
  refine ⟨by decide, fun h => ?_⟩
  exact assoc_counterexample_reduct_not_typed _
    (HasType.preservation (h.hasType_iff.mp assoc_counterexample_typed)
      assoc_counterexample_steps)

/-- A `⊤` middle component owning both cut channels admits associativity:
both sides of this instance are typed by the same `⊤` channel. -/
theorem cong_assoc_top_owned :
    Cong (Atom := TestAtom)
      (.cut .bot (.cut .one ((.emptyOutput (.var 0) : Proc TestAtom).liftAt 1)
          (.emptyChoice (.const 0)))
        (.emptyOutput (.var 0)))
      (.cut .one (.emptyOutput (.var 0))
        (.cut .bot ((.emptyChoice (.const 0) : Proc TestAtom).rename (PiCalculus.swapNameAt 0))
          ((.emptyOutput (.var 0) : Proc TestAtom).liftAt 1))) :=
  Cong.assoc _ _ _ _ _ (Or.inr rfl) (Or.inr rfl)

/-- Absorption needs `⊤` on every branch of a choice: with one `⊤` branch
and one `1` branch the choice does not absorb, and it cannot take on an
extra unused channel. -/
theorem choice_one_top_branch_not_absorbs :
    (Proc.choice (.var 0) (.emptyChoice (.var 0)) (.emptyOutput (.var 0)) :
        Proc TestAtom).absorbs = false ∧
    ¬ HasType
        (((∅ : Context TestAtom).insert (.var 0) (.«with» .top .one)).insert (.const 0) .bot)
        (.choice (.var 0) (.emptyChoice (.var 0)) (.emptyOutput (.var 0))) := by
  refine ⟨by decide, fun h => ?_⟩
  have h₀ : HasType ((∅ : Context TestAtom).insert (.var 0) (.«with» .top .one))
      (.choice (.var 0) (.emptyChoice (.var 0)) (.emptyOutput (.var 0))) :=
    HasType.«with» (HasType.top Finmap.notMem_empty) HasType.one Finmap.notMem_empty
  have habs := (h₀.insert_iff_absorbs (k := .const 0) (by decide) (by decide) .bot).mp h
  exact absurd habs (by decide)

/-- An empty-output process cut against an empty output at `⊥`, with the
first component depending on an outer channel, is not typable: this is
the untypable core of the counterexample's reduct. -/
theorem outer_dependent_unit_cut_not_typed (Γ : Context TestAtom) :
    ¬ HasType Γ (.cut .bot (.emptyOutput (.var 1)) (.emptyOutput (.var 0))) :=
  bot_cut_outer_core_not_typed Γ

end ReductionTests

end Cslib.ClassicalProcesses
