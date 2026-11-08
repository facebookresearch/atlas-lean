/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Halting sets of multi-stack (TM2) machines are the r.e. sets
-/
module

public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
public import MathlibExt.Computability.TuringMachine.Recursive.ToTM2
public import Mathlib.Computability.RE

/-!
# Halting sets of multi-stack (TM2) machines are the r.e. sets

The partial counterpart of the Turing–Kleene equivalence. A predicate `p : ℕ → Prop` is
recursively enumerable (`REPred p`) iff some `FinTM2` halts exactly on the inputs
`encodeNat n` with `p n`.

* `rePred_tm2HaltsOn` : the halting set of any `FinTM2` is r.e. The proof runs the coded
  simulation of `OfTM2` until the first halted configuration.
* `exists_tm2HaltsOn_iff_of_rePred` : every r.e. predicate is the halting set of a
  `FinTM2`. The machine is `fwdTM c` from `ToTM2` for a code `c` whose evaluation is defined
  exactly on `p`. The wrapped machine follows `tr` step for step, so it halts iff `tr` does.

## Main results

- `TM2HaltsOn` : a `FinTM2` halts on an input word.
- `dom_eval_iff_exists_iterate` : a run halts iff some iterate is a configuration without a
  successor.
- `rePred_tm2HaltsOn`, `exists_tm2HaltsOn_iff_of_rePred` (and
  `exists_finite_tm2HaltsOn_iff_of_rePred`, with finite stack alphabets), and together
  `rePred_iff_exists_tm2HaltsOn`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt.TM2Recursive

open Turing

/-- A bundled multi-stack machine (`FinTM2`) halts when started on the input word `l`. -/
def TM2HaltsOn (tm : FinTM2) (l : List (tm.Γ tm.k₀)) : Prop :=
  (StateTransition.eval tm.step (initList tm l)).Dom

/-! ### Runs of a deterministic step function -/

section Runs

variable {σ : Type*} {f : σ → Option σ}

theorem reaches_of_iterate_eq_some {a b : σ} :
    ∀ {k : ℕ}, (flip bind f)^[k] (some a) = some b → StateTransition.Reaches f a b
  | 0, h => by
    obtain rfl := Option.some.inj h
    exact Relation.ReflTransGen.refl
  | k + 1, h => by
    rw [Function.iterate_succ_apply'] at h
    cases hk : (flip bind f)^[k] (some a) with
    | none => rw [hk] at h; cases h
    | some c =>
      rw [hk] at h
      exact (reaches_of_iterate_eq_some hk).tail h

/-- A run that reaches `none` passes through a configuration without a successor. -/
theorem exists_iterate_eq_some_of_eq_none {a : σ} :
    ∀ {k : ℕ}, (flip bind f)^[k] (some a) = none →
      ∃ j b, (flip bind f)^[j] (some a) = some b ∧ f b = none
  | 0, h => by cases h
  | k + 1, h => by
    rw [Function.iterate_succ_apply'] at h
    cases hk : (flip bind f)^[k] (some a) with
    | none => exact exists_iterate_eq_some_of_eq_none hk
    | some c =>
      rw [hk] at h
      exact ⟨k, c, hk, h⟩

/-- A run halts iff some iterate is a configuration without a successor. -/
theorem dom_eval_iff_exists_iterate {a : σ} :
    (StateTransition.eval f a).Dom ↔ ∃ k b, (flip bind f)^[k] (some a) = some b ∧ f b = none := by
  constructor
  · intro h
    obtain ⟨hr, hb⟩ := StateTransition.mem_eval.mp (Part.get_mem h)
    obtain ⟨k, hk⟩ := exists_iterate_eq_of_reaches hr
    exact ⟨k, _, hk, hb⟩
  · rintro ⟨k, b, hk, hb⟩
    exact Part.dom_iff_mem.mpr ⟨b, StateTransition.mem_eval.mpr ⟨reaches_of_iterate_eq_some hk, hb⟩⟩

theorem iterate_none_eq (m : ℕ) : (flip bind f)^[m] none = none := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply]; exact ih

/-- After a configuration without a successor, the run is `none`. -/
theorem iterate_eq_none_of_lt {a b : σ} {k : ℕ} (hk : (flip bind f)^[k] (some a) = some b)
    (hb : f b = none) {m : ℕ} (hm : k < m) : (flip bind f)^[m] (some a) = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [show k + d + 1 = d + (k + 1) by omega, Function.iterate_add_apply,
    Function.iterate_succ_apply', hk]
  exact (congrArg _ hb).trans (iterate_none_eq d)

end Runs

theorem step_eq_none_iff {tm : FinTM2} (c : tm.Cfg) : tm.step c = none ↔ c.l = none := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  | some l => simp [FinTM2.step, TM2.step]

/-! ### Halting sets are r.e. -/

attribute [local instance] FinTM2.kFin FinTM2.ΛFin FinTM2.σFin FinTM2.Γk₀Fin primcodableArrow
  primcodableΛ primcodableσ

/-- **The halting set of a multi-stack machine (`FinTM2`) is r.e.** -/
theorem rePred_tm2HaltsOn (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool) :
    REPred fun n ↦ TM2HaltsOn tm ((Computability.encodeNat n).map e.symm) := by
  let initC : ℕ → CodedCfg tm := fun n ↦ (some tm.main, tm.initialState,
    Function.update (fun _ ↦ []) tm.k₀
      ((Computability.encodeNat n).map fun b ↦ code tm tm.k₀ (e.symm b)))
  let halted : Option (CodedCfg tm) → Bool := fun o ↦ o.elim true fun c ↦ c.1.isNone
  have hinitP : Primrec fun n ↦ some (initC n) := by
    refine Primrec.option_some.comp (Primrec.pair (Primrec.const _) (Primrec.pair
      (Primrec.const _) ((primrec_arrow_update tm.k₀).comp (Primrec.const _) ?_)))
    exact Primrec.list_map primrec_encodeNat
      ((Primrec.dom_finite fun b : Bool ↦ code tm tm.k₀ (e.symm b)).comp Primrec.snd).to₂
  have hhaltedP : Primrec halted :=
    (Primrec.option_casesOn Primrec.id (Primrec.const true)
      ((Primrec.dom_finite fun l : Option tm.Λ ↦ l.isNone).comp
        (Primrec.fst.comp Primrec.snd)).to₂).of_eq fun o ↦ by cases o <;> rfl
  have hrun := partrec_run hinitP (primrec_optStepC tm) hhaltedP (Primrec.const 0)
  refine hrun.dom_re.of_eq fun n ↦ ?_
  let input := (Computability.encodeNat n).map e.symm
  have hinit : enc tm (initList tm input) = initC n := by
    simp only [enc, initC, encStk_initList, input, List.map_map]
    rfl
  have hiter : ∀ k, (optStepC tm)^[k] (some (initC n)) =
      ((flip bind tm.step)^[k] (some (initList tm input))).map (enc tm) := fun k ↦ by
    have := (optStepC_iterate tm k (o := some (initList tm input)) fun c hc ↦ by
      obtain rfl := Option.mem_some_iff.mp hc
      exact relevant_initList tm input).1
    rwa [Option.map_some, hinit] at this
  have hhalt : ∀ k, halted ((optStepC tm)^[k] (some (initC n))) = true ↔
      (flip bind tm.step)^[k] (some (initList tm input)) = none ∨
        ∃ c, (flip bind tm.step)^[k] (some (initList tm input)) = some c ∧ tm.step c = none :=
    fun k ↦ by
      rw [hiter k]
      cases (flip bind tm.step)^[k] (some (initList tm input)) with
      | none => simp [halted]
      | some c =>
        simp only [halted, enc, Option.map_some, Option.elim_some, Option.isNone_iff_eq_none,
          reduceCtorEq, false_or, Option.some.injEq, exists_eq_left']
        exact (step_eq_none_iff c).symm
  rw [Part.map_Dom, TM2HaltsOn, dom_eval_iff_exists_iterate]
  refine Nat.rfind_dom.trans ?_
  simp only [Part.mem_some_iff, Part.some_dom, implies_true, and_true]
  constructor
  · rintro ⟨k, hk⟩
    rcases (hhalt k).mp hk.symm with h | ⟨c, hc, hstep⟩
    · exact exists_iterate_eq_some_of_eq_none h
    · exact ⟨k, c, hc, hstep⟩
  · rintro ⟨k, c, hc, hstep⟩
    exact ⟨k, ((hhalt k).mpr (Or.inr ⟨c, hc, hstep⟩)).symm⟩

/-! ### R.e. sets are halting sets -/

section Wrapped

open PartrecToTM2 ToPartrec

variable (c : Code)

/-- The wrapped machine `fwdTM c` halts on `n` iff the code `c` is defined on `[n]`, when `c`
has singleton outputs on `[n]`. -/
theorem tm2HaltsOn_fwdTM_iff (n : ℕ) (hc : ∀ v ∈ c.eval [n], ∃ m, v = [m]) :
    TM2HaltsOn (fwdTM c) ((Computability.encodeNat n).map (Equiv.refl Bool).symm) ↔
      (c.eval [n]).Dom := by
  have hinit : initList (fwdTM c) ((Computability.encodeNat n).map (Equiv.refl Bool).symm) =
      (⟨some (Sum.inl Phase.pre0), none,
        mkStk [] [] [] [] (Computability.encodeNat n) []⟩ : FCfg c) := by
    simp only [initList]
    congr 1
    funext k
    rcases k with (_ | _ | _ | _) | (_ | _)
    all_goals first
      | rfl
      | (simp only [fwdTM, mkStk, Equiv.refl, ↓reduceDIte]
         change List.map (id : Bool → Bool) _ = _
         exact List.map_id _)
  set P := (Computability.encodeNat n).length + 1 + ((Computability.encodeNat n).length + 1) + 1
  let d₀ : FCfg c := ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
    mkStk (trList [n]) [] [] [] [] []⟩
  have hpre : frun c P (some (initList (fwdTM c)
      ((Computability.encodeNat n).map (Equiv.refl Bool).symm))) = some d₀ := by
    rw [hinit, pre_phase, ← trList_singleton]
  have h₀ : TrRel c (init c [n]) d₀ := ⟨rfl, rfl, start_mem c, rfl⟩
  have heval := tr_eval c [n]
  have hdom : (StateTransition.eval (TM2.step tr) (init c [n])).Dom ↔ (c.eval [n]).Dom := by
    rw [heval]
    simp
  rw [← hdom, TM2HaltsOn, dom_eval_iff_exists_iterate]
  constructor
  · rintro ⟨K, b, hK, hb⟩
    by_contra hnot
    cases hx : (flip bind (TM2.step tr))^[K + 1] (some (init c [n])) with
    | none => exact hnot (dom_eval_iff_exists_iterate.mpr (exists_iterate_eq_some_of_eq_none hx))
    | some x =>
      obtain ⟨d, hd, -⟩ := run_rel c h₀ (K + 1) hx
      have hnone := iterate_eq_none_of_lt hK hb (m := K + 1 + P) (by omega)
      have hsome : frun c (K + 1 + P) (some (initList (fwdTM c)
          ((Computability.encodeNat n).map (Equiv.refl Bool).symm))) = some d := by
        rw [frun_add, hpre, hd]
      exact absurd (hnone.symm.trans hsome) (by simp)
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp ((hdom.mp h))
    obtain ⟨m, rfl⟩ := hc v hv
    have hmem : halt [m] ∈ StateTransition.eval (TM2.step tr) (init c [n]) := by
      rw [heval]
      exact Part.mem_map _ hv
    obtain ⟨N, hN⟩ := exists_iterate_eq_of_reaches (StateTransition.mem_eval.mp hmem).1
    obtain ⟨⟨dl, dv, ds⟩, hd, hdv, hds, hdl⟩ := run_rel c h₀ N hN
    simp only [halt] at hdv hds hdl
    simp only [LabelRel] at hdl
    subst hdv hds hdl
    have hpost := post_phase c (Computability.encodeNat m)
    rw [← trList_singleton] at hpost
    refine ⟨(Computability.encodeNat m).length + 1 + ((Computability.encodeNat m).length + 1) +
      (N + P), ⟨none, none, mkStk [] [] [] [] [] (Computability.encodeNat m)⟩, ?_, rfl⟩
    have hfin : frun c ((Computability.encodeNat m).length + 1 +
        ((Computability.encodeNat m).length + 1) + (N + P)) (some (initList (fwdTM c)
          ((Computability.encodeNat n).map (Equiv.refl Bool).symm))) =
        some ⟨none, none, mkStk [] [] [] [] [] (Computability.encodeNat m)⟩ := by
      rw [frun_add c ((Computability.encodeNat m).length + 1 +
        ((Computability.encodeNat m).length + 1)), frun_add c N P, hpre, hd]
      exact hpost
    exact hfin

end Wrapped

/-- **Every r.e. predicate is the halting set of a multi-stack machine (`FinTM2`)** whose stack
alphabets are all finite. -/
theorem exists_finite_tm2HaltsOn_iff_of_rePred {p : ℕ → Prop} (hp : REPred p) :
    ∃ (tm : FinTM2) (_ : ∀ k, Finite (tm.Γ k)) (e : tm.Γ tm.k₀ ≃ Bool),
      ∀ n, p n ↔ TM2HaltsOn tm ((Computability.encodeNat n).map e.symm) := by
  have hg : Partrec fun n ↦ (Part.assert (p n) fun _ ↦ Part.some ()).map fun _ ↦ (0 : ℕ) :=
    Partrec.map hp (Computable.const 0).to₂
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.part_iff₁.mpr hg)
  have hfin : ∀ k, Finite ((fwdTM c).Γ k) := fun k ↦ by
    rcases k with k | k
    · exact inferInstanceAs (Finite Turing.PartrecToTM2.Γ')
    · exact inferInstanceAs (Finite Bool)
  refine ⟨fwdTM c, hfin, Equiv.refl Bool, fun n ↦ ?_⟩
  have hcn : c.eval [n] = (Part.assert (p n) fun _ ↦ Part.some ()).map fun _ ↦ [0] := by
    have := hc ⟨[n], rfl⟩
    simp only [Part.map_eq_map, Part.map_map] at this
    exact this
  refine Iff.trans ?_ (tm2HaltsOn_fwdTM_iff c n fun v hv ↦ ⟨0, ?_⟩).symm
  · rw [hcn, Part.map_Dom]
    exact ⟨fun h ↦ ⟨h, trivial⟩, fun h ↦ h.1⟩
  · rw [hcn] at hv
    obtain ⟨_, -, rfl⟩ := Part.mem_map_iff _ |>.mp hv
    rfl

/-- **Every r.e. predicate is the halting set of a multi-stack machine (`FinTM2`).** -/
theorem exists_tm2HaltsOn_iff_of_rePred {p : ℕ → Prop} (hp : REPred p) :
    ∃ (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool),
      ∀ n, p n ↔ TM2HaltsOn tm ((Computability.encodeNat n).map e.symm) :=
  let ⟨tm, _, e, h⟩ := exists_finite_tm2HaltsOn_iff_of_rePred hp
  ⟨tm, e, h⟩

/-- **R.e. equals halting set of a multi-stack machine (`FinTM2`).** -/
theorem rePred_iff_exists_tm2HaltsOn {p : ℕ → Prop} :
    REPred p ↔ ∃ (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool),
      ∀ n, p n ↔ TM2HaltsOn tm ((Computability.encodeNat n).map e.symm) :=
  ⟨exists_tm2HaltsOn_iff_of_rePred, fun ⟨tm, e, h⟩ ↦
    (rePred_tm2HaltsOn tm e).of_eq fun n ↦ (h n).symm⟩

end MetaMathlibExt.TM2Recursive
