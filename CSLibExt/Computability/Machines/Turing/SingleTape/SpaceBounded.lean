/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Machines.Turing.SingleTape.Bridge
import Mathlib.Tactic.Ring

/-!
# Space-bounded single-tape machines and linear bounded automata

A single-tape machine `tm` runs in space `s` (`SingleTapeTM.SpaceBoundedBy tm s`) when every
configuration of its run on an input `l` uses at most `s l.length` cells. Space is CSLib's
`SingleTapeTM.Cfg.spaceUsed`: the head cell together with the cells to its left and right up to
the last non-blank cell on each side (a `StackTape` drops trailing blanks). A **linear bounded
automaton** (`SingleTapeTM.IsLBA`) runs in space `n + 1` on inputs of length `n`.

A configuration is a state, the symbol under the head and the two tape halves around the head, so
there are finitely many configurations of bounded space: at most `cfgBound k` use at most `k`
cells (`SingleTapeTM.encard_le_cfgBound`; Sipser's Lemma 5.8 counts them exactly; CSLib's
`MultiTape/ConfigBound.lean` counts multi-tape configurations of bounded storage the same way). A
reachable configuration is reached by a path no longer than the number of reachable
configurations (CSLib's `Relation.ReflTransGen.relatesInSteps_lt_encard`), so a machine running in
space `s` halts on `l` within `cfgBound (s l.length)` steps if it halts at all; and because a run
is deterministic, iterating the step that many times finds the halting configuration. Running
the coded step of `ToRecursive` that many steps decides halting: the halting set of a machine
running in computable space is computable, and in particular that of a linear bounded automaton.
This is a fixed-machine halting analogue of Sipser's Theorem 5.9 (see below for what differs).

Sipser's LBA keeps its head on the input, between two endmarkers. Here the blank cells next to the
input play the endmarkers: a machine whose head stays on the input or on these two cells, and that
writes non-blank symbols only on the input, uses at most `n + 1` cells (one cell on the empty
input), so it is an `IsLBA`. A machine that, on a blank cell, writes a blank and does not move is
of this kind (`SingleTapeTM.isLBA_of_stays_on_blank`). `IsLBA` is more permissive, since it only
bounds, at each moment, the window holding the head and the non-blank cells: such a machine may,
for instance, shift its input along the tape. Decidability holds for this larger class.

Sipser's Theorem 5.9 differs in two ways. It is uniform in the machine (the language `A_LBA` of
pairs of an LBA and an input), while here the machine is fixed, because the uniform version needs
a code type for CSLib machines, which CSLib does not have. And it decides *acceptance*, while
CSLib's deterministic machines have no accepting states and this file decides *halting*;
acceptance in the sense of a decider (halting with a given output, `SingleTapeTM.Outputs`) is not
stated here.

## Main definitions

- `Cslib.Turing.SingleTapeTM.SpaceBoundedBy`, `Cslib.Turing.SingleTapeTM.IsLBA`.
- `Cslib.Turing.SingleTapeTM.cfgBound`: a bound on the number of configurations of bounded space.

## Main results

- `Cslib.Turing.SingleTapeTM.isLBA_of_stays_on_blank`: a machine that, on a blank cell, writes a
  blank and does not move is a linear bounded automaton.
- `Cslib.Turing.SingleTapeTM.encard_le_cfgBound`: finitely many configurations of bounded space.
- `Cslib.Turing.SingleTapeTM.SpaceBoundedBy.exists_halted_relatesWithinSteps`: a machine running in
  space `s` that halts on `l` halts within `cfgBound (s l.length)` steps.
- `Cslib.Turing.SingleTapeTM.SpaceBoundedBy.computablePred_haltsOn`: halting of a machine running
  in computable space is computable.
- `Cslib.Turing.SingleTapeTM.IsLBA.computablePred_haltsOn`,
  `Cslib.Turing.SingleTapeTM.IsLBA.computablePred_haltsOn_encodeNat`,
  `Cslib.Turing.SingleTapeTM.IsLBA.singleTapeDecidable_haltsOn_encodeNat`: halting of a linear
  bounded automaton is decidable (a fixed-machine halting analogue of Sipser, Theorem 5.9).

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §5.1:
  the definition of linear bounded automata, Lemma 5.8, and (for the analogue proved here)
  Theorem 5.9.
-/

@[expose] public section

set_option autoImplicit false

open Relation Computability Encodable MetaMathlibExt.TM2Recursive

namespace Cslib.Turing.SingleTapeTM

variable {Symbol : Type} [Inhabited Symbol] [Fintype Symbol] (tm : SingleTapeTM Symbol)

/-! ### Space bounds -/

/-- **Space-bounded single-tape machines.** Let $s : \mathbb{N} \to \mathbb{N}$. A single-tape
Turing machine $M$ runs in space $s$ when, for every input word $l$ of length $|l|$, every
configuration reachable from the initial configuration of $M$ on $l$ uses at most $s(|l|)$
cells, whether or not the run halts. The cells used by a configuration are the head cell
together with the cells on each side of it up to the outermost non-blank cell. -/
def SpaceBoundedBy (s : ℕ → ℕ) : Prop :=
  ∀ (l : List Symbol) (c : tm.Cfg), ReflTransGen tm.TransitionRelation (tm.initCfg l) c →
    c.spaceUsed ≤ s l.length

/-- **Linear bounded automaton.** A single-tape machine is a linear bounded automaton when it runs
in space $n + 1$ on inputs of length $n$: every configuration of its run on an input of length $n$
uses at most $n + 1$ cells, whether or not the run halts.

The input itself uses $\max(1, n)$ cells, and the extra cell lets the head step onto a blank cell
next to the input, the analogue of Sipser's endmarkers. With the bound $n$ instead, no machine
would qualify, since the empty input already uses one cell. -/
def IsLBA : Prop :=
  tm.SpaceBoundedBy (· + 1)

variable {tm}

/-- **Space bounds can be weakened.** If a single-tape machine runs in space
$s : \mathbb{N} \to \mathbb{N}$ and $s' : \mathbb{N} \to \mathbb{N}$ satisfies $s(n) \le s'(n)$ for
every $n \in \mathbb{N}$, then it runs in space $s'$. -/
theorem SpaceBoundedBy.mono {s s' : ℕ → ℕ} (h : tm.SpaceBoundedBy s) (hs : ∀ n, s n ≤ s' n) :
    tm.SpaceBoundedBy s' :=
  fun l c hc ↦ (h l c hc).trans (hs _)

/-- **A space bound is at least the space of the input.** If a single-tape machine runs in space
$s : \mathbb{N} \to \mathbb{N}$, then $\max(1, n) \le s(n)$ for the length $n$ of every input word,
since the initial configuration on an input of length $n$ uses $\max(1, n)$ cells. -/
theorem SpaceBoundedBy.max_one_le {s : ℕ → ℕ} (h : tm.SpaceBoundedBy s) (l : List Symbol) :
    max 1 l.length ≤ s l.length :=
  Cfg.spaceUsed_initCfg tm l ▸ h l _ .refl

/-! ### A criterion for linear bounded automata -/

omit [Inhabited Symbol] [Fintype Symbol] in
/-- A `StackTape` with a non-blank first cell is not empty. -/
private theorem one_le_length_of_head_ne_none {s : StackTape Symbol} (h : s.head ≠ none) :
    1 ≤ s.length := by
  obtain ⟨_ | ⟨x, l⟩, hl⟩ := s
  · exact absurd rfl h
  · simp [StackTape.length]

/-- The space invariant of a machine that, on a blank cell, writes a blank and does not move, on
an input of length `n`: at most `a` cells to the left and `b` cells to the right of the head may
be non-blank, with `a + b ≤ n`, and `a + b + 1 ≤ n` when the head is on a non-blank cell. -/
private def SpaceInv (n : ℕ) (t : BiTape Symbol) : Prop :=
  ∃ a b : ℕ, a + b ≤ n ∧ (t.head ≠ none → a + b + 1 ≤ n) ∧ t.left.length ≤ a ∧
    t.right.length ≤ b

omit [Inhabited Symbol] [Fintype Symbol] in
/-- The input tape satisfies the space invariant. -/
private theorem spaceInv_mk₁ (l : List Symbol) : SpaceInv l.length (BiTape.mk₁ l) := by
  cases l with
  | nil => exact ⟨0, 0, le_rfl, fun h ↦ absurd rfl h, le_rfl, le_rfl⟩
  | cons x r =>
    refine ⟨0, r.length, by simp, fun _ ↦ by simp, by simp [BiTape.mk₁], ?_⟩
    simp [BiTape.mk₁]

/-- A step of a machine that, on a blank cell, writes a blank and does not move keeps the space
invariant. -/
private theorem spaceInv_step (hM : ∀ q, (tm.tr q none).1 = ⟨none, none⟩) {n : ℕ}
    {c c' : tm.Cfg} (hc : SpaceInv n c.BiTape) (h : tm.TransitionRelation c c') :
    SpaceInv n c'.BiTape := by
  obtain ⟨_ | q, t⟩ := c
  · cases h
  rw [TransitionRelation, step_some] at h
  obtain rfl := Option.some_injective _ h
  obtain ⟨a, b, hab, hhead, hl, hr⟩ := hc
  dsimp only at hhead hl hr ⊢
  generalize hs : (tm.tr q t.head).1 = s
  rcases ht : t.head with _ | x
  · rw [ht, hM q] at hs
    rw [← hs, ← ht]
    exact ⟨a, b, hab, hhead, hl, hr⟩
  have hab1 := hhead (by simp [ht])
  simp only [StackTape.length] at hl hr
  obtain ⟨w, _ | _ | _⟩ := s <;>
    dsimp only [BiTape.optionMove, BiTape.move, BiTape.moveLeft, BiTape.moveRight, BiTape.write]
  · exact ⟨a, b, hab, fun _ ↦ hab1, hl, hr⟩
  · refine ⟨a - 1, b + 1, by omega, fun h ↦ ?_, ?_, ?_⟩
    · have := one_le_length_of_head_ne_none h
      simp only [StackTape.length] at this
      omega
    · simp only [StackTape.length, StackTape.toList_tail, List.length_tail]
      omega
    · exact (StackTape.length_cons_le _ _).trans (by simpa [StackTape.length] using hr)
  · refine ⟨a + 1, b - 1, by omega, fun h ↦ ?_, ?_, ?_⟩
    · have := one_le_length_of_head_ne_none h
      simp only [StackTape.length] at this
      omega
    · exact (StackTape.length_cons_le _ _).trans (by simpa [StackTape.length] using hl)
    · simp only [StackTape.length, StackTape.toList_tail, List.length_tail]
      omega

/-- **A machine that, on a blank cell, writes a blank and does not move is a linear bounded
automaton.** Its head never leaves a blank cell, so it stays on the input or on the two blank
cells next to it, and it writes non-blank symbols only on the input. The machine may change state
on a blank cell, or halt there. -/
theorem isLBA_of_stays_on_blank (h : ∀ q, (tm.tr q none).1 = ⟨none, none⟩) : tm.IsLBA := by
  intro l c hc
  have hinv : SpaceInv l.length c.BiTape := by
    induction hc with
    | refl => exact spaceInv_mk₁ l
    | tail _ hs ih => exact spaceInv_step h ih hs
  obtain ⟨a, b, hab, -, hl, hr⟩ := hinv
  simp only [Cfg.spaceUsed, BiTape.spaceUsed]
  omega

variable (tm)

/-! ### Finitely many configurations of bounded space -/

/-- **Configuration bound.** For a single-tape machine with state set $Q$ over a finite alphabet
$\Sigma$ and $k \in \mathbb{N}$, the configuration bound at $k$ is the number
$(|Q| + 1)(|\Sigma| + 1)(|\Sigma| + 2)^{2k}$.

A configuration that uses at most $k$ cells is determined by a state or the halting state, the
symbol or blank under the head, and the first $k$ cells to either side of the head, each a symbol,
a blank, or past the last non-blank cell; so this number bounds how many such configurations
there are. -/
def cfgBound (k : ℕ) : ℕ :=
  (Fintype.card tm.State + 1) * (Fintype.card Symbol + 1) * (Fintype.card Symbol + 2) ^ (2 * k)

/-- **Configurations of bounded space are finitely many.** Let $M$ be a single-tape machine with
state set $Q$ over a finite alphabet $\Sigma$, where a configuration uses the cell under the head
and the cells on either side of it up to the last non-blank one. For every $k \in \mathbb{N}$, at
most $(|Q| + 1)(|\Sigma| + 1)(|\Sigma| + 2)^{2k}$ configurations of $M$ use at most $k$ cells. -/
theorem encard_le_cfgBound (k : ℕ) : {c : tm.Cfg | c.spaceUsed ≤ k}.encard ≤ tm.cfgBound k := by
  -- A configuration of space at most `k` is determined by its state, its head symbol, and the
  -- first `k` cells to either side of the head, read with `getElem?`.
  let enc : tm.Cfg → Option tm.State × Option Symbol × (Fin k → Option (Option Symbol)) ×
      (Fin k → Option (Option Symbol)) := fun c ↦
    (c.state, c.BiTape.head, fun i ↦ c.BiTape.left.toList[i]?, fun i ↦ c.BiTape.right.toList[i]?)
  have hlist {L L' : List (Option Symbol)} (hL : L.length ≤ k) (hL' : L'.length ≤ k)
      (h : (fun i : Fin k ↦ L[i]?) = fun i ↦ L'[i]?) : L = L' := by
    refine List.ext_getElem? fun i ↦ ?_
    by_cases hi : i < k
    · exact congrFun h ⟨i, hi⟩
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have hinj : Set.InjOn enc {c | c.spaceUsed ≤ k} := by
    rintro ⟨q, h, ⟨L, hL⟩, ⟨R, hR⟩⟩ hc ⟨q', h', ⟨L', hL'⟩, ⟨R', hR'⟩⟩ hc' he
    simp only [enc, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, eL, eR⟩ := he
    simp only [Set.mem_ofPred_eq, Cfg.spaceUsed, BiTape.spaceUsed, StackTape.length] at hc hc'
    obtain rfl := hlist (by omega) (by omega) eL
    obtain rfl := hlist (by omega) (by omega) eR
    rfl
  refine (Set.encard_le_encard_of_injOn (Set.mapsTo_univ _ _) hinj).trans_eq ?_
  simp [cfgBound, two_mul, pow_add]
  ring

variable {tm}

/-! ### Pigeonhole -/

/-- **Space-bounded machines halt within the configuration bound.** Let $M$ be a single-tape
machine with state set $Q$ over a finite alphabet $\Sigma$ that runs in space
$s : \mathbb{N} \to \mathbb{N}$. If $M$ halts on an input word $w$ of length $n$, then from the
initial configuration on $w$ it reaches a configuration in the halting state in at most
$(|Q| + 1)(|\Sigma| + 1)(|\Sigma| + 2)^{2 s(n)}$ steps.

Its run visits only configurations of space at most $s(n)$, and does not repeat one before
halting. -/
theorem SpaceBoundedBy.exists_halted_relatesWithinSteps {s : ℕ → ℕ} (h : tm.SpaceBoundedBy s)
    {l : List Symbol} (hl : tm.HaltsOn l) :
    ∃ c : tm.Cfg, RelatesWithinSteps tm.TransitionRelation (tm.initCfg l) c
      (tm.cfgBound (s l.length)) ∧ c.state = none := by
  obtain ⟨c, hc, hstate⟩ := hl
  obtain ⟨n, hn, hlt⟩ := hc.relatesInSteps_lt_encard
  have hle : {x | ReflTransGen tm.TransitionRelation (tm.initCfg l) x}.encard ≤
      tm.cfgBound (s l.length) :=
    (Set.encard_le_encard fun x hx ↦ h l x hx).trans (tm.encard_le_cfgBound _)
  exact ⟨c, ⟨n, by exact_mod_cast (hlt.trans_le hle).le, hn⟩, hstate⟩

/-! ### Deciding halting -/

variable (tm)

/-- One step of `tm`, or no change on a halted configuration. -/
private def stepOrSelf (c : tm.Cfg) : tm.Cfg :=
  (tm.step c).getD c

/-- One coded step of `tm`, or no change on a halted code. -/
private def codedStepOrSelf (c : tm.CodedCfg) : tm.CodedCfg :=
  (tm.codedStep c).getD c

variable {tm}

/-- A run of `n` steps is `n` iterates of `stepOrSelf`. -/
private theorem iterate_stepOrSelf_of_relatesInSteps {a c : tm.Cfg} {n : ℕ}
    (h : RelatesInSteps tm.TransitionRelation a c n) : (stepOrSelf tm)^[n] a = c := by
  induction h with
  | refl => rfl
  | tail _ _ _ _ hstep ih =>
    rw [Function.iterate_succ_apply', ih, stepOrSelf, show tm.step _ = _ from hstep]
    rfl

/-- The iterates of `stepOrSelf` stay on the run. -/
private theorem reflTransGen_iterate_stepOrSelf (a : tm.Cfg) (n : ℕ) :
    ReflTransGen tm.TransitionRelation a ((stepOrSelf tm)^[n] a) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    generalize (stepOrSelf tm)^[n] a = x at ih ⊢
    rcases hs : tm.step x with _ | c
    · simpa only [stepOrSelf, hs, Option.getD_none] using ih
    · simpa only [stepOrSelf, hs, Option.getD_some] using ih.tail hs

/-- `stepOrSelf` fixes halted configurations. -/
private theorem stepOrSelf_of_state_eq_none {c : tm.Cfg} (h : c.state = none) :
    stepOrSelf tm c = c := by
  obtain ⟨_ | _, _⟩ := c
  · rfl
  · cases h

/-- Iterates of `stepOrSelf` on codes follow iterates of `stepOrSelf`. -/
private theorem toCodedCfg_iterate_stepOrSelf (n : ℕ) (c : tm.Cfg) :
    ((stepOrSelf tm)^[n] c).toCodedCfg = (codedStepOrSelf tm)^[n] c.toCodedCfg :=
  Function.Semiconj.iterate_right (f := Cfg.toCodedCfg) (fun c ↦ by
    simp only [stepOrSelf, codedStepOrSelf, codedStep_toCodedCfg, Option.getD_map]) n c

/-- A machine running in space `s` halts on `l` iff it has halted after
`cfgBound (s l.length)` iterates of `stepOrSelf`. -/
private theorem SpaceBoundedBy.haltsOn_iff_iterate {s : ℕ → ℕ} (h : tm.SpaceBoundedBy s)
    (l : List Symbol) :
    tm.HaltsOn l ↔ ((stepOrSelf tm)^[tm.cfgBound (s l.length)] (tm.initCfg l)).state = none := by
  refine ⟨fun hl ↦ ?_, fun hl ↦ ⟨_, reflTransGen_iterate_stepOrSelf _ _, hl⟩⟩
  obtain ⟨c, ⟨n, hn, hc⟩, hstate⟩ := h.exists_halted_relatesWithinSteps hl
  rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply, iterate_stepOrSelf_of_relatesInSteps hc,
    Function.iterate_fixed (stepOrSelf_of_state_eq_none hstate)]
  exact hstate

/-- **Halting of a machine running in computable space is computable.** Let $M$ be a single-tape
machine with state set $Q$ over a finite alphabet $\Sigma$, fix any primitive recursive coding of
$\Sigma$, and let $s : \mathbb{N} \to \mathbb{N}$ be computable. If $M$ runs in space $s$, then the
set of input words over $\Sigma$ on which $M$ halts is computable.

The decision procedure runs $M$ for $(|Q| + 1)(|\Sigma| + 1)(|\Sigma| + 2)^{2 s(n)}$ steps on an
input of length $n$ and checks whether it has halted. -/
theorem SpaceBoundedBy.computablePred_haltsOn [Primcodable Symbol] {s : ℕ → ℕ}
    (hs : Computable s) (h : tm.SpaceBoundedBy s) : ComputablePred tm.HaltsOn := by
  classical
  let _ : Primcodable tm.State := Primcodable.ofEquiv _ (Fintype.equivFin _)
  have hiter : Primrec fun p : ℕ × List Symbol ↦
      (codedStepOrSelf tm)^[p.1] (tm.initCfg p.2).toCodedCfg :=
    Primrec.nat_iterate Primrec.fst ((primrec_toCodedCfg_initCfg tm).comp Primrec.snd)
      ((Primrec.option_getD.comp (primrec_codedStep tm) Primrec.id).comp Primrec.snd).to₂
  have hbound : Primrec tm.cfgBound :=
    Primrec.nat_mul.comp (Primrec.const _) ((Primrec₂.unpaired'.1 Nat.Primrec.pow).comp
      (Primrec.const _) (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))
  have hhalt : Primrec fun c : tm.CodedCfg ↦ decide (c.1 = none) :=
    (Primrec.dom_finite fun o : Option tm.State ↦ decide (o = none)).comp Primrec.fst
  refine Computable.computablePred ((hhalt.to_comp.comp (hiter.to_comp.comp
    ((hbound.to_comp.comp (hs.comp Primrec.list_length.to_comp)).pair Computable.id))).of_eq
    fun l ↦ ?_)
  rw [← toCodedCfg_iterate_stepOrSelf]
  exact decide_eq_decide.mpr (h.haltsOn_iff_iterate l).symm

/-- **Halting of a linear bounded automaton is decidable.** Let $M$ be a single-tape machine over
a finite alphabet $\Sigma$, and fix any primitive recursive coding of $\Sigma$. If $M$ is a linear
bounded automaton, then the set of input words over $\Sigma$ on which $M$ halts is computable.

Source: Sipser, *Introduction to the Theory of Computation*, Theorem 5.9, of which this is a
fixed-machine halting analogue: Sipser decides acceptance uniformly over machine descriptions,
which needs a code type for CSLib machines. -/
theorem IsLBA.computablePred_haltsOn [Primcodable Symbol] (h : tm.IsLBA) :
    ComputablePred tm.HaltsOn :=
  SpaceBoundedBy.computablePred_haltsOn Primrec.succ.to_comp h

/-- **Halting of a linear bounded automaton on binary codes is decidable.** Let $M$ be a
single-tape machine over a finite alphabet $\Sigma$ that is a linear bounded automaton, let
$\alpha$ be a primitive recursively coded type, and let $\iota : \{0, 1\} \to \Sigma$ be any map.
For $a \in \alpha$, let $w_a$ be the word over $\Sigma$ obtained by applying $\iota$ to each bit of
the binary expansion, least significant bit first and without leading zeros, of the
natural-number code of $a$; so $w_a$ is empty when that code is $0$. Then the set of
$a \in \alpha$ such that $M$ halts on $w_a$ is computable. -/
theorem IsLBA.computablePred_haltsOn_encodeNat {α : Type*} [Primcodable α] (h : tm.IsLBA)
    (ι : Bool → Symbol) : ComputablePred fun a : α ↦ tm.HaltsOn ((encodeNat (encode a)).map ι) := by
  let _ : Primcodable Symbol := Primcodable.ofEquiv _ (Fintype.equivFin _)
  obtain ⟨_, hc⟩ := h.computablePred_haltsOn
  exact ⟨fun _ ↦ inferInstance, hc.comp (Primrec.list_map (primrec_encodeNat.comp Primrec.encode)
    ((Primrec.dom_finite ι).comp Primrec.snd).to₂).to_comp⟩

/-- **A single-tape machine decides the halting problem of a linear bounded automaton.** Let $M$
be a linear bounded automaton over a finite tape alphabet $\Sigma$, let $\iota$ be any map from
the Booleans to $\Sigma$, and let $\alpha$ be a primitively encodable type. For $a \in \alpha$, let
$w_a$ be the word obtained by writing, letter by letter through $\iota$, the binary expansion
(least significant bit first) of the natural-number code of $a$. Then the predicate on $\alpha$
that holds at $a$ exactly when $M$ halts on the input $w_a$ is decidable by a single-tape
machine. -/
theorem IsLBA.singleTapeDecidable_haltsOn_encodeNat {α : Type*} [Primcodable α] (h : tm.IsLBA)
    (ι : Bool → Symbol) :
    Decidability.SingleTapeDecidable fun a : α ↦ tm.HaltsOn ((encodeNat (encode a)).map ι) :=
  Decidability.singleTapeDecidable_iff_computablePred.mpr (h.computablePred_haltsOn_encodeNat ι)

end Cslib.Turing.SingleTapeTM
