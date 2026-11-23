/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Classes
public import CSLibExt.Computability.Circuit.Snoc

/-!
# Flat `ACGate` circuits as CSLib circuits

`Classes.lean` defines the circuit classes `AC0`, `AC0Mod` and `ACC0` (unbounded fan-in) and
`NCK` (fan-in at most two, `IsFanInLeTwo`) over one flat circuit model: a list
`C : List (ACGate n)` whose gate `j` is an input variable, a
constant, or a gate reading gates `< j` (`WellFormedCircuit`), evaluated by `circuitEval` and
measured by `circuitDepth`. The flat form exists for the serial encoding: `acGateToPair`
writes each gate as a `(kind, refs)` pair (a `mod` gate has no kind of its own and is written as
the always-false kind `5`), and the resulting `SerialCircuit` is what log-space uniformity
(`UniformCircuitFamily`) describes and what the Circuit Value and succinct-circuit problems
decode.

This file translates that model into CSLib's circuit model (`Cslib.Circuits.Circuit`):

* `acSignature` and `acInterpretation`: the `ACGate` basis (Boolean constants, NOT, and AND,
  OR and `mod m` gates of every arity) as a CSLib signature with its Boolean interpretation,
  which agrees with `gateValue`.
* `toCircuit C hC`: the CSLib circuit of a well-formed flat circuit, with one output per flat
  gate. A `var i` gate becomes the input wire `i`; every other gate becomes one CSLib gate.
* `ofFn_eval_toCircuit`: on every assignment `x`, the outputs of `toCircuit C hC` are the list
  `circuitEval C x`, so for a nonempty `C` its last output is the gate whose value `AC0`,
  `AC0Mod` and `NCK` read.
* `size_toCircuit`: one gate for each flat gate that is not a `var` gate, so at most `C.length`
  gates (`size_toCircuit_le`).
* Depth. The flat model gives `var` and `const` gates depth `0`; CSLib gives input wires depth
  `0` and every gate, constants included, depth at least `1` (`Line.depth_pos`). The recurrence
  `acCircuitDepths` is that of `circuitDepths` with depth `1` for `const` gates
  (`acGateDepthOf`). It gives the depth of every output exactly (`outputDepths_toCircuit`,
  `ofFn_outputDepths_toCircuit`), and its largest entry is the depth of the circuit
  (`depth_toCircuit`). Against the flat depths, each output is as deep as its flat gate or one
  level deeper (`getElem_circuitDepths_le_outputDepths_toCircuit`, `outputDepths_toCircuit_le`),
  and exactly as deep when `C` has no `const` gate (`outputDepths_toCircuit_eq`). Both circuit
  depths are maxima over all flat gates, since every flat gate is an output, so
  `circuitDepth C ≤ (toCircuit C hC).depth ≤ circuitDepth C + 1`
  (`circuitDepth_le_depth_toCircuit`, `depth_toCircuit_le`), with equality when `C` has no
  `const` gate (`depth_toCircuit_eq`). The one-gate circuit `[const true]` has flat depth `0` and
  CSLib depth `1`, so the upper bound is attained.

The class definitions are unchanged and stay on flat circuits.
-/

@[expose] public section

namespace Cslib.Complexity.Classes

open Cslib.Circuits

/-! ### The `ACGate` basis as a CSLib signature -/

/-- Operation symbols of the `ACGate` basis: Boolean constants, negation, and conjunction,
disjunction and `mod m` gates of every arity, arity zero included. -/
inductive ACOp where
  /-- A Boolean constant. -/
  | const (value : Bool)
  /-- Negation. -/
  | not
  /-- Conjunction of `arity` arguments. -/
  | and (arity : ℕ)
  /-- Disjunction of `arity` arguments. -/
  | or (arity : ℕ)
  /-- The `mod modulus` gate on `arity` arguments (see `acInterpretation`). -/
  | mod (modulus arity : ℕ)
  deriving DecidableEq, Repr

/-- The `ACGate` basis as a CSLib signature: a constant takes no argument, negation takes one,
and `and k`, `or k` and `mod m k` take `k`. -/
abbrev acSignature : Signature where
  Op := ACOp
  Arity
    | .const _ => 0
    | .not => 1
    | .and k => k
    | .or k => k
    | .mod _ k => k

/-- The Boolean meaning of the `ACGate` basis, as in `gateValue`: a constant outputs its value,
negation flips its argument, `and k` and `or k` are the conjunction and the disjunction of their
`k` arguments (`true` and `false` when `k = 0`), and `mod m k` outputs `true` exactly when
`m ≠ 0` and the number of `true` arguments is divisible by `m`. -/
def acInterpretation : Interpretation acSignature Bool
  | .const b, _ => b
  | .not, f => !f 0
  | .and _, f => (List.ofFn f).all id
  | .or _, f => (List.ofFn f).any id
  | .mod m _, f => if m = 0 then false else ((List.ofFn f).filter id).length % m = 0

/-! ### Translation -/

/-- Append one flat gate `g` to a CSLib circuit whose `k` outputs carry the first `k` gates of a
flat circuit, given that `g` references only those gates (`h`). A `var i` gate adds no CSLib
gate: its output is the input wire `i`. Every other gate adds one CSLib gate, which reads the
outputs named by its references and becomes the new last output. -/
def snocACGate {n k : ℕ} (c : Circuit acSignature n k) :
    (g : ACGate n) → (∀ a ∈ gateInputs g, a < k) → Circuit acSignature n (k + 1)
  | .var i, _ => ⟨c.program, Fin.snoc c.outputs (.input i)⟩
  | .const b, _ => c.snocLine ⟨.const b, Fin.elim0⟩
  | .notGate a, h => c.snocLine ⟨.not, fun _ => c.outputs ⟨a, h a (List.mem_singleton_self a)⟩⟩
  | .andGate l, h =>
      c.snocLine ⟨.and l.length,
        fun (i : Fin l.length) => c.outputs ⟨l[i], h _ (List.getElem_mem _)⟩⟩
  | .orGate l, h =>
      c.snocLine ⟨.or l.length,
        fun (i : Fin l.length) => c.outputs ⟨l[i], h _ (List.getElem_mem _)⟩⟩
  | .modGate m l, h =>
      c.snocLine ⟨.mod m l.length,
        fun (i : Fin l.length) => c.outputs ⟨l[i], h _ (List.getElem_mem _)⟩⟩

/-- The CSLib circuit of the first `k` gates of a well-formed flat circuit `C`, built gate by
gate with `snocACGate`: output `t` carries flat gate `t`. -/
def toCircuitUpTo {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    (k : ℕ) → k ≤ C.length → Circuit acSignature n k
  | 0, _ => ⟨.empty, Fin.elim0⟩
  | k + 1, hk => snocACGate (toCircuitUpTo C hC k (Nat.le_of_succ_le hk)) C[k] (hC k hk)

/-- The CSLib circuit of a well-formed flat circuit `C`, with one output per flat gate: output `t`
carries gate `t` (`eval_toCircuit`). Input gates `var i` become input wires and add no CSLib
gate (`size_toCircuit`). -/
def toCircuit {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    Circuit acSignature n C.length :=
  toCircuitUpTo C hC C.length le_rfl

/-! ### Flat evaluation and depth, one gate at a time -/

private theorem length_foldl_snoc {α β : Type*} (F : List α → β → α) (C : List β)
    (acc : List α) :
    (C.foldl (fun vs g => vs ++ [F vs g]) acc).length = acc.length + C.length := by
  induction C generalizing acc with
  | nil => simp
  | cons g C ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
      List.length_nil]; omega

/-- `circuitEval` has one value per gate. -/
@[simp] theorem length_circuitEval {n : ℕ} (C : List (ACGate n)) (x : Fin n → Bool) :
    (circuitEval C x).length = C.length := by
  simpa [circuitEval] using length_foldl_snoc (fun vs g => gateValue vs x g) C []

/-- `circuitDepths` has one depth per gate. -/
@[simp] theorem length_circuitDepths {n : ℕ} (C : List (ACGate n)) :
    (circuitDepths C).length = C.length := by
  simpa [circuitDepths] using length_foldl_snoc (fun ds (g : ACGate n) => gateDepthOf ds g) C []

/-- Evaluating one more gate appends its value, computed from the values of the earlier
gates. -/
theorem circuitEval_append_singleton {n : ℕ} (C : List (ACGate n)) (g : ACGate n)
    (x : Fin n → Bool) :
    circuitEval (C ++ [g]) x = circuitEval C x ++ [gateValue (circuitEval C x) x g] := by
  simp [circuitEval, List.foldl_append]

/-- Measuring one more gate appends its depth, computed from the depths of the earlier
gates. -/
theorem circuitDepths_append_singleton {n : ℕ} (C : List (ACGate n)) (g : ACGate n) :
    circuitDepths (C ++ [g]) = circuitDepths C ++ [gateDepthOf (circuitDepths C) g] := by
  simp [circuitDepths, List.foldl_append]

/-! ### Evaluation -/

/-- A constant gate outputs its value. -/
@[simp] theorem acInterpretation_const (b : Bool) (f : Fin 0 → Bool) :
    acInterpretation (.const b) f = b := rfl

/-- Negation flips its argument. -/
@[simp] theorem acInterpretation_not (f : Fin 1 → Bool) :
    acInterpretation .not f = !f 0 := rfl

/-- `and k` outputs `true` exactly when all `k` arguments are `true` (so `true` when
`k = 0`). -/
theorem acInterpretation_and (k : ℕ) (f : Fin k → Bool) :
    acInterpretation (.and k) f = decide (∀ i, f i = true) := by
  change (List.ofFn f).all id = _
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  simp [List.mem_ofFn]

/-- `or k` outputs `true` exactly when some argument is `true` (so `false` when `k = 0`). -/
theorem acInterpretation_or (k : ℕ) (f : Fin k → Bool) :
    acInterpretation (.or k) f = decide (∃ i, f i = true) := by
  change (List.ofFn f).any id = _
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_iff]
  simp [List.mem_ofFn]

/-- `mod m k` outputs `true` exactly when `m ≠ 0` and the number of `true` arguments is
divisible by `m`. -/
theorem acInterpretation_mod (m k : ℕ) (f : Fin k → Bool) :
    acInterpretation (.mod m k) f = (decide (m ≠ 0) && decide (m ∣ (List.ofFn f).count true)) := by
  by_cases hm : m = 0
  · simp [acInterpretation, hm]
  · simp only [acInterpretation, hm, ite_false, ne_eq, not_false_eq_true, decide_true,
      Bool.true_and, Nat.dvd_iff_mod_eq_zero, List.count_eq_length_filter]
    congr

/-- Appending a flat gate keeps the values of the earlier outputs. -/
theorem eval_snocACGate_castSucc {n k : ℕ} (c : Circuit acSignature n k) (g : ACGate n)
    (h : ∀ a ∈ gateInputs g, a < k) (x : Fin n → Bool) (t : Fin k) :
    (snocACGate c g h).eval acInterpretation x t.castSucc = c.eval acInterpretation x t := by
  cases g with
  | var i => simp [snocACGate, Circuit.eval]
  | _ => simp only [snocACGate, Circuit.eval_snocLine_castSucc]

/-- If output `t` of `c` carries `vs.getD t false` for every `t < k`, the new output of
`snocACGate c g h` carries `gateValue vs x g`. -/
theorem eval_snocACGate_last {n k : ℕ} (c : Circuit acSignature n k) (g : ACGate n)
    (h : ∀ a ∈ gateInputs g, a < k) (x : Fin n → Bool) (vs : List Bool)
    (hvs : ∀ t : Fin k, c.eval acInterpretation x t = vs.getD t false) :
    (snocACGate c g h).eval acInterpretation x (Fin.last k) = gateValue vs x g := by
  have hw : ∀ t : Fin k, Wire.elim x (c.program.eval acInterpretation x) (c.outputs t) =
      vs.getD t false := hvs
  cases g with
  | var i => simp [snocACGate, Circuit.eval, gateValue]
  | const b => simp [snocACGate, gateValue, Line.eval]
  | notGate a => simp [snocACGate, gateValue, Line.eval, hw]
  | andGate l =>
    have hl := List.ofFn_getElem_eq_map l (fun a => vs.getD a false)
    simp only [List.getD_eq_getElem?_getD] at hl
    simp [snocACGate, gateValue, Line.eval, acInterpretation,
      Function.comp_def, hw, hl, List.all_map]
  | orGate l =>
    have hl := List.ofFn_getElem_eq_map l (fun a => vs.getD a false)
    simp only [List.getD_eq_getElem?_getD] at hl
    simp [snocACGate, gateValue, Line.eval, acInterpretation,
      Function.comp_def, hw, hl, List.any_map]
  | modGate m l =>
    have hl := List.ofFn_getElem_eq_map l (fun a => vs.getD a false)
    simp only [List.getD_eq_getElem?_getD] at hl
    simp [snocACGate, gateValue, Line.eval, acInterpretation,
      Function.comp_def, hw, hl, List.filter_map]

private theorem eval_toCircuitUpTo_take {n : ℕ} (C : List (ACGate n))
    (hC : WellFormedCircuit C) (x : Fin n → Bool) :
    ∀ (k : ℕ) (hk : k ≤ C.length) (t : Fin k),
      (toCircuitUpTo C hC k hk).eval acInterpretation x t =
        (circuitEval (C.take k) x).getD t false
  | 0, _, t => t.elim0
  | k + 1, hk, t => by
    have hlen : (circuitEval (C.take k) x).length = k := by simp; omega
    have htake : C.take (k + 1) = C.take k ++ [C[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
    rw [toCircuitUpTo, htake, circuitEval_append_singleton]
    refine Fin.lastCases ?_ (fun s => ?_) t
    · rw [eval_snocACGate_last _ _ _ x _ (eval_toCircuitUpTo_take C hC x k _),
        List.getD_append_right _ _ _ _ (by simp [hlen])]
      simp [hlen]
    · rw [eval_snocACGate_castSucc, eval_toCircuitUpTo_take C hC x k _,
        List.getD_append _ _ _ _ (by simp [hlen])]
      simp

/-- Output `t` of the CSLib circuit of a well-formed flat circuit `C` is the value of flat gate
`t`. -/
theorem eval_toCircuit {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C)
    (x : Fin n → Bool) (t : Fin C.length) :
    (toCircuit C hC).eval acInterpretation x t = (circuitEval C x)[t] := by
  have h := eval_toCircuitUpTo_take C hC x C.length le_rfl t
  rw [List.take_of_length_le le_rfl] at h
  rw [toCircuit, h]
  exact List.getD_eq_getElem _ _ (by simp)

/-- Evaluating the CSLib circuit of a well-formed flat circuit gives exactly `circuitEval`. -/
theorem ofFn_eval_toCircuit {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C)
    (x : Fin n → Bool) :
    List.ofFn ((toCircuit C hC).eval acInterpretation x) = circuitEval C x := by
  apply List.ext_getElem (by simp)
  intro t h₁ h₂
  rw [List.getElem_ofFn]
  exact eval_toCircuit C hC x ⟨t, by simpa using h₁⟩

/-! ### Size -/

/-- Appending a flat gate adds at most one CSLib gate. -/
theorem size_snocACGate_le {n k : ℕ} (c : Circuit acSignature n k) (g : ACGate n)
    (h : ∀ a ∈ gateInputs g, a < k) : (snocACGate c g h).size ≤ c.size + 1 := by
  cases g with
  | var i => exact Nat.le_succ _
  | _ => simp only [snocACGate, Circuit.size_snocLine, le_refl]

private theorem size_toCircuitUpTo_le {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    ∀ (k : ℕ) (hk : k ≤ C.length), (toCircuitUpTo C hC k hk).size ≤ k
  | 0, _ => le_rfl
  | k + 1, hk => by
    rw [toCircuitUpTo]
    exact (size_snocACGate_le _ _ _).trans (Nat.succ_le_succ (size_toCircuitUpTo_le C hC k _))

/-- The CSLib circuit of a well-formed flat circuit has at most as many gates as the flat
circuit. -/
theorem size_toCircuit_le {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    (toCircuit C hC).size ≤ C.length :=
  size_toCircuitUpTo_le C hC C.length le_rfl

private theorem size_snocACGate {n k : ℕ} (c : Circuit acSignature n k) (g : ACGate n)
    (h : ∀ a ∈ gateInputs g, a < k) :
    (snocACGate c g h).size = c.size + [g].countP (fun x => match x with
      | .var _ => false
      | _ => true) := by
  cases g <;> rfl

private theorem size_toCircuitUpTo {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    ∀ (k : ℕ) (hk : k ≤ C.length), (toCircuitUpTo C hC k hk).size =
      (C.take k).countP (fun g => match g with
        | .var _ => false
        | _ => true)
  | 0, _ => rfl
  | k + 1, hk => by
    have htake : C.take (k + 1) = C.take k ++ [C[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
    rw [toCircuitUpTo, htake, List.countP_append, size_snocACGate, size_toCircuitUpTo C hC k]

/-- The CSLib circuit of a well-formed flat circuit has one gate for each flat gate that is not an
input gate `var i`. -/
theorem size_toCircuit {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    (toCircuit C hC).size = C.countP (fun g => match g with
      | .var _ => false
      | _ => true) := by
  have h := size_toCircuitUpTo C hC C.length le_rfl
  rwa [List.take_of_length_le le_rfl] at h

/-! ### Depth -/

private theorem foldr_max_le_iff (l : List ℕ) (D : ℕ) : l.foldr max 0 ≤ D ↔ ∀ a ∈ l, a ≤ D := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

private theorem le_foldr_max {l : List ℕ} {a : ℕ} (ha : a ∈ l) : a ≤ l.foldr max 0 :=
  (foldr_max_le_iff l _).mp le_rfl a ha

private theorem fin_foldl_max {m : ℕ} (F : Fin m → ℕ) (init : ℕ) :
    Fin.foldl m (fun d j => max d (F j)) init = max init ((List.ofFn F).foldr max 0) := by
  induction m generalizing init with
  | zero => simp
  | succ m ih => rw [Fin.foldl_succ, ih, List.ofFn_succ, List.foldr_cons, Nat.max_assoc]

private theorem line_depth_eq {σ : Signature} {n g : ℕ} (line : Line σ n g)
    (wd : Wire n g → ℕ) :
    line.depth wd = (List.ofFn fun j => wd (line.wires j)).foldr max 0 + 1 := by
  rw [Line.depth, fin_foldl_max, Nat.zero_max]

private theorem gateDepthOf_le_add {n : ℕ} (ds es : List ℕ) (g : ACGate n) (e : ℕ)
    (h : ∀ a ∈ gateInputs g, ds.getD a 0 ≤ es.getD a 0 + e) :
    gateDepthOf ds g ≤ gateDepthOf es g + e := by
  have hl : ∀ l : List ℕ, (∀ a ∈ l, ds.getD a 0 ≤ es.getD a 0 + e) →
      List.foldr max 0 (l.map fun a => ds.getD a 0) ≤
        List.foldr max 0 (l.map fun a => es.getD a 0) + e := by
    intro l hl
    rw [foldr_max_le_iff]
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact (hl a ha).trans
      (Nat.add_le_add_right (le_foldr_max (List.mem_map_of_mem (f := fun a => es.getD a 0) ha)) e)
  cases g with
  | var => simp [gateDepthOf]
  | const => simp [gateDepthOf]
  | notGate a =>
    have := h a (List.mem_singleton_self a)
    simp only [gateDepthOf]
    omega
  | andGate l => have := hl l h; simp only [gateDepthOf]; omega
  | orGate l => have := hl l h; simp only [gateDepthOf]; omega
  | modGate m l => have := hl l h; simp only [gateDepthOf]; omega

/-- Appending a flat gate keeps the depths of the earlier outputs. -/
theorem outputDepths_snocACGate_castSucc {n k : ℕ} (c : Circuit acSignature n k)
    (g : ACGate n) (h : ∀ a ∈ gateInputs g, a < k) (t : Fin k) :
    (snocACGate c g h).outputDepths t.castSucc = c.outputDepths t := by
  cases g with
  | var i => simp [snocACGate, Circuit.outputDepths]
  | _ => simp only [snocACGate, Circuit.outputDepths_snocLine_castSucc]

/-- The new output of `snocACGate` for a constant gate has depth `1`. -/
theorem outputDepths_snocACGate_const {n k : ℕ} (c : Circuit acSignature n k) (b : Bool)
    (h : ∀ a ∈ gateInputs (ACGate.const b : ACGate n), a < k) :
    (snocACGate c (.const b) h).outputDepths (Fin.last k) = 1 := by
  simp [snocACGate, line_depth_eq]

/-- For a flat gate `g` that is not a constant, if output `t` of `c` has depth `us.getD t 0` for
every `t < k`, the new output of `snocACGate c g h` has depth `gateDepthOf us g`. -/
theorem outputDepths_snocACGate_last {n k : ℕ} (c : Circuit acSignature n k) (g : ACGate n)
    (h : ∀ a ∈ gateInputs g, a < k) (hg : ∀ b, g ≠ .const b) (us : List ℕ)
    (hus : ∀ t : Fin k, c.outputDepths t = us.getD t 0) :
    (snocACGate c g h).outputDepths (Fin.last k) = gateDepthOf us g := by
  have hw : ∀ t : Fin k, c.program.wireDepths (c.outputs t) = us.getD t 0 := hus
  have hl : ∀ l : List ℕ, (List.ofFn fun (j : Fin l.length) => us[l[(j : ℕ)]]?.getD 0) =
      l.map fun a => us[a]?.getD 0 := fun l => List.ofFn_getElem_eq_map l (fun a => us[a]?.getD 0)
  cases g with
  | var i => simp [snocACGate, Circuit.outputDepths, gateDepthOf]
  | const b => exact absurd rfl (hg b)
  | notGate a => simp [snocACGate, line_depth_eq, gateDepthOf, hw]
  | andGate l =>
    simp [snocACGate, line_depth_eq, gateDepthOf, hw, hl]
  | orGate l =>
    simp [snocACGate, line_depth_eq, gateDepthOf, hw, hl]
  | modGate m l =>
    simp [snocACGate, line_depth_eq, gateDepthOf, hw, hl]

private theorem outputDepths_snocACGate_last_bounds {n k : ℕ} (c : Circuit acSignature n k)
    (g : ACGate n) (h : ∀ a ∈ gateInputs g, a < k) (ds : List ℕ)
    (h₁ : ∀ t : Fin k, ds.getD t 0 ≤ c.outputDepths t)
    (h₂ : ∀ t : Fin k, c.outputDepths t ≤ ds.getD t 0 + 1) :
    gateDepthOf ds g ≤ (snocACGate c g h).outputDepths (Fin.last k) ∧
      (snocACGate c g h).outputDepths (Fin.last k) ≤ gateDepthOf ds g + 1 := by
  by_cases hg : ∃ b, g = .const b
  · obtain ⟨b, rfl⟩ := hg
    rw [outputDepths_snocACGate_const]
    simp [gateDepthOf]
  · have hg' : ∀ b, g ≠ .const b := fun b hb => hg ⟨b, hb⟩
    have hus : ∀ t : Fin k, c.outputDepths t = (List.ofFn c.outputDepths).getD t 0 := fun t => by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    have hus' : ∀ a (ha : a < k), c.outputDepths ⟨a, ha⟩ = (List.ofFn c.outputDepths).getD a 0 :=
      fun a ha => hus ⟨a, ha⟩
    rw [outputDepths_snocACGate_last c g h hg' _ hus]
    constructor
    · have := gateDepthOf_le_add ds (List.ofFn c.outputDepths) g 0 fun a ha => by
        rw [Nat.add_zero, ← hus' a (h a ha)]
        exact h₁ ⟨a, h a ha⟩
      rwa [Nat.add_zero] at this
    · exact gateDepthOf_le_add _ ds g 1 fun a ha => by
        rw [← hus' a (h a ha)]
        exact h₂ ⟨a, h a ha⟩

private theorem depth_toCircuitUpTo {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    ∀ (k : ℕ) (hk : k ≤ C.length) (t : Fin k),
      (circuitDepths (C.take k)).getD t 0 ≤ (toCircuitUpTo C hC k hk).outputDepths t ∧
        (toCircuitUpTo C hC k hk).outputDepths t ≤ (circuitDepths (C.take k)).getD t 0 + 1
  | 0, _, t => t.elim0
  | k + 1, hk, t => by
    have hlen : (circuitDepths (C.take k)).length = k := by simp; omega
    have htake : C.take (k + 1) = C.take k ++ [C[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
    rw [toCircuitUpTo, htake, circuitDepths_append_singleton]
    refine Fin.lastCases ?_ (fun s => ?_) t
    · rw [List.getD_append_right _ _ _ _ (by simp [hlen])]
      simpa [hlen] using outputDepths_snocACGate_last_bounds _ C[k] (hC k hk) _
        (fun t => (depth_toCircuitUpTo C hC k _ t).1) (fun t => (depth_toCircuitUpTo C hC k _ t).2)
    · rw [outputDepths_snocACGate_castSucc, List.getD_append _ _ _ _ (by simp [hlen])]
      exact depth_toCircuitUpTo C hC k _ s

private theorem depth_toCircuitUpTo_eq {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C)
    (hconst : ∀ b, ACGate.const b ∉ C) :
    ∀ (k : ℕ) (hk : k ≤ C.length) (t : Fin k),
      (toCircuitUpTo C hC k hk).outputDepths t = (circuitDepths (C.take k)).getD t 0
  | 0, _, t => t.elim0
  | k + 1, hk, t => by
    have hlen : (circuitDepths (C.take k)).length = k := by simp; omega
    have htake : C.take (k + 1) = C.take k ++ [C[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
    rw [toCircuitUpTo, htake, circuitDepths_append_singleton]
    refine Fin.lastCases ?_ (fun s => ?_) t
    · have hg : ∀ b, C[k] ≠ .const b := fun b hb => hconst b (hb ▸ List.getElem_mem hk)
      rw [outputDepths_snocACGate_last _ C[k] (hC k hk) hg _
          (depth_toCircuitUpTo_eq C hC hconst k _),
        List.getD_append_right _ _ _ _ (by simp [hlen])]
      simp [hlen]
    · rw [outputDepths_snocACGate_castSucc, List.getD_append _ _ _ _ (by simp [hlen])]
      exact depth_toCircuitUpTo_eq C hC hconst k _ s

/-- Each output of the CSLib circuit of a well-formed flat circuit is at least as deep as its
flat gate. -/
theorem getElem_circuitDepths_le_outputDepths_toCircuit {n : ℕ} (C : List (ACGate n))
    (hC : WellFormedCircuit C) (t : Fin C.length) :
    (circuitDepths C)[t] ≤ (toCircuit C hC).outputDepths t := by
  have h := (depth_toCircuitUpTo C hC C.length le_rfl t).1
  rwa [List.take_of_length_le le_rfl, List.getD_eq_getElem _ _ (by simp)] at h

/-- Each output of the CSLib circuit of a well-formed flat circuit is at most one level deeper
than its flat gate. -/
theorem outputDepths_toCircuit_le {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C)
    (t : Fin C.length) :
    (toCircuit C hC).outputDepths t ≤ (circuitDepths C)[t] + 1 := by
  have h := (depth_toCircuitUpTo C hC C.length le_rfl t).2
  rwa [List.take_of_length_le le_rfl, List.getD_eq_getElem _ _ (by simp)] at h

/-- If a well-formed flat circuit has no constant gate, each output of its CSLib circuit has
exactly the depth of its flat gate. -/
theorem outputDepths_toCircuit_eq {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C)
    (hconst : ∀ b, ACGate.const b ∉ C) (t : Fin C.length) :
    (toCircuit C hC).outputDepths t = (circuitDepths C)[t] := by
  have h := depth_toCircuitUpTo_eq C hC hconst C.length le_rfl t
  rwa [List.take_of_length_le le_rfl, List.getD_eq_getElem _ _ (by simp)] at h

/-- The CSLib circuit of a well-formed flat circuit is at least as deep as the flat circuit. -/
theorem circuitDepth_le_depth_toCircuit {n : ℕ} (C : List (ACGate n))
    (hC : WellFormedCircuit C) : circuitDepth C ≤ (toCircuit C hC).depth := by
  rw [circuitDepth, foldr_max_le_iff]
  intro a ha
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem ha
  have ht' : t < C.length := by simpa using ht
  exact (getElem_circuitDepths_le_outputDepths_toCircuit C hC ⟨t, ht'⟩).trans
    ((toCircuit C hC).outputDepths_le_depth _)

/-- The CSLib circuit of a well-formed flat circuit is at most one level deeper than the flat
circuit. -/
theorem depth_toCircuit_le {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    (toCircuit C hC).depth ≤ circuitDepth C + 1 := by
  rw [Circuit.depth_le_iff]
  intro t
  exact (outputDepths_toCircuit_le C hC t).trans
    (Nat.add_le_add_right (le_foldr_max (List.getElem_mem _)) 1)

/-- If a well-formed flat circuit has no constant gate, its CSLib circuit has exactly its
depth. -/
theorem depth_toCircuit_eq {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C)
    (hconst : ∀ b, ACGate.const b ∉ C) :
    (toCircuit C hC).depth = circuitDepth C := by
  refine le_antisymm ?_ (circuitDepth_le_depth_toCircuit C hC)
  rw [Circuit.depth_le_iff]
  intro t
  rw [outputDepths_toCircuit_eq C hC hconst]
  exact le_foldr_max (List.getElem_mem _)

/-! ### Exact depth, constants included -/

/-- Depth of one gate given the depths of earlier gates, as CSLib counts it: as in
`gateDepthOf`, except that a constant gate has depth `1`. -/
def acGateDepthOf (ds : List ℕ) {n : ℕ} : ACGate n → ℕ
  | .const _ => 1
  | g => gateDepthOf ds g

/-- Depths of all gates in order, as CSLib counts them: the recurrence of `circuitDepths` with
`acGateDepthOf` in place of `gateDepthOf`. -/
def acCircuitDepths {n : ℕ} (C : List (ACGate n)) : List ℕ :=
  C.foldl (fun ds g => ds ++ [acGateDepthOf ds g]) []

/-- `acCircuitDepths` has one depth per gate. -/
@[simp] theorem length_acCircuitDepths {n : ℕ} (C : List (ACGate n)) :
    (acCircuitDepths C).length = C.length := by
  simpa [acCircuitDepths] using
    length_foldl_snoc (fun ds (g : ACGate n) => acGateDepthOf ds g) C []

/-- Measuring one more gate as CSLib counts it appends its depth, computed from the depths of
the earlier gates. -/
theorem acCircuitDepths_append_singleton {n : ℕ} (C : List (ACGate n)) (g : ACGate n) :
    acCircuitDepths (C ++ [g]) =
      acCircuitDepths C ++ [acGateDepthOf (acCircuitDepths C) g] := by
  simp [acCircuitDepths, List.foldl_append]

private theorem outputDepths_snocACGate_last_acGateDepthOf {n k : ℕ}
    (c : Circuit acSignature n k) (g : ACGate n) (h : ∀ a ∈ gateInputs g, a < k) (us : List ℕ)
    (hus : ∀ t : Fin k, c.outputDepths t = us.getD t 0) :
    (snocACGate c g h).outputDepths (Fin.last k) = acGateDepthOf us g := by
  by_cases hg : ∃ b, g = .const b
  · obtain ⟨b, rfl⟩ := hg
    exact outputDepths_snocACGate_const c b h
  · rw [outputDepths_snocACGate_last c g h (fun b hb => hg ⟨b, hb⟩) us hus]
    cases g with
    | const b => exact absurd ⟨b, rfl⟩ hg
    | _ => rfl

private theorem outputDepths_toCircuitUpTo {n : ℕ} (C : List (ACGate n))
    (hC : WellFormedCircuit C) :
    ∀ (k : ℕ) (hk : k ≤ C.length) (t : Fin k),
      (toCircuitUpTo C hC k hk).outputDepths t = (acCircuitDepths (C.take k)).getD t 0
  | 0, _, t => t.elim0
  | k + 1, hk, t => by
    have hlen : (acCircuitDepths (C.take k)).length = k := by simp; omega
    have htake : C.take (k + 1) = C.take k ++ [C[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some]
    rw [toCircuitUpTo, htake, acCircuitDepths_append_singleton]
    refine Fin.lastCases ?_ (fun s => ?_) t
    · rw [outputDepths_snocACGate_last_acGateDepthOf _ C[k] (hC k hk) _
          (outputDepths_toCircuitUpTo C hC k _),
        List.getD_append_right _ _ _ _ (by simp [hlen])]
      simp [hlen]
    · rw [outputDepths_snocACGate_castSucc, List.getD_append _ _ _ _ (by simp [hlen])]
      exact outputDepths_toCircuitUpTo C hC k _ s

/-- Output `t` of the CSLib circuit of a well-formed flat circuit `C` has depth
`(acCircuitDepths C)[t]`, constant gates included. -/
theorem outputDepths_toCircuit {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C)
    (t : Fin C.length) :
    (toCircuit C hC).outputDepths t = (acCircuitDepths C)[t] := by
  have h := outputDepths_toCircuitUpTo C hC C.length le_rfl t
  rwa [List.take_of_length_le le_rfl, List.getD_eq_getElem _ _ (by simp)] at h

/-- The output depths of the CSLib circuit of a well-formed flat circuit are exactly
`acCircuitDepths C`. -/
theorem ofFn_outputDepths_toCircuit {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    List.ofFn (toCircuit C hC).outputDepths = acCircuitDepths C := by
  apply List.ext_getElem (by simp)
  intro t h₁ h₂
  rw [List.getElem_ofFn]
  exact outputDepths_toCircuit C hC ⟨t, by simpa using h₁⟩

/-- The depth of the CSLib circuit of a well-formed flat circuit is the largest entry of
`acCircuitDepths C`. -/
theorem depth_toCircuit {n : ℕ} (C : List (ACGate n)) (hC : WellFormedCircuit C) :
    (toCircuit C hC).depth = (acCircuitDepths C).foldr max 0 := by
  rw [Circuit.depth, fin_foldl_max, ofFn_outputDepths_toCircuit, Nat.zero_max]

end Cslib.Complexity.Classes
