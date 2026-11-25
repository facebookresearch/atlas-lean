/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Logics.Propositional.CNF.Semantics
import CSLibExt.Computability.Complexity.Karp.ThreeSatComplete
import CSLibExt.Computability.Complexity.FramedCNF.Normalize
import CSLibExt.Computability.Complexity.PolynomialEncoding.Bounds
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListParts
import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-!
# MINIMUM ONES 3-SAT is NP-complete

`minOnesThreeSat_npComplete` proves NP membership using one certificate bit per literal
occurrence, and NP-hardness by padding the clauses of a 3-SAT instance to exactly three
literals. The certificate length depends only on the formula, even when the declared
number of variables is exponentially larger than its binary encoding.
-/

namespace MetaMathlibExt.Complexity.NPComplete.MinOnesThreeSat

@[expose] public section

/-- **MINIMUM ONES 3-SAT instances.** An instance of MINIMUM ONES 3-SAT is a triple
$(n, \varphi, K)$ of a natural number $n$ (the number of variables), a CNF formula $\varphi$ and a
natural number $K$ (the bound). No condition is placed on $\varphi$ here; clauses of exactly three
literals are required separately, by well-formedness. -/
abbrev MinOnesThreeSatInstance := ℕ × Cslib.Logic.LegacyPL.CNF × ℕ

/-- **Well-formed MINIMUM ONES 3-SAT instances.** A triple $(n, \varphi, K)$ of a natural number
$n$, a CNF formula $\varphi$ and a natural number $K$ is well formed when every clause of $\varphi$
is a list of exactly three literals and every literal of every clause has variable index less
than $n$. -/
def WellFormed (i : MinOnesThreeSatInstance) : Prop :=
  (∀ clause ∈ i.2.1, clause.length = 3 ∧ ∀ l ∈ clause, l.1 < i.1)

/-- **Feasible MINIMUM ONES 3-SAT instances.** A triple $(n, \varphi, K)$ of a natural number $n$,
a CNF formula $\varphi$ and a natural number $K$ is feasible when there is an assignment of truth
values to the variables $0, \dots, n-1$ that, with every variable $x \ge n$ set to false,
satisfies $\varphi$ and sets at most $K$ of the variables $0, \dots, n-1$ to true. -/
def MinOnesThreeSatFeasible
    (i : MinOnesThreeSatInstance) : Prop :=
  ∃ assign : List Bool, assign.length = i.1 ∧
    (Cslib.Logic.LegacyPL.CNF.Satisfies (fun x => assign.getD x false) i.2.1) ∧
    (assign.filter (fun b => b)).length ≤ i.2.2

open Classical in
/-- **The MINIMUM ONES 3-SAT decision problem.** MINIMUM ONES 3-SAT is the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
triple $(n, \varphi, K)$ of a natural number $n$, a CNF formula $\varphi$ and a natural number $K$
such that every clause of $\varphi$ is a list of exactly three literals whose variables are all
less than $n$, and some assignment of truth values to the variables $0, \dots, n-1$ satisfies
$\varphi$ and sets at most $K$ of them to true. Every other bitstring is rejected. -/
noncomputable def minOnesThreeSatDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinOnesThreeSatInstance) x with
  | some i => decide (WellFormed i ∧ MinOnesThreeSatFeasible i)
  | none => false

end

open BitstringEncoding Cslib.CookLevin Cslib.Logic.LegacyPL

/-! ### Occurrence certificates

A marked occurrence puts its variable in the set of true variables. A satisfying assignment
can mark the last occurrence of each true variable, so repeated literals cost only once.
-/

private def selected : List Nat → List Bool → List Nat
  | x :: xs, b :: bs => if b then x :: selected xs bs else selected xs bs
  | _, _ => []

private def well (n : Nat) (φ : CNF) := φ.all fun c =>
  c.length == 3 && c.all (fun l => decide (l.1 < n))

private def result (x w : List Bool) : Bool :=
  match bitDecode (α := MinOnesThreeSatInstance) x with
  | none => false
  | some (n, φ, k) =>
    let zs := selected (varsOf φ) w
    well n φ && decide (zs.length ≤ k) &&
      φ.all (fun c => c.any (fun l => zs.contains l.1 == l.2))

namespace Certificate

private def mark (v : Nat → Bool) : List Nat → List Bool
  | [] => []
  | x :: xs => (v x && !(xs.contains x)) :: mark v xs

private theorem length_mark (v : Nat → Bool) (xs : List Nat) : (mark v xs).length = xs.length := by
  induction xs <;> simp [mark, *]

private theorem selected_mark (v : Nat → Bool) (xs : List Nat) :
    selected xs (mark v xs) = xs.dedup.filter v := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases ha : a ∈ xs <;> cases hv : v a <;> simp [mark, selected, ha, hv, ih]

private theorem getD_range_map (v : Nat → Bool) {x n : Nat} (h : x < n) :
    ((List.range n).map v).getD x false = v x := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp

private theorem weight_range_map (v : Nat → Bool) (n : Nat) :
    (((List.range n).map v).filter id).length = ((List.range n).filter v).length := by
  rw [List.filter_map]
  simp

private theorem length_le_of_subset {a b : List Nat} (ha : a.Nodup)
    (hab : ∀ x ∈ a, x ∈ b) : a.length ≤ b.length := by
  rw [← List.toFinset_card_of_nodup ha]
  apply (Finset.card_le_card (t := b.toFinset) ?_).trans (List.toFinset_card_le _)
  intro x hx
  exact List.mem_toFinset.mpr (hab x (List.mem_toFinset.mp hx))

private theorem check_some {x : List Bool} {n k : Nat} {φ : CNF}
    (hd : bitDecode x = some (n, φ, k)) (w : List Bool) :
    result x w = true ↔ WellFormed (n, φ, k) ∧ (selected (varsOf φ) w).length ≤ k ∧
      φ.Satisfies (fun z => (selected (varsOf φ) w).contains z) := by
  simp [result, well, hd, WellFormed, CNF.Satisfies, and_assoc, CNFClause.Satisfies,
    CNFLiteral.Satisfies]

private theorem length_vars {n k : Nat} {φ : CNF} (hw : WellFormed (n, φ, k)) :
    (varsOf φ).length = 3 * φ.length := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    have hc := (hw c List.mem_cons_self).1
    have ht := ih fun d hd => hw d (List.mem_cons_of_mem c hd)
    simp only [varsOf, List.flatMap_cons, List.length_append, List.length_map] at *
    simp only [List.length_cons]
    omega

private theorem verifier_correct (x : List Bool) :
    minOnesThreeSatDec x = true ↔ ∃ w : List Bool, w.length ≤ 3 * x.length ∧ result x w := by
  cases hd : bitDecode (α := MinOnesThreeSatInstance) x with
  | none => simp [minOnesThreeSatDec, result, hd]
  | some i =>
    obtain ⟨n, φ, k⟩ := i
    simp only [minOnesThreeSatDec, hd, decide_eq_true_eq]
    constructor
    · rintro ⟨hw, a, ha, hs, hk⟩
      let v := fun z => a.getD z false
      have hnames (z) (hz : z ∈ varsOf φ) : z < n := by
        obtain ⟨c, hc, hz⟩ := List.mem_flatMap.mp hz
        obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hz
        exact (hw c hc).2 l hl
      have hr : (List.range n).map v = a := by
        apply List.ext_getElem
        · simpa using ha.symm
        · intro z h₁ h₂
          simp only [List.getElem_map, List.getElem_range, v]
          exact List.getD_eq_getElem _ _ h₂
      let names := varsOf φ
      refine ⟨mark v names, ?_, (check_some hd _).mpr ⟨hw, ?_, ?_⟩⟩
      · rw [length_mark, length_vars hw]
        apply Nat.mul_le_mul_left
        exact Cslib.Complexity.PolynomialEncoding.decoded_middle_list_length_le hd
      · rw [selected_mark]
        calc
          _ ≤ ((List.range n).filter v).length := by
            apply length_le_of_subset ((List.nodup_dedup _).filter _)
            intro z hz
            simp only [List.mem_filter, List.mem_dedup] at hz
            simp [hnames _ hz.1, hz.2]
          _ = (a.filter id).length := by rw [← weight_range_map, hr]
          _ ≤ k := hk
      · rw [selected_mark]
        intro c hc
        obtain ⟨⟨z, b⟩, hl, hb⟩ := hs c hc
        refine ⟨(z, b), hl, ?_⟩
        have hmem := mem_varsOf hl hc
        change v z = b at hb
        simpa [CNFLiteral.Satisfies, List.contains_iff_mem, names, hmem] using hb
    · rintro ⟨w, _, hw⟩
      obtain ⟨hf, hk, hs⟩ := (check_some hd w).mp hw
      let s := selected (varsOf φ) w
      let v := fun z => s.contains z
      refine ⟨hf, (List.range n).map v, by simp, ?_, ?_⟩
      · intro c hc
        obtain ⟨l, hl, hb⟩ := hs c hc
        exact ⟨l, hl, (Certificate.getD_range_map v ((hf c hc).2 l hl)).trans hb⟩
      · change (((List.range n).map v).filter id).length ≤ k
        rw [weight_range_map]
        apply (length_le_of_subset (List.nodup_range.filter v) (b := s) ?_).trans hk
        intro z hz
        exact List.contains_iff_mem.mp (List.mem_filter.mp hz).2

end Certificate

/-! ### Reduction from 3-SAT

Each source clause occurs twice. Both copies have length at least three, with opposite
polarities on the padding literals. Thus even the empty source clause remains unsatisfiable.
Writing either binary bound takes one bit more than the token count.
-/

namespace Reduction

open Cslib.CookLevin Cslib.Logic.LegacyPL Cslib.Complexity.Karp
open MetaMathlibExt.BitstringEncoding MetaMathlibExt.ComplexityTheory

private def pad (b : Bool) (c : CNFClause) : CNFClause :=
  c ++ List.replicate (3 - c.length) (0, b)

private def padded (φ : CNF) : CNF := φ.map (pad true) ++ φ.map (pad false)

private theorem pad_sat (φ : CNF) (v : Nat → Bool) :
    CNF.Satisfies v (padded φ) ↔ φ.Satisfies v := by
  constructor
  · intro hs c hc
    have hm : pad (!(v 0)) c ∈ padded φ := by
      cases v 0
      · exact List.mem_append_left _ (List.mem_map_of_mem hc)
      · exact List.mem_append_right _ (List.mem_map_of_mem hc)
    obtain ⟨l, hl, he⟩ := hs _ hm
    rcases List.mem_append.mp hl with h | h
    · exact ⟨l, h, he⟩
    · obtain rfl := List.eq_of_mem_replicate h
      simp [CNFLiteral.Satisfies] at he
  · intro hs d hd
    rcases List.mem_append.mp hd with h | h <;> obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h <;>
      obtain ⟨l, hl, he⟩ := hs c hc <;> exact ⟨l, List.mem_append_left _ hl, he⟩

open Cslib.Complexity.SatVerifier in
private def upper (φ : CNF) : Nat := 2 ^ (toks φ).length

open Cslib.Complexity.SatVerifier in
private theorem lt_upper {x : Nat} {φ : CNF} (hx : x ∈ varsOf φ) : x < upper φ := by
  apply Nat.size_le.mp
  have h := Machine.varsOf_sum_le φ
  have hm : (Computability.encodeNat x).length + 1 ∈
      (varsOf φ).map (fun z => (Computability.encodeNat z).length + 1) := List.mem_map_of_mem hx
  have hh := List.le_sum_of_mem hm
  rw [BinaryNatEncoding.length_encodeNat] at hh
  omega

private def output (φ : CNF) : List Bool :=
  bitEncode ((upper φ, padded φ, upper φ) : MinOnesThreeSatInstance)

private def reduce (x : List Bool) : List Bool :=
  ((decodeCNF x).map output).getD []

private theorem feasible_iff_sat {φ : CNF} {n : Nat}
    (hf : WellFormed (n, φ, n)) : MinOnesThreeSatFeasible (n, φ, n) ↔ CNFSat φ := by
  rw [cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨a, _, hs, _⟩
    exact ⟨_, hs⟩
  · rintro ⟨v, hs⟩
    refine ⟨(List.range n).map v, by simp, ?_, ?_⟩
    · intro c hc
      obtain ⟨l, hl, hb⟩ := hs c hc
      exact ⟨l, hl, (Certificate.getD_range_map v ((hf c hc).2 l hl)).trans hb⟩
    · exact (List.length_filter_le ..).trans (by simp)

private theorem output_correct (φ : CNF) :
    minOnesThreeSatDec (output φ) = true ↔ is3 φ = true ∧ CNFSat φ := by
  simp only [output, minOnesThreeSatDec, bitDecode_bitEncode, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, hf⟩
    obtain ⟨v, hv⟩ := cnfSat_iff_exists_satisfies.mp ((feasible_iff_sat hw).mp hf)
    refine ⟨List.all_eq_true.mpr (fun c hc => decide_eq_true ?_),
      cnfSat_iff_exists_satisfies.mpr ⟨v, (pad_sat φ v).mp hv⟩⟩
    have hh := (hw (pad true c) (List.mem_append_left _ (List.mem_map_of_mem hc))).1
    simp only [pad, List.length_append, List.length_replicate] at hh
    omega
  · rintro ⟨h3, hs⟩
    obtain ⟨v, hv⟩ := cnfSat_iff_exists_satisfies.mp hs
    have hpad (b : Bool) (c : CNFClause) (hc : c ∈ φ) :
        (pad b c).length = 3 ∧ ∀ m ∈ pad b c, m.1 < upper φ := by
      have hc3 : c.length ≤ 3 := of_decide_eq_true (List.all_eq_true.mp h3 c hc)
      refine ⟨by simp [pad]; omega, ?_⟩
      intro m hm
      rcases List.mem_append.mp hm with h | h
      · exact lt_upper (mem_varsOf h hc)
      · obtain rfl := List.eq_of_mem_replicate h
        exact Nat.two_pow_pos _
    have hw : WellFormed (upper φ, padded φ, upper φ) := by
      intro d hd
      rcases List.mem_append.mp hd with h | h <;> obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h <;>
        exact hpad _ c hc
    exact ⟨hw, (feasible_iff_sat hw).mpr
      (cnfSat_iff_exists_satisfies.mpr ⟨v, (pad_sat φ v).mpr hv⟩)⟩

private theorem reduce_correct (x : List Bool) : sat3Dec x = minOnesThreeSatDec (reduce x) := by
  apply Bool.eq_iff_iff.mpr
  cases hd : decodeCNF x with
  | none =>
    have hx (φ : CNF) : encodeCNF φ ≠ x := by
      rintro rfl
      simp at hd
    have hbad : minOnesThreeSatDec [] = false := rfl
    simp [sat3Dec, reduce, hd, hx, hbad]
  | some φ =>
    obtain rfl := (decodeCNF_eq_some_iff x φ).mp hd
    simp only [reduce, hd, Option.map_some, Option.getD_some, output_correct,
      sat3Dec, decide_eq_true_eq]
    constructor
    · rintro ⟨ψ, he, h⟩
      exact encodeCNF_injective he ▸ h
    · exact fun h => ⟨φ, rfl, h⟩

open Cslib.Complexity.SatVerifier

private abbrev Word := List Bool

-- Nested frames let the emitter write each literal as soon as its tokens arrive.
private def frameBits (w : Word) : Word := w.flatMap fun b => [true, b]

private theorem frame_append (u v : Word) :
    frameBits (u ++ v) = frameBits u ++ frameBits v := List.flatMap_append ..

private theorem delim_bits (w : Word) : delimit w = frameBits w ++ [false] :=
  Emit3.delimit_eq w

private abbrev twice (w : Word) := frameBits (frameBits w)
private abbrev thrice (w : Word) := frameBits (twice w)
private abbrev four (w : Word) := frameBits (thrice w)

private def litOutput (l : Nat × Bool) : Word := twice (delimit (bitEncode l))

private theorem lit_output (l : Nat × Bool) :
    litOutput l = four (Computability.encodeNat l.1) ++
      thrice [false, l.2] ++ twice [false] := by
  change twice (delimit (delimit (Computability.encodeNat l.1) ++ [l.2])) = _
  simp only [delim_bits, four, thrice, twice, frame_append, List.append_assoc]
  rfl

private abbrev remCount (m : Nat) : Fin 4 := ⟨3 - m, by omega⟩

private def nextCount (q : Fin 4) : Sym → Fin 4
  | .lit _ => ⟨q.val - 1, by omega⟩
  | .cl => 3
  | _ => q

private def emitToken (b : Bool) (q : Fin 4) : Sym → Word
  | .bit a => four [a]
  | .lit p => thrice [false, p] ++ twice [false]
  | .cl => (List.replicate q.val (0, b)).flatMap litOutput ++ frameBits [false]
  | _ => []

private def stream (b : Bool) (q : Fin 4) : List Sym → Word
  | [] => []
  | s :: ss => emitToken b q s ++ stream b (nextCount q s) ss

private theorem stream_bits (b : Bool) (q : Fin 4) (w : Word) (rest : List Sym) :
    stream b q (w.map Sym.bit ++ rest) = four w ++ stream b q rest := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have h : four (a :: w) = four [a] ++ four w := by
      change four ([a] ++ w) = _
      simp only [four, thrice, twice, frame_append]
    simp [h, stream, emitToken, nextCount, ih, List.append_assoc]

private theorem stream_clause_aux (b : Bool) (c : CNFClause) (r : List Sym) (m : Nat) :
    stream b (remCount m) (c.flatMap litToks ++ .cl :: r) =
      c.flatMap litOutput ++
      (List.replicate (3 - (m + c.length)) (0, b)).flatMap litOutput ++
      frameBits [false] ++ stream b 3 r := by
  induction c generalizing m with
  | nil => simp [stream, emitToken, nextCount, remCount]
  | cons l c ih =>
    have hq : nextCount (remCount m) (.lit l.2) = remCount (m + 1) := by
      apply Fin.ext
      simp only [nextCount]
      omega
    simp only [List.flatMap_cons, litToks, List.append_assoc, List.cons_append, List.nil_append,
      stream_bits, stream, emitToken, hq, ih, lit_output, List.length_cons]
    rw [show m + 1 + c.length = m + (c.length + 1) by omega]

private theorem frame_formula (φ : CNF) :
    frameBits (bitEncode φ) = φ.flatMap (fun c => c.flatMap litOutput ++ frameBits [false]) := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change frameBits (delimit (bitEncode c) ++ bitEncode φ) = _
    rw [frame_append, ih, List.flatMap_cons]
    congr 1
    rw [delim_bits, frame_append]
    congr 1
    induction c with
    | nil => rfl
    | cons l c ih =>
      change twice (delimit (bitEncode l) ++ bitEncode c) = _
      simp only [twice, frame_append, List.flatMap_cons, litOutput] at *
      rw [ih]

private theorem stream_formula (φ : CNF) (b : Bool) :
    stream b 3 (toks φ) = frameBits (bitEncode (φ.map (pad b))) := by
  rw [frame_formula]
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    change stream b (remCount 0) (clauseToks c ++ toks φ) = _
    simp only [clauseToks, List.append_assoc, List.cons_append, List.nil_append,
      stream_clause_aux, Nat.zero_add, ih, List.map_cons, List.flatMap_cons, pad,
      List.flatMap_append]

private theorem output_stream (φ : CNF) :
    output φ = delimit (Computability.encodeNat (upper φ)) ++ stream true 3 (toks φ) ++
      stream false 3 (toks φ) ++ [false] ++ Computability.encodeNat (upper φ) := by
  change delimit (Computability.encodeNat (upper φ)) ++
    (delimit (bitEncode (padded φ)) ++ Computability.encodeNat (upper φ)) = _
  rw [delim_bits (bitEncode (padded φ)), frame_formula]
  simp only [stream_formula, frame_formula, padded, List.flatMap_append, List.append_assoc]

private def maxEmit := Finset.univ.sup fun t : Bool × Fin 4 × Sym =>
  (emitToken t.1 t.2.1 t.2.2).length

private theorem stream_length (b : Bool) (q : Fin 4) (ss : List Sym) :
    (stream b q ss).length ≤ maxEmit * ss.length := by
  induction ss generalizing q with
  | nil => simp [stream]
  | cons s ss ih =>
    have h : (emitToken b q s).length ≤ maxEmit :=
      Finset.le_sup (f := fun t : Bool × Fin 4 × Sym => (emitToken t.1 t.2.1 t.2.2).length)
        (Finset.mem_univ (b, q, s))
    simpa [stream, Nat.mul_succ, Nat.add_comm] using Nat.add_le_add h (ih (nextCount q s))

open Turing Function MetaMathlibExt.TM2Program

private inductive K
  | input | forward | pos | neg | out | count
  deriving DecidableEq

private def stackList : List K := [.input, .forward, .pos, .neg, .out, .count]

private theorem mem_stacks (k : K) : k ∈ stackList := by cases k <;> decide

private instance stacksFinite : Fintype K := Fintype.ofList stackList mem_stacks

@[reducible] private def Γ : K → Type
  | .input | .forward => Sym
  | .pos | .neg | .out | .count => Bool

private instance stackFinite (k : K) : Fintype (Γ k) := by cases k <;> infer_instance

private inductive Lab
  | start | invert | scan (q : Fin 4) | neg | pos | header | done
  deriving DecidableEq, Fintype

private abbrev Stmt := TM2.Stmt Γ Lab Bool

private def symCases (k : K) (get : Γ k → Sym) (act : Sym → Stmt) (stop : Stmt) :
    List Sym → Stmt
  | [] => .load (fun _ => false) stop
  | s :: ss => .peek k (fun _ o => o.map get == some s) <| .branch id
      (.pop k (fun _ _ => false) (act s)) (symCases k get act stop ss)

private def syms : List Sym := [.bit false, .bit true, .lit false, .lit true, .cl,
  .val false, .val true, .dead]

private theorem all_syms (s : Sym) : s ∈ syms := by
  cases s <;> (try rename_i b; cases b) <;> decide

private theorem symCases_cons (k : K) (get : Γ k → Sym) (act : Sym → Stmt) (stop : Stmt)
    (ss : List Sym) (S : ∀ k, List (Γ k)) (a : Γ k) (r : List (Γ k)) (hs : S k = a :: r)
    (hm : get a ∈ ss) (v : Bool) :
    TM2.stepAux (symCases k get act stop ss) v S =
      TM2.stepAux (act (get a)) false (update S k r) := by
  induction ss generalizing v with
  | nil => simp at hm
  | cons s ss ih =>
    by_cases he : get a = s
    · simp [symCases, TM2.stepAux, hs, he]
    · simp [symCases, TM2.stepAux, hs, he, ih (by simpa [he] using hm)]

private theorem symCases_nil (k : K) (get : Γ k → Sym) (act : Sym → Stmt) (stop : Stmt)
    (ss : List Sym) (S : ∀ k, List (Γ k)) (hs : S k = []) (v : Bool) :
    TM2.stepAux (symCases k get act stop ss) v S = TM2.stepAux stop false S := by
  induction ss generalizing v <;> simp [symCases, TM2.stepAux, *]

private def transfer (k : K) (readBit : Γ k → Bool) (self : Lab) (stop : Stmt) : Stmt :=
  .peek k (fun _ o => o.isSome) <| .branch id
    (.pop k (fun _ o => (o.map readBit).getD false) <| .push .out id <|
      .load (fun _ => false) <| .goto (fun _ => self)) stop

private def prog : Lab → Stmt
  | .start => .push .out (fun _ => true) <| .goto (fun _ => .invert)
  | .invert => symCases .input id (fun s =>
      .push .forward (fun _ => s) <| .push .out (fun _ => false) <|
      .push .count (fun _ => false) <| .goto (fun _ => .invert))
      (.push .out (fun _ => false) <| .goto (fun _ => .scan 3)) syms
  | .scan q => symCases .forward id (fun s =>
      pushList .pos (emitToken true q s) <| pushList .neg (emitToken false q s) <|
        .goto (fun _ => .scan (nextCount q s))) (.goto (fun _ => .neg)) syms
  | .neg => transfer .neg id .neg (.goto (fun _ => .pos))
  | .pos => transfer .pos id .pos (pushList .out [false, true, true] (.goto (fun _ => .header)))
  | .header => .pop .count (fun _ o => o.isSome) <| .branch id
      (pushList .out [false, true] (.goto (fun _ => .header))) (.goto (fun _ => .done))
  | .done => .halt

private def st (t f : List Sym) (p g o h : Word) : ∀ k, List (Γ k)
  | .input => t
  | .forward => f
  | .pos => p
  | .neg => g
  | .out => o
  | .count => h

@[simp] private theorem update_input (t f : List Sym) (p g o h : Word) (new : List (Γ .input)) :
    update (st t f p g o h) K.input new = st new f p g o h := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_forward (t f : List Sym) (p g o h : Word) (new : List (Γ .forward)) :
    update (st t f p g o h) K.forward new = st t new p g o h := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_pos (t f : List Sym) (p g o h : Word) (new : List (Γ .pos)) :
    update (st t f p g o h) K.pos new = st t f new g o h := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_neg (t f : List Sym) (p g o h : Word) (new : List (Γ .neg)) :
    update (st t f p g o h) K.neg new = st t f p new o h := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_out (t f : List Sym) (p g o h : Word) (new : List (Γ .out)) :
    update (st t f p g o h) K.out new = st t f p g new h := by
  funext k
  cases k <;> rfl

@[simp] private theorem update_count (t f : List Sym) (p g o h : Word) (new : List (Γ .count)) :
    update (st t f p g o h) K.count new = st t f p g o new := by
  funext k
  cases k <;> rfl

@[simp] private theorem st_input (t f : List Sym) (p g o h : Word) :
    st t f p g o h .input = t := rfl

@[simp] private theorem st_forward (t f : List Sym) (p g o h : Word) :
    st t f p g o h .forward = f := rfl

@[simp] private theorem st_pos (t f : List Sym) (p g o h : Word) :
    st t f p g o h .pos = p := rfl

@[simp] private theorem st_neg (t f : List Sym) (p g o h : Word) :
    st t f p g o h .neg = g := rfl

@[simp] private theorem st_out (t f : List Sym) (p g o h : Word) :
    st t f p g o h .out = o := rfl

@[simp] private theorem st_count (t f : List Sym) (p g o h : Word) :
    st t f p g o h .count = h := rfl

private theorem invert_run (t f : List Sym) (o h : Word) (v : Bool) :
    Run prog (t.length + 1) ⟨some .invert, v, st t f [] [] o h⟩
      ⟨some (.scan 3), false, st [] (t.reverse ++ f) [] []
        (false :: (List.replicate t.length false ++ o)) (List.replicate t.length false ++ h)⟩ := by
  induction t generalizing f o h v with
  | nil =>
    apply Run.single
    rw [prog, symCases_nil _ _ _ _ _ _ rfl]
    simp [TM2.stepAux]
  | cons s t ih =>
    have r : Run prog 1 ⟨some .invert, v, st (s :: t) f [] [] o h⟩
        ⟨some .invert, false, st t (s :: f) [] [] (false :: o) (false :: h)⟩ := by
      apply Run.single
      rw [prog, symCases_cons .input id _ _ syms _ s t rfl (all_syms s)]
      simp [TM2.stepAux]
    simpa [List.replicate_succ', List.append_assoc, Nat.add_comm] using
      r.trans (ih (s :: f) (false :: o) (false :: h) false)

private theorem scan_run (f : List Sym) (q : Fin 4) (p g o h : Word) (v : Bool) :
    Run prog (f.length + 1) ⟨some (.scan q), v, st [] f p g o h⟩
      ⟨some .neg, false, st [] [] ((stream true q f).reverse ++ p)
        ((stream false q f).reverse ++ g) o h⟩ := by
  induction f generalizing q p g v with
  | nil =>
    apply Run.single
    rw [prog, symCases_nil _ _ _ _ _ _ rfl]
    simp [TM2.stepAux, stream]
  | cons s f ih =>
    have r : Run prog 1 ⟨some (.scan q), v, st [] (s :: f) p g o h⟩
        ⟨some (.scan (nextCount q s)), false, st [] f ((emitToken true q s).reverse ++ p)
          ((emitToken false q s).reverse ++ g) o h⟩ := by
      apply Run.single
      rw [prog, symCases_cons .forward id _ _ syms _ s f rfl (all_syms s)]
      simp [TM2.stepAux, stepAux_pushList]
    simpa [stream, List.append_assoc, Nat.add_comm] using r.trans (ih _ _ _ false)

private theorem neg_run (p g o h : Word) (v : Bool) :
    Run prog (g.length + 1) ⟨some .neg, v, st [] [] p g o h⟩
      ⟨some .pos, false, st [] [] p [] (g.reverse ++ o) h⟩ := by
  induction g generalizing o v with
  | nil => exact Run.single (by simp [prog, transfer, TM2.stepAux])
  | cons b g ih =>
    have r : Run prog 1 ⟨some .neg, v, st [] [] p (b :: g) o h⟩
        ⟨some .neg, false, st [] [] p g (b :: o) h⟩ :=
      Run.single (by simp [prog, transfer, TM2.stepAux])
    simpa [List.append_assoc, Nat.add_comm] using r.trans (ih (b :: o) false)

private theorem pos_run (p o h : Word) (v : Bool) :
    Run prog (p.length + 1) ⟨some .pos, v, st [] [] p [] o h⟩
      ⟨some .header, false, st [] [] [] [] ([true, true, false] ++ p.reverse ++ o) h⟩ := by
  induction p generalizing o v with
  | nil => exact Run.single (by simp [prog, transfer, stepAux_pushList, TM2.stepAux])
  | cons b p ih =>
    have r : Run prog 1 ⟨some .pos, v, st [] [] (b :: p) [] o h⟩
        ⟨some .pos, false, st [] [] p [] (b :: o) h⟩ :=
      Run.single (by simp [prog, transfer, TM2.stepAux])
    simpa [List.append_assoc, Nat.add_comm] using r.trans (ih (b :: o) false)

private theorem header_run (n : Nat) (o : Word) (v : Bool) :
    Run prog (n + 1) ⟨some .header, v, st [] [] [] [] o (List.replicate n false)⟩
      ⟨some .done, false, st [] [] [] [] (frameBits (List.replicate n false) ++ o) []⟩ := by
  induction n generalizing o v with
  | zero => exact Run.single (by simp [prog, TM2.stepAux, frameBits])
  | succ n ih =>
    have r : Run prog 1
        ⟨some .header, v, st [] [] [] [] o (List.replicate (n + 1) false)⟩
        ⟨some .header, true, st [] [] [] [] (true :: false :: o) (List.replicate n false)⟩ :=
      Run.single (by simp [prog, TM2.stepAux, List.replicate_succ, stepAux_pushList])
    simpa [List.replicate_succ', frame_append, frameBits, List.append_assoc, Nat.add_comm] using
      r.trans (ih (true :: false :: o) true)

private def budget (n : Nat) := (2 * maxEmit + 3) * n + 6

private theorem emitter_run (φ : CNF) (v : Bool) (S : ∀ k, List (Γ k))
    (ht : S .input = (toks φ).reverse) (ho : S .out = [])
    (hempty : ∀ k, k ≠ .input → k ≠ .out → S k = []) :
    ∃ u S', RunLe prog (budget (toks φ).length) ⟨some .start, v, S⟩
      ⟨some .done, u, S'⟩ ∧ S' .out = output φ := by
  let ts := toks φ
  let n := ts.length
  let zeros := List.replicate n false
  let p := stream true 3 ts
  let g := stream false 3 ts
  have hS : S = st ts.reverse [] [] [] [] [] := by
    funext k
    cases k <;> first | exact ht | exact ho | apply hempty <;> decide
  have r₀ : Run prog 1 ⟨some .start, v, S⟩
      ⟨some .invert, v, st ts.reverse [] [] [] [true] []⟩ :=
    Run.single (by rw [hS]; simp [prog, TM2.stepAux])
  have r₁ : Run prog (n + 1) ⟨some .invert, v, st ts.reverse [] [] [] [true] []⟩
      ⟨some (.scan 3), false, st [] ts [] [] (false :: (zeros ++ [true])) zeros⟩ := by
    simpa [zeros, n] using invert_run ts.reverse [] [true] [] v
  have r₂ : Run prog (n + 1) ⟨some (.scan 3), false,
      st [] ts [] [] (false :: (zeros ++ [true])) zeros⟩ ⟨some .neg, false,
      st [] [] p.reverse g.reverse (false :: (zeros ++ [true])) zeros⟩ := by
    simpa [p, g] using scan_run ts 3 [] [] (false :: (zeros ++ [true])) zeros false
  have r₃ := neg_run p.reverse g.reverse (false :: (zeros ++ [true])) zeros false
  have r₄ := pos_run p.reverse (g ++ false :: (zeros ++ [true])) zeros false
  simp only [List.reverse_reverse, List.length_reverse] at r₃ r₄
  have r₅ := header_run n ([true, true, false] ++ p ++ (g ++ false :: (zeros ++ [true]))) false
  refine ⟨_, _, ((r₀.trans r₁).trans r₂ |>.trans r₃ |>.trans r₄ |>.trans r₅).le ?_, ?_⟩
  · have hp := stream_length true 3 ts
    have hg := stream_length false 3 ts
    change (stream true 3 ts).length ≤ maxEmit * n at hp
    change (stream false 3 ts).length ≤ maxEmit * n at hg
    change 1 + (n + 1) + (n + 1) + (g.length + 1) + (p.length + 1) + (n + 1) ≤ budget n
    simp only [budget, Nat.add_mul, Nat.mul_assoc, p, g]
    omega
  · rw [output_stream, upper, Emit3.encodeNat_two_pow, delim_bits, frame_append]
    simp [zeros, n, ts, p, g, List.append_assoc, frameBits]

private abbrev emitter : Emitter where
  K := K
  Γ := Γ
  L := Lab
  prog := prog
  start := .start
  done := .done
  start_ne_done := by decide
  prog_done := rfl
  cT := .input
  cO := .out
  cT_ne_cO := by decide
  iT := Equiv.refl _
  eO := Equiv.refl _
  g := output
  noOut := []
  B := budget
  B_mono _ _ h := Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _
  run φ v S ht ho hempty := by
    obtain ⟨v', S', hr, he⟩ := emitter_run φ v S (by simpa using ht) ho hempty
    exact ⟨v', S', hr, by simpa using he⟩

private theorem reduction_poly : IsPolyTime reduce := by
  have hp := TokThen.isPolyTime_out emitter stackList (by decide) mem_stacks
    (Polynomial.C (2 * maxEmit + 5) * Polynomial.X + Polynomial.C 9)
    (by
      intro n
      change 2 * n + 3 + budget n ≤ _
      simp only [budget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Nat.add_mul]
      omega)
  have he : TokThen.out emitter = reduce := by
    funext x
    cases hd : decodeCNF x <;> simp [TokThen.out, reduce, hd]
  exact he ▸ hp

private theorem hardness (L : DecisionProblem) (hL : L ∈ NP) :
    PolyManyOneRed L minOnesThreeSatDec :=
  (sat3Dec_npComplete.2 L hL).trans ⟨reduce, reduction_poly, reduce_correct⟩

end Reduction

/-! ### Streaming decoder

The parser combinators follow the pair and list frames of the instance encoding. Natural
numbers are normalized while reading, so the parser agrees with the decoder on every bitstring.
-/

namespace Lexer

open BitstringEncoding Cslib.Complexity.PolynomialEncoding
open Cslib.CookLevin Cslib.Complexity.SatVerifier Cslib.Logic.LegacyPL

private inductive Event
  | n (b : Bool) | k (b : Bool) | token (s : Sym)
  deriving DecidableEq, Fintype

private abbrev Out := List Event

private structure Parser where
  Q : Type
  [fin : Fintype Q]
  [dec : DecidableEq Q]
  initial : Q
  feed : Q → Bool → Option (Q × Out)
  finish : Q → Option Out

attribute [instance] Parser.fin Parser.dec

private def Parser.read (p : Parser) (q : p.Q) : List Bool → Option (p.Q × Out)
  | [] => some (q, [])
  | b :: bs => do
    let (q', u) ← p.feed q b
    let (q'', v) ← p.read q' bs
    pure (q'', u ++ v)

private def Parser.parseFrom (p : Parser) (q : p.Q) (w : List Bool) : Option Out := do
  let (q', u) ← p.read q w
  return u ++ (← p.finish q')

private def Parser.parse (p : Parser) (w : List Bool) := p.parseFrom p.initial w

private def put (u : Out) (v : Option Out) : Option Out := v.map (u ++ ·)

private theorem parseFrom_cons (p : Parser) (q : p.Q) (b : Bool) (w : List Bool) :
    p.parseFrom q (b :: w) = (p.feed q b).bind fun r => put r.2 (p.parseFrom r.1 w) := by
  simp only [Parser.parseFrom, Parser.read]
  cases h : p.feed q b with
  | none => rfl
  | some r =>
    obtain ⟨q', u⟩ := r
    cases h' : p.read q' w with
    | none => simp [h', put]
    | some r =>
      obtain ⟨q'', v⟩ := r
      cases p.finish q'' <;> simp [put, h']

private theorem parseFrom_nil (p : Parser) (q : p.Q) : p.parseFrom q [] = p.finish q := by
  simp [Parser.parseFrom, Parser.read]

private def liftFeed {Q T : Type} (f : Q → T) (s : Option (Q × Out)) : Option (T × Out) :=
  s.map fun r => (f r.1, r.2)

private abbrev pairP (a b : Parser) : Parser where
  Q := (Bool × a.Q) ⊕ b.Q
  initial := .inl (false, a.initial)
  feed
    | .inr q, c => liftFeed .inr (b.feed q c)
    | .inl (true, q), c => liftFeed (fun z => .inl (false, z)) (a.feed q c)
    | .inl (false, q), true => some (.inl (true, q), [])
    | .inl (false, q), false => (a.finish q).map fun u => (.inr b.initial, u)
  finish
    | .inl _ => none
    | .inr q => b.finish q

private theorem pair_right (a b : Parser) (q : b.Q) (w : List Bool) :
    (pairP a b).parseFrom (.inr q) w = b.parseFrom q w := by
  induction w generalizing q with
  | nil => simp [parseFrom_nil, pairP]
  | cons c cs ih =>
    rw [parseFrom_cons, parseFrom_cons b]
    change (liftFeed _ (b.feed q c)).bind _ = _
    cases h : b.feed q c with
    | none => rfl
    | some r => exact congrArg (put r.2) (ih r.1)

private theorem pair_left (a b : Parser) (q : a.Q) (w : List Bool) :
    (pairP a b).parseFrom (.inl (false, q)) w = (do
      let (u, v) ← undelimit w
      let s ← a.parseFrom q u
      put s (b.parse v)) := by
  cases w with
  | nil => simp [parseFrom_nil, pairP, undelimit]
  | cons c w =>
    cases c with
    | false =>
      simp only [parseFrom_cons, undelimit, pairP]
      cases h : a.finish q <;> simp [pair_right, Parser.parse, parseFrom_nil, h]
    | true =>
      cases w with
      | nil => simp [parseFrom_cons, parseFrom_nil, pairP, undelimit, put]
      | cons c w =>
        simp only [parseFrom_cons, pairP, liftFeed, Option.bind_some, undelimit]
        cases h : a.feed q c with
        | none => cases undelimit w <;> simp [put, parseFrom_cons, h]
        | some r =>
          obtain ⟨q', u⟩ := r
          have ih := pair_left a b q' w
          simp only [Option.map_some, Option.bind_some]
          change put [] (put u ((pairP a b).parseFrom (.inl (false, q')) w)) = _
          rw [ih]
          cases hu : undelimit w with
          | none => simp [put]
          | some z =>
            obtain ⟨f, t⟩ := z
            cases hf : a.parseFrom q' f <;> cases ht : b.parse t <;>
              simp [parseFrom_cons, h, hf, ht, put]
termination_by w.length

private abbrev listP (a : Parser) (term : Out) : Parser where
  Q := Option (Bool × a.Q)
  initial := none
  feed
    | some (true, q), c => liftFeed (fun z => some (false, z)) (a.feed q c)
    | s, true => some (some (true, (s.map Prod.snd).getD a.initial), [])
    | s, false => (a.finish ((s.map Prod.snd).getD a.initial)).map fun u => (none, u ++ term)
  finish
    | none => some []
    | some _ => none

private theorem list_left (a : Parser) (e : Out) (q : a.Q) (x : List Bool) :
    (listP a e).parseFrom (some (false, q)) x = (do
      let (u, v) ← undelimit x
      let s ← a.parseFrom q u
      put (s ++ e) ((listP a e).parse v)) := by
  cases x with
  | nil => simp [parseFrom_nil, listP, undelimit]
  | cons c x =>
    cases c with
    | false =>
      simp only [parseFrom_cons, undelimit, listP]
      cases h : a.finish q <;> simp [h, Parser.parse, parseFrom_nil]
    | true =>
      cases x with
      | nil => simp [parseFrom_cons, parseFrom_nil, listP, undelimit, put]
      | cons c x =>
        simp only [parseFrom_cons, listP, liftFeed, Option.bind_some, undelimit,
          Option.map_some, Option.getD_some]
        cases h : a.feed q c with
        | none => cases undelimit x <;> simp [put, parseFrom_cons, h]
        | some r =>
          obtain ⟨q', u⟩ := r
          have ih := list_left a e q' x
          simp only [Option.map_some, Option.bind_some]
          change put [] (put u ((listP a e).parseFrom (some (false, q')) x)) =
            (do let z ← (undelimit x).map (fun z => (c :: z.1, z.2))
                let s ← a.parseFrom q z.1
                put (s ++ e) ((listP a e).parse z.2))
          rw [ih]
          cases hu : undelimit x with
          | none => simp [put]
          | some z =>
            obtain ⟨f, t⟩ := z
            cases hf : a.parseFrom q' f <;> cases ht : (listP a e).parse t <;>
              simp [parseFrom_cons, h, hf, ht, put]
termination_by x.length

private def Correct {α : Type} [BitstringEncoding α] (a : Parser) (emit : α → Out) :=
  ∀ x, a.parse x = (bitDecode x).map emit

private theorem pair_correct {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    {a b : Parser} {e : α → Out} {f : β → Out} (ha : Correct a e) (hb : Correct b f) :
    Correct (pairP a b) (fun z : α × β => e z.1 ++ f z.2) := by
  intro x
  rw [Parser.parse, pair_left]
  change _ = (match undelimit x with
    | none => none
    | some (u, v) => match bitDecode (α := α) u, bitDecode (α := β) v with
      | some a, some b => some (a, b)
      | _, _ => none).map _
  cases hu : undelimit x with
  | none => rfl
  | some z =>
    obtain ⟨u, v⟩ := z
    change ((a.parse u).bind _) = _
    rw [ha, hb]
    cases h₁ : bitDecode (α := α) u <;> cases h₂ : bitDecode (α := β) v <;> simp [h₁, h₂, put]

private theorem list_correct {α : Type} [BitstringEncoding α]
    {a : Parser} {f : α → Out} (ha : Correct a f) (e : Out) :
    Correct (listP a e) (fun xs : List α => xs.flatMap (fun z => f z ++ e)) := by
  intro x
  match x with
  | [] => rfl
  | b :: t =>
    have h : (listP a e).parse (b :: t) =
        (listP a e).parseFrom (some (false, a.initial)) (b :: t) := by
      simp only [Parser.parse, parseFrom_cons]
      cases b <;> rfl
    rw [h, list_left]
    cases hu : undelimit (b :: t) with
    | none => rw [decode_list_none_of_undelimit_none (by simp) hu]; rfl
    | some z =>
      obtain ⟨u, v⟩ := z
      have hx := (undelimit_eq_some_iff _ _ _).mp hu
      have hl : v.length < (b :: t).length := by simp [hx]
      have ih := list_correct ha e v
      change (a.parse u).bind _ = _
      rw [ha, ih, hx, decode_list_delimit]
      cases bitDecode (α := α) u <;> cases bitDecode (α := List α) v <;> rfl
termination_by x => x.length
decreasing_by simp_all

private abbrev natP (tag : Bool → Event) : Parser where
  Q := Bool
  initial := false
  feed _ b := some (!b, [tag b])
  finish q := some (if q then [tag true] else [])

private theorem nat_from (tag : Bool → Event) (q : Bool) (x : List Bool) :
    (natP tag).parseFrom q x = some (x.map tag ++
      if !(x.getLast?.getD (!q)) then [tag true] else []) := by
  induction x generalizing q with
  | nil => simp [parseFrom_nil, natP]
  | cons b bs ih =>
    rw [parseFrom_cons]
    change put [tag b] ((natP tag).parseFrom (!b) bs) = _
    rw [ih]
    cases bs with
    | nil => simp [put]
    | cons c cs =>
      have hn := List.getLast?_eq_some_getLast (by simp : c :: cs ≠ [])
      simp [put, hn]

private theorem nat_correct (tag : Bool → Event) :
    Correct (natP tag) (fun n : Nat => (Computability.encodeNat n).map tag) := by
  intro x
  change (natP tag).parseFrom false x =
    some ((Computability.encodeNat (Computability.decodeNat x)).map tag)
  rw [nat_from, ← Cslib.Complexity.FramedCNF.normalizeNat_eq_encode_decode]
  cases h : x.getLast? with
  | none => simp [Cslib.Complexity.FramedCNF.normalizeNat, h]
  | some b => cases b <;> simp [Cslib.Complexity.FramedCNF.normalizeNat, h]

private def signP : Parser where
  Q := Option Bool
  initial := none
  feed
    | none, b => some (some b, [.token (.lit b)])
    | some _, _ => none
  finish q := if q.isSome then some [] else none

private theorem sign_correct : Correct signP (fun b : Bool => [.token (.lit b)]) := by
  intro x
  rcases x with _ | ⟨b, _ | ⟨c, bs⟩⟩ <;> rfl

private abbrev litP := pairP (natP (.token ∘ Sym.bit)) signP
private abbrev clauseP := listP litP []
private abbrev formulaP := listP clauseP [.token .cl]
private abbrev instanceP := pairP (natP Event.n) (pairP formulaP (natP Event.k))

private theorem lit_correct : Correct litP (fun l => (litToks l).map Event.token) := by
  intro x
  have h := pair_correct (nat_correct (Event.token ∘ Sym.bit)) sign_correct x
  rw [h]
  congr 1
  funext l
  simp [litToks]

private theorem formula_correct : Correct formulaP (fun φ => (toks φ).map Event.token) := by
  simpa [toks, clauseToks, List.map_flatMap, Function.comp_def] using
    list_correct (list_correct lit_correct []) [.token .cl]

private theorem instance_correct : Correct instanceP (fun z : MinOnesThreeSatInstance =>
    (Computability.encodeNat z.1).map Event.n ++ ((toks z.2.1).map Event.token ++
      (Computability.encodeNat z.2.2).map Event.k)) :=
  pair_correct (nat_correct _) (pair_correct formula_correct (nat_correct _))

/-! ### Polynomial-time verifier

The machine first separates the two binary bounds and the formula tokens. It scans each literal
against the variable bound and, for a marked occurrence, adds the variable to a lookup table
and decrements the weight budget. The existing SAT checker evaluates the formula on this table.
-/

namespace Verifier

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open MetaMathlibExt.TM2Recursive (bitsVal bitsVal_encodeNat)
open Cslib.Complexity

private inductive Aux
  | input | witness | revN | revK | revF | bound | budget | formula | temp
  deriving DecidableEq

private def auxList : List Aux := [.input, .witness, .revN, .revK, .revF, .bound, .budget,
  .formula, .temp]
private instance auxFinite : Fintype Aux :=
  Fintype.ofList auxList fun a => by cases a <;> decide

private abbrev K := Aux ⊕ Check.K
private abbrev Store := K → List Sym

noncomputable section

private instance stateDec : DecidableEq instanceP.Q := instanceP.dec

private def lexFeed (q : instanceP.Q) (b : Bool) := instanceP.feed q b
private def lexFinish (q : instanceP.Q) := instanceP.finish q

private inductive L
  | lex (q : instanceP.Q) | flipN | flipK | flipF
  | take (left : Fin 4)
  | word (left : Fin 4) (marked less : Bool)
  | restore (left : Fin 4) (marked : Bool)
  | sub (left : Fin 4) | refill (left : Fin 4)
  | check (label : Check.DLab ⊕ Lookup.Lab) | no
  deriving DecidableEq, Fintype

private abbrev Stmt := TM2.Stmt (fun _ : K => Sym) L Bool

-- One finite control transition can inspect stacks and emit a fixed list of symbols.
private inductive Act
  | next (l : L)
  | look (k : K) (f : Option Sym → Act)
  | drop (k : K) (a : Act)
  | emit (k : K) (syms : List Sym) (a : Act)

private def Act.eval : Act → Store → L × Store
  | .next l, S => (l, S)
  | .look k f, S => (f (S k).head?).eval S
  | .drop k a, S => a.eval (update S k (S k).tail)
  | .emit k ss a, S => a.eval (update S k (ss.reverse ++ S k))

private def switch (k : K) (f : Option Sym → Stmt) : List Sym → Stmt
  | [] => f none
  | s :: ss => .peek k (fun _ o => o == some s) <| .branch id (f (some s)) (switch k f ss)

private def syms : List Sym := [.bit false, .bit true, .lit false, .lit true, .cl,
  .val false, .val true, .dead]

private theorem mem_syms (s : Sym) : s ∈ syms := by
  cases s <;> (try rename_i b; cases b) <;> decide

private theorem switch_aux (k : K) (f : Option Sym → Stmt) (ss : List Sym)
    (S : Store) (v : Bool) (valid : ∀ s ∈ (S k).head?, s ∈ ss)
    (h : ∀ o b, TM2.stepAux (f o) b S = TM2.stepAux (f o) false S) :
    TM2.stepAux (switch k f ss) v S = TM2.stepAux (f (S k).head?) false S := by
  induction ss generalizing v with
  | nil =>
    cases ht : (S k).head? with
    | none => exact h _ _
    | some s => simp [ht] at valid
  | cons s ss ih =>
    by_cases ht : (S k).head? = some s
    · simpa [switch, TM2.stepAux, ht] using h (some s) true
    · have hne : ((S k).head? == some s) = false := beq_eq_false_iff_ne.mpr ht
      simp only [switch, TM2.stepAux, hne, id_eq, Bool.cond_false]
      apply ih
      intro z hz
      have he : z ≠ s := by rintro rfl; exact ht hz
      simpa [he] using valid z hz

private def Act.compile : Act → Stmt
  | .next l => .load (fun _ => false) (.goto fun _ => l)
  | .look k f => switch k (fun o => (f o).compile) syms
  | .drop k a => .pop k (fun v _ => v) a.compile
  | .emit k ss a => pushList k ss a.compile

private theorem compile_spec (a : Act) (v : Bool) (S : Store) :
    TM2.stepAux a.compile v S = ⟨some (a.eval S).1, false, (a.eval S).2⟩ := by
  induction a generalizing v S with
  | next => rfl
  | drop k a ih => exact ih ..
  | emit k ss a ih =>
    rw [Act.compile, stepAux_pushList]
    exact ih ..
  | look k f ih =>
    rw [Act.compile, switch_aux]
    · exact ih ..
    · exact fun s _ => mem_syms s
    · intro o b
      rw [ih, ih]

private abbrev X : K := .inl .input
private abbrev W : K := .inl .witness
private abbrev RN : K := .inl .revN
private abbrev RK : K := .inl .revK
private abbrev RF : K := .inl .revF
private abbrev N : K := .inl .bound
private abbrev D : K := .inl .budget
private abbrev F : K := .inl .formula
private abbrev U : K := .inl .temp
private abbrev T : K := .inr .T
private abbrev B : K := .inr .B
private abbrev bits (bs : List Bool) := bs.map Sym.bit

private def nBits : List Event → List Sym := List.filterMap fun e => match e with
  | .n b => some (.bit b)
  | _ => none

private def kBits : List Event → List Sym := List.filterMap fun e => match e with
  | .k b => some (.bit b)
  | _ => none

private def tokens : List Event → List Sym := List.filterMap fun e => match e with
  | .token s => some s
  | _ => none

private def collect (e : Out) (a : Act) : Act :=
  .emit RN (nBits e) (.emit RK (kBits e) (.emit RF (tokens e) (.emit T (tokens e) a)))

private def move (a b : K) (again done_ : L) : Act := .look a fun
  | none => .next done_
  | some s => .drop a (.emit b [s] (.next again))

private def ifMarked (b : Bool) (s : Sym) (a : Act) : Act :=
  if b then .emit B [s] a else a

-- For least-significant-bit-first words, each higher differing bit replaces the comparison.
private def nextLt (a b lt : Bool) : Bool := if a == b then lt else b

private def down (q : Fin 4) : Fin 4 := ⟨q.val - 1, by omega⟩

private def code : L → Act
  | .lex q => .look X fun
      | some (.bit b) => .drop X <| match lexFeed q b with
        | none => .next .no
        | some (q', out) => collect out (.next (.lex q'))
      | _ => match lexFinish q with
        | none => .next .no
        | some out => collect out (.next .flipN)
  | .flipN => move RN N .flipN .flipK
  | .flipK => move RK D .flipK .flipF
  | .flipF => move RF F .flipF (.take 3)
  | .take q => .look F fun
      | none => .next (.check (.inl .start))
      | some .cl => .drop F (.next (if q = 0 then .take 3 else .no))
      | _ => if q = 0 then .next .no else
          .look W fun o => .next (.word q (o == some (.bit true)) false)
  | .word q m lt => .look F fun
      | some (.bit b) => .drop F <| ifMarked m (.bit b) <| .look N fun
        | some (.bit c) => .drop N <| .emit U [.bit c] <| .next (.word q m (nextLt b c lt))
        | _ => .next (.word q m (nextLt b false lt))
      | some (.lit _) => .look N fun o =>
        if lt || o.isSome then .drop F <| .drop W <| ifMarked m (.val true)
          (.next (.restore (down q) m))
        else .next .no
      | _ => .next .no
  | .restore q m => move U N (.restore q m) (if m then .sub q else .take q)
  | .sub q => .look D fun
      | some (.bit false) => .drop D (.emit U [.bit true] (.next (.sub q)))
      | some (.bit true) => .drop D (.emit D [.bit false] (.next (.refill q)))
      | _ => .next .no
  | .refill q => move U D (.refill q) (.take q)
  | _ => .next .no

private def emb : SEmb (fun _ : Check.K => Sym) (fun _ : K => Sym) where
  e := .inr
  inj := Sum.inr_injective
  ι _ := Equiv.refl _

private def redirect (l : Check.DLab ⊕ Lookup.Lab) : L :=
  if l = .inl .no then .no else .check l

private def prog : L → Stmt
  | .check l => mapS emb redirect (Check.prog Machine.lkH Lookup.start l)
  | .no => .halt
  | l => (code l).compile

private theorem one {l l' : L} {S S' : Store} (v : Bool)
    (hc : prog l = (code l).compile) (he : (code l).eval S = (l', S')) :
    Run prog 1 ⟨some l, v, S⟩ ⟨some l', false, S'⟩ :=
  Run.single (by rw [hc, compile_spec, he])

-- Register snapshots used by the simulation proofs. The first three reversed streams
-- (rn, rk, rf) are transposed into n, d and f. The SAT checker reads t and b.
private structure Reg where
  x : List Sym := []
  w : List Sym := []
  rn : List Sym := []
  rk : List Sym := []
  rf : List Sym := []
  n : List Sym := []
  d : List Sym := []
  f : List Sym := []
  u : List Sym := []
  t : List Sym := []
  b : List Sym := []

private def Reg.store (s : Reg) : Store
  | .inl .input => s.x
  | .inl .witness => s.w
  | .inl .revN => s.rn
  | .inl .revK => s.rk
  | .inl .revF => s.rf
  | .inl .bound => s.n
  | .inl .budget => s.d
  | .inl .formula => s.f
  | .inl .temp => s.u
  | .inr .T => s.t
  | .inr .B => s.b
  | .inr _ => []

private abbrev cfg (l : L) (s : Reg) (v := false) : TM2.Cfg (fun _ : K => Sym) L Bool :=
  ⟨some l, v, s.store⟩

@[simp] private theorem readX (s : Reg) : s.store X = s.x := rfl

@[simp] private theorem writeX (s : Reg) (a : List Sym) :
    update s.store X a = ({s with x := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readW (s : Reg) : s.store W = s.w := rfl

@[simp] private theorem writeW (s : Reg) (a : List Sym) :
    update s.store W a = ({s with w := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readRN (s : Reg) : s.store RN = s.rn := rfl

@[simp] private theorem writeRN (s : Reg) (a : List Sym) :
    update s.store RN a = ({s with rn := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readRK (s : Reg) : s.store RK = s.rk := rfl

@[simp] private theorem writeRK (s : Reg) (a : List Sym) :
    update s.store RK a = ({s with rk := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readRF (s : Reg) : s.store RF = s.rf := rfl

@[simp] private theorem writeRF (s : Reg) (a : List Sym) :
    update s.store RF a = ({s with rf := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readN (s : Reg) : s.store N = s.n := rfl

@[simp] private theorem writeN (s : Reg) (a : List Sym) :
    update s.store N a = ({s with n := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readD (s : Reg) : s.store D = s.d := rfl

@[simp] private theorem writeD (s : Reg) (a : List Sym) :
    update s.store D a = ({s with d := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readF (s : Reg) : s.store F = s.f := rfl

@[simp] private theorem writeF (s : Reg) (a : List Sym) :
    update s.store F a = ({s with f := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readU (s : Reg) : s.store U = s.u := rfl

@[simp] private theorem writeU (s : Reg) (a : List Sym) :
    update s.store U a = ({s with u := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readT (s : Reg) : s.store T = s.t := rfl

@[simp] private theorem writeT (s : Reg) (a : List Sym) :
    update s.store T a = ({s with t := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

@[simp] private theorem readB (s : Reg) : s.store B = s.b := rfl

@[simp] private theorem writeB (s : Reg) (a : List Sym) :
    update s.store B a = ({s with b := a} : Reg).store := by
  funext k
  rcases k with k | k <;> cases k <;> rfl

private abbrev Cfg := TM2.Cfg (fun _ : K => Sym) L Bool

private def Go (cost : Nat) (c : Cfg) : Option Cfg → Prop
  | none => ∃ s : Reg, RunLe prog cost c (cfg .no s)
  | some d => RunLe prog cost c d

private theorem Go.pre {a b : Nat} {c d : Cfg} {e : Option Cfg}
    (h : RunLe prog a c d) (g : Go b d e) : Go (a + b) c e := by
  cases e with
  | none => obtain ⟨s, h'⟩ := g; exact ⟨s, h.trans h'⟩
  | some => exact h.trans g

private theorem Go.enlarge {a b : Nat} {c : Cfg} {e : Option Cfg}
    (g : Go a c e) (h : a ≤ b) : Go b c e := by
  cases e with
  | none => obtain ⟨s, h'⟩ := g; exact ⟨s, h'.mono h⟩
  | some => exact g.mono h

private def Reg.add (s : Reg) (es : Out) : Reg :=
  {s with
    rn := (nBits es).reverse ++ s.rn
    rk := (kBits es).reverse ++ s.rk
    rf := (tokens es).reverse ++ s.rf
    t := (tokens es).reverse ++ s.t}

private theorem collect_step (s : Reg) (e : Out) (l : L) :
    (collect e (.next l)).eval s.store = (l, (s.add e).store) := by
  simp [Act.eval, collect, Reg.add]

private theorem lexer_run (q : instanceP.Q) (x : List Bool) (s : Reg) (v : Bool) :
    Go (x.length + 1) (cfg (.lex q) {s with x := bits x} v)
      ((instanceP.parseFrom q x).map fun e => cfg .flipN (({s with x := []} : Reg).add e)) := by
  induction x generalizing q s v with
  | nil =>
    rw [parseFrom_nil]
    cases h : instanceP.finish q with
    | none =>
      change lexFinish q = none at h
      refine ⟨{s with x := []}, (one v rfl ?_).le (by rfl)⟩
      simp [code, Act.eval, h]
    | some e =>
      change lexFinish q = some e at h
      apply Run.le _ (le_refl 1)
      apply one v rfl
      simp [code, Act.eval, h, collect_step]
  | cons b bs ih =>
    rw [parseFrom_cons]
    cases h : instanceP.feed q b with
    | none =>
      change lexFeed q b = none at h
      refine ⟨{s with x := bits bs}, (one v rfl ?_).le (by simp)⟩
      simp [code, Act.eval, h]
    | some r =>
      obtain ⟨q', u⟩ := r
      change lexFeed q b = some (q', u) at h
      let s' := ({s with x := bits bs} : Reg).add u
      have r : Run prog 1 (cfg (.lex q) {s with x := bits (b :: bs)} v) (cfg (.lex q') s') := by
        apply one v rfl
        simp [code, Act.eval, h, collect_step, s']
      have rest := ih q' s' false
      cases hr : instanceP.parseFrom q' bs <;>
        simpa [hr, put, s', Reg.add, cfg, Nat.add_comm, tokens, nBits, kBits,
          List.append_assoc] using Go.pre (r.le le_rfl) rest

private theorem move_run {a b : K} {l next : L} (hc : prog l = (code l).compile)
    (he : code l = move a b l next) (hab : a ≠ b) (S : Store)
    (from_ to_ : List Sym) (v : Bool) :
    Run prog (from_.length + 1) ⟨some l, v, update (update S a from_) b to_⟩
      ⟨some next, false, update (update S a []) b (from_.reverse ++ to_)⟩ := by
  induction from_ generalizing to_ v with
  | nil =>
    apply one v hc
    simp [he, move, Act.eval, hab, update_of_ne]
  | cons x xs ih =>
    have h : Run prog 1 ⟨some l, v, update (update S a (x :: xs)) b to_⟩
        ⟨some l, false, update (update S a xs) b (x :: to_)⟩ := by
      apply one v hc
      simp [he, move, Act.eval, hab.symm, update_comm hab]
    simpa [List.append_assoc, Nat.add_comm] using h.trans (ih (x :: to_) false)

private def limit (p : Parser) : Nat :=
  (Finset.univ.sup fun qb : p.Q × Bool => (((p.feed qb.1 qb.2).map Prod.snd).getD []).length) +
  (Finset.univ.sup fun q : p.Q => ((p.finish q).getD []).length)

private theorem parse_bound (p : Parser) (q : p.Q) (x : List Bool) {es : Out}
    (hx : p.parseFrom q x = some es) : es.length ≤ limit p * (x.length + 1) := by
  induction x generalizing q es with
  | nil =>
    rw [parseFrom_nil] at hx
    have h := Finset.le_sup (f := fun s : p.Q => ((p.finish s).getD []).length) (Finset.mem_univ q)
    simpa [limit, hx] using h.trans (Nat.le_add_left _ _)
  | cons b bs ih =>
    rw [parseFrom_cons] at hx
    obtain ⟨⟨q', u⟩, h, h'⟩ := Option.bind_eq_some_iff.mp hx
    obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h'
    have hstep := Finset.le_sup (f := fun qb : p.Q × Bool =>
      (((p.feed qb.1 qb.2).map Prod.snd).getD []).length) (Finset.mem_univ (q, b))
    have hu : u.length ≤ limit p := by simpa [limit, h] using hstep.trans (Nat.le_add_right _ _)
    have htail := ih q' hw
    simp only [List.length_cons, List.length_append, Nat.mul_succ] at *
    omega

-- Subtraction keeps the width of the original budget and rejects a borrow past its last bit.
private def predBits : List Bool → Option (List Bool)
  | [] => none
  | true :: bs => some (false :: bs)
  | false :: bs => (predBits bs).map (true :: ·)

private theorem pred_spec (bs : List Bool) :
    match predBits bs with
    | none => bitsVal bs = 0
    | some cs => bitsVal bs = bitsVal cs + 1 ∧ cs.length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true =>
      simp only [predBits, bitsVal, List.foldr_cons, Bool.cond_true, Bool.cond_false,
        Nat.add_zero, List.length_cons, and_self]
    | false =>
      cases h : predBits bs with
      | none => simpa [predBits, h, bitsVal] using ih
      | some cs =>
        rw [h] at ih
        simp only [predBits, h, Option.map_some, bitsVal, List.foldr_cons, Bool.cond_true,
          Bool.cond_false, Nat.add_zero, List.length_cons] at *
        omega

private theorem sub_run (q : Fin 4) (d u : List Bool) (s : Reg) :
    Go (2 * d.length + u.length + 2) (cfg (.sub q) {s with d := bits d, u := bits u})
      ((predBits d).map fun r => cfg (.take q) {s with d := bits (u.reverse ++ r), u := []}) := by
  induction d generalizing u with
  | nil =>
    refine ⟨{s with d := [], u := bits u}, (one false rfl ?_).le (by simp)⟩
    simp [code, Act.eval]
  | cons b d ih =>
    cases b with
    | true =>
      have h₁ : Run prog 1 (cfg (.sub q) {s with d := bits (true :: d), u := bits u})
          (cfg (.refill q) {s with d := bits (false :: d), u := bits u}) := by
        apply one false rfl; simp [code, Act.eval]
      have h₂ := move_run (a := U) (b := D) (l := .refill q) rfl rfl (by decide)
        s.store (bits u) (bits (false :: d)) false
      simp only [writeU, writeD, List.length_map, ← List.map_reverse, ← List.map_append] at h₂
      exact (h₁.trans h₂).le (by simp; omega)
    | false =>
      have h₁ : Run prog 1 (cfg (.sub q) {s with d := bits (false :: d), u := bits u})
          (cfg (.sub q) {s with d := bits d, u := bits (true :: u)}) := by
        apply one false rfl; simp [code, Act.eval]
      have h := Go.pre (h₁.le le_rfl) (ih (true :: u))
      apply Go.enlarge (b := 2 * (false :: d).length + u.length + 2)
        (a := 1 + (2 * d.length + (true :: u).length + 2)) _ (by simp; omega)
      cases he : predBits d <;> simpa [predBits, he, List.append_assoc] using h

private def cmp (bs ns : List Bool) (lt : Bool) : Bool :=
  match bs with
  | [] => lt
  | b :: bs => cmp bs ns.tail (nextLt b (ns.headD false) lt)

private def Normal (ns : List Bool) := ns = [] ∨ ns.getLast? = some true

private theorem normal_tail {b : Bool} {ns : List Bool} (h : Normal (b :: ns)) : Normal ns := by
  cases ns with
  | nil => exact Or.inl rfl
  | cons c ns => simpa [Normal] using h

private theorem pos_of_normal {ns : List Bool} (hn : Normal ns) (hne : ns ≠ []) :
    0 < bitsVal ns := by
  induction ns with
  | nil => simp at hne
  | cons c ns ih =>
    cases ns with
    | nil => simp [Normal] at hn; simp [hn, bitsVal]
    | cons b ts =>
      have hh := ih (normal_tail hn) (by simp)
      change 0 < 2 * bitsVal (b :: ts) + _
      omega

private theorem cmp_correct (bs ns : List Bool) (hn : Normal ns) (lt : Bool) :
    (cmp bs ns lt || !(ns.drop bs.length).isEmpty) = true ↔
      bitsVal bs < bitsVal ns ∨ (bitsVal bs = bitsVal ns ∧ lt) := by
  induction bs generalizing ns lt with
  | nil =>
    by_cases he : ns = []
    · simp [he, cmp, bitsVal]
    · have hp := pos_of_normal hn he
      simp [cmp, he, show bitsVal [] = 0 by rfl, hp]
  | cons b bs ih =>
    cases ns with
    | nil =>
      simp only [List.length_cons, List.drop_nil, List.isEmpty_nil, Bool.not_true,
        Bool.or_false, cmp, List.tail_nil, List.headD_nil]
      have h := ih [] (Or.inl rfl) (nextLt b false lt)
      cases b <;> simp [nextLt, bitsVal] at * <;> omega
    | cons c ns =>
      simp only [List.length_cons, List.drop_succ_cons, cmp, List.tail_cons, List.headD_cons]
      rw [ih ns (normal_tail hn)]
      cases b <;> cases c <;> simp [bitsVal, nextLt] <;> omega

private theorem word_bits (q : Fin 4) (m lt : Bool) (bs ns : List Bool) (f u t : List Sym)
    (s : Reg) :
    Run prog bs.length (cfg (.word q m lt)
      {s with f := bits bs ++ f, n := bits ns, u := u, b := t})
      (cfg (.word q m (cmp bs ns lt)) {s with
        f := f
        n := bits (ns.drop bs.length)
        u := (bits (ns.take bs.length)).reverse ++ u
        b := (if m then (bits bs).reverse else []) ++ t}) := by
  induction bs generalizing lt ns u t with
  | nil => simpa [cmp] using Run.zero (M := prog) (cfg (.word q m lt)
        {s with f := f, n := bits ns, u := u, b := t})
  | cons b bs ih =>
    let t' := if m then Sym.bit b :: t else t
    cases ns with
    | nil =>
      have h : Run prog 1
          (cfg (.word q m lt) {s with f := bits (b :: bs) ++ f, n := [], u := u, b := t})
          (cfg (.word q m (nextLt b false lt))
            {s with f := bits bs ++ f, n := [], u := u, b := t'}) := by
        apply one false rfl; cases m <;> simp [code, Act.eval, ifMarked, t']
      have r := h.trans (ih _ [] u t')
      cases m <;> simpa [cmp, t', List.append_assoc, Nat.add_comm] using r
    | cons c ns =>
      have h : Run prog 1
          (cfg (.word q m lt)
            {s with f := bits (b :: bs) ++ f, n := bits (c :: ns), u := u, b := t})
          (cfg (.word q m (nextLt b c lt))
            {s with f := bits bs ++ f, n := bits ns, u := Sym.bit c :: u, b := t'}) := by
        apply one false rfl; cases m <;> simp [code, Act.eval, ifMarked, t']
      have r := h.trans (ih _ ns (.bit c :: u) t')
      cases m <;> simpa [cmp, t', List.append_assoc, Nat.add_comm] using r

private theorem Go.bind {α : Type} {r : Option α} {f : α → Cfg} {g : α → Option Cfg}
    {c : Cfg} {a b : Nat} (h : Go a c (r.map f))
    (h' : ∀ v, r = some v → Go b (f v) (g v)) :
    Go (a + b) c (r.bind g) := by
  cases r with
  | none => exact Go.enlarge h (Nat.le_add_right ..)
  | some v => exact Go.pre h (h' v rfl)

private structure Cursor where
  w : List Bool
  d : List Bool
  table : List Sym

private def Cursor.state (c : Cursor) (s : Reg) (f : List Sym) (ns : List Bool) : Reg :=
  {s with w := bits c.w, d := bits c.d, b := c.table, f := f, n := bits ns, u := []}

private def entry (z : Nat) : List Sym :=
  .val true :: (bits (Computability.encodeNat z)).reverse

-- An absent witness bit is false. A present true bit consumes one unit of the budget.
private def visit (n z : Nat) (c : Cursor) : Option Cursor :=
  if z < n then
    if c.w.headD false then
      (predBits c.d).map fun d => ⟨c.w.tail, d, entry z ++ c.table⟩
    else some ⟨c.w.tail, c.d, c.table⟩
  else none

private theorem visit_run (q : Fin 4) (l : Nat × Bool) (n : Nat) (c : Cursor)
    (s : Reg) (tail_ : List Sym) :
    Go (2 * (Computability.encodeNat l.1).length + 2 * c.d.length + 6)
      (cfg (.take q) (c.state s (litToks l ++ tail_) (Computability.encodeNat n)))
      ((if q = 0 then none else visit n l.1 c).map fun c' =>
        cfg (.take (down q)) (c'.state s tail_ (Computability.encodeNat n))) := by
  let bs := Computability.encodeNat l.1
  let ns := Computability.encodeNat n
  let start := c.state s (litToks l ++ tail_) ns
  have head (t : L) (he : (if q = 0 then L.no else L.word q (c.w.headD false) false) = t) :
      Run prog 1 (cfg (.take q) start) (cfg t start) := by
    apply one false rfl
    simp only [code, Act.eval, start, Cursor.state, readF, litToks, List.append_assoc]
    cases hb : Computability.encodeNat l.1 <;> cases hw : c.w with
    | nil => by_cases hq : q = 0 <;> simpa [hq, hw, hb, Act.eval] using he
    | cons b w => cases b <;> by_cases hq : q = 0 <;> simpa [hq, hw, hb, Act.eval] using he
  by_cases hq : q = 0
  · rw [ite_eq_left hq]
    change ∃ s', RunLe prog (2 * bs.length + 2 * c.d.length + 6) _ (cfg .no s')
    exact ⟨start, (head .no (by simp [hq])).le
      (show 1 ≤ 2 * bs.length + 2 * c.d.length + 6 by omega)⟩
  simp only [hq, ite_false]
  let m := c.w.headD false
  have r₀ := head (.word q m false) (by simp [hq, m])
  let rest := Sym.lit l.2 :: tail_
  let base := c.state s tail_ ns
  let consumed := ns.take bs.length
  let left := ns.drop bs.length
  let tbl := (if m then (bits bs).reverse else []) ++ c.table
  let mid : Reg := {base with f := rest, n := bits left, u := (bits consumed).reverse, b := tbl}
  have r₁ : Run prog (1 + bs.length) (cfg (.take q) start)
      (cfg (.word q m (cmp bs ns false)) mid) := by
    apply r₀.trans
    simpa [start, base, mid, Cursor.state, litToks, rest, bs, ns, consumed, left, tbl] using
      word_bits q m false bs ns rest [] c.table base
  have hnorm : Normal ns := (encodeNat_decodeNat_eq_iff ns).mp (by simp [ns])
  have htest : (cmp bs ns false || (bits left).head?.isSome) = decide (l.1 < n) := by
    apply Bool.eq_iff_iff.mpr
    simpa [bs, ns, left, bitsVal_encodeNat] using cmp_correct bs ns hnorm false
  by_cases hz : l.1 < n
  · have htest' : (cmp bs ns false || (bits left).head?.isSome) = true := htest.trans (by simp [hz])
    let tbl' := if m then entry l.1 ++ c.table else c.table
    let after : Reg := {mid with f := tail_, w := bits c.w.tail, b := tbl'}
    have r₂ : Run prog 1 (cfg (.word q m (cmp bs ns false)) mid)
        (cfg (.restore (down q) m) after) := by
      apply one false rfl
      simp only [code, Act.eval, mid, readF, rest, List.head?_cons, readN, List.head?_map] at *
      rw [ite_eq_left htest']
      cases hm : m <;> simp [Act.eval, ifMarked, after, mid, base, Cursor.state, tbl,
        tbl', entry, hm, bs, List.map_tail]
    let ready : Reg := {after with n := bits ns, u := []}
    have r₃ : Run prog (consumed.length + 1) (cfg (.restore (down q) m) after)
        (cfg (if m then .sub (down q) else .take (down q)) ready) := by
      have h := move_run (a := U) (b := N) (l := .restore (down q) m) rfl rfl (by decide)
        after.store (bits consumed).reverse (bits left) false
      simpa [writeU, writeN, ready, after, mid, consumed, left, ← List.map_append] using h
    have rr := (r₁.trans r₂).trans r₃
    have hlen : consumed.length ≤ bs.length := by simp [consumed]
    have hb : bs.length = (Computability.encodeNat l.1).length := rfl
    cases hm : m with
    | false =>
      have h' : visit n l.1 c = some ⟨c.w.tail, c.d, c.table⟩ := by
        simp only [visit, hz, ↓reduceIte]
        change (if m then _ else _) = _
        simp only [hm, Bool.false_eq_true, ↓reduceIte]
      rw [h']
      apply Run.le _ (show 1 + bs.length + 1 + (consumed.length + 1) ≤ _ by omega)
      simpa [hm, ready, after, mid, base, start, ns, Cursor.state, tbl'] using rr
    | true =>
      simp only [hm, ite_true] at rr
      have sub := sub_run (down q) c.d [] ready
      have h := Go.pre (rr.le le_rfl) sub
      apply Go.enlarge (a := 1 + bs.length + 1 + (consumed.length + 1) + (2 * c.d.length + 0 + 2))
        _ (by omega)
      have hvisit : visit n l.1 c =
          (predBits c.d).map fun d => ⟨c.w.tail, d, entry l.1 ++ c.table⟩ := by
        simp only [visit, hz, ↓reduceIte]
        change (if m then _ else _) = _
        simp only [hm, ↓reduceIte]
      rw [hvisit]
      cases hd : predBits c.d <;> simpa [hd, hm, ready, after, mid, base, start, ns, Cursor.state,
        tbl'] using h
  · have htest' : (cmp bs ns false || (bits left).head?.isSome) = false :=
      htest.trans (by simp [hz])
    have rr : Run prog 1 (cfg (.word q m (cmp bs ns false)) mid) (cfg .no mid) := by
      apply one false rfl
      simp only [code, Act.eval, mid, readF, rest, List.head?_cons, readN,
        htest', Bool.false_eq_true,
        ite_false]
    simp only [visit, hz, ite_false]
    exact ⟨mid, (r₁.trans rr).le
      (show 1 + bs.length + 1 ≤ 2 * bs.length + 2 * c.d.length + 6 by omega)⟩

private abbrev Item := Option (Nat × Bool)
private def items (φ : CNF) : List Item := φ.flatMap fun c => c.map some ++ [none]

private def chars : Item → List Sym
  | none => [.cl]
  | some l => litToks l

private def names (is : List Item) : List Nat := is.filterMap fun o => o.map Prod.fst

private def advance (q : Fin 4) (i : Item) : Fin 4 :=
  if i.isSome then down q else 3

private def allowed (q : Fin 4) (i : Item) : Bool := (q != 0) == i.isSome

private def widths (q : Fin 4) : List Item → Bool
  | [] => true
  | i :: is => allowed q i && widths (advance q i) is

private def actItem (n : Nat) (q : Fin 4) (c : Cursor) (i : Item) : Option Cursor :=
  if allowed q i then i.elim (some c) (fun l => visit n l.1 c) else none

private def scan (n : Nat) (q : Fin 4) (c : Cursor) : List Item → Option (Fin 4 × Cursor)
  | [] => some (q, c)
  | i :: is => (actItem n q c i).bind fun c' => scan n (advance q i) c' is

private theorem act_length {n : Nat} {q : Fin 4} {c c' : Cursor} {i : Item}
    (h : actItem n q c i = some c') : c'.d.length = c.d.length := by
  unfold actItem at h
  split at h <;> try contradiction
  cases i with
  | none => simpa using congrArg (fun o : Option Cursor => (o.map (·.d.length))) h.symm
  | some l =>
    change visit n l.1 c = some c' at h
    unfold visit at h
    split at h <;> try contradiction
    split at h
    · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      have hs := pred_spec c.d
      rw [hd] at hs
      exact hs.2
    · cases h; rfl

private theorem item_run (n : Nat) (q : Fin 4) (c : Cursor) (i : Item) (s : Reg)
    (r : List Sym) :
    Go ((2 * c.d.length + 8) * (chars i).length)
      (cfg (.take q) (c.state s (chars i ++ r) (Computability.encodeNat n)))
      ((actItem n q c i).map fun c' => cfg (.take (advance q i))
        (c'.state s r (Computability.encodeNat n))) := by
  cases i with
  | none =>
    have step : Run prog 1 (cfg (.take q) (c.state s (chars none ++ r) (Computability.encodeNat n)))
        (cfg (if q = 0 then .take 3 else .no) (c.state s r (Computability.encodeNat n))) := by
      apply one false rfl
      simp [code, Act.eval, Cursor.state, chars]
    by_cases h : q = 0
    · simp only [h, ↓reduceIte] at step
      simpa [actItem, allowed, advance, h, chars, Go] using
        step.le (show 1 ≤ 2 * c.d.length + 8 by omega)
    · rw [show actItem n q c none = none by simp [actItem, allowed, h]]
      refine ⟨c.state s r (Computability.encodeNat n), ?_⟩
      simpa [h, chars] using step.le (show 1 ≤ 2 * c.d.length + 8 by omega)
  | some l =>
    have hh := visit_run q l n c s r
    have hb : 2 * (Computability.encodeNat l.1).length + 2 * c.d.length + 6 ≤
        (2 * c.d.length + 8) * (chars (some l)).length := by
      simp [chars, litToks, Nat.mul_succ, Nat.add_mul]
      nlinarith
    by_cases h : q = 0 <;>
      simpa [actItem, allowed, advance, h, chars] using Go.enlarge hh hb

private theorem scan_run (n : Nat) (q : Fin 4) (c : Cursor) (is : List Item) (s : Reg) :
    Go ((2 * c.d.length + 8) * (is.flatMap chars).length)
      (cfg (.take q) (c.state s (is.flatMap chars) (Computability.encodeNat n)))
      ((scan n q c is).map fun r =>
        cfg (.take r.1) (r.2.state s [] (Computability.encodeNat n))) := by
  induction is generalizing q c with
  | nil => exact (Run.zero _).le (by simp)
  | cons i is ih =>
    have h₁ := item_run n q c i s (is.flatMap chars)
    let g := fun c' => (scan n (advance q i) c' is).map
      fun r => cfg (.take r.1) (r.2.state s [] (Computability.encodeNat n))
    have h₂ (c') (h : actItem n q c i = some c') :
        Go ((2 * c.d.length + 8) * (is.flatMap chars).length)
          (cfg (.take (advance q i)) (c'.state s (is.flatMap chars) (Computability.encodeNat n)))
          (g c') := by simpa [g, act_length h] using ih (advance q i) c'
    simpa [scan, g, List.flatMap_cons, Nat.mul_add, Option.map_bind] using Go.bind h₁ h₂

private theorem chars_items (φ : CNF) : (items φ).flatMap chars = toks φ := by
  simp [items, chars, toks, List.flatMap_assoc, List.flatMap_map]
  rfl

private theorem names_items (φ : CNF) : names (items φ) = varsOf φ := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [items, List.flatMap_cons, names, List.filterMap_append] at *
    simp [ih, varsOf, List.filterMap_map]

private theorem widths_clause (q : Fin 4) (c : CNFClause) (is : List Item) :
    widths q (c.map some ++ none :: is) = (decide (c.length = q.val) && widths 3 is) := by
  induction c generalizing q with
  | nil => fin_cases q <;> rfl
  | cons l c ih =>
    simp only [List.map_cons, List.cons_append, widths, advance, Option.isSome_some,
      ↓reduceIte, ih, List.length_cons]
    fin_cases q <;> simp [allowed, down]; rfl

private theorem widths_items (φ : CNF) :
    widths 3 (items φ) = φ.all (fun c => c.length == 3) := by
  induction φ with
  | nil => rfl
  | cons c φ ih =>
    simp only [items, List.flatMap_cons, List.append_assoc, List.cons_append, List.nil_append] at *
    by_cases he : c.length = 3 <;> simp [widths_clause, ih, he]

private def rows (zs : List Nat) : List Ent :=
  zs.map fun z => (Computability.encodeNat z, some true)

private theorem tbl_cons (z : Nat) (zs : List Nat) :
    tblStk (rows (z :: zs)) = tblStk (rows zs) ++ entry z := by
  simp [tblStk, rows, entry, entToks, markOf]

private theorem live_rows (zs : List Nat) (x : Nat) :
    liveVal (rows zs) (Computability.encodeNat x) = zs.contains x := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    by_cases hz : z = x
    · simp [liveVal, rows, hz]
    · simpa [liveVal, rows, encodeNat_inj, hz, Ne.symm hz] using ih

private def ScanSpec (n : Nat) (q : Fin 4) (c : Cursor) (is : List Item) : Prop :=
  widths q is ∧ (∀ z ∈ names is, z < n) ∧
    (selected (names is) c.w).length ≤ bitsVal c.d

private theorem scan_spec (n : Nat) (q : Fin 4) (c : Cursor) (is : List Item) :
    (scan n q c is).isSome = true ↔ ScanSpec n q c is := by
  induction is generalizing q c with
  | nil => simp [scan, ScanSpec, widths, names, selected]
  | cons i is ih =>
    cases i with
    | none =>
      by_cases hq : q = 0 <;> simp [scan, ScanSpec, actItem, widths, allowed, advance,
        names, hq, ih, ScanSpec] at *
    | some l =>
      by_cases hq : q = 0
      · simp [scan, ScanSpec, actItem, widths, allowed, hq]
      by_cases hz : l.1 < n
      · cases hw : c.w with
        | nil =>
          simpa [scan, ScanSpec, actItem, widths, allowed, advance, hq, visit, hz, hw,
            names, selected] using ih (down q) ⟨[], c.d, c.table⟩
        | cons b w =>
          cases b with
          | false =>
            simpa [scan, ScanSpec, actItem, widths, allowed, advance, hq, visit, hz, hw,
              names, selected] using ih (down q) ⟨w, c.d, c.table⟩
          | true =>
            have hs := pred_spec c.d
            cases hd : predBits c.d with
            | none =>
              rw [hd] at hs
              simp [scan, ScanSpec, actItem, widths, allowed, advance, hq, visit, hz, hw,
                names, selected, hd, hs]
            | some d =>
              rw [hd] at hs
              simpa [scan, ScanSpec, actItem, widths, allowed, advance, hq, visit, hz, hw,
                names, selected, hd, hs.1] using ih (down q) ⟨w, d, entry l.1 ++ c.table⟩
      · simp [scan, ScanSpec, actItem, widths, allowed, advance, hq, visit, hz, names]

-- After the scan, table entries appear in reverse occurrence order on the checker stack.
private theorem scan_table {n : Nat} {q : Fin 4} {c : Cursor} {is : List Item}
    {r : Fin 4 × Cursor} (h : scan n q c is = some r) :
    r.2.table = tblStk (rows (selected (names is) c.w)) ++ c.table := by
  induction is generalizing q c with
  | nil => cases h; rfl
  | cons i is ih =>
    obtain ⟨c', ha, hr⟩ := Option.bind_eq_some_iff.mp h
    rw [ih hr]
    unfold actItem at ha
    split at ha <;> try contradiction
    cases i with
    | none => cases ha; rfl
    | some l =>
      change visit n l.1 c = some c' at ha
      unfold visit at ha
      split at ha <;> try contradiction
      cases hw : c.w with
      | nil =>
        simp only [hw, List.headD_nil, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq] at ha
        cases ha
        cases hnames : names is <;> simp [names, selected, hw] at *
      | cons b w =>
        cases b with
        | false =>
          simp only [hw, List.headD_cons, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at ha
          cases ha
          rfl
        | true =>
          simp only [hw, List.headD_cons, ↓reduceIte] at ha
          obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp ha
          simp [names, selected, tbl_cons, List.append_assoc]

private theorem table_bound (is : List Item) (w : List Bool) :
    (tblStk (rows (selected (names is) w))).length ≤ (is.flatMap chars).length := by
  induction is generalizing w with
  | nil => rfl
  | cons i is ih =>
    cases i with
    | none => simpa [names, chars, Nat.add_comm] using (ih w).trans (Nat.le_add_left _ 1)
    | some l =>
      cases w with
      | nil => simp [names, selected, rows, tblStk]
      | cons b w =>
        cases b
        · simpa [names, selected] using (ih w).trans (Nat.le_add_left _ (chars (some l)).length)
        · simp only [names, List.filterMap_cons, Option.map_some, selected, ↓reduceIte, tbl_cons,
            List.length_append, entry, List.length_cons, List.length_reverse, List.length_map,
            List.flatMap_cons, chars, litToks, List.length_nil]
          have := ih w
          unfold names at this
          omega

private theorem range_iff (n : Nat) (φ : CNF) :
    (∀ z ∈ varsOf φ, z < n) ↔ ∀ c ∈ φ, ∀ l ∈ c, l.1 < n := by
  simp [varsOf]
  grind

private def startCur (k : Nat) (w : List Bool) : Cursor := ⟨w, Computability.encodeNat k, []⟩

private theorem scan_ok (n k : Nat) (φ : CNF) (w : List Bool) :
    (scan n 3 (startCur k w) (items φ)).isSome =
      (well n φ && decide ((selected (varsOf φ) w).length ≤ k)) := by
  apply Bool.eq_iff_iff.mpr
  rw [scan_spec]
  simp only [ScanSpec, widths_items, names_items, startCur, bitsVal_encodeNat, range_iff,
    well, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq]
  grind

private abbrev yes : L := .check (.inl .yes)

private def Done (cost : Nat) (c : Cfg) (r : Bool) : Prop :=
  ∃ v S, RunLe prog cost c ⟨some (if r then yes else .no), v, S⟩

private theorem Done.pre {a b : Nat} {c d : Cfg} {r : Bool}
    (hr : RunLe prog a c d) (h : Done b d r) : Done (a + b) c r := by
  obtain ⟨v, S, hs⟩ := h
  exact ⟨v, S, hr.trans hs⟩

private theorem Done.mono {a b : Nat} {c : Cfg} {r : Bool} (h : Done a c r) (hb : a ≤ b) :
    Done b c r := by
  obtain ⟨v, S, hr⟩ := h
  exact ⟨v, S, hr.mono hb⟩

private theorem checker_run (φ : CNF) (es : List Ent) (s : Reg)
    (ht : s.t = (toks φ).reverse) (hb : s.b = tblStk es) :
    Done ((toks φ).length * (8 * (tblStk es).length + 9) + 1)
      (cfg (.check (.inl .start)) s) (checkSpec φ es) := by
  let S := fun k : Check.K => s.store (.inr k)
  have hag : Agree emb S s.store := by intro k; simp [S, emb]
  have hm : Embeds emb redirect (Check.prog Machine.lkH Lookup.start) prog := by
    intro l
    by_cases h : l = .inl .no
    · subst h; right; rfl
    · left; simp [redirect, h, prog]
  obtain ⟨v, S', hr⟩ := Check.run Machine.lookupSpec φ es false S ht hb rfl rfl rfl rfl rfl rfl
  obtain ⟨S'', h, _, _⟩ := runLe_embed redirect hm hr hag
  refine ⟨v, S'', ?_⟩
  cases he : checkSpec φ es <;> simpa [he, redirect, cfg, Nat.add_assoc] using h

private def project (n k : Nat) (φ : CNF) : Out :=
  (Computability.encodeNat n).map Event.n ++ ((toks φ).map Event.token ++
    (Computability.encodeNat k).map Event.k)

private theorem project_blocks (n k : Nat) (φ : CNF) :
    nBits (project n k φ) = bits (Computability.encodeNat n) ∧
    kBits (project n k φ) = bits (Computability.encodeNat k) ∧ tokens (project n k φ) = toks φ := by
  simp [nBits, kBits, tokens, project, List.filterMap_map]

private def magnitude (x : List Bool) := limit instanceP * (x.length + 1)

-- Both the scan and the final table lookups are quadratic in the emitted token bound.
private def totalPoly : Polynomial Nat :=
  let y := Polynomial.C (limit instanceP) * (Polynomial.X + 1)
  Polynomial.X + Polynomial.C 8 + Polynomial.C 24 * (y + 1) ^ 2

-- Compose parsing, initialization, the budget scan and the shared SAT checker.
private theorem verified (x w : List Bool) :
    Done (totalPoly.eval (x.length + w.length))
      (cfg (.lex instanceP.initial) {x := bits x, w := bits w}) (result x w) := by
  let zero : Reg := {w := bits w}
  have lex := lexer_run instanceP.initial x zero false
  have hparse := instance_correct x
  change instanceP.parseFrom instanceP.initial x =
    (bitDecode (α := MinOnesThreeSatInstance) x).map _ at hparse
  rw [hparse] at lex
  let y := magnitude x
  have ht : x.length + 8 + 24 * (y + 1) ^ 2 ≤ totalPoly.eval (x.length + w.length) := by
    simp only [totalPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one, y, magnitude]
    gcongr <;> exact Nat.le_add_right _ _
  cases hd : bitDecode (α := MinOnesThreeSatInstance) x with
  | none =>
    rw [hd] at lex
    obtain ⟨s, hr⟩ := lex
    refine ⟨false, s.store, ?_⟩
    simpa [result, hd, cfg, zero] using hr.mono
      (show x.length + 1 ≤ totalPoly.eval (x.length + w.length) by omega)
  | some z =>
    obtain ⟨n, φ, k⟩ := z
    let es := project n k φ
    have he : instanceP.parseFrom instanceP.initial x = some es := by
      simpa [hd, es, project, List.append_assoc] using hparse
    have size : es.length ≤ y := parse_bound _ _ _ he
    have hn : (Computability.encodeNat n).length ≤ y := by
      simp [es, project] at size
      simp only [BinaryNatEncoding.length_encodeNat]
      omega
    have hk : (Computability.encodeNat k).length ≤ y := by
      simp [es, project] at size
      simp only [BinaryNatEncoding.length_encodeNat]
      omega
    have hf : (toks φ).length ≤ y := by simp [es, project] at size; omega
    let ns := Computability.encodeNat n
    let ds := Computability.encodeNat k
    let ts := toks φ
    let s₁ : Reg := {zero with
      rn := (bits ns).reverse, rk := (bits ds).reverse, rf := ts.reverse, t := ts.reverse}
    let s₂ : Reg := {s₁ with rn := [], n := bits ns}
    let s₃ : Reg := {s₂ with rk := [], d := bits ds}
    let s₄ : Reg := {s₃ with rf := [], f := ts}
    have blocks := project_blocks n k φ
    have r₁ : RunLe prog (x.length + 1)
        (cfg (.lex instanceP.initial) {x := bits x, w := bits w}) (cfg .flipN s₁) := by
      rw [hd] at lex
      change RunLe prog _ _ (cfg .flipN (zero.add es)) at lex
      simpa [es, Reg.add, blocks, s₁, zero, ts, ns, ds] using lex
    have r₂ : Run prog (ns.length + 1) (cfg .flipN s₁) (cfg .flipK s₂) := by
      simpa [s₁, s₂] using move_run (a := RN) (b := N) (l := .flipN) rfl rfl (by decide)
        s₁.store (bits ns).reverse [] false
    have r₃ : Run prog (ds.length + 1) (cfg .flipK s₂) (cfg .flipF s₃) := by
      simpa [s₂, s₃] using move_run (a := RK) (b := D) (l := .flipK) rfl rfl (by decide)
        s₂.store (bits ds).reverse [] false
    have r₄ : Run prog (ts.length + 1) (cfg .flipF s₃) (cfg (.take 3) s₄) := by
      simpa [s₃, s₄] using move_run (a := RF) (b := F) (l := .flipF) rfl rfl (by decide)
        s₃.store ts.reverse [] false
    have pre := ((r₁.trans (r₂.le le_rfl)).trans (r₃.le le_rfl)).trans (r₄.le le_rfl)
    let c := startCur k w
    have walk := scan_run n 3 c (items φ) s₄
    rw [chars_items] at walk
    have ok := scan_ok n k φ w
    let cost := x.length + 1 + (ns.length + 1) + (ds.length + 1) + (ts.length + 1) +
      (2 * ds.length + 8) * ts.length
    have hbudget : cost + 1 + (ts.length * (8 * ts.length + 9) + 1) ≤
        totalPoly.eval (x.length + w.length) := by
      apply le_trans _ ht
      change ns.length ≤ y at hn
      change ds.length ≤ y at hk
      change ts.length ≤ y at hf
      unfold cost
      calc
        _ ≤ x.length + 1 + (y + 1) + (y + 1) + (y + 1) + (2 * y + 8) * y + 1 +
            (y * (8 * y + 9) + 1) := by gcongr
        _ ≤ _ := by nlinarith
    cases hsc : scan n 3 c (items φ) with
    | none =>
      rw [hsc] at walk
      obtain ⟨s, hr⟩ := walk
      have hno : result x w = false := by
        change scan n 3 c (items φ) = none at hsc
        rw [show startCur k w = c from rfl, hsc] at ok
        simp [result, hd, ← ok]
      rw [hno]
      refine ⟨_, _, (pre.trans hr).mono ?_⟩
      change cost ≤ _
      omega
    | some r =>
      rw [hsc] at walk
      have rt := scan_table hsc
      simp only [c, startCur, names_items, List.append_nil] at rt
      let es' := rows (selected (varsOf φ) w)
      let endS := r.2.state s₄ [] ns
      have step : Run prog 1 (cfg (.take r.1) endS) (cfg (.check (.inl .start)) endS) := by
        apply one false rfl
        simp [code, Act.eval, endS, Cursor.state]
      have finish := checker_run φ es' endS rfl rt
      have hout : result x w = checkSpec φ es' := by
        rw [show startCur k w = c from rfl, hsc] at ok
        simp [result, hd, ← ok, checkSpec, es', live_rows]
      rw [hout]
      have hall := Done.pre (((pre.trans walk).trans (step.le le_rfl))) finish
      apply hall.mono
      apply le_trans _ hbudget
      have hh := table_bound (items φ) w
      rw [names_items, chars_items] at hh
      change (tblStk es').length ≤ ts.length at hh
      change cost + 1 + (ts.length * (8 * (tblStk es').length + 9) + 1) ≤ _
      gcongr

private noncomputable abbrev component : Host.Comp where
  K := K
  Γ := fun _ => Sym
  L := L
  prog := prog
  ks := Finset.univ.toList
  ks_nodup := Finset.nodup_toList _
  mem_ks _ := by simp

private theorem result_poly :
    ComplexityTheory.IsPolyTime (fun p : List Bool × List Bool => result p.1 p.2) := by
  apply Host.isPolyTime_verifier (c := component) (cX := X) (cW := W)
    (gX := Sym.bit) (gW := Sym.bit) (start := .lex instanceP.initial) (yes := yes) (no := .no)
    result totalPoly (by decide) (by intro h; cases h) rfl rfl
  intro x w
  obtain ⟨v, S, hr⟩ := verified x w
  refine ⟨v, S, ?_⟩
  have h : update (update (fun _ : K => []) X (bits x)) W (bits w) =
      ({x := bits x, w := bits w} : Reg).store := by
    funext k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  simpa only [h] using hr

end
end Verifier
end Lexer

/-- **MINIMUM ONES 3-SAT is NP-complete.** Let MINIMUM ONES 3-SAT be the decision problem that
accepts a bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding, to a
triple $(n, \varphi, K)$ of a natural number $n$, a CNF formula $\varphi$ and a natural number $K$
such that every clause of $\varphi$ is a list of exactly three literals whose variables are all
less than $n$, and some assignment of truth values to the variables $0, \dots, n-1$ satisfies
$\varphi$ and sets at most $K$ of them to true. Then MINIMUM ONES 3-SAT belongs to NP, and every
decision problem $L$ in NP reduces to it by a polynomial-time many-one reduction: there is a
polynomial-time computable map $f$ on bitstrings such that, for every bitstring $x$, $L$ accepts
$x$ exactly when MINIMUM ONES 3-SAT accepts $f(x)$.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability: A Guide to the Theory of NP-Completeness* (1979), MINIMUM ONES 3-SAT. -/
public theorem minOnesThreeSat_npComplete :
    minOnesThreeSatDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minOnesThreeSatDec := by
  refine ⟨⟨Polynomial.C 3 * Polynomial.X, fun p => result p.1 p.2, Lexer.Verifier.result_poly,
    ?_⟩, Reduction.hardness⟩
  intro x
  simpa using Certificate.verifier_correct x

end MetaMathlibExt.Complexity.NPComplete.MinOnesThreeSat
