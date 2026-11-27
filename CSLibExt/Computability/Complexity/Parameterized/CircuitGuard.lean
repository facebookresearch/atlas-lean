/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.CircuitChecks
public import CSLibExt.Computability.Complexity.PolynomialEncoding.RowTrace
import CSLibExt.Computability.Complexity.Parameterized.Identity
import CSLibExt.Computability.Complexity.PolynomialEncoding.RowDedup
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip
import Mathlib.Data.List.Enum

/-!
# A polynomial-time machine for the weighted-circuit validity guard

Gate addresses are binary. Verify each reference against the earlier index
and build bounded weft and depth tables in circuit order. Saturating the
values at one more than the requested budget preserves every bound check
and gives all intermediate rows a fixed encoded width.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.NormalForm

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity
open PolynomialEncoding Comprehension BitScan

local notation "Bits" => List Bool
local notation "N" => (bitEncode (α := ℕ))
local notation "G" => (bitEncode (α := WCGate))

private theorem encInj : Function.Injective N := by
  intro a b h
  apply Option.some.inj
  simpa only [bitDecode_bitEncode] using congrArg (bitDecode (α := ℕ)) h

private theorem leR {A : Type} {e : A → Bits} {f g : A → ℕ}
    (hf : Represented e (fun a => N (f a))) (hg : Represented e (fun a => N (g a))) :
    Represented e (fun a => [decide (f a ≤ g a)]) :=
  (hf.test₂ BitZip.polyDecodedLE hg).transport
    (by intro a; simp only [BinaryNatEncoding.bitEncode_nat, Computability.decode_encodeNat])

private theorem anyOr {A : Type} {e : A → Bits} {p q : A → Bool}
    (hp : Represented e (fun x => [p x])) (hq : Represented e (fun x => [q x])) :
    Represented e (fun x => [p x || q x]) :=
  (hp.cond (Represented.const _ [true]) hq).transport (by intro x; cases p x <;> rfl)

private theorem allR {A B : Type} {e : A → Bits} {r : B → Bits} {rows : A → List B}
    {p : B × A → Bool} (hr : Represented e (fun a => frames r (rows a)))
    (hp : Represented (pair r e) (fun a => [p a])) :
    Represented e (fun a => [(rows a).all (fun b => p (b, a))]) := by
  apply (hr.testAny hp.neg).neg.transport
  intro a
  congr 1
  exact List.all_eq_not_any_not.symm

private def maximum (values refs : List ℕ) :=
  refs.foldr (fun i m => max (values.getD i 0) m) 0

private theorem maximum_le (values refs : List ℕ) (n : ℕ) :
    maximum values refs ≤ n ↔ ∀ i ∈ refs, values.getD i 0 ≤ n := by
  induction refs with
  | nil => simp [maximum]
  | cons i rs ih => simpa [maximum, max_le_iff] using
      and_congr_right (fun _ : values.getD i 0 ≤ n => ih)

private theorem maximum_clip (cap : ℕ) (values refs : List ℕ) :
    maximum (values.map (min cap)) refs = min cap (maximum values refs) := by
  induction refs with
  | nil => simp [maximum]
  | cons i rs ih =>
    have v : (values.map (min cap)).getD i 0 = min cap (values.getD i 0) := by
      simpa using (List.getD_map (l := values) (n := i) (d := 0) (min cap))
    change max _ (maximum _ rs) = min cap (max _ (maximum values rs))
    rw [v, ih]
    omega

private theorem ixRep {A : Type} (r : A → Bits) :
    Represented (Represented.numbered r) (fun p => N p.2) := by
  have hu : Represented (Represented.numbered r) (fun p => unary p.2) :=
    ⟨_, polyField true false, fun p => hd_pack _ _⟩
  exact (hu.after isPolyTime_encodeLength).transport (by simp)

private theorem itemRep {A : Type} (r : A → Bits) :
    Represented (Represented.numbered r) (fun p => r p.1) :=
  ⟨_, polyField false true, fun _ => tl_pack _ _⟩

private theorem maxOkR {D : Type} {e : D → Bits} {values refs : D → List ℕ}
    (hv : Represented e (fun a => frames N (values a)))
    (hr : Represented e (fun a => frames N (refs a))) (n : ℕ) :
    Represented e (fun a => [decide (maximum (values a) (refs a) ≤ n)]) := by
  let row := Represented.numbered N
  let q := pair row e
  have idx := (ixRep N).fst e
  have member := (hr.snd row).testAny
    (Represented.equal encInj ((Represented.input N).fst q) (idx.snd N))
  have val := (itemRep N).fst e
  have condition := anyOr member.neg (leR val (Represented.const q (N n)))
  apply (allR hv.enumerate condition).transport
  intro x
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.forall_mem_zipIdx', Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, maximum_le]
  have mem (j : ℕ) : ((refs x).any (fun i => decide (i = j))) = false ↔ j ∉ refs x := by
    simp
    grind
  constructor
  · intro h j hj
    by_cases hi : j < (values x).length
    · rw [List.getD_eq_getElem _ 0 hi]
      exact (h j hi).resolve_left (fun hn => (mem j).mp hn hj)
    · rw [List.getD_eq_default _ 0 (by omega)]
      exact Nat.zero_le _
  · intro h j hi
    by_cases hj : j ∈ refs x
    · apply Or.inr
      have hz := h j hj
      rwa [List.getD_eq_getElem (values x) 0 hi] at hz
    · exact Or.inl ((mem _).mpr hj)

private abbrev ctx := pair G (frames N)

private theorem gateKind : Represented G (fun g => N g.1) :=
  (Represented.input N).fst (bitEncode (α := List ℕ))

private theorem gateRefs : Represented G (fun g => frames N g.2) :=
  ((Represented.input (bitEncode (α := List ℕ))).snd N).transport
    (fun g => (frames_encode g.2).symm)

private def wired (g : WCGate) := decide (g.1 = 2 ∨ g.1 = 3 ∨ g.1 = 4)

private theorem wiredR : Represented G (fun g => [wired g]) := by
  have eq (i : ℕ) := Represented.equal encInj gateKind (Represented.const G (N i))
  apply (anyOr (eq 2) (anyOr (eq 3) (eq 4))).transport
  intro g
  simp [wired]

private def big (g : WCGate) := decide ((g.1 = 3 ∨ g.1 = 4) ∧ 2 < g.2.length)

private theorem bigR : Represented G (fun g => [big g]) := by
  have eq (i : ℕ) := Represented.equal encInj gateKind (Represented.const G (N i))
  have arity : Represented G (fun g => N g.2.length) :=
    (gateRefs.count.after isPolyTime_encodeLength).transport (by simp)
  apply ((anyOr (eq 3) (eq 4)).both (leR arity (Represented.const G (N 2))).neg).transport
  intro g
  by_cases hh : 2 < g.2.length
  · simp [big, hh, Nat.not_le_of_gt hh]
  · simp [big, hh, Nat.le_of_not_gt hh]

private theorem preds_eq (g : WCGate) : wcGatePreds g = if wired g then g.2 else [] := by
  obtain ⟨k,r⟩ := g
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ k =>
        cases k with
        | zero => rfl
        | succ k => cases k <;> rfl

private theorem predsR : Represented G (fun g => frames N (wcGatePreds g)) := by
  apply (wiredR.cond gateRefs (Represented.const _ [])).transport
  intro g
  rw [preds_eq]
  cases wired g <;> rfl

private theorem depth_eq (v : List ℕ) (g : WCGate) :
    wcGateDepth v g = if g.1 ≤ 1 then 0 else 1 + maximum v g.2 := by
  obtain ⟨k, r⟩ := g
  cases k with
  | zero => rfl
  | succ k => cases k <;> simp [wcGateDepth, maximum, Nat.add_comm]

private theorem weft_eq (v : List ℕ) (g : WCGate) :
    wcGateWeft v g = (big g).toNat + maximum v (wcGatePreds g) := by
  obtain ⟨k, r⟩ := g
  by_cases h : (k = 3 ∨ k = 4) ∧ 2 < r.length <;> simp [wcGateWeft, big, h, maximum]

private theorem depthOkR (b : ℕ) :
    Represented ctx (fun p => [decide (wcGateDepth p.2 p.1 ≤ b)]) := by
  have low := (leR gateKind (Represented.const G (N 1))).fst (frames N)
  cases b with
  | zero =>
    apply low.transport
    intro p
    rw [depth_eq]
    by_cases h : p.1.1 ≤ 1 <;> simp [h]
  | succ b =>
    have m := maxOkR ((Represented.input (frames N)).snd G) (gateRefs.fst (frames N)) b
    apply (anyOr low m).transport
    intro p
    rw [depth_eq]
    by_cases h : p.1.1 ≤ 1 <;> simp [h]
    omega

private theorem weftOkR (b : ℕ) :
    Represented ctx (fun p => [decide (wcGateWeft p.2 p.1 ≤ b)]) := by
  have m (n : ℕ) := maxOkR ((Represented.input (frames N)).snd G) (predsR.fst (frames N)) n
  let g := bigR.fst (frames N)
  cases b with
  | zero =>
    apply (g.neg.both (m 0)).transport
    intro p
    rw [weft_eq]
    cases big p.1 <;> simp
  | succ b =>
    apply (g.cond (m b) (m (b+1))).transport
    intro p
    rw [weft_eq]
    cases big p.1 <;> simp
    omega

private theorem minRep {D : Type} {e : D → Bits} {v : D → ℕ}
    (h : ∀ b, Represented e (fun x => [decide (v x ≤ b)])) (b : ℕ) :
    Represented e (fun x => N (min b (v x))) := by
  induction b with
  | zero => exact (Represented.const _ (N 0)).transport (by simp)
  | succ b ih =>
    apply ((h b).cond ih (Represented.const _ (N (b+1)))).transport
    intro x
    by_cases hc : v x ≤ b
    · simp [hc, Nat.min_eq_right (Nat.le_succ_of_le hc)]
    · simp [hc, Nat.min_eq_left (by omega : b+1 ≤ v x)]

private theorem measureGuard (f : List ℕ → WCGate → ℕ)
    (ho : ∀ b, Represented ctx (fun p => [decide (f p.2 p.1 ≤ b)]))
    (hclip : ∀ cap xs g, min cap (f (xs.map (min cap)) g) = min cap (f xs g)) (b : ℕ) :
    Represented (frames G) (fun C =>
      [(C.foldl (fun v g => v ++ [f v g]) []).all (· ≤ b)]) := by
  let cap := b+1
  let clipped (xs : List ℕ) (g : WCGate) := min cap (f xs g)
  have hlen (xs : List ℕ) (g : WCGate) : (N (clipped xs g)).length ≤ cap := by
    rw [BinaryNatEncoding.length_bitEncode]
    exact (Nat.size_le.mpr (clipped xs g).lt_two_pow_self).trans (Nat.min_le_left ..)
  have tr := RowTrace.represented G N clipped cap hlen (minRep ho cap)
  have full (C : List WCGate) (ds : List ℕ) :
      C.foldl (fun v g => v ++ [clipped v g]) (ds.map (min cap)) =
        (C.foldl (fun v g => v ++ [f v g]) ds).map (min cap) := by
    induction C generalizing ds with
    | nil => rfl
    | cons g C ih =>
      simp only [List.foldl_cons, clipped, hclip]
      simpa only [List.map_append, List.map_singleton] using ih (ds ++ [f ds g])
  let q := pair N (frames G)
  apply (allR tr (leR ((Represented.input N).fst (frames G)) (Represented.const q (N b)))).transport
  intro C
  have hfold := full C []
  simp only [List.map_nil] at hfold
  rw [hfold]
  congr 1
  rw [List.all_map]
  apply congrArg (_root_.List.all _)
  funext i
  apply Bool.eq_iff_iff.mpr
  change decide (min (b+1) i ≤ b) = true ↔ decide (i ≤ b) = true
  simp only [decide_eq_true_eq]
  omega

open Classical in
private theorem wfR : Represented (frames G) (fun C => [decide (WCWellFormed C)]) := by
  classical
  let r := Represented.numbered G
  let e := frames G
  let q := pair r e
  have rows := (Represented.input e).enumerate
  have gate := (itemRep G).fst e
  have refs : Represented q (fun p => frames N p.1.1.2) := by
    obtain ⟨s, hs, spec⟩ := gate
    obtain ⟨f, hf, post⟩ := gateRefs
    exact ⟨_, hs.comp hf, fun p => (congrArg f (spec p)).trans (post _)⟩
  have anyBad := refs.testAny (leR (((ixRep G).fst e).snd N) ((Represented.input N).fst q))
  have w : Represented q (fun p => [wired p.1.1]) := by
    obtain ⟨s, hs, spec⟩ := gate
    obtain ⟨f, hf, post⟩ := wiredR
    exact ⟨_, hs.comp hf, fun p => (congrArg f (spec p)).trans (post _)⟩
  apply (allR rows (w.both anyBad).neg).transport
  intro C
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.forall_mem_zipIdx', Bool.not_eq_true', Bool.and_eq_false_imp,
    wired, decide_eq_true_eq, List.any_eq_false, not_le]
  change (∀ i (hi : i < C.length), _ → ∀ _ ∈ _, _) ↔ _
  constructor
  · intro h i hi j hj g
    exact h i hi g j hj
  · intro h i hi g j hj
    exact h i hi j hj g

/-- Every part of the canonical weighted-circuit syntax check is computed in
polynomial time for fixed budgets, including the bounds on all unused gates. -/
theorem represented_validCircuit (t d : ℕ) :
    Represented (bitEncode (α := List WCGate)) (fun C => [validCircuit t d C]) := by
  classical
  have weft := measureGuard wcGateWeft weftOkR (fun cap xs g => by
    rw [weft_eq, weft_eq, maximum_clip]
    cases big g <;> simp
    omega) t
  have depth := measureGuard wcGateDepth depthOkR (fun cap xs g => by
    rw [depth_eq, depth_eq, maximum_clip]
    split <;> omega) d
  have h := (wfR.both weft).both depth
  obtain ⟨s, hs, eq⟩ := h
  refine ⟨s, hs, fun C => ?_⟩
  rw [← frames_encode, eq]
  apply congrArg (fun b : Bool => [b])
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, validCircuit_iff,
    wcCircuitWefts, wcCircuitDepths, and_assoc]

/-- Run the guard on any gate table produced by a represented computation. -/
theorem represented_validCircuit_of_table {A : Type} {e : A → Bits} {C : A → List WCGate}
    (hC : Represented e (fun a => frames G (C a))) (t d : ℕ) :
    Represented e (fun a => [validCircuit t d (C a)]) := by
  obtain ⟨f, hf, ef⟩ := hC
  obtain ⟨g, hg, eg⟩ := represented_validCircuit t d
  exact ⟨_, hf.comp hg, fun a => by simp only [Function.comp_def, ef, frames_encode, eg]⟩

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.NormalForm
