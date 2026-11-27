/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.BagMachine
public import CSLibExt.Computability.Complexity.Parameterized.BagAssignment
public import CSLibExt.Computability.Complexity.Parameterized.HardnessCircuitOutput
public import CSLibExt.Computability.Complexity.Parameterized.WeightedAssignments
public import CSLibExt.Computability.Complexity.Parameterized.SupportMachine
import CSLibExt.Computability.Complexity.PolynomialEncoding.DecodedInstance
import CSLibExt.Computability.Complexity.PolynomialEncoding.IndexRange

/-!
# W[1]-hardness of parameterized Clique

Compress the variable support before enumerating the variable domain and assignment slots.
On compressed instances twice the serialized gate count bounds both enumerations. This
yields an ordinary polynomial-time machine for each fixed depth, including the cost of
writing the graph and its binary clique parameter.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity
open PolynomialEncoding Comprehension

namespace CliqueHardness

local notation "Bits" => List Bool
local notation "N" => (bitEncode (α := ℕ))
local notation "G" => (bitEncode (α := WCGate))
local notation "Lit" => (pair N (fun b : Bool => [b]))
local notation "S" => (frames N)

private theorem filter_range (a b : ℕ) :
    (List.range a).filter (fun i => decide (i < b)) = List.range (min b a) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [List.range_succ, List.filter_append, ih]
    by_cases h : a < b
    · rw [Nat.min_eq_right (by omega : a ≤ b), Nat.min_eq_right (by omega : a + 1 ≤ b)]
      simp [List.range_succ, h]
    · simp [h, Nat.min_eq_left (by omega : b ≤ a), Nat.min_eq_left (by omega : b ≤ a + 1)]

/-- Emit an initial segment of the naturals, clipped to twice the number of
explicitly represented rows even if its binary bound is enormous. -/
private theorem represented_range {D T : Type} {e : D → Bits} {r : T → Bits}
    {rows : D → List T} {limit : D → ℕ}
    (hr : Represented e (fun x => frames r (rows x)))
    (hl : Represented e (fun x => N (limit x))) :
    Represented e (fun x => S (List.range (min (limit x) (2 * (rows x).length)))) := by
  have both := hr.count.append hr.count
  have complete : Represented e (fun x => S (List.range (2 * (rows x).length))) := by
    apply (both.after IndexRange.isPolyTime_encodeRange).transport
    intro x
    simp [frames_encode, two_mul]
  have keep := BagRows.represented_natLT ((Represented.input N).fst e) (hl.snd N)
  exact (complete.filtered keep).transport (fun x =>
    congrArg S (filter_range (2 * (rows x).length) (limit x)))

private theorem family_encoding (f : CircuitNormalMachine.Family) :
    CircuitNormalMachine.familyWord f = frames (frames (frames Lit)) f := by
  simp [CircuitNormalMachine.familyWord, NormalFormMachine.mapFamily,
    NormalFormMachine.encodeFamily, NormalFormMachine.encodeFormula,
    frames, Function.comp_def, List.map_map]
  rfl

abbrev Circuit := ℕ × List WCGate

def localQuery (d : ℕ) (p : Circuit × ℕ) : Bits × ℕ :=
  let gates := p.1.2
  let cap := 2 * gates.length
  BagRows.query (2^d) (List.range (min p.2 cap)) (List.range (min p.1.1 cap))
    (CircuitNormalMachine.family d p.1.1 gates)

private theorem represented_localQuery (d : ℕ) :
    Represented (pair (bitEncode (α := Circuit)) N) (fun p => bitEncode (localQuery d p)) := by
  let L := bitEncode (α := List WCGate)
  let E := bitEncode (α := Circuit)
  have n : Represented (pair E N) (fun p => N p.1.1) := ((Represented.input N).fst L).fst N
  have k := (Represented.input N).snd E
  have gates : Represented (pair E N) (fun p => frames G p.1.2) :=
    (((Represented.input L).snd N).fst N).transport (fun _ => (frames_encode _).symm)
  have family := (CircuitNormalMachine.represented_family n gates d).transport (fun _ =>
    family_encoding _)
  exact BagRows.represented_query (2^d) (represented_range gates k) (represented_range gates n)
    family

def stage (d : ℕ) (p : Bits × ℕ) : Bits × ℕ :=
  match bitDecode (α := Circuit) p.1 with
  | none => ([], 0)
  | some C => localQuery d (C, p.2)

private theorem isPolyTime_stage (d : ℕ) : IsPolyTime (stage d) := by
  let gate := CodecMachine.nat.prod CodecMachine.nat.list
  let cm : CodecMachine Circuit := CodecMachine.nat.prod gate.list
  have h := cm.isPolyTime_decodeFirst (localQuery d) (([], 0) : Bits × ℕ) (represented_localQuery d)
  convert h using 1
  funext p
  unfold stage
  cases bitDecode (α := Circuit) p.1 <;> rfl

/-- The concrete map on every raw input word and parameter. -/
def reduce (d : ℕ) (p : Bits × ℕ) : Bits × ℕ := stage d (Support.compact p)

/-- A canonical polynomial-time TM2 computes the entire reduction for each fixed depth. -/
theorem isPolyTime_reduce (d : ℕ) : IsPolyTime (reduce d) :=
  Support.isPolyTime_compact.comp (isPolyTime_stage d)

private theorem compact_bounds {p : Bits × ℕ} {n : ℕ} {C : List WCGate}
    (h : bitDecode (α := Circuit) (Support.compact p).1 = some (n, C)) :
    n ≤ 2 * C.length ∧ (Support.compact p).2 ≤ 2 * C.length := by
  have hnil : bitDecode (α := Circuit) [] = none := rfl
  cases hx : bitDecode (α := Circuit) p.1 with
  | none => simp [Support.compact, hx, hnil] at h
  | some q =>
    obtain ⟨m,gates⟩ := q
    by_cases hk : p.2 ≤ m
    · simp only [Support.compact, hx, hk, ↓reduceIte, bitDecode_bitEncode, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Support.compact, hx, hk, ↓reduceIte, List.length_map]
      have hcard := Support.active_card_le m gates
      exact ⟨Support.labels_length_le m p.2 gates, (min_le_right _ _).trans (by omega)⟩
    · simp [Support.compact, hx, hk, hnil] at h

/-- For fixed circuit depth, a computable function of the source weight bounds
the target clique size. -/
theorem parameter_le (d : ℕ) (p : Bits × ℕ) :
    (reduce d p).2 ≤ (p.2 + 1) ^ max 2 (2 * 2^d) := by
  unfold reduce stage
  cases hx : bitDecode (α := Circuit) (Support.compact p).1 with
  | none => exact Nat.zero_le _
  | some q =>
    obtain ⟨n, C⟩ := q
    change (tuples (List.range _) (max 2 (2 * 2^d))).length ≤ _
    apply (length_tuples_le _ _).trans
    rw [List.length_range]
    exact Nat.pow_le_pow_left (by have := Support.compact_weight_le p; omega) _

private theorem computable_bound (b : ℕ) : Computable (fun k : ℕ => (k+1)^b) := by
  induction b with
  | zero => simpa using (Computable.const (1 : ℕ) : Computable (fun _ : ℕ => 1))
  | succ b ih =>
    simpa [pow_succ] using Primrec.nat_mul.to_comp.comp ih Computable.succ

/-- The source's exact-weight condition and the target clique condition agree,
including undecodable words and weighted circuits with empty gate lists. -/
theorem correct (d : ℕ) (x : Bits) (k : ℕ) :
    WeightedCircuitSat 1 d x k ↔ CliqueParam (reduce d (x,k)).1 (reduce d (x,k)).2 := by
  apply (Support.compact_correct 1 d x k).trans
  cases hx : bitDecode (α := Circuit) (Support.compact (x,k)).1 with
  | none =>
    have graphNil : bitDecode (α := ℕ × List (ℕ × ℕ)) [] = none := rfl
    simp [reduce, stage, hx, WeightedCircuitSat, CliqueParam, graphNil]
  | some q =>
    obtain ⟨n, C⟩ := q
    obtain ⟨hn, hk⟩ := compact_bounds hx
    have sem := BagRows.weightedCircuitSat_iff_familyHasAssignment hx d (Support.compact (x,k)).2
    have width (p) (hp : p ∈ CircuitNormalMachine.family d n C) (c) (hc : c ∈ p) :
        c.toFinset.card ≤ 2^d := by
      exact c.toFinset_card_le.trans ((CircuitNormalMachine.family_fits d n C p hp c hc).1)
    have query := BagRows.query_correct (2^d) (Support.compact (x,k)).2 n _ width
    simpa only [reduce, stage, hx, localQuery, Nat.min_eq_left hk, Nat.min_eq_left hn] using
      sem.trans query.symm

/-- Each fixed-depth weighted weft-one circuit problem FPT-reduces to Clique. -/
theorem weightedCircuitSat_reduces_clique (d : ℕ) :
    FPTReduces (WeightedCircuitSat 1 d) CliqueParam :=
  (FPTReduces.refl _).postcomp_poly (isPolyTime_reduce d) _ (computable_bound _)
    (fun x k => parameter_le d (x,k)) (correct d)

end CliqueHardness

/-- Every problem in the canonical first W-level FPT-reduces to parameterized Clique. -/
theorem clique_wOne_hard : ∀ P ∈ WLevel 1, FPTReduces P CliqueParam := by
  rintro P ⟨d, h⟩
  exact h.trans (CliqueHardness.weightedCircuitSat_reduces_clique d)

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
