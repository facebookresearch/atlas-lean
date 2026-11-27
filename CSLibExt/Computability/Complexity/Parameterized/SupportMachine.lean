/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.CompactCircuit
public import CSLibExt.Computability.Complexity.Parameterized.SupportRank
public import CSLibExt.Computability.Complexity.Parameterized.Transitivity
import CSLibExt.Computability.Complexity.PolynomialEncoding.RowDedup
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip
import CSLibExt.Computability.Complexity.PolynomialEncoding.BinaryAddition
import CSLibExt.Computability.Complexity.PolynomialEncoding.DecodedInstance
import CSLibExt.Computability.Complexity.PolynomialEncoding.IndexRange

/-!
# Computing the compact variable domain

All list comprehensions traverse the explicitly stored gates, references, or
distinct active variables. Binary comparisons and addition handle the declared
input count and the weight without expanding them into enormous ranges.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.Support

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity
open PolynomialEncoding Comprehension BitScan

local notation "Bits" => List Bool
local notation "N" => (bitEncode (α := ℕ))
local notation "G" => (bitEncode (α := WCGate))

private theorem enc_inj : Function.Injective N := by
  intro i j h
  apply Option.some.inj
  simpa only [bitDecode_bitEncode] using congrArg (bitDecode (α := ℕ)) h

private theorem leR {D : Type} {e : D → Bits} {a b : D → ℕ}
    (ha : Represented e (fun x => N (a x))) (hb : Represented e (fun x => N (b x))) :
    Represented e (fun x => [decide (a x ≤ b x)]) :=
  (ha.test₂ BitZip.polyDecodedLE hb).transport
    (by intro x; simp only [BinaryNatEncoding.bitEncode_nat, Computability.decode_encodeNat])

private theorem ltR {D : Type} {e : D → Bits} {a b : D → ℕ}
    (ha : Represented e (fun x => N (a x))) (hb : Represented e (fun x => N (b x))) :
    Represented e (fun x => [decide (a x < b x)]) :=
  (leR hb ha).neg.transport (by
    intro x
    by_cases h : a x < b x
    · simp [h, Nat.not_le_of_gt h]
    · simp [h, Nat.le_of_not_gt h])

private theorem minR {D : Type} {e : D → Bits} {a b : D → ℕ}
    (ha : Represented e (fun x => N (a x))) (hb : Represented e (fun x => N (b x))) :
    Represented e (fun x => N (min (a x) (b x))) :=
  ((leR ha hb).cond ha hb).transport (by
    intro x
    by_cases h : a x ≤ b x
    · simp [h]
    · simp [h, min_eq_right (by omega : b x ≤ a x)])

private theorem addR {D : Type} {e : D → Bits} {a b : D → ℕ}
    (ha : Represented e (fun x => N (a x))) (hb : Represented e (fun x => N (b x))) :
    Represented e (fun x => N (a x + b x)) := by
  obtain ⟨sa, pa, ea⟩ := ha
  obtain ⟨sb, pb, eb⟩ := hb
  exact ⟨_, (polyPair pa pb).comp BinaryAddition.polyDecodedAdd, fun x => by
    simp only [Function.comp_def, ea, eb, BinaryNatEncoding.bitEncode_nat,
      Computability.decode_encodeNat]⟩

private theorem countR {D A : Type} {e : D → Bits} {f : A → Bits} {l : D → List A}
    (h : Represented e (fun x => frames f (l x))) :
    Represented e (fun x => N (l x).length) :=
  (h.count.after isPolyTime_encodeLength).transport (by simp)

private def isInput (g : WCGate) : Bool := decide (g.1 = 0 ∧ g.2.length = 1)
private def name (g : WCGate) : ℕ := g.2.headD 0
private def names (n : ℕ) (C : List WCGate) : List ℕ :=
  ((C.filter fun g => isInput g && decide (name g < n)).map name).dedup

private theorem names_nodup (n : ℕ) (C : List WCGate) : (names n C).Nodup := List.nodup_dedup _

private theorem names_set (n : ℕ) (C : List WCGate) : (names n C).toFinset = active n C := by
  ext i
  simp only [names, active, List.mem_toFinset, List.mem_dedup, List.mem_map, List.mem_filter,
    Bool.and_eq_true, decide_eq_true_eq, List.mem_filterMap]
  constructor
  · rintro ⟨⟨kind, refs⟩, ⟨hg, hvar, hlt⟩, rfl⟩
    obtain ⟨rfl, len⟩ : kind = 0 ∧ refs.length = 1 := by simpa [isInput] using hvar
    obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp len
    exact ⟨_, hg, by simpa [inputOf, name] using hlt⟩
  · rintro ⟨g, hg, eq⟩
    unfold inputOf at eq
    split at eq
    · rename_i j
      by_cases hj : j < n
      · simp only [hj, ite_true, Option.some.injEq] at eq
        subst i
        exact ⟨(0, [j]), ⟨hg, rfl, hj⟩, rfl⟩
      · simp [hj] at eq
    · contradiction

private theorem names_length (n : ℕ) (C : List WCGate) :
    (names n C).length = (active n C).card := by
  rw [← names_set, List.toFinset_card_of_nodup (names_nodup ..)]

private theorem names_rank {n k : ℕ} {C : List WCGate} {i : ℕ} (hi : i ∈ active n C) :
    ((names n C).filter (· < i)).length = (labels n k C).idxOf i := by
  rw [index_count n k C hi, ← List.toFinset_card_of_nodup ((names_nodup n C).filter _),
    List.toFinset_filter, names_set]
  rfl

private theorem repName : Represented G (fun g => N (name g)) :=
  ⟨_, (polyField false true).comp (polyField true false), by
    rintro ⟨kind, refs⟩
    change hd (tl (pack (N kind) (bitEncode refs))) = N (refs.headD 0)
    rw [tl_pack]
    cases refs with
    | nil => rfl
    | cons i rs => exact hd_pack (N i) (bitEncode rs)⟩

private theorem repInput : Represented G (fun g => [isInput g]) := by
  let e := bitEncode (α := List ℕ)
  have hkind : Represented G (fun g => N g.1) := (Represented.input N).fst e
  have hrefs : Represented G (fun g => frames N g.2) :=
    ((Represented.input e).snd N).transport (fun g => (frames_encode g.2).symm)
  have k := Represented.equal enc_inj hkind (Represented.const G (N 0))
  have l := Represented.equal enc_inj (countR hrefs) (Represented.const G (N 1))
  exact (k.both l).transport (by simp [isInput])
private theorem repNames {D : Type} {e : D → Bits} {n : D → ℕ} {C : D → List WCGate}
    (hn : Represented e (fun d => N (n d))) (hC : Represented e (fun d => frames G (C d))) :
    Represented e (fun d => frames N (names (n d) (C d))) := by
  have hf := (repInput.fst e).both (ltR (repName.fst e) (hn.snd G))
  exact Represented.dedup enc_inj ((hC.filtered hf).mapped (repName.fst e))

private theorem repDummies {D : Type} {e : D → Bits} {n k m : D → ℕ}
    (hn : Represented e (fun d => N (n d))) (hk : Represented e (fun d => N (k d)))
    (hum : Represented e (fun d => unary (m d))) (hmb : ∀ d, m d ≤ n d) :
    Represented e (fun d => N (dummyCount (n d) (m d) (k d))) := by
  have hm : Represented e (fun d => N (m d)) :=
    (hum.after isPolyTime_encodeLength).transport (by simp)
  have range : Represented e (fun d => frames N (List.range (m d))) :=
    (hum.after IndexRange.isPolyTime_encodeRange).transport (by simp [frames_encode])
  have w := minR hk hm
  have lo := ltR ((Represented.input N).fst e) (w.snd N)
  have hi := ltR (addR ((addR hk hm).snd N) ((Represented.input N).fst e))
    ((addR hn w).snd N)
  have rows := range.filtered (lo.both hi)
  apply (countR rows).transport
  intro d
  rw [dummyCount_eq_filter (hmb d)]
  congr 1

private def gateByRank (n k : ℕ) (C : List WCGate) (g : WCGate) : WCGate :=
  if isInput g then
    (0, [if name g < n then ((names n C).filter (· < name g)).length else (labels n k C).length])
  else g

private theorem gateByRank_eq (n k : ℕ) (C : List WCGate) (g : WCGate) (hg : g ∈ C) :
    gateByRank n k C g = reindexGate n (labels n k C) g := by
  obtain ⟨kind, refs⟩ := g
  cases kind with
  | succ j => simp [gateByRank, isInput, reindexGate]
  | zero =>
    cases refs with
    | nil => rfl
    | cons i rs =>
      cases rs with
      | cons j t => simp [gateByRank, isInput, reindexGate]
      | nil =>
        by_cases hi : i < n
        · have ha : i ∈ active n C :=
            List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, hg, by simp [inputOf, hi]⟩)
          simp [gateByRank, reindexGate, isInput, name, hi, names_rank (k := k) ha]
        · simp [gateByRank, reindexGate, isInput, name, hi]

private theorem labels_len (n k : ℕ) (C : List WCGate) :
    (labels n k C).length = (active n C).card + dummyCount n (active n C).card k := by
  simpa [labels] using compactUniverse_card k _ (active_subset n C)

private theorem repGates {D : Type} {e : D → Bits} {n k : D → ℕ} {C : D → List WCGate}
    (hn : Represented e (fun d => N (n d))) (hk : Represented e (fun d => N (k d)))
    (hC : Represented e (fun d => frames G (C d))) :
    Represented e (fun d => bitEncode
      (bitEncode ((labels (n d) (k d) (C d)).length,
        (C d).map (reindexGate (n d) (labels (n d) (k d) (C d)))),
        min (k d) (active (n d) (C d)).card)) := by
  have vars := repNames hn hC
  have hum : Represented e (fun d => unary (active (n d) (C d)).card) :=
    vars.count.transport (by intro d; rw [names_length])
  have hm : Represented e (fun d => N (active (n d) (C d)).card) :=
    (hum.after isPolyTime_encodeLength).transport (by simp)
  have hmb (d : D) : (active (n d) (C d)).card ≤ n d := by
    simpa using Finset.card_le_card (active_subset (n d) (C d))
  have hnum : Represented e (fun d => N (labels (n d) (k d) (C d)).length) :=
    (addR hm (repDummies hn hk hum hmb)).transport (by intro d; rw [labels_len])
  have rankRows := (vars.snd G).filtered
    (ltR ((Represented.input N).fst (pair G e)) ((repName.fst e).snd N))
  have v := (ltR (repName.fst e) (hn.snd G)).cond (countR rankRows) (hnum.snd G)
  have gate : Represented (pair G e) (fun p => G (gateByRank (n p.2) (k p.2) (C p.2) p.1)) := by
    apply ((repInput.fst e).cond ((Represented.const _ (N 0)).packed v.frame)
      ((Represented.input G).fst e)).transport
    intro p
    simp only [gateByRank]
    split
    · change pack (N 0) (delimit _) = pack (N 0) (delimit (N _) ++ [])
      simp
      split <;> simp_all
    · rfl
  have allGates : Represented e (fun d => bitEncode
      ((C d).map (reindexGate (n d) (labels (n d) (k d) (C d))))) := by
    apply (hC.mapped gate).transport
    intro d
    rw [frames_encode]
    congr 1
    exact List.map_congr_left (fun g hg => gateByRank_eq _ _ _ g hg)
  exact ((hnum.packed allGates).after isPolyTime_bitEncode).packed (minR hk hm)

private abbrev Input := (ℕ × List WCGate) × ℕ

private def compactOut (d : Input) :=
  let n := d.1.1
  let C := d.1.2
  let k := d.2
  if k ≤ n then
    let L := labels n k C
    (bitEncode (L.length, C.map (reindexGate n L)), min k (active n C).card)
  else ([], 0)

private theorem repCompact :
    Represented (pair (bitEncode (α := ℕ × List WCGate)) N)
      (fun d => bitEncode (compactOut d)) := by
  let E := bitEncode (α := ℕ × List WCGate)
  let L := bitEncode (α := List WCGate)
  have hn : Represented (pair E N) (fun p => N p.1.1) := ((Represented.input N).fst L).fst N
  have hk : Represented (pair E N) (fun p => N p.2) := (Represented.input N).snd E
  have hC : Represented (pair E N) (fun p => frames G p.1.2) :=
    (((Represented.input L).snd N).fst N).transport (fun d => (frames_encode _).symm)
  apply ((leR hk hn).cond (repGates hn hk hC)
    (Represented.const _ (bitEncode (([], 0) : Bits × ℕ)))).transport
  intro p
  by_cases h : p.2 ≤ p.1.1 <;> simp [compactOut, h]

/-- The actual support compression in the circuit-to-clique candidate is
polynomial time on canonical input pairs, even when their internal circuit
encoding is malformed or noncanonical. -/
theorem isPolyTime_compact : IsPolyTime compact := by
  let cm := CodecMachine.nat.prod ((CodecMachine.nat.prod CodecMachine.nat.list).list)
  have ht := cm.isPolyTime_decodeFirst compactOut (([], 0) : Bits × ℕ) repCompact
  convert ht using 1
  funext p
  cases h : bitDecode (α := ℕ × List WCGate) p.1 with
  | none => simp [compact, h]
  | some q => rcases q with ⟨n,C⟩; simp [compact, compactOut, h]

/-- Support compression is a parameter-nonincreasing FPT reduction on each
weighted-satisfiability source problem, with an ordinary polynomial-time machine. -/
theorem compact_reduction (t d : ℕ) :
    FPTReduces (WeightedCircuitSat t d) (WeightedCircuitSat t d) :=
  (FPTReduces.refl _).postcomp_poly isPolyTime_compact id Computable.id
    (fun x k => compact_weight_le (x, k)) (compact_correct t d)

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.Support
