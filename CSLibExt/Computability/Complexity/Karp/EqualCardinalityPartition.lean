/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Partition
public import CSLibExt.Computability.Complexity.Defs
import CSLibExt.Computability.Complexity.Karp.PartitionComplete
import CSLibExt.Computability.Complexity.BoolClosure
import CSLibExt.Computability.Complexity.PairProjection
import CSLibExt.Computability.Complexity.PolynomialEncoding.StreamScan
import MathlibExt.Computability.TuringMachine.Recursive.OfTM2

/-!
# PARTITION into halves of equal cardinality is NP-complete

INSTANCE: a finite set `A` and a size `s(a) ∈ ℤ⁺` for each `a ∈ A`. QUESTION: is there a
subset `A' ⊆ A` with `|A'| = |A|/2` such that `∑_{a ∈ A'} s(a) = ∑_{a ∈ A - A'} s(a)`?

The instance is the list of sizes, as in the proved PARTITION of
`CSLibExt.Computability.Complexity.Karp.Partition` (whose instance type is reused): the elements
of `A` are the positions of the list, and a subset `A'` is a sublist (a choice of positions).
`|A'| = |A|/2` is written `2 * |A'| = |A|`, which also requires `|A|` to be even; the two sums are
equal exactly when the sum over `A'` is half the total.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SP12] PARTITION, comment ("Remains
NP-complete even if we require that `|A'| = |A|/2`, or if the elements in `A` are ordered as
`a₁, a₂, ..., a₂ₙ` and we require that `A'` contain exactly one of `a₂ᵢ₋₁, a₂ᵢ` for
`1 ≤ i ≤ n`"); the entry's reference is "[Karp, 1972]. Transformation from 3DM (see
Section 3.1.5)"; R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of
Computer Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9.
-/

/-
For membership in NP, the same positional mask is checked against the input weights and a list
of ones. For hardness, replace each weight `a` by `2*a+1` and append one `1` per input entry.
Every half-length sublist contributes the same total offset from these ones, so balance of
its weight is equivalent to balance of the original weights it selects. Using `2*a+1` rather
than `a+1` makes the change a single low-bit insertion.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EqualCardinalityPartition

open Partition (PartitionInstance)

/-- Well-formedness of an instance: every size is positive. -/
def WellFormed (i : PartitionInstance) : Prop :=
  ∀ a ∈ i, 0 < a

/-- Some sublist `A'` of half the length has half the total size. -/
def EqualCardinalityPartitionFeasible (i : PartitionInstance) : Prop :=
  ∃ s : List ℕ, s.Sublist i ∧ 2 * s.length = i.length ∧ s.sum * 2 = i.sum

open Classical in
/-- PARTITION into halves of equal cardinality as a decision problem over bitstrings. -/
noncomputable def equalCardinalityPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionInstance) x with
  | some i => decide (WellFormed i ∧ EqualCardinalityPartitionFeasible i)
  | none => false

open BitstringEncoding ComplexityTheory Computability
open Cslib.Complexity Cslib.Complexity.Karp Cslib.Complexity.PolynomialEncoding
open Cslib.Complexity.PolynomialEncoding.StreamScan
open SSVerify (count_pick ssCheck_encode)

private abbrev Bits := List Bool

private abbrev frames (ps : List Bits) : Bits := (ps.map delimit).flatten

private theorem frames_cons (p : Bits) (ps : List Bits) :
    frames (p :: ps) = delimit p ++ frames ps := rfl

private theorem frames_append (ps qs : List Bits) :
    frames (ps ++ qs) = frames ps ++ frames qs := by
  simp only [frames, List.map_append, List.flatten_append]

private theorem blocks_noPayload (close : Option Bool → Bits) (p r : Bits) :
    blocks [] (fun _ => []) close (delimit p ++ r) =
      close p.getLast? ++ blocks [] (fun _ => []) close r := by
  have hp : p.flatMap (fun _ => ([] : Bits)) = [] := by
    induction p with
    | nil => rfl
    | cons _ _ ih => simp [ih]
  simp [blocks_frame, hp]

private theorem encode_list (as : List ℕ) : bitEncode as = frames (as.map encodeNat) := rfl

/-! ### Membership: the two tests use the same mask -/

private abbrev ones : Bits → Bits := marks (delimit (encodeNat 1))

private theorem ones_frames (ps : List Bits) :
    ones (frames ps) = bitEncode (List.replicate ps.length (1 : ℕ)) := by
  unfold frames ones
  rw [marks_frames, encode_list]
  simp only [frames, List.map_replicate]

private def emptyMarks : Bits → Bits :=
  blocks [] (fun _ => []) (fun last => if last.isNone then [true] else [])

private def positive (x : Bits) : Bool := !(emptyMarks x).headD false

private theorem positive_frames (ps : List Bits) :
    positive (frames ps) = true ↔ ∀ p ∈ ps, p ≠ [] := by
  induction ps with
  | nil => simp [positive, emptyMarks, frames]
  | cons p ps ih =>
    unfold positive emptyMarks at ih ⊢
    rw [frames_cons, blocks_noPayload]
    cases p <;> simp_all

private theorem decodeNat_pos_iff (p : Bits) : 0 < decodeNat p ↔ p ≠ [] := by
  cases p with
  | nil => decide
  | cons b p =>
    rw [iff_true_right (List.cons_ne_nil _ _)]
    by_contra! h
    have hn := FramedCNF.normalizeNat_eq_encode_decode (b :: p)
    rw [show decodeNat (b :: p) = 0 by omega, show encodeNat 0 = [] from rfl] at hn
    unfold FramedCNF.normalizeNat at hn
    split at hn <;> simp at hn

private theorem pick_double (as : List ℕ) (w : Bits) :
    (SSVerify.pick (as.map (· * 2)) w).sum = (SSVerify.pick as w).sum * 2 := by
  induction as generalizing w with
  | nil => rfl
  | cons a as ih =>
    rw [List.map_cons, SSVerify.sum_pick_cons, SSVerify.sum_pick_cons, ih]
    cases w.headD false <;> simp [Nat.add_mul]

private def verify (q : Bits × Bits) : Bool :=
  (positive q.1 && SSVerify.ssCheck (Partition.reduceToSubsetSum q.1) q.2) &&
    SSVerify.ssCheck (Partition.reduceToSubsetSum (ones q.1)) q.2

private theorem polyVerify : IsPolyTime verify := by
  have hmarks : IsPolyTime emptyMarks := polyBlocks _ _ _
  have hp : IsPolyTime positive := hmarks.comp
    (isPolyTime_dup.comp (isPolyTime_heads (fun b _ => !b)))
  have ho : IsPolyTime ones := polyBlocks _ _ _
  have hr := Partition.MembershipMachine.isPolyTime_reduceToSubsetSum
  exact polyCombinePair
    (polyCombinePair (isPolyTime_fst.comp hp) (hr.map_fst.comp isPolyTime_ssCheck))
    ((ho.comp hr).map_fst.comp isPolyTime_ssCheck)

private theorem verify_frames (ps : List Bits) (w : Bits) :
    verify (frames ps, w) = true ↔
      let as := ps.map decodeNat
      WellFormed as ∧ (SSVerify.pick as w).sum * 2 = as.sum ∧
        2 * (SSVerify.pick as w).length = as.length := by
  let as := ps.map decodeNat
  have hd : bitDecode (frames ps) = some as := by
    simp [decode_list_nat, undelimitBlocks_flatten_delimit, as]
  have hp : positive (frames ps) = true ↔ WellFormed as := by
    simp [positive_frames, WellFormed, as, decodeNat_pos_iff]
  have hc : (SSVerify.pick (List.replicate ps.length 1) w).sum =
      (SSVerify.pick as w).length := by
    simpa only [as, List.length_map] using count_pick as w
  have hr : (List.replicate ps.length (1 : ℕ)).sum = as.length := by simp [as]
  simp only [verify, Bool.and_eq_true, hp, Partition.reduceToSubsetSum, hd, ones_frames,
    bitDecode_bitEncode, ssCheck_encode, pick_double, hc, hr]
  change ((WellFormed as ∧ (SSVerify.pick as w).sum * 2 = as.sum) ∧
      (SSVerify.pick as w).length * 2 = as.length) ↔ _
  rw [and_assoc, Nat.mul_comm (SSVerify.pick as w).length 2]

private theorem membership : equalCardinalityPartitionDec ∈ NP := by
  refine ⟨Polynomial.X, verify, polyVerify, fun x => ?_⟩
  cases hd : bitDecode (α := List ℕ) x with
  | none =>
    simp [equalCardinalityPartitionDec, hd, verify, Partition.reduceToSubsetSum, noSS,
      ssCheck_encode, SSVerify.pick]
  | some as =>
    have h := hd
    rw [decode_list_nat] at h
    obtain ⟨ps, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain rfl := blocks_decode_sound hp
    simp only [equalCardinalityPartitionDec, hd, decide_eq_true_eq, Polynomial.eval_X,
      verify_frames]
    constructor
    · rintro ⟨hpos, s, hs, hlen, hsum⟩
      obtain ⟨w, hw, rfl⟩ := SSVerify.exists_pick hs
      refine ⟨w, ?_, hpos, hsum, hlen⟩
      simpa only [hw, List.length_map] using length_le_length_flatten_delimit ps
    · rintro ⟨w, _, hpos, hsum, hlen⟩
      exact ⟨hpos, SSVerify.pick _ w, SSVerify.pick_sublist _ w, hlen, hsum⟩

/-! ### Hardness: positive padding preserves exactly the balanced selections -/

private def shift (a : ℕ) : ℕ := a * 2 + 1

private def pad (as : List ℕ) : List ℕ := as.map shift ++ List.replicate as.length 1

private theorem pad_wellFormed (as : List ℕ) : WellFormed (pad as) := by
  intro a ha
  simp only [pad, List.mem_append, List.mem_map, List.mem_replicate] at ha
  rcases ha with ⟨b, _, rfl⟩ | ⟨_, rfl⟩ <;> simp [shift]

private theorem sum_shift (as : List ℕ) : (as.map shift).sum = as.sum * 2 + as.length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons, List.sum_cons, List.length_cons, shift, ih]; omega

private theorem feasible_pad (as : List ℕ) :
    EqualCardinalityPartitionFeasible (pad as) ↔ Partition.PartitionFeasible as := by
  constructor
  · rintro ⟨s, hs, hlen, hsum⟩
    obtain ⟨p, r, rfl, hp, hr⟩ := List.sublist_append_iff.mp hs
    obtain ⟨q, hq, rfl⟩ := List.sublist_map_iff.mp hp
    obtain ⟨n, _, rfl⟩ := List.sublist_replicate_iff.mp hr
    refine ⟨q, hq, ?_⟩
    simp only [pad, List.length_append, List.length_map, List.length_replicate, List.sum_append,
      List.sum_replicate, smul_eq_mul, mul_one, sum_shift] at hlen hsum
    omega
  · rintro ⟨s, hs, hsum⟩
    have hlen := hs.length_le
    refine ⟨s.map shift ++ List.replicate (as.length - s.length) 1,
      (hs.map shift).append ((List.replicate_sublist_replicate 1).2 (Nat.sub_le _ _)), ?_, ?_⟩ <;>
      simp only [pad, List.length_append, List.length_map, List.length_replicate, List.sum_append,
        List.sum_replicate, smul_eq_mul, mul_one, sum_shift] <;> omega

private def shiftRaw : Bits → Bits := blocks [true, true] (fun b => [true, b]) (fun _ => [false])

private theorem encode_shift (a : ℕ) : encodeNat (shift a) = true :: encodeNat a := by
  rw [TM2Recursive.encodeNat_eq_cons (by simp [shift] : shift a ≠ 0)]
  have hm : shift a % 2 = 1 := by unfold shift; omega
  have hd : shift a / 2 = a := by unfold shift; omega
  simp [hm, hd]

private theorem shiftRaw_frame (p r : Bits) :
    shiftRaw (delimit p ++ r) = delimit (true :: p) ++ shiftRaw r := by
  unfold shiftRaw
  rw [blocks_frame, DenseSAT.Converter.delimit_eq]
  simp [List.append_assoc]

private theorem shiftRaw_frames (ps : List Bits) :
    shiftRaw (frames ps) = frames (ps.map (true :: ·)) := by
  induction ps with
  | nil => simp [shiftRaw, frames]
  | cons p ps ih => rw [frames_cons, shiftRaw_frame, ih, List.map_cons, frames_cons]

private theorem decode_shift (p : Bits) : decodeNat (true :: p) = shift (decodeNat p) := by
  have hn : FramedCNF.normalizeNat (true :: p) = true :: FramedCNF.normalizeNat p := by
    cases p with
    | nil => rfl
    | cons b p => simp [FramedCNF.normalizeNat, List.getLast?_cons_cons, apply_ite]
  rw [FramedCNF.normalizeNat_eq_encode_decode, FramedCNF.normalizeNat_eq_encode_decode,
    ← encode_shift] at hn
  simpa only [decode_encodeNat] using congrArg decodeNat hn

private theorem decode_padded_frames (ps : List Bits) :
    bitDecode (shiftRaw (frames ps) ++ ones (frames ps)) = some (pad (ps.map decodeNat)) := by
  rw [shiftRaw_frames, ones_frames, encode_list, ← frames_append, decode_list_nat,
    undelimitBlocks_flatten_delimit]
  simp [pad, List.map_append, List.map_map, Function.comp_def, decode_shift, decode_encodeNat]

-- Every complete frame ends in `false`; a final `true` makes any prefix undecodable.
private theorem decode_append_true (x : Bits) : bitDecode (α := List ℕ) (x ++ [true]) = none := by
  have hlast (ps : List Bits) : (frames ps).getLast? ≠ some true := by
    induction ps with
    | nil => decide
    | cons p ps ih =>
      rw [frames_cons, List.getLast?_append, DenseSAT.Converter.delimit_eq p,
        List.getLast?_append]
      cases h : (frames ps).getLast? <;> simp_all
  rw [decode_list_nat, Option.map_eq_none_iff]
  cases h : undelimitBlocks (x ++ [true]) with
  | none => rfl
  | some ps =>
    exfalso
    apply (hlast ps).elim
    change ((ps.map delimit).flatten).getLast? = some true
    rw [← blocks_decode_sound h]
    simp

private def padRaw (x : Bits) : Bits := shiftRaw x ++ ones x ++ listRejectSuffix x

private theorem polyPadRaw : IsPolyTime padRaw :=
  polyAppend (polyAppend (polyBlocks _ _ _) (polyBlocks _ _ _)) polyListRejectSuffix

private theorem pad_correct (x : Bits) :
    Partition.partitionDec x = equalCardinalityPartitionDec (padRaw x) := by
  cases hx : undelimitBlocks x with
  | none =>
    have hd : bitDecode (α := List ℕ) x = none := by simp [decode_list_nat, hx]
    have hp : bitDecode (α := List ℕ) (padRaw x) = none := by
      rw [padRaw, listRejectSuffix, hx]
      exact decode_append_true _
    simp [Partition.partitionDec, equalCardinalityPartitionDec, hd, hp]
  | some ps =>
    have hd : bitDecode x = some (ps.map decodeNat) := by simp [decode_list_nat, hx]
    have hp : bitDecode (padRaw x) = some (pad (ps.map decodeNat)) := by
      rw [padRaw, listRejectSuffix, hx]
      simpa only [Option.isSome_some, ↓reduceIte, List.append_nil, blocks_decode_sound hx] using
        decode_padded_frames ps
    simp [Partition.partitionDec, equalCardinalityPartitionDec, hd, hp, pad_wellFormed,
      feasible_pad]

private theorem hardness : NPHard equalCardinalityPartitionDec :=
  NPHard.of_polyManyOneRed Partition.partition_npComplete.2 ⟨padRaw, polyPadRaw, pad_correct⟩

/-- **PARTITION into halves of equal cardinality is NP-complete.** Source: Garey and Johnson (1979),
[SP12], comment. -/
public theorem equalCardinalityPartition_npComplete :
    equalCardinalityPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L equalCardinalityPartitionDec :=
  ⟨membership, hardness⟩

end MetaMathlibExt.Complexity.NPComplete.EqualCardinalityPartition
