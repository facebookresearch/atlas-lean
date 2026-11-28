/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Composition
import CSLibExt.Computability.Complexity.PolynomialEncoding.Comprehension
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip
import CSLibExt.Computability.Complexity.PairEncodingConverter

/-!
# Composition of fixed-parameter reductions

The second reduction uses a computable unary padding at its *output*
parameter from the first reduction. Prepare a finite table of all possible
padding words up to the first reduction's parameter bound. The table and
the original padding are computable advice depending only on the original
parameter. Its lookup, including reading and copying the selected word,
takes polynomial time on the padded input.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

open BitstringEncoding ComplexityTheory Cslib.Complexity
open Cslib.Complexity.PolynomialEncoding
open BitScan Comprehension

local notation "Bits" => List Bool

private def unary (i : ℕ) : Bits := List.replicate i true

private theorem computable_unary : Computable unary := by
  have h := Computable.nat_rec (α := ℕ) (σ := Bits) Computable.id (Computable.const [])
    (Computable.list_cons.comp (Computable.const true)
      (Computable.snd.comp Computable.snd)).to₂
  refine h.of_eq ?_
  intro i
  induction i with
  | zero => rfl
  | succ i ih => exact congrArg (true :: ·) ih

private theorem primrec_delimit : Primrec delimit := by
  have h := Primrec.list_foldr (α := Bits) (β := Bool) (σ := Bits) Primrec.id
    (Primrec.const [false]) (Primrec.list_cons.comp (Primrec.const true)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂
  refine h.of_eq ?_
  intro x
  induction x with
  | nil => rfl
  | cons b x ih => exact congrArg (true :: b :: ·) ih

private def row (f : ℕ → ℕ) (i : ℕ) : Bits := pack (bitEncode i) (unary (f i))

private def table (f : ℕ → ℕ) (n : ℕ) : List Bits :=
  Nat.rec [row f 0] (fun i rs => row f (i + 1) :: rs) n

private theorem computable_table {f : ℕ → ℕ} (hf : Computable f) : Computable (table f) := by
  have hr : Computable (row f) := Computable.list_append.comp
    (primrec_delimit.to_comp.comp TM2Recursive.primrec_encodeNat.to_comp)
    (computable_unary.comp hf)
  exact Computable.nat_rec Computable.id (Computable.const [row f 0])
    (Computable.list_cons.comp (hr.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)).to₂

private def advice (a b g : ℕ → ℕ) (k : ℕ) : Bits :=
  pack (unary (a k)) ((table b (g k)).flatMap delimit)

private theorem computable_advice {a b g : ℕ → ℕ}
    (ha : Computable a) (hb : Computable b) (hg : Computable g) : Computable (advice a b g) := by
  have hfr : Primrec (fun rs : List Bits => rs.flatMap delimit) :=
    Primrec.list_flatMap Primrec.id (primrec_delimit.comp Primrec.snd).to₂
  exact Computable.list_append.comp (primrec_delimit.to_comp.comp (computable_unary.comp ha))
    (hfr.to_comp.comp ((computable_table hb).comp hg))

private def emit (w : Bits) : Bits := if hd (hd w) == tl w then tl (hd w) else []

private theorem polyEmit : IsPolyTime emit := by
  let hL := polyField true false
  let hR := polyField false true
  have h := (polyPair (hL.comp hL) hR).comp BitZip.polyEq
  exact polyIf (h.comp (isPolyTime_of_bool fun b => [b])) (hL.comp hR) (polyConst [])

private theorem codes_eq (i j : ℕ) : (bitEncode i == bitEncode j) = (i == j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  constructor
  · intro h
    apply Option.some.inj
    simpa only [bitDecode_bitEncode] using congrArg (bitDecode (α := ℕ)) h
  · exact congrArg bitEncode

private theorem emit_row (f : ℕ → ℕ) (j i : ℕ) :
    emit (pack (row f j) (bitEncode i)) = if j = i then unary (f j) else [] := by
  simp only [emit, row, hd_pack, tl_pack, codes_eq, beq_iff_eq]

private theorem lookup (f : ℕ → ℕ) (n i : ℕ) :
    (table f n).flatMap (fun r => emit (pack r (bitEncode i))) =
      if i ≤ n then unary (f i) else [] := by
  induction n with
  | zero =>
    change emit (pack (row f 0) (bitEncode i)) ++ [] = _
    rw [emit_row]
    by_cases hi : i = 0 <;> simp_all [eq_comm]
  | succ n ih =>
    change emit (pack (row f (n + 1)) (bitEncode i)) ++
      (table f n).flatMap _ = _
    rw [emit_row, ih]
    by_cases hi : i = n + 1
    · subst i
      simp
    · have : (i ≤ n + 1) = (i ≤ n) := propext (by omega)
      simp [Ne.symm hi, this]

private theorem polyPairPack : IsPolyTime (fun p : Bits × Bits => pack p.1 p.2) :=
  polyDelimit.map_fst.comp polyAppendPair

/-- Writing the canonical representation of an arbitrary input as a bitstring
is polynomial time, including the extra framing of the output bit list. -/
theorem isPolyTime_bitEncode {α : Type} [BitstringEncoding α] :
    IsPolyTime (bitEncode (α := α)) := by
  let m := DenseSAT.EncodeBits.computable
  exact ⟨{ m with outputsFun := fun a => m.outputsFun (bitEncode a) }⟩

private theorem polyFirst : IsPolyTime (Prod.fst : Bits × ℕ → Bits) := by
  apply polyEncoded (polyField true false)
  rintro ⟨x, k⟩
  change field _ _ (delimit (bitEncode x) ++ bitEncode k) = bitEncode x
  simp [field_delimit]

private theorem polyKey : IsPolyTime (fun p : Bits × ℕ => bitEncode p.2) := by
  apply polyEncoded ((polyField false true).comp (isPolyTime_bitEncode (α := Bits)))
  rintro ⟨x, k⟩
  change bitEncode (field _ _ (delimit (bitEncode x) ++ bitEncode k)) = bitEncode (bitEncode k)
  simp [field_delimit]

/-- A computably bounded intermediate parameter permits composition of two
FPT-time machines on ATLAS's unary-padding definition. -/
theorem FPTTime.comp_bounded {β : Type} [BitstringEncoding β]
    {R : Bits × ℕ → Bits × ℕ} {T : Bits × ℕ → β} (hr : FPTTime R) (ht : FPTTime T)
    {g : ℕ → ℕ} (hg : Computable g) (hbound : ∀ x k, (R (x, k)).2 ≤ g k) :
    FPTTime (T ∘ R) := by
  obtain ⟨a, ha, A, hA, eqA⟩ := hr
  obtain ⟨b, hb, B, hB, eqB⟩ := ht
  let first (z : Bits) := A (hd z, hd (tl z))
  have hfirst : IsPolyTime first :=
    (polyPair (polyField true false) ((polyField false true).comp (polyField true false))).comp hA
  let nextPad (z : Bits) := (rowsOf (tl (tl z))).flatMap
    (fun r => emit (pack r (bitEncode (first z).2)))
  have hpad : IsPolyTime nextPad :=
    polyFlatMap ((polyField false true).comp (polyField false true)) (hfirst.comp polyKey) polyEmit
  let run (p : Bits × Bits) :=
    let z := pack p.1 p.2
    B ((first z).1, nextPad z)
  have hrun : IsPolyTime run := polyPairPack.comp ((polyPair (hfirst.comp polyFirst) hpad).comp hB)
  refine FPTTime.of_computable_advice (computable_advice ha hb hg) hrun ?_
  intro x k
  let z := pack x (advice a b g k)
  have hfirstz : first z = R (x, k) := by
    simpa [first, z, advice, unary] using (eqA x k).symm
  have hpz : nextPad z = unary (b (R (x, k)).2) := by
    simp only [nextPad, hfirstz]
    simp only [z, advice, tl_pack, rowsOf_frames, lookup, hbound x k, ite_true]
  change T (R (x, k)) = B ((first z).1, nextPad z)
  rw [hfirstz, hpz]
  exact eqB _ _

/-- FPT many-one reductions are transitive. Both machine times and the
possibly nonmonotone output-parameter bound are composed effectively. -/
theorem FPTReduces.trans {P Q S : ParamProblem} (h₁ : FPTReduces P Q) (h₂ : FPTReduces Q S) :
    FPTReduces P S := by
  obtain ⟨R, hr, g, hg, hR⟩ := h₁
  obtain ⟨T, ht, b, hb, hT⟩ := h₂
  refine ⟨T ∘ R, hr.comp_bounded ht hg (fun x k => (hR x k).1),
    parameterEnvelope b ∘ g, (computable_parameterEnvelope hb).comp hg, ?_⟩
  intro x k
  exact ⟨(hT _ _).1.trans (parameterEnvelope_le (hR x k).1), (hR x k).2.trans (hT _ _).2⟩

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
