/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Comprehension
public import CSLibExt.Computability.Complexity.Karp.SubsetSumVerify
public import MathlibExt.Computability.BinaryNatEncoding
import CSLibExt.Computability.Complexity.FramedCNF.NormalizeMachine

/-!
# Compositional polynomial-time binary addition

The carry and sum bits use the shared verifier's ripple-carry functions.
Each iteration consumes a bit from the second operand. The residual words
and the accumulated output fit in the initial framed machine state.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.BinaryAddition

open MetaMathlibExt ComplexityTheory BitstringEncoding
open BitScan Comprehension Iteration Karp.SSVerify

local notation "Bits" => List Bool

private theorem polyInc (c : Bool) : IsPolyTime (incB c) := by
  let step (carry a : Bool) : Bool × Bits := (a && carry, [a ^^ carry])
  let finish (carry : Bool) : Bits := if carry then [true] else []
  have h : scan step finish c = incB c := by
    funext x
    induction x generalizing c with
    | nil => rfl
    | cons b x ih => exact congrArg ((b ^^ c) :: ·) (ih _)
  exact h ▸ polyScan step finish c

private def st (x y : Bits) (c : Bool) (acc : Bits) := pack x (pack y (pack [c] acc))

private def step (s : Bits) : Bits :=
  let x := hd s
  let y := hd (tl s)
  let c := (hd (tl (tl s))).headD false
  let acc := tl (tl (tl s))
  if y.isEmpty then false :: (acc ++ incB c x)
  else true :: st x.tail y.tail (carry (x.headD false) (y.headD false) c)
    (acc ++ [x.headD false ^^ y.headD false ^^ c])

private theorem polyStep : IsPolyTime step := by
  let hx := polyField true false
  let hr := polyField false true
  let hy := hr.comp hx
  let hc := ((hr.comp hr).comp hx).comp polyHead
  let ha := (hr.comp hr).comp hr
  have hoff := polyIf hc (hx.comp (polyInc true)) (hx.comp (polyInc false))
  have hoff' : IsPolyTime
      (fun s => incB ((hd (tl (tl s))).headD false) (hd s)) := by
    convert hoff using 1
    funext s
    change incB _ _ = if (hd (tl (tl s))).headD false then incB true (hd s) else incB false (hd s)
    cases (hd (tl (tl s))).headD false <;> rfl
  have hn := polyBool3 carry (hx.comp polyHead) (hy.comp polyHead) hc
  have hv := polyBool3 (fun a b c => a ^^ b ^^ c) (hx.comp polyHead) (hy.comp polyHead) hc
  exact polyIf (hy.comp polyEmpty) (polyAppend (polyConst [false]) (polyAppend ha hoff'))
    (polyAppend (polyConst [true]) (polyPack (hx.comp polyTail)
      (polyPack (hy.comp polyTail) (polyPack hn (polyAppend ha hv)))))

private theorem room (x y : Bits) (b c : Bool) (acc : Bits) :
    (st x.tail y c (acc ++ [b])).length ≤ (st x (false :: y) true acc).length := by
  simp [st, pack, length_delimit]
  omega

private theorem run (N : ℕ) (x y : Bits) (c : Bool) (acc : Bits) (h : (st x y c acc).length ≤ N) :
    Iterates step N (y.length + 1) (st x y c acc) (acc ++ addB c x y) := by
  induction y generalizing x c acc with
  | nil => apply Iterates.halt h; simp [step, st, addB]
  | cons b y ih =>
    let a := x.headD false
    let c' := carry a b c
    let d := a ^^ b ^^ c
    have r : (st x.tail y c' (acc ++ [d])).length ≤ (st x (b :: y) c acc).length := by
      calc
        _ ≤ (st x (false :: y) true acc).length := room x y d c' acc
        _ = _ := by simp [st, pack, length_delimit]
    apply Iterates.next h (y := st x.tail y c' (acc ++ [d]))
    · simp [step, st, a, c', d]
    · simpa only [addB, List.append_assoc, List.singleton_append, List.length_cons, a, c', d]
        using ih x.tail c' (acc ++ [d]) (r.trans h)

/-- The ripple-carry sum of two framed raw bit vectors is polynomial time. -/
theorem polyAddPacked : IsPolyTime (fun z : Bits => addB false (hd z) (tl z)) := by
  let init (z : Bits) := st (hd z) (tl z) false []
  have hi : IsPolyTime init :=
    polyPack (polyField true false) (polyPack (polyField false true)
      (polyPack (polyConst [false]) (polyConst [])))
  apply isPolyTime_of_iterates_from hi polyStep (Polynomial.X + 1) Polynomial.X
  intro z
  refine ⟨(tl z).length + 1, ?_, ?_⟩
  · simp [init, st, pack, length_delimit]
    omega
  · simpa [init] using run (init z).length (hd z) (tl z) false [] le_rfl

/-- Add two arbitrary decoded natural-number fields and emit the canonical
binary result. The polynomial is in the two word lengths. -/
theorem polyDecodedAdd : IsPolyTime (fun p : Bits × Bits =>
    bitEncode (Computability.decodeNat p.1 + Computability.decodeNat p.2)) := by
  let norm := FramedCNF.NormalizeMachine.isPolyTime_normalizeNat
  have hn := (((norm.map_fst.comp isPolyTime_swap).comp norm.map_fst).comp isPolyTime_swap)
  have hp : IsPolyTime (fun p : Bits × Bits => pack p.1 p.2) :=
    polyDelimit.map_fst.comp polyAppendPair
  have h := (hn.comp hp).comp polyAddPacked
  simpa only [Function.comp_def, Prod.swap, hd_pack, tl_pack,
    FramedCNF.normalizeNat_eq_encode_decode, addB_encodeNat, Bool.toNat_false, Nat.add_zero,
    BinaryNatEncoding.bitEncode_nat] using h

end Cslib.Complexity.PolynomialEncoding.BinaryAddition
