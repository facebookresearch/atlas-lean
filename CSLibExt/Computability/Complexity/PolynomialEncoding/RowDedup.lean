/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.PolynomialEncoding.Represented
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip
import Mathlib.Data.List.Enum
public import Mathlib.Data.List.Dedup

/-!
# Removing repeated rows in polynomial time

The output order follows Lean's list deduplication, which retains the last occurrence.
-/

@[expose] public section

namespace Cslib.Complexity.PolynomialEncoding.Comprehension.Represented

open MetaMathlibExt BitstringEncoding ComplexityTheory

local notation "Bits" => List Bool

/-- Equality of values in an injective representation is decided by comparing their words. -/
theorem equal {D A : Type} [DecidableEq A] {e : D → Bits} {enc : A → Bits}
    (inj : Function.Injective enc) {a b : D → A}
    (ha : Represented e (fun x => enc (a x))) (hb : Represented e (fun x => enc (b x))) :
    Represented e (fun x => [decide (a x = b x)]) := by
  apply (ha.test₂ BitZip.polyEq hb).transport
  intro x
  congr 1
  exact Bool.eq_iff_iff.mpr (by simp [inj.eq_iff])

private def cmpLength (q : Bool) (a b : Option Bool) : Bool :=
  if a.isNone then true else if b.isNone then false else q

private theorem foldLength (q : Bool) (x y : Bits) : BitZip.fold cmpLength q x y =
    decide (x.length < y.length ∨ x.length = y.length ∧ q) := by
  match x, y with
  | [], [] => simp [BitZip.fold.eq_1]
  | [], b :: ys =>
    rw [BitZip.fold.eq_2, foldLength]
    simp [cmpLength]
    omega
  | a :: xs, [] =>
    rw [BitZip.fold.eq_3, foldLength]
    simp [cmpLength]
  | a :: xs, b :: ys =>
    rw [BitZip.fold.eq_4, foldLength]
    simp [cmpLength]
termination_by x.length + y.length

/-- Strict length comparison of two raw words. -/
theorem polyShorter : IsPolyTime (fun p : Bits × Bits => decide (p.1.length < p.2.length)) := by
  simpa [foldLength] using BitZip.polyFold cmpLength id false

private def later {A : Type} [DecidableEq A] (a b : A × ℕ) : Bool := decide (a.2 < b.2 ∧ a.1 = b.1)

private theorem last_occurrences {A : Type} [DecidableEq A] (xs : List A) (i : ℕ) :
    (((xs.zipIdx i).filter fun a => !(xs.zipIdx i).any (later a)).map Prod.fst) = xs.dedup := by
  induction xs generalizing i with
  | nil => rfl
  | cons v xs ih =>
    rw [List.zipIdx_cons]
    let tail := xs.zipIdx (i+1)
    have ht (p : A × ℕ) (hp : p ∈ tail) : i < p.2 := by
      have h : ∀ p ∈ xs.zipIdx (i+1), i < p.2 := List.forall_mem_zipIdx.mpr (by intros; omega)
      exact h _ hp
    have hf (p : A × ℕ) (hp : p ∈ tail) : later p (v,i) = false := by
      have := ht p hp
      simp [later]
      omega
    have hh : tail.any (later (v,i)) = decide (v ∈ xs) := by
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq, List.any_eq_true, List.exists_mem_zipIdx]
      simp [later, List.mem_iff_getElem]
      grind
    change ((((v,i) :: tail).filter fun a => !((v,i) :: tail).any (later a)).map Prod.fst) = _
    have he : (tail.filter fun p => !((v,i) :: tail).any (later p)) =
        tail.filter fun p => !tail.any (later p) := by
      apply List.filter_congr
      intro p hp
      simp [hf p hp]
    rw [List.filter_cons, he]
    have hh0 : later (v,i) (v,i) = false := by simp [later]
    by_cases mem : v ∈ xs
    · simpa [List.any_cons, hh0, hh, mem, List.dedup_cons_of_mem, tail] using ih (i+1)
    · simpa [List.any_cons, hh0, hh, mem, List.dedup_cons_of_notMem, tail] using
        congrArg (v :: ·) (ih (i+1))


/-- Deduplicate any table with injectively encoded rows in polynomial time. -/
theorem dedup {D A : Type} [DecidableEq A] {enc : A → Bits} (inj : Function.Injective enc)
    {e : D → Bits} {rows : D → List A} (hr : Represented e (fun x => frames enc (rows x))) :
    Represented e (fun x => frames enc (rows x).dedup) := by
  let v := numbered enc
  let p := pair v e
  have val : Represented v (fun a => enc a.1) :=
    ⟨_, BitScan.polyField false true, by intro a; exact tl_pack (unary a.2) (enc a.1)⟩
  have pos : Represented v (fun a => unary a.2) :=
    ⟨_, BitScan.polyField true false, by intro a; exact hd_pack (unary a.2) (enc a.1)⟩
  have ix := hr.enumerate
  have lt := ((pos.fst e).snd v).test₂ polyShorter (pos.fst p)
  have test := lt.both (equal inj ((val.fst e).snd v) (val.fst p))
  have existsLater := (ix.snd v).testAny (test.transport
    (g := fun a : (A × ℕ) × ((A × ℕ) × D) => [later a.2.1 a.1])
    (by
      intro a
      by_cases hi : a.2.1.2 < a.1.2 <;> by_cases h : a.2.1.1 = a.1.1 <;> simp [later, hi, h]))
  apply ((ix.filtered existsLater.neg).mapped (val.fst e)).transport
  intro x
  exact congrArg (frames enc) (last_occurrences (rows x) 0)

end Cslib.Complexity.PolynomialEncoding.Comprehension.Represented
