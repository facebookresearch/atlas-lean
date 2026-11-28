/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.BagRows
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Represented
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitZip

/-!
# Compiling the local assignment tests for weighted signed clauses

The tests use bounded scans over the listed slots, assignments, clauses and literals.
All integers are compared at their binary widths.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows

open MetaMathlibExt BitstringEncoding ComplexityTheory Cslib.Complexity
open PolynomialEncoding PolynomialEncoding.Comprehension

local notation "Bits" => List Bool
local notation "N" => (bitEncode (α := ℕ))
local notation "Entry" => (pair N N)
local notation "Lit" => (pair N (fun b : Bool => [b]))
local notation "Cl" => (frames Lit)

private theorem first {D A B : Type} {e : D → Bits} {a : A → Bits} {b : B → Bits}
    {f : D → A × B} (h : Represented e (fun x => pair a b (f x))) :
    Represented e (fun x => a (f x).1) :=
  (h.after (BitScan.polyField true false)).transport (fun _ => hd_pack _ _)

private theorem second {D A B : Type} {e : D → Bits} {a : A → Bits} {b : B → Bits}
    {f : D → A × B} (h : Represented e (fun x => pair a b (f x))) :
    Represented e (fun x => b (f x).2) :=
  (h.after (BitScan.polyField false true)).transport (fun _ => tl_pack _ _)

/-- Compare two canonical binary naturals. -/
theorem represented_natLE {D : Type} {e : D → Bits} {a b : D → ℕ}
    (h : Represented e (fun x => N (a x))) (k : Represented e (fun x => N (b x))) :
    Represented e (fun x => [decide (a x ≤ b x)]) :=
  (h.test₂ BitZip.polyDecodedLE k).transport (by
    intro x
    change [decide (Computability.decodeNat (Computability.encodeNat _) ≤
      Computability.decodeNat (Computability.encodeNat _))] = _
    rw [Computability.decode_encodeNat, Computability.decode_encodeNat])

/-- Strict comparison of canonical binary naturals. -/
theorem represented_natLT {D : Type} {e : D → Bits} {a b : D → ℕ}
    (h : Represented e (fun x => N (a x))) (k : Represented e (fun x => N (b x))) :
    Represented e (fun x => [decide (a x < b x)]) :=
  (represented_natLE k h).neg.transport (by
    intro x
    by_cases p : a x < b x
    · simp [p, Nat.not_le_of_gt p]
    · simp [p, Nat.le_of_not_gt p])

/-- Equality of canonical binary naturals. -/
theorem represented_natEq {D : Type} {e : D → Bits} {a b : D → ℕ}
    (h : Represented e (fun x => N (a x))) (k : Represented e (fun x => N (b x))) :
    Represented e (fun x => [decide (a x = b x)]) := by
  apply (h.test₂ BitZip.polyEq k).transport
  intro x
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro hh
    change N (a x) = N (b x) at hh
    have de := congrArg (bitDecode (α := ℕ)) hh
    simpa only [bitDecode_bitEncode, Option.some.injEq] using de
  · exact congrArg N

section

variable {D : Type} {e : D → Bits} {p q : D → Prop}
variable [∀ x, Decidable (p x)] [∀ x, Decidable (q x)]
variable (hp : Represented e (fun x => [decide (p x)]))
variable (hq : Represented e (fun x => [decide (q x)]))
include hp hq

private theorem andD : Represented e (fun x => [decide (p x ∧ q x)]) :=
  (hp.both hq).transport (by intro x; by_cases h : p x <;> simp [h])

private theorem orD : Represented e (fun x => [decide (p x ∨ q x)]) :=
  (hp.cond (Represented.const _ [true]) hq).transport (by intro x; by_cases h : p x <;> simp [h])

private theorem impD : Represented e (fun x => [decide (p x → q x)]) :=
  (hp.cond hq (Represented.const _ [true])).transport (by intro x; by_cases h : p x <;> simp [h])

end

private theorem allRows {D A : Type} {e : D → Bits} {r : A → Bits}
    {xs : D → List A} {p : A × D → Bool} (rs : Represented e (fun x => frames r (xs x)))
    (hr : Represented (pair r e) (fun a => [p a])) :
    Represented e (fun x => [(xs x).all fun a => p (a,x)]) :=
  ((rs.testAny hr.neg).neg).transport (by simp [List.not_any_eq_all_not])

/-- The test for a locally falsified literal is polynomial-time for arbitrary represented inputs. -/
theorem represented_forcesFalse {D : Type} {e : D → Bits}
    {slots : D → List ℕ} {a : D → Local} {lit : D → ℕ × Bool}
    (hs : Represented e (fun x => frames N (slots x)))
    (ha : Represented e (fun x => frames Entry (a x)))
    (hl : Represented e (fun x => Lit (lit x))) :
    Represented e (fun x => [forcesFalse (slots x) (a x) (lit x)]) := by
  let slotEnv := pair N e
  have j := (Represented.input Entry).fst slotEnv
  have i := ((Represented.input N).fst e).snd Entry
  have v := ((first hl).snd N).snd Entry
  have pred := orD (andD (represented_natLE i (first j)) (represented_natLT (second j) v))
    (andD (represented_natLE (first j) i) (represented_natLT v (second j)))
  have yes := allRows hs ((ha.snd N).testAny pred)
  have cmp := represented_natEq (second ((Represented.input Entry).fst e)) ((first hl).snd Entry)
  have no := ha.testAny cmp
  apply ((second hl).cond yes no).transport
  intro x
  cases h : (lit x).2 <;> simp [forcesFalse, h, Bool.beq_eq_decide_eq]

private theorem sameSlot {D : Type} {e : D → Bits} {a b : D → ℕ × ℕ}
    (ha : Represented e (fun x => Entry (a x))) (hb : Represented e (fun x => Entry (b x))) :
    Represented e (fun x => [decide ((a x).1 = (b x).1 → (a x).2 = (b x).2)]) :=
  impD (represented_natEq (first ha) (first hb)) (represented_natEq (second ha) (second hb))

/-- Checking agreement on every shared slot of two local assignments is polynomial-time. -/
theorem represented_agrees {D : Type} {e : D → Bits} {a b : D → Local}
    (ha : Represented e (fun x => frames Entry (a x)))
    (hb : Represented e (fun x => frames Entry (b x))) :
    Represented e (fun x => [agrees (a x) (b x)]) :=
  allRows ha (allRows (hb.snd Entry)
    (sameSlot (((Represented.input Entry).fst e).snd Entry)
      ((Represented.input Entry).fst (pair Entry e))))

/-- Check slot coverage, increasing order, and all clauses in polynomial time. -/
theorem represented_allowed {D : Type} {e : D → Bits}
    {slots shape : D → List ℕ} {p : D → Formula} {a : D → Local}
    (hs : Represented e (fun x => frames N (slots x)))
    (hb : Represented e (fun x => frames N (shape x)))
    (hp : Represented e (fun x => frames Cl (p x)))
    (ha : Represented e (fun x => frames Entry (a x))) :
    Represented e (fun x => [allowed (slots x) (shape x) (p x) (a x)]) := by
  have slot := (Represented.input N).fst e
  have ent := (Represented.input Entry).fst e
  have covers := allRows hb ((ha.snd N).testAny
    (represented_natEq (first ((Represented.input Entry).fst _)) (slot.snd Entry)))
  have inShape := allRows ha ((hb.snd Entry).testAny
    (represented_natEq ((Represented.input N).fst _) ((first ent).snd N)))
  have fstRow := ent.snd Entry
  have sndRow := (Represented.input Entry).fst (pair Entry e)
  have mono := allRows ha (allRows (ha.snd Entry) (andD (sameSlot fstRow sndRow)
    (impD (represented_natLT (first fstRow) (first sndRow))
      (represented_natLT (second fstRow) (second sndRow)))))
  have ff := represented_forcesFalse ((hs.snd Cl).snd Lit) ((ha.snd Cl).snd Lit)
    ((Represented.input Lit).fst (pair Cl e))
  have clauses := allRows hp (allRows ((Represented.input Cl).fst e) ff).neg
  apply (((covers.both inShape).both mono).both clauses).transport
  intro x
  have contains (l : List ℕ) (a : ℕ) :
      (l.any fun b => decide (b = a)) = l.contains a := Bool.eq_iff_iff.mpr (by
    simp [List.any_eq_true])
  simp only [allowed, Bool.beq_eq_decide_eq, contains]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized.BagRows
