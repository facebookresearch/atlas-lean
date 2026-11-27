/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Identity
import CSLibExt.Computability.Complexity.PolynomialEncoding.BitOperations
import CSLibExt.Computability.Complexity.Karp.SubsetSumDigits

/-!
# Parameter-dependent padding and composition

Computable padding can carry a whole computable word. Use the positive
binary number obtained by appending a most significant one to that word as
the length of the unary padding. The polynomial-time machine reads its
length in binary and strips the final sentinel.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

open ComplexityTheory BitstringEncoding
open Cslib.Complexity.PolynomialEncoding.BitScan

local notation "Bits" => List Bool

/-- A computable envelope for a possibly nonmonotone output-parameter bound. -/
def parameterEnvelope (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.rec (f 0) (fun i a => max a (f (i + 1))) n

theorem parameterEnvelope_le {f : ℕ → ℕ} {i n : ℕ} (h : i ≤ n) :
    f i ≤ parameterEnvelope f n := by
  induction n with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact le_rfl
  | succ n ih =>
    by_cases hi : i ≤ n
    · exact (ih hi).trans (le_max_left ..)
    · have : i = n + 1 := by omega
      subst i
      exact le_max_right ..

theorem computable_parameterEnvelope {f : ℕ → ℕ} (hf : Computable f) :
    Computable (parameterEnvelope f) :=
  Computable.nat_rec Computable.id (Computable.const (f 0))
    (Primrec.nat_max.to_comp.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.succ.comp (Computable.fst.comp Computable.snd)))).to₂

/-- Postcomposition with an ordinary polynomial-time reduction may change
the parameter by any computably bounded amount. -/
theorem FPTReduces.postcomp_poly {P Q S : ParamProblem} (h : FPTReduces P Q)
    {T : Bits × ℕ → Bits × ℕ} (hT : IsPolyTime T) (b : ℕ → ℕ) (hb : Computable b)
    (hbound : ∀ x k, (T (x, k)).2 ≤ b k)
    (hcorrect : ∀ x k, Q x k ↔ S (T (x, k)).1 (T (x, k)).2) : FPTReduces P S := by
  obtain ⟨R, hr, g, hg, h⟩ := h
  refine ⟨T ∘ R, hr.comp_poly hT, parameterEnvelope b ∘ g,
    (computable_parameterEnvelope hb).comp hg, ?_⟩
  intro x k
  exact ⟨(hbound _ _).trans (parameterEnvelope_le (h x k).1), (h x k).2.trans (hcorrect _ _)⟩

private def delay (s : Option Bool) (b : Bool) : Option Bool × Bits := (some b, s.toList)

private theorem scan_delay (b : Bool) (w : Bits) :
    scan delay (fun _ => []) (some b) w = (b :: w).dropLast := by
  induction w generalizing b with
  | nil => rfl
  | cons a w ih => exact congrArg (b :: ·) (ih a)

/-- A finite-state transducer can drop the last bit using a one-bit delay. -/
theorem isPolyTime_dropLast : IsPolyTime (fun w : Bits => w.dropLast) := by
  have h : scan delay (fun _ => []) none = fun w => w.dropLast := by
    funext w
    cases w with
    | nil => rfl
    | cons b w => exact scan_delay b w
  exact h ▸ polyScan delay (fun _ => []) none

/-- Any computable parameter-dependent word can be provided to an ordinary
polynomial-time algorithm under the exact unary-padding definition of FPT time. -/
theorem FPTTime.of_computable_advice {β : Type} [BitstringEncoding β] {R : Bits × ℕ → β}
    {a : ℕ → Bits} (ha : Computable a) {A : Bits × Bits → β} (hA : IsPolyTime A)
    (h : ∀ x k, R (x, k) = A (x, a k)) : FPTTime R := by
  let pad (k : ℕ) := TM2Recursive.bitsVal (a k ++ [true])
  have hp : Computable pad := TM2Recursive.primrec_bitsVal.to_comp.comp
    (Computable.list_append.comp ha (Computable.const [true]))
  let read (w : Bits) := (bitEncode w.length).dropLast
  have hread : IsPolyTime read := isPolyTime_encodeLength.comp isPolyTime_dropLast
  let readSnd (p : Bits × Bits) := (p.1, read p.2)
  have hrs : IsPolyTime readSnd := (isPolyTime_swap.comp hread.map_fst).comp isPolyTime_swap
  refine ⟨pad, hp, A ∘ readSnd, hrs.comp hA, ?_⟩
  intro x k
  have recover : read (List.replicate (pad k) true) = a k := by
    simp only [read, List.length_replicate, pad, BinaryNatEncoding.bitEncode_nat]
    rw [Cslib.Complexity.Karp.EmitSS.encodeNat_bitsVal _ (by simp), List.dropLast_concat]
  rw [h]
  change _ = A (x, read _)
  rw [recover]

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
