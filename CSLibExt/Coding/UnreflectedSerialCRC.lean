/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.List.Induction
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Unreflected serial CRC

The bit-level shift-register refinement of the polynomial CRC in
`CSLibExt.Coding.CRC`: an unreflected (non-reflected) serial LFSR
over `ZMod 2` processing a message bit by bit. The register, read
as a polynomial, after the whole message equals the shifted
message polynomial remainder `(m * X^r) % g` — exactly the check
value the polynomial-level encoder appends. The CRC-3 generator
`X^3 + X + 1` fixtures from the roadmap leaf are included, and
reversing the payload changes the result, as the unreflected
convention requires.

Discharges ECE roadmap leaf `ECE.HW.CRC.L1` (serial CRC register
semantics).
-/

@[expose] public section

namespace CSLibExt.Coding.UnreflectedSerialCRC

/-- A payload bit as a polynomial over `ZMod 2`: `1` for `true`, `0` for
`false`. -/
noncomputable def bitPoly (b : Bool) : Polynomial (ZMod 2) :=
  if b then 1 else 0

/-- The message polynomial of an MSB-first payload: for a payload `bits` of
declared length `l = bits.length`, `m = ∑_j bit_j * X^(l-1-j)`, where
`bits.get j` is the `j`-th bit sent. Leading zeros contribute zero terms but
are counted in `l`. -/
noncomputable def messagePoly (bits : List Bool) : Polynomial (ZMod 2) :=
  ∑ j : Fin bits.length,
    bitPoly (bits.get j) * Polynomial.X ^ (bits.length - 1 - j.val)

/-- The polynomial represented by a width-`r` register: register index `i`
holds the coefficient of `X^i` (unreflected). -/
noncomputable def registerToPoly (r : ℕ) (v : Fin r → ZMod 2) : Polynomial (ZMod 2) :=
  ∑ i : Fin r, Polynomial.C (v i) * Polynomial.X ^ i.val

/-- One unreflected serial step, as a hardware transition: the register
shifts toward higher indices, the input bit enters at index `0`, and the
outgoing high bit (the coefficient of `X^(r-1)`) is fed back through the
generator taps `g.coeff i` (addition is XOR in `ZMod 2`). No polynomial
division occurs in the transition itself; `registerToPoly_stepRegister`
proves that this transition represents `(s * X + b) % g`. Zero
initialization and no input/output XOR are used. -/
noncomputable def stepRegister (g : Polynomial (ZMod 2)) (r : ℕ) (v : Fin r → ZMod 2)
    (b : Bool) : Fin r → ZMod 2 :=
  fun i =>
    (if i.val = 0 then (bitPoly b).coeff 0
      else v ⟨i.val - 1, by have hi : i.val < r := i.isLt; omega⟩) +
    (if h : 0 < r then v ⟨r - 1, by omega⟩ * g.coeff i.val else 0)

/-- The zero initial register of width `r`. -/
def initialRegister (r : ℕ) : Fin r → ZMod 2 :=
  fun _ => 0

/-- A Mealy-style machine specification, mirroring the canonical transducer
API shape: a transition function and a start state. -/
structure MealySpec (State In Out : Type) where
  /-- Successor state and output on one input letter. -/
  step : State → In → State × Out
  /-- The start state. -/
  start : State

/-- The zero-init unreflected serial LFSR for generator `g` and register
width `r`, as a Mealy-style machine: state `Fin r → ZMod 2`, input `Bool`,
output the new register, start the zero register. -/
noncomputable def serialLFSR (g : Polynomial (ZMod 2)) (r : ℕ) :
    MealySpec (Fin r → ZMod 2) Bool (Fin r → ZMod 2) where
  step v b := let v' := stepRegister g r v b; (v', v')
  start := initialRegister r

/-- The register reached by running the serial step over `bits` from the
zero initial register. -/
noncomputable def runRegister (g : Polynomial (ZMod 2)) (r : ℕ) (bits : List Bool) :
    Fin r → ZMod 2 :=
  bits.foldl (fun v b => stepRegister g r v b) (initialRegister r)

/-- The final register for a payload: the payload followed by `r` zero
bits, run from the zero initial register. -/
noncomputable def finalRegister (g : Polynomial (ZMod 2)) (r : ℕ) (bits : List Bool) :
    Fin r → ZMod 2 :=
  runRegister g r (bits ++ List.replicate r false)

/-- The concrete CRC-3 generator `X^3 + X + 1` over `ZMod 2`, the running
example of the existing Atlas CRC tests. -/
noncomputable def crc3Generator : Polynomial (ZMod 2) :=
  Polynomial.X ^ 3 + Polynomial.X + 1

/-- Helper: `messagePoly` of the empty payload. -/
private theorem messagePoly_nil_aux : messagePoly [] = 0 := by
  simp [messagePoly]

/-- Helper: `messagePoly` cons recurrence. -/
private theorem messagePoly_cons_aux (b : Bool) (bits : List Bool) :
    messagePoly (b :: bits) = bitPoly b * Polynomial.X ^ bits.length + messagePoly bits := by
  unfold messagePoly
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [List.get_cons_zero]
  have h0 : (bits.length + 1 - 1 - (0 : Fin (bits.length + 1)).val) = bits.length := by
    simp
  rw [h0]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [List.get_cons_succ']
  have hsucc : (i.succ).val = i.val + 1 := Fin.val_succ i
  rw [hsucc]
  congr 1
  congr 1
  omega

/-- Helper: `messagePoly` snoc recurrence. -/
private theorem messagePoly_snoc_aux (bits : List Bool) (b : Bool) :
    messagePoly (bits ++ [b]) = messagePoly bits * Polynomial.X + bitPoly b := by
  induction bits with
  | nil =>
    simp only [List.nil_append, messagePoly_nil_aux, zero_mul, zero_add]
    have hc := messagePoly_cons_aux b []
    simp [messagePoly_nil_aux] at hc
    exact hc
  | cons a tl ih =>
    have hcons1 : messagePoly ((a :: tl) ++ [b]) = messagePoly (a :: (tl ++ [b])) := by
      simp
    rw [hcons1, messagePoly_cons_aux, messagePoly_cons_aux, ih]
    have hlen : (tl ++ [b]).length = tl.length + 1 := by simp
    rw [hlen, pow_succ]
    ring

/-- Helper: `messagePoly` of an append. -/
private theorem messagePoly_append_aux (l1 l2 : List Bool) :
    messagePoly (l1 ++ l2) = messagePoly l1 * Polynomial.X ^ l2.length + messagePoly l2 := by
  induction l1 with
  | nil =>
    simp [messagePoly_nil_aux]
  | cons a tl ih =>
    have h1 : ((a :: tl) ++ l2) = (a :: (tl ++ l2)) := by simp
    rw [h1, messagePoly_cons_aux, messagePoly_cons_aux, ih]
    have hlen : (tl ++ l2).length = tl.length + l2.length := by simp
    rw [hlen, pow_add]
    ring

private theorem bitPoly_false_aux : bitPoly false = 0 := by simp [bitPoly]

private theorem bitPoly_true_aux : bitPoly true = 1 := by simp [bitPoly]

/-- Helper: `messagePoly` of all-false list. -/
private theorem messagePoly_replicate_false_aux (n : ℕ) :
    messagePoly (List.replicate n false) = 0 := by
  induction n with
  | zero => simp [messagePoly_nil_aux]
  | succ k ih =>
    rw [List.replicate_succ, messagePoly_cons_aux, bitPoly_false_aux]
    simp [ih]

private theorem runRegister_nil_aux (g : Polynomial (ZMod 2)) (r : ℕ) :
    runRegister g r [] = initialRegister r := by
  simp [runRegister]

private theorem runRegister_snoc_aux (g : Polynomial (ZMod 2)) (r : ℕ) (bits : List Bool)
    (b : Bool) :
    runRegister g r (bits ++ [b]) = stepRegister g r (runRegister g r bits) b := by
  simp [runRegister, List.foldl_append]

/-- Helper: CRC-3 generator is monic. -/
private theorem crc3_monic_aux : crc3Generator.Monic := by
  unfold crc3Generator
  have h : (Polynomial.X ^ 3 + Polynomial.X + 1 : Polynomial (ZMod 2))
    = Polynomial.X ^ 3 + (Polynomial.X + 1) := by ring
  rw [h]
  apply Polynomial.monic_X_pow_add
  compute_degree!

/-- Helper: CRC-3 generator natDegree. -/
private theorem crc3_natDegree_aux : crc3Generator.natDegree = 3 := by
  unfold crc3Generator
  compute_degree!

/-- Helper: CRC-3 generator degree. -/
private theorem crc3_degree_aux : crc3Generator.degree = 3 := by
  unfold crc3Generator
  compute_degree!

/-- The zero register represents the zero polynomial. -/
theorem registerToPoly_initialRegister (r : ℕ) :
    registerToPoly r (initialRegister r) = 0 := by
  unfold registerToPoly initialRegister
  simp

/-- Helper: coefficients of `registerToPoly`. -/
private theorem coeff_registerToPoly_aux (r : ℕ) (v : Fin r → ZMod 2) (n : ℕ) :
    (registerToPoly r v).coeff n = if h : n < r then v ⟨n, h⟩ else 0 := by
  unfold registerToPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  by_cases hn : n < r
  · rw [dite_eq_left hn]
    have hiff : ∀ i : Fin r, (n = i.val) ↔ (i = ⟨n, hn⟩) := by
      intro i
      constructor
      · intro hcon
        exact Fin.ext hcon.symm
      · intro hcon
        rw [hcon]
    simp only [hiff]
    rw [Finset.sum_ite_eq']
    simp
  · rw [dite_eq_right hn]
    have hzero : ∀ i : Fin r, (if n = i.val then v i else (0 : ZMod 2)) = 0 := by
      intro i
      have hi := i.isLt
      apply ite_eq_right
      omega
    simp only [hzero, Finset.sum_const_zero]

/-- Helper: `registerToPoly` has degree below `r`. -/
private theorem degree_registerToPoly_aux (r : ℕ) (v : Fin r → ZMod 2) :
    (registerToPoly r v).degree < r := by
  unfold registerToPoly
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe r)).mpr
  intro i _
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact WithBot.coe_lt_coe.mpr i.isLt

/-- Helper: the hardware step represents the shifted-plus-bit polynomial up to a
multiple of the generator. -/
private theorem stepRegister_identity_aux (g : Polynomial (ZMod 2)) (r : ℕ)
    (hg : g.Monic) (hr : g.natDegree = r) (hr1 : 1 ≤ r)
    (v : Fin r → ZMod 2) (b : Bool) :
    registerToPoly r (stepRegister g r v b)
      = registerToPoly r v * Polynomial.X + bitPoly b
        + Polynomial.C (v ⟨r - 1, by omega⟩) * g := by
  rw [Polynomial.ext_iff]
  intro n
  by_cases hn0 : n = 0
  · subst hn0
    rw [coeff_registerToPoly_aux, dite_eq_left (by omega : 0 < r)]
    rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_mul_X_zero]
    unfold stepRegister
    rw [ite_eq_left rfl, dite_eq_left (by omega : 0 < r)]
    show (bitPoly b).coeff 0 + v ⟨r - 1, by omega⟩ * g.coeff 0
      = (0 + (bitPoly b).coeff 0) + v ⟨r - 1, by omega⟩ * g.coeff 0
    ring
  · by_cases hn : n < r
    · rw [coeff_registerToPoly_aux, dite_eq_left hn]
      rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul]
      obtain ⟨m, rfl⟩ := (⟨n - 1, by omega⟩ : ∃ m, n = m + 1)
      rw [Polynomial.coeff_mul_X, coeff_registerToPoly_aux,
        dite_eq_left (by omega : m < r)]
      have hb : (bitPoly b).coeff (m + 1) = 0 := by
        cases b <;> simp [bitPoly, Polynomial.coeff_one]
      rw [hb]
      unfold stepRegister
      have hne : (⟨m + 1, hn⟩ : Fin r).val ≠ 0 := by
        show m + 1 ≠ 0
        omega
      rw [ite_eq_right hne, dite_eq_left (by omega : 0 < r)]
      show v ⟨m, by omega⟩ + v ⟨r - 1, by omega⟩ * g.coeff (m + 1)
        = (v ⟨m, by omega⟩ + 0) + v ⟨r - 1, by omega⟩ * g.coeff (m + 1)
      ring
    · rw [coeff_registerToPoly_aux, dite_eq_right hn]
      rw [Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_C_mul]
      obtain ⟨m, rfl⟩ := (⟨n - 1, by omega⟩ : ∃ m, n = m + 1)
      rw [Polynomial.coeff_mul_X, coeff_registerToPoly_aux]
      by_cases hm : m < r
      · rw [dite_eq_left hm]
        have hb : (bitPoly b).coeff (m + 1) = 0 := by
          cases b <;> simp [bitPoly, Polynomial.coeff_one]
        rw [hb]
        have hmr : m + 1 = r := by omega
        have hg1 : g.coeff (m + 1) = 1 := by
          rw [hmr]
          have h := hg.coeff_natDegree
          rwa [hr] at h
        rw [hg1]
        have hmeq : m = r - 1 := by omega
        have hfin : (⟨m, hm⟩ : Fin r) = ⟨r - 1, by omega⟩ := Fin.ext hmeq
        rw [hfin]
        show (0 : ZMod 2) = (v ⟨r - 1, by omega⟩ + 0) + v ⟨r - 1, by omega⟩ * 1
        rw [mul_one, add_zero]
        exact (CharTwo.add_self_eq_zero _).symm
      · rw [dite_eq_right hm]
        have hb : (bitPoly b).coeff (m + 1) = 0 := by
          cases b <;> simp [bitPoly, Polynomial.coeff_one]
        rw [hb]
        have hg0 : g.coeff (m + 1) = 0 := by
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          omega
        rw [hg0]
        simp

/-- One serial step represents one polynomial long-division step:
the register after reading `b` represents `(s * X + b) % g`. -/
theorem registerToPoly_stepRegister (g : Polynomial (ZMod 2)) (r : ℕ)
    (hg : g.Monic) (hr : g.natDegree = r) (v : Fin r → ZMod 2) (b : Bool) :
    registerToPoly r (stepRegister g r v b) =
      Polynomial.modByMonic (registerToPoly r v * Polynomial.X + bitPoly b) g := by
  rcases eq_zero_or_pos r with rfl | hr0
  · have hg1 : g = 1 := by
      have hc : g.coeff 0 = 1 := by
        have h := hg.coeff_natDegree
        rwa [hr] at h
      rw [Polynomial.eq_C_of_natDegree_eq_zero hr, hc, Polynomial.C_1]
    rw [hg1]
    simp [registerToPoly, Polynomial.modByMonic_one]
  · have hr1 : 1 ≤ r := hr0
    have hident := stepRegister_identity_aux g r hg hr hr1 v b
    have hdeg : (registerToPoly r (stepRegister g r v b)).degree < g.degree := by
      have h1 := degree_registerToPoly_aux r (stepRegister g r v b)
      have h2 : g.degree = (r : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hg.ne_zero, hr]
      rw [h2]
      exact h1
    have hself := (Polynomial.modByMonic_eq_self_iff hg).mpr hdeg
    have hdiv : g ∣ registerToPoly r (stepRegister g r v b)
        - (registerToPoly r v * Polynomial.X + bitPoly b) := by
      use Polynomial.C (v ⟨r - 1, by omega⟩)
      rw [hident]
      ring
    rw [← hself]
    exact Polynomial.modByMonic_eq_of_dvd_sub hg hdiv

/-- Run invariant: after processing any MSB-first list `bits` from the zero
register, the register represents `Polynomial.modByMonic (messagePoly bits) g`. -/
theorem registerToPoly_run_eq_messagePoly_mod (g : Polynomial (ZMod 2))
    (r : ℕ) (hg : g.Monic) (hr : g.natDegree = r) (hr1 : 1 ≤ r)
    (bits : List Bool) :
    registerToPoly r (runRegister g r bits) = Polynomial.modByMonic (messagePoly bits) g := by
  have _ : 1 ≤ r := hr1
  induction bits using List.reverseRecOn with
  | nil =>
    rw [runRegister_nil_aux, registerToPoly_initialRegister, messagePoly_nil_aux]
    simp
  | append_singleton l b ih =>
    rw [runRegister_snoc_aux, registerToPoly_stepRegister g r hg hr,
      messagePoly_snoc_aux, ih]
    have hdiv : g ∣ ((messagePoly l %ₘ g) * Polynomial.X + bitPoly b)
        - (messagePoly l * Polynomial.X + bitPoly b) := by
      have h1 : g ∣ messagePoly l %ₘ g - messagePoly l :=
        Polynomial.dvd_modByMonic_sub _ _
      have heq : ((messagePoly l %ₘ g) * Polynomial.X + bitPoly b)
          - (messagePoly l * Polynomial.X + bitPoly b)
        = (messagePoly l %ₘ g - messagePoly l) * Polynomial.X := by ring
      rw [heq]
      exact dvd_mul_of_dvd_left h1 _
    exact Polynomial.modByMonic_eq_of_dvd_sub hg hdiv

/-- Appending `r` zero bits multiplies the message polynomial by `X^r`:
the augmented MSB-first string is the polynomial `m * X^r`. -/
theorem messagePoly_append_zeros (bits : List Bool) (r : ℕ) :
    messagePoly (bits ++ List.replicate r false) =
      messagePoly bits * Polynomial.X ^ r := by
  rw [messagePoly_append_aux, messagePoly_replicate_false_aux]
  have hlen : (List.replicate r false).length = r := by simp
  rw [hlen]
  simp

/-- A leading zero does not change the message polynomial value; the
declared length still grows by one, as `messagePoly_cons_false_length`
records, and the leading zero is processed as a serial step. -/
theorem messagePoly_cons_false (bits : List Bool) :
    messagePoly (false :: bits) = messagePoly bits := by
  rw [messagePoly_cons_aux, bitPoly_false_aux]
  simp

/-- The declared length of a payload with a leading zero is one more than
the declared length of its tail: `l` is preserved, not recomputed from the
polynomial. -/
theorem messagePoly_cons_false_length (bits : List Bool) :
    (false :: bits).length = bits.length + 1 := by
  simp

/-- The final register for a payload with a leading zero represents the
same remainder as for its tail, after one extra serial step. -/
theorem final_register_cons_false (g : Polynomial (ZMod 2)) (r : ℕ)
    (hg : g.Monic) (hr : g.natDegree = r) (hr1 : 1 ≤ r) (bits : List Bool) :
    registerToPoly r (finalRegister g r (false :: bits)) =
      registerToPoly r (finalRegister g r bits) := by
  unfold finalRegister
  rw [registerToPoly_run_eq_messagePoly_mod g r hg hr hr1,
      registerToPoly_run_eq_messagePoly_mod g r hg hr hr1]
  have happ : ((false :: bits) ++ List.replicate r false)
    = false :: (bits ++ List.replicate r false) := by simp
  rw [happ, messagePoly_cons_false]

/-- An all-zero payload of any declared length gives the zero final
register polynomial. -/
theorem final_register_all_zero (g : Polynomial (ZMod 2)) (r : ℕ)
    (hg : g.Monic) (hr : g.natDegree = r) (hr1 : 1 ≤ r) (l : ℕ) :
    registerToPoly r (finalRegister g r (List.replicate l false)) = 0 := by
  unfold finalRegister
  rw [registerToPoly_run_eq_messagePoly_mod g r hg hr hr1]
  have hadd : List.replicate l false ++ List.replicate r false
    = List.replicate (l + r) false := (List.replicate_add l r false).symm
  rw [hadd, messagePoly_replicate_false_aux]
  simp

/-- The final state represents `(X^r * m) mod g` for an MSB-first payload
followed by `r` zero bits. This is the leaf obligation. -/
theorem final_register_represents_shifted_message_remainder
    (g : Polynomial (ZMod 2)) (r : ℕ) (hg : g.Monic) (hr : g.natDegree = r)
    (hr1 : 1 ≤ r) (bits : List Bool) :
    registerToPoly r (finalRegister g r bits) =
      Polynomial.modByMonic (Polynomial.X ^ r * messagePoly bits) g := by
  unfold finalRegister
  rw [registerToPoly_run_eq_messagePoly_mod g r hg hr hr1, messagePoly_append_zeros]
  rw [mul_comm]

/-- CRC-3 fixture, payload `101` (MSB first): the final register represents
`X^2`. -/
theorem final_register_crc3_payload_101 :
    registerToPoly 3 (finalRegister crc3Generator 3 [true, false, true]) =
      Polynomial.X ^ 2 := by
  have hhead := final_register_represents_shifted_message_remainder
    crc3Generator 3 crc3_monic_aux crc3_natDegree_aux (by decide) [true, false, true]
  rw [hhead]
  have hmsg : messagePoly [true, false, true] = Polynomial.X ^ 2 + 1 := by
    simp only [messagePoly_cons_aux, messagePoly_nil_aux, bitPoly_true_aux,
      bitPoly_false_aux]
    simp
  rw [hmsg]
  have hdiv : crc3Generator
      ∣ (Polynomial.X ^ 3 * (Polynomial.X ^ 2 + 1) : Polynomial (ZMod 2))
        - Polynomial.X ^ 2 := by
    have hneg : (-(Polynomial.X ^ 2 : Polynomial (ZMod 2))) = Polynomial.X ^ 2 :=
      CharTwo.neg_eq _
    have heq : ((Polynomial.X ^ 3 * (Polynomial.X ^ 2 + 1) : Polynomial (ZMod 2))
        - Polynomial.X ^ 2)
      = (Polynomial.X ^ 3 * (Polynomial.X ^ 2 + 1) + Polynomial.X ^ 2) := by
      rw [sub_eq_add_neg, hneg]
    rw [heq]
    unfold crc3Generator
    use Polynomial.X ^ 2
    ring
  have hdeg1 : (Polynomial.X ^ 2 : Polynomial (ZMod 2)).degree = 2 := by
    compute_degree!
  have hmod : ((Polynomial.X ^ 2 : Polynomial (ZMod 2)) %ₘ crc3Generator)
      = Polynomial.X ^ 2 := by
    apply (Polynomial.modByMonic_eq_self_iff crc3_monic_aux).mpr
    rw [hdeg1, crc3_degree_aux]
    decide
  have heq := Polynomial.modByMonic_eq_of_dvd_sub crc3_monic_aux hdiv
  rw [hmod] at heq
  exact heq

/-- CRC-3 fixture, payload `110` (MSB first): the final register represents
`1`. Reversing this non-palindromic payload changes the result, as the next
statement records. -/
theorem final_register_crc3_payload_110 :
    registerToPoly 3 (finalRegister crc3Generator 3 [true, true, false]) =
      1 := by
  have hhead := final_register_represents_shifted_message_remainder
    crc3Generator 3 crc3_monic_aux crc3_natDegree_aux (by decide) [true, true, false]
  rw [hhead]
  have hmsg : messagePoly [true, true, false]
      = Polynomial.X ^ 2 + Polynomial.X := by
    simp only [messagePoly_cons_aux, messagePoly_nil_aux, bitPoly_true_aux,
      bitPoly_false_aux]
    simp
  rw [hmsg]
  have hdiv : crc3Generator
      ∣ (Polynomial.X ^ 3 * (Polynomial.X ^ 2 + Polynomial.X) : Polynomial (ZMod 2))
        - 1 := by
    have hneg : (-(1 : Polynomial (ZMod 2))) = 1 := CharTwo.neg_eq _
    have heq : ((Polynomial.X ^ 3 * (Polynomial.X ^ 2 + Polynomial.X)
        : Polynomial (ZMod 2)) - 1)
      = (Polynomial.X ^ 3 * (Polynomial.X ^ 2 + Polynomial.X) + 1) := by
      rw [sub_eq_add_neg, hneg]
    rw [heq]
    unfold crc3Generator
    use Polynomial.X ^ 2 + Polynomial.X + 1
    have h2 : (2 : Polynomial (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
    linear_combination -(Polynomial.X + Polynomial.X ^ 2 + Polynomial.X ^ 3) * h2
  have hdeg1 : (1 : Polynomial (ZMod 2)).degree = 0 := by compute_degree!
  have hmod : ((1 : Polynomial (ZMod 2)) %ₘ crc3Generator) = 1 := by
    apply (Polynomial.modByMonic_eq_self_iff crc3_monic_aux).mpr
    rw [hdeg1, crc3_degree_aux]
    decide
  have heq := Polynomial.modByMonic_eq_of_dvd_sub crc3_monic_aux hdiv
  rw [hmod] at heq
  exact heq

/-- CRC-3 fixture, reversed payload `011` (MSB first): the final register
represents `X^2 + 1`, different from the payload `110` case. -/
theorem final_register_crc3_payload_011 :
    registerToPoly 3 (finalRegister crc3Generator 3 [false, true, true]) =
      Polynomial.X ^ 2 + 1 := by
  have hhead := final_register_represents_shifted_message_remainder
    crc3Generator 3 crc3_monic_aux crc3_natDegree_aux (by decide) [false, true, true]
  rw [hhead]
  have hmsg : messagePoly [false, true, true] = Polynomial.X + 1 := by
    simp only [messagePoly_cons_aux, messagePoly_nil_aux, bitPoly_true_aux,
      bitPoly_false_aux]
    simp
  rw [hmsg]
  have hdiv : crc3Generator
      ∣ (Polynomial.X ^ 3 * (Polynomial.X + 1) : Polynomial (ZMod 2))
        - (Polynomial.X ^ 2 + 1) := by
    have hneg : (-(Polynomial.X ^ 2 + 1 : Polynomial (ZMod 2)))
        = Polynomial.X ^ 2 + 1 := CharTwo.neg_eq _
    have heq : ((Polynomial.X ^ 3 * (Polynomial.X + 1) : Polynomial (ZMod 2))
        - (Polynomial.X ^ 2 + 1))
      = (Polynomial.X ^ 3 * (Polynomial.X + 1) + (Polynomial.X ^ 2 + 1)) := by
      rw [sub_eq_add_neg, hneg]
    rw [heq]
    unfold crc3Generator
    use Polynomial.X + 1
    have h2 : (2 : Polynomial (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
    linear_combination -(Polynomial.X) * h2
  have hdeg1 : (Polynomial.X ^ 2 + 1 : Polynomial (ZMod 2)).degree = 2 := by
    compute_degree!
  have hmod : ((Polynomial.X ^ 2 + 1 : Polynomial (ZMod 2)) %ₘ crc3Generator)
      = Polynomial.X ^ 2 + 1 := by
    apply (Polynomial.modByMonic_eq_self_iff crc3_monic_aux).mpr
    rw [hdeg1, crc3_degree_aux]
    decide
  have heq := Polynomial.modByMonic_eq_of_dvd_sub crc3_monic_aux hdiv
  rw [hmod] at heq
  exact heq

end CSLibExt.Coding.UnreflectedSerialCRC
