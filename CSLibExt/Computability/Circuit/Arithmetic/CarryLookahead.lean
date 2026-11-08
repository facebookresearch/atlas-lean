/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.Arithmetic.RippleCarry

/-!
# The Kogge-Stone carry-lookahead adder as a CSLib circuit

A carry-lookahead adder computes all carries in parallel from per-bit *generate* `g_i = x_i ∧ y_i`
and *propagate* `p_i = x_i ⊕ y_i` signals. A block of bits generates a carry, or propagates an
incoming one, according to the associative operator `(G, P) ∘ (G', P') = (G ∨ (P ∧ G'), P ∧ P')`
(`combine`, `combine_assoc`), and the carry into bit `i + 1` is `G ∨ (P ∧ c₀)` for the block of
bits `0..i` (`carry_add`). Kogge and Stone (*A parallel algorithm for the efficient solution of a
general class of recurrence equations*, IEEE Trans. Computers C-22 (1973)) compute these prefixes
in `K` levels: level `k` combines each bit's block with the block `2 ^ (k - 1)` positions lower, so
after level `k` bit `i` holds the block of the `2 ^ k` bits ending at `i` (`gpSpec`,
`gpSpec_succ`); with `n ≤ 2 ^ K` every bit holds its full prefix. See also Cormen, Leiserson and
Rivest, *Introduction to Algorithms*, first edition (1990), Section 29.2.2 ("Carry-lookahead
addition", a prefix computation over the same operator), and Harris and Harris, *Digital Design
and Computer Architecture*, second edition (2012), Section 5.2.1 (prefix adders).

`carryLookaheadAdder n K` is this network over the XOR/AND/OR basis of `RippleCarry.lean`
(`arithSignature`): level 0 has a generate and a propagate gate per bit, each of the `K` levels
has three gates per bit, and a final level computes each carry (two gates) and sum bit (one gate).
Main results:

* `carryLookaheadAdder_sum`, `carryLookaheadAdder_carry`: for `n ≤ 2 ^ K`, on the bits of
  `x y : BitVec n` and a carry `c` (`rcaInput`), the outputs are the bits of
  `(BitVec.adc x y c).2 = x + y + c` and the carry out `(BitVec.adc x y c).1`.
* `carryLookaheadAdder_size`: `5 n + 3 n K` gates. With `K = Nat.log2 n + 1` (`claLevels`, which
  satisfies `n ≤ 2 ^ K`, `le_two_pow_claLevels`) this is `O(n log n)` gates.
* `carryLookaheadAdder_depth`: for `K ≥ 1` and `n ≥ 2` the depth is exactly `2 K + 3`, so
  `2 log₂ n + 5` with `claLevels n` levels (`carryLookaheadAdder_depth_claLevels`), against
  `2 n + 1` for the ripple-carry adder (`rippleCarryAdder_depth`).

Depth is computed through `Program.depths_eq_eval`: CSLib's gate depths are the evaluation of
the program in `ℕ` under `depthInterpretation` (a gate is one deeper than its deepest argument)
with inputs at depth `0`, so the evaluation lemmas for appended gates serve for both values and
depths.

## Cost model

Circuit size (CSLib's `Circuit.size`, the gate count) and depth (`Circuit.depth`) are the cost
measures; inputs and output designation are free, as in CSLib's circuit model.
-/

@[expose] public section

namespace Cslib.Circuits

/-! ## Appending a block of gates -/

section Append

universe v u

variable {σ : Signature.{v}} {m : ℕ} {U : Type u}

/-- Append the gates `f 0, …, f (c - 1)` to `p`; gate `g + j` is `f j`. -/
def appendGates {g : ℕ} (p : Program σ m g) :
    (c : ℕ) → ((j : ℕ) → j < c → Line σ m (g + j)) → Program σ m (g + c)
  | 0, _ => p
  | c + 1, f => (appendGates p c fun j h => f j (by omega)).gate (f c (by omega))

/-- Gates of `p` keep their values. -/
theorem appendGates_eval_lt {g : ℕ} (p : Program σ m g) (i : Interpretation σ U)
    (x : Fin m → U) : ∀ (c : ℕ) (f : (j : ℕ) → j < c → Line σ m (g + j)) (k : ℕ) (hk : k < g)
      (hk' : k < g + c), (appendGates p c f).eval i x ⟨k, hk'⟩ = p.eval i x ⟨k, hk⟩
  | 0, _, _, _, _ => rfl
  | c + 1, f, k, hk, hk' => by
      have : (⟨k, hk'⟩ : Fin (g + c + 1)) = Fin.castSucc ⟨k, by omega⟩ := rfl
      rw [appendGates, this, Program.eval_gate_castSucc]
      exact appendGates_eval_lt p i x c _ k hk _

/-- The gates of `appendGates p c f` below `g + c'` are those of `appendGates p c' f`. -/
theorem appendGates_eval_le {g : ℕ} (p : Program σ m g) (i : Interpretation σ U)
    (x : Fin m → U) : ∀ (c : ℕ) (f : (j : ℕ) → j < c + 1 → Line σ m (g + j)) (k : ℕ)
      (hk : k < g + c),
      (appendGates p (c + 1) f).eval i x ⟨k, by omega⟩ =
        (appendGates p c fun j h => f j (by omega)).eval i x ⟨k, hk⟩
  | c, f, k, hk => by
      have : (⟨k, by omega⟩ : Fin (g + c + 1)) = Fin.castSucc ⟨k, hk⟩ := rfl
      rw [appendGates, this, Program.eval_gate_castSucc]

/-- Gate `g + j` evaluates its line on the values of the gates before it. -/
theorem appendGates_eval_ge {g : ℕ} (p : Program σ m g) (i : Interpretation σ U)
    (x : Fin m → U) : ∀ (c : ℕ) (f : (j : ℕ) → j < c → Line σ m (g + j)) (j : ℕ) (hj : j < c),
      (appendGates p c f).eval i x ⟨g + j, by omega⟩ =
        (f j hj).eval i x (fun l => (appendGates p c f).eval i x ⟨l.val, by omega⟩)
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | c + 1, f, j, hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · rw [appendGates_eval_le p i x c f (g + j) (by omega),
          appendGates_eval_ge p i x c (fun j h => f j (by omega)) j h]
        congr 1
        funext l
        rw [appendGates_eval_le p i x c f l.val (by omega)]
      · have : (⟨g + j, by omega⟩ : Fin (g + j + 1)) = Fin.last (g + j) := rfl
        rw [appendGates, this, Program.eval_gate_last]
        congr 1
        funext l
        have : (⟨l.val, by omega⟩ : Fin (g + j + 1)) = Fin.castSucc l := rfl
        rw [this, Program.eval_gate_castSucc]

end Append

namespace CarryLookahead

/-! ## Generate and propagate -/

variable {n : ℕ} (x y : BitVec n) (c : Bool)

/-- The block operator: `hi` placed above `lo`. -/
def combine (hi lo : Bool × Bool) : Bool × Bool := (hi.1 || (hi.2 && lo.1), hi.2 && lo.2)

theorem combine_assoc (a b d : Bool × Bool) :
    combine (combine a b) d = combine a (combine b d) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨d1, d2⟩ := d
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases d1 <;> cases d2 <;> rfl

/-- Generate and propagate of bit `i`. -/
def gpBit (i : ℕ) : Bool × Bool := (x.getLsbD i && y.getLsbD i, x.getLsbD i ^^ y.getLsbD i)

/-- Generate and propagate of the block of bits `lo, …, lo + len - 1`. -/
def gpRange (lo : ℕ) : ℕ → Bool × Bool
  | 0 => (false, true)
  | len + 1 => combine (gpBit x y (lo + len)) (gpRange lo len)

theorem gpRange_one (lo : ℕ) : gpRange x y lo 1 = gpBit x y lo := by
  simp only [gpRange, combine, Nat.add_zero, Bool.and_false, Bool.or_false, Bool.and_true]

/-- Blocks compose. -/
theorem gpRange_add (lo a : ℕ) : ∀ b : ℕ,
    gpRange x y lo (a + b) = combine (gpRange x y (lo + a) b) (gpRange x y lo a)
  | 0 => by
      obtain ⟨g1, g2⟩ := gpRange x y lo a
      simp only [gpRange, combine, Bool.false_or, Bool.true_and]
  | b + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 by omega, gpRange, gpRange_add lo a b, gpRange,
        ← combine_assoc, show lo + (a + b) = lo + a + b by omega]

/-- **The carry into a block's top**: `carry (lo + len) = G ∨ (P ∧ carry lo)`. -/
theorem carry_add (lo : ℕ) : ∀ len : ℕ,
    BitVec.carry (lo + len) x y c =
      ((gpRange x y lo len).1 || ((gpRange x y lo len).2 && BitVec.carry lo x y c))
  | 0 => by simp [gpRange]
  | len + 1 => by
      rw [← Nat.add_assoc, BitVec.carry_succ, carry_add lo len]
      simp only [gpRange, combine, gpBit]
      cases x.getLsbD (lo + len) <;> cases y.getLsbD (lo + len) <;>
        cases (gpRange x y lo len).1 <;> cases (gpRange x y lo len).2 <;>
        cases BitVec.carry lo x y c <;> rfl

/-- The lowest bit of the block bit `i` holds after `k` Kogge-Stone levels. -/
def lowBit (k i : ℕ) : ℕ := i + 1 - min (i + 1) (2 ^ k)

/-- After `k` levels, bit `i` holds the block of the (at most) `2 ^ k` bits ending at `i`. -/
def gpSpec (k i : ℕ) : Bool × Bool := gpRange x y (lowBit k i) (i + 1 - lowBit k i)

theorem gpSpec_zero (i : ℕ) : gpSpec x y 0 i = gpBit x y i := by
  have : lowBit 0 i = i := by simp [lowBit]
  simp only [gpSpec, this, show i + 1 - i = 1 by omega, gpRange_one]

/-- **The Kogge-Stone step**: level `k + 1` combines bit `i` with bit `i - 2 ^ k` when it exists,
and keeps bit `i` otherwise. -/
theorem gpSpec_succ (k i : ℕ) :
    gpSpec x y (k + 1) i =
      if 2 ^ k ≤ i then combine (gpSpec x y k i) (gpSpec x y k (i - 2 ^ k))
      else gpSpec x y k i := by
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  split_ifs with h
  · have h1 : lowBit k i = i + 1 - 2 ^ k := by simp only [lowBit]; omega
    have h2 : lowBit (k + 1) i = lowBit k (i - 2 ^ k) := by simp only [lowBit, hp]; omega
    simp only [gpSpec]
    rw [h2, h1, show i + 1 - lowBit k (i - 2 ^ k) =
        (i - 2 ^ k + 1 - lowBit k (i - 2 ^ k)) + 2 ^ k by simp only [lowBit]; omega,
      gpRange_add, show lowBit k (i - 2 ^ k) + (i - 2 ^ k + 1 - lowBit k (i - 2 ^ k)) =
        i + 1 - 2 ^ k by simp only [lowBit]; omega, show i + 1 - (i + 1 - 2 ^ k) = 2 ^ k by omega]
  · have h1 : lowBit (k + 1) i = lowBit k i := by simp only [lowBit, hp]; omega
    simp only [gpSpec, h1]

/-- With `n ≤ 2 ^ K`, after `K` levels bit `i < n` holds the whole prefix `0..i`, so its carry
out is `G ∨ (P ∧ c)`. -/
theorem carry_of_gpSpec {K i : ℕ} (hK : n ≤ 2 ^ K) (hi : i < n) :
    BitVec.carry (i + 1) x y c = ((gpSpec x y K i).1 || ((gpSpec x y K i).2 && c)) := by
  have h0 : lowBit K i = 0 := by simp only [lowBit]; omega
  have := carry_add x y c 0 (i + 1)
  simp only [Nat.zero_add, BitVec.carry_zero] at this
  simp only [gpSpec, h0, Nat.sub_zero]
  exact this

/-! ## The circuit -/

/-- The gate count after level `0` (`k = 0`) and after Kogge-Stone level `k`. -/
def levelBase (n : ℕ) : ℕ → ℕ
  | 0 => 0 + 2 * n
  | k + 1 => levelBase n k + 3 * n

/-- The gate holding the generate signal of bit `i` after level `k`. -/
def gNum (n : ℕ) : ℕ → ℕ → ℕ
  | 0, i => 0 + 2 * i
  | k + 1, i => levelBase n k + (3 * i + 1)

/-- The gate holding the propagate signal of bit `i` after level `k`. -/
def pNum (n : ℕ) : ℕ → ℕ → ℕ
  | 0, i => 0 + (2 * i + 1)
  | k + 1, i => levelBase n k + (3 * i + 2)

theorem gNum_lt {n : ℕ} (k : ℕ) {i : ℕ} (hi : i < n) : gNum n k i < levelBase n k := by
  cases k <;> simp only [gNum, levelBase] <;> omega

theorem pNum_lt {n : ℕ} (k : ℕ) {i : ℕ} (hi : i < n) : pNum n k i < levelBase n k := by
  cases k <;> simp only [pNum, levelBase] <;> omega

theorem levelBase_mono (n : ℕ) : ∀ k, levelBase n 0 ≤ levelBase n k
  | 0 => Nat.le_refl _
  | k + 1 => by have := levelBase_mono n k; simp only [levelBase] at *; omega

/-- The bit combined with bit `i` at level `k + 1` (bit `i` itself when there is none). -/
def partner (k i : ℕ) : ℕ := if 2 ^ k ≤ i then i - 2 ^ k else i

theorem partner_lt {n k i : ℕ} (hi : i < n) : partner k i < n := by
  have := Nat.two_pow_pos k
  unfold partner; split_ifs <;> omega

/-- Level-0 gate `j`: the generate (even `j`) or propagate (odd `j`) signal of bit `j / 2`. -/
def line0 (n j : ℕ) (hj : j < 2 * n) : Line arithSignature (2 * n + 1) (0 + j) :=
  if j % 2 = 0 then binLine .and (Wire.input ⟨j / 2, by omega⟩) (Wire.input ⟨n + j / 2, by omega⟩)
  else binLine .xor (Wire.input ⟨j / 2, by omega⟩) (Wire.input ⟨n + j / 2, by omega⟩)

/-- Gate `j` of Kogge-Stone level `k + 1`, for bit `i = j / 3` and its partner `q`: role `0`
computes `P_i ∧ G_q`, role `1` the new `G_i ∨ (P_i ∧ G_q)`, role `2` the new `P_i ∧ P_q`. -/
def lineK (n k j : ℕ) (hj : j < 3 * n) : Line arithSignature (2 * n + 1) (levelBase n k + j) :=
  if h0 : j % 3 = 0 then
    binLine .and
      (Wire.gate ⟨pNum n k (j / 3), by have := pNum_lt k (n := n) (i := j / 3) (by omega); omega⟩)
      (Wire.gate ⟨gNum n k (partner k (j / 3)),
        by have := gNum_lt k (n := n) (partner_lt (k := k) (i := j / 3) (by omega)); omega⟩)
  else if h1 : j % 3 = 1 then
    binLine .or
      (Wire.gate ⟨gNum n k (j / 3), by have := gNum_lt k (n := n) (i := j / 3) (by omega); omega⟩)
      (Wire.gate ⟨levelBase n k + (j - 1), by omega⟩)
  else
    binLine .and
      (Wire.gate ⟨pNum n k (j / 3), by have := pNum_lt k (n := n) (i := j / 3) (by omega); omega⟩)
      (Wire.gate ⟨pNum n k (partner k (j / 3)),
        by have := pNum_lt k (n := n) (partner_lt (k := k) (i := j / 3) (by omega)); omega⟩)

/-- Level `0` and Kogge-Stone levels `1, …, k`. -/
def levels (n : ℕ) : (k : ℕ) → Program arithSignature (2 * n + 1) (levelBase n k)
  | 0 => appendGates .empty (2 * n) (line0 n)
  | k + 1 => appendGates (levels n k) (3 * n) (lineK n k)

/-- Gate `j` of the final level, for bit `i = j / 3`: role `0` computes `P_i ∧ c`, role `1` the
carry `c_{i+1} = G_i ∨ (P_i ∧ c)`, role `2` the sum bit `p_i ⊕ c_i`. -/
def lineF (n K j : ℕ) (hj : j < 3 * n) : Line arithSignature (2 * n + 1) (levelBase n K + j) :=
  if h0 : j % 3 = 0 then
    binLine .and
      (Wire.gate ⟨pNum n K (j / 3), by have := pNum_lt K (n := n) (i := j / 3) (by omega); omega⟩)
      (Wire.input ⟨2 * n, by omega⟩)
  else if h1 : j % 3 = 1 then
    binLine .or
      (Wire.gate ⟨gNum n K (j / 3), by have := gNum_lt K (n := n) (i := j / 3) (by omega); omega⟩)
      (Wire.gate ⟨levelBase n K + (j - 1), by omega⟩)
  else
    binLine .xor (Wire.gate ⟨pNum n 0 (j / 3),
        by have := pNum_lt 0 (n := n) (i := j / 3) (by omega); have := levelBase_mono n K; omega⟩)
      (if hq : j / 3 = 0 then Wire.input ⟨2 * n, by omega⟩
        else Wire.gate ⟨levelBase n K + (3 * (j / 3 - 1) + 1), by omega⟩)

/-- All gates of the `n`-bit adder with `K` Kogge-Stone levels. -/
def claProgram (n K : ℕ) : Program arithSignature (2 * n + 1) (levelBase n K + 3 * n) :=
  appendGates (levels n K) (3 * n) (lineF n K)

/-- The `n`-bit Kogge-Stone carry-lookahead adder with `K` levels: outputs the `n` sum bits and
the carry out. -/
def carryLookaheadAdder (n K : ℕ) :
    Circuit arithSignature (2 * n + 1) (n + 1) where
  size := levelBase n K + 3 * n
  program := claProgram n K
  outputs o :=
    if h : o.val < n then Wire.gate ⟨levelBase n K + (3 * o.val + 2), by omega⟩
    else if h' : n = 0 then Wire.input ⟨2 * n, by omega⟩
    else Wire.gate ⟨levelBase n K + (3 * (n - 1) + 1), by omega⟩

/-- Enough levels for `n` bits: `Nat.log2 n + 1`, with `n ≤ 2 ^ claLevels n`. -/
def claLevels (n : ℕ) : ℕ := Nat.log2 n + 1

theorem le_two_pow_claLevels (n : ℕ) : n ≤ 2 ^ claLevels n := Nat.le_of_lt Nat.lt_log2_self

/-! ## Correctness -/

variable {n : ℕ} (x y : BitVec n) (c : Bool)

theorem rcaInput_eq_a {a i : ℕ} (h : a = i) (hi : i < n) (ha : a < 2 * n + 1) :
    rcaInput x y c ⟨a, ha⟩ = x.getLsbD i := by
  subst h; exact rcaInput_a x y c hi ha

theorem rcaInput_eq_b {a i : ℕ} (h : a = n + i) (hi : i < n) (ha : a < 2 * n + 1) :
    rcaInput x y c ⟨a, ha⟩ = y.getLsbD i := by
  subst h; exact rcaInput_b x y c hi ha

/-- The values after level `0`: generate and propagate of each bit. -/
theorem levels_zero_eval (i : ℕ) (hi : i < n) :
    (levels n 0).eval arithInterpretation (rcaInput x y c) ⟨gNum n 0 i, gNum_lt 0 hi⟩ =
      (gpSpec x y 0 i).1 ∧
    (levels n 0).eval arithInterpretation (rcaInput x y c) ⟨pNum n 0 i, pNum_lt 0 hi⟩ =
      (gpSpec x y 0 i).2 := by
  rw [gpSpec_zero]
  constructor
  · change (appendGates Program.empty (2 * n) (line0 n)).eval _ _ ⟨0 + 2 * i, _⟩ = _
    rw [appendGates_eval_ge Program.empty _ _ (2 * n) (line0 n) (2 * i) (by omega)]
    have h2 : 2 * i % 2 = 0 := by omega
    simp only [line0, h2, ↓reduceIte, binLine_eval, arithInterpretation, Wire.elim_input,
      Nat.one_ne_zero]
    rw [rcaInput_eq_a x y c (by omega : 2 * i / 2 = i) hi,
      rcaInput_eq_b x y c (by omega : n + 2 * i / 2 = n + i) hi]
    rfl
  · change (appendGates Program.empty (2 * n) (line0 n)).eval _ _ ⟨0 + (2 * i + 1), _⟩ = _
    rw [appendGates_eval_ge Program.empty _ _ (2 * n) (line0 n) (2 * i + 1) (by omega)]
    have h2 : (2 * i + 1) % 2 = 1 := by omega
    simp only [line0, h2, Nat.one_ne_zero, ↓reduceIte, binLine_eval, arithInterpretation,
      Wire.elim_input]
    rw [rcaInput_eq_a x y c (by omega : (2 * i + 1) / 2 = i) hi,
      rcaInput_eq_b x y c (by omega : n + (2 * i + 1) / 2 = n + i) hi]
    rfl

private theorem or_and_self (a b : Bool) : (a || (b && a)) = a := by cases a <;> cases b <;> rfl

/-- **Each Kogge-Stone level is correct**: after level `k`, the generate and propagate gates of
bit `i` hold `gpSpec x y k i`. -/
theorem levels_eval : ∀ (k i : ℕ) (hi : i < n),
    (levels n k).eval arithInterpretation (rcaInput x y c) ⟨gNum n k i, gNum_lt k hi⟩ =
      (gpSpec x y k i).1 ∧
    (levels n k).eval arithInterpretation (rcaInput x y c) ⟨pNum n k i, pNum_lt k hi⟩ =
      (gpSpec x y k i).2
  | 0, i, hi => levels_zero_eval x y c i hi
  | k + 1, i, hi => by
      have ih := levels_eval k
      have hq := partner_lt (k := k) hi
      -- level-`k` values seen from inside level `k + 1`
      have hG : ∀ b (hb : b < n), (appendGates (levels n k) (3 * n) (lineK n k)).eval
          arithInterpretation (rcaInput x y c) ⟨gNum n k b, by have := gNum_lt k hb; omega⟩ =
          (gpSpec x y k b).1 := fun b hb => by
        rw [appendGates_eval_lt _ _ _ _ _ (gNum n k b) (gNum_lt k hb)]; exact (ih b hb).1
      have hP : ∀ b (hb : b < n), (appendGates (levels n k) (3 * n) (lineK n k)).eval
          arithInterpretation (rcaInput x y c) ⟨pNum n k b, by have := pNum_lt k hb; omega⟩ =
          (gpSpec x y k b).2 := fun b hb => by
        rw [appendGates_eval_lt _ _ _ _ _ (pNum n k b) (pNum_lt k hb)]; exact (ih b hb).2
      -- role 0: `P_i ∧ G_q`
      have hT : (appendGates (levels n k) (3 * n) (lineK n k)).eval arithInterpretation
          (rcaInput x y c) ⟨levelBase n k + 3 * i, by omega⟩ =
          ((gpSpec x y k i).2 && (gpSpec x y k (partner k i)).1) := by
        rw [appendGates_eval_ge _ _ _ (3 * n) (lineK n k) (3 * i) (by omega)]
        have e0 : 3 * i % 3 = 0 := by omega
        have e1 : 3 * i / 3 = i := by omega
        simp only [lineK, e0, e1, ↓reduceDIte, binLine_eval, arithInterpretation,
          Wire.elim_gate, Nat.one_ne_zero, ↓reduceIte]
        rw [hP i hi, hG _ hq]
      have hS := gpSpec_succ x y k i
      constructor
      · change (appendGates (levels n k) (3 * n) (lineK n k)).eval _ _
          ⟨levelBase n k + (3 * i + 1), _⟩ = _
        rw [appendGates_eval_ge _ _ _ (3 * n) (lineK n k) (3 * i + 1) (by omega)]
        have e0 : (3 * i + 1) % 3 = 1 := by omega
        have e1 : (3 * i + 1) / 3 = i := by omega
        simp only [lineK, e0, e1, Nat.one_ne_zero, ↓reduceDIte, binLine_eval,
          arithInterpretation, Wire.elim_gate, ↓reduceIte, Nat.add_sub_cancel]
        rw [hG i hi, hT, hS]
        unfold partner
        split_ifs <;> simp [combine, or_and_self]
      · change (appendGates (levels n k) (3 * n) (lineK n k)).eval _ _
          ⟨levelBase n k + (3 * i + 2), _⟩ = _
        rw [appendGates_eval_ge _ _ _ (3 * n) (lineK n k) (3 * i + 2) (by omega)]
        have e0 : (3 * i + 2) % 3 = 2 := by omega
        have e1 : (3 * i + 2) / 3 = i := by omega
        have n0 : ¬ (2 : ℕ) = 0 := by decide
        have n1 : ¬ (2 : ℕ) = 1 := by decide
        simp only [lineK, e0, e1, n0, n1, ↓reduceDIte, binLine_eval, arithInterpretation,
          Wire.elim_gate, ↓reduceIte, Nat.one_ne_zero]
        rw [hP i hi, hP _ hq, hS]
        unfold partner
        split_ifs <;> simp [combine]

/-- Level-`0` gates keep their values through the later levels. -/
theorem levels_eval_base {U : Type} (I : Interpretation arithSignature U)
    (inp : Fin (2 * n + 1) → U) : ∀ (K a : ℕ) (ha : a < levelBase n 0),
    (levels n K).eval I inp ⟨a, by have := levelBase_mono n K; omega⟩ =
      (levels n 0).eval I inp ⟨a, ha⟩
  | 0, _, _ => rfl
  | K + 1, a, ha => by
      have h : a < levelBase n K + 3 * n := by have := levelBase_mono n K; omega
      change (appendGates (levels n K) (3 * n) (lineK n K)).eval _ _ ⟨a, h⟩ = _
      rw [appendGates_eval_lt _ _ _ _ _ a (by have := levelBase_mono n K; omega)]
      exact levels_eval_base I inp K a ha

/-- **The carry gates**: gate `3 i + 1` of the final level carries `BitVec.carry (i + 1)`. -/
theorem claProgram_carry {K : ℕ} (hK : n ≤ 2 ^ K) (i : ℕ) (hi : i < n) :
    (claProgram n K).eval arithInterpretation (rcaInput x y c)
        ⟨levelBase n K + (3 * i + 1), by omega⟩ = BitVec.carry (i + 1) x y c := by
  have hL := levels_eval x y c K i hi
  have hU : (claProgram n K).eval arithInterpretation (rcaInput x y c)
      ⟨levelBase n K + 3 * i, by omega⟩ = ((gpSpec x y K i).2 && c) := by
    unfold claProgram
    rw [appendGates_eval_ge _ _ _ (3 * n) (lineF n K) (3 * i) (by omega)]
    have e0 : 3 * i % 3 = 0 := by omega
    have e1 : 3 * i / 3 = i := by omega
    simp only [lineF, e0, e1, ↓reduceDIte, binLine_eval, arithInterpretation,
      Wire.elim_gate, Wire.elim_input, Nat.one_ne_zero, ↓reduceIte]
    rw [appendGates_eval_lt _ _ _ _ _ (pNum n K i) (pNum_lt K hi), hL.2, rcaInput_c]
  unfold claProgram at hU ⊢
  rw [appendGates_eval_ge _ _ _ (3 * n) (lineF n K) (3 * i + 1) (by omega)]
  have e0 : (3 * i + 1) % 3 = 1 := by omega
  have e1 : (3 * i + 1) / 3 = i := by omega
  simp only [lineF, e0, e1, Nat.one_ne_zero, ↓reduceDIte, binLine_eval, arithInterpretation,
    Wire.elim_gate, ↓reduceIte, Nat.add_sub_cancel]
  rw [appendGates_eval_lt _ _ _ _ _ (gNum n K i) (gNum_lt K hi), hL.1, hU,
    carry_of_gpSpec x y c hK hi]

/-- **The sum gates**: gate `3 i + 2` of the final level is `x_i ⊕ y_i ⊕ carry i`. -/
theorem claProgram_sum {K : ℕ} (hK : n ≤ 2 ^ K) (i : ℕ) (hi : i < n) :
    (claProgram n K).eval arithInterpretation (rcaInput x y c)
        ⟨levelBase n K + (3 * i + 2), by omega⟩ =
      ((x.getLsbD i ^^ y.getLsbD i) ^^ BitVec.carry i x y c) := by
  have hp : (claProgram n K).eval arithInterpretation (rcaInput x y c)
      ⟨pNum n 0 i, by have := pNum_lt 0 hi; have := levelBase_mono n K; omega⟩ =
      (x.getLsbD i ^^ y.getLsbD i) := by
    unfold claProgram
    rw [appendGates_eval_lt _ _ _ _ _ (pNum n 0 i)
        (by have := pNum_lt 0 hi; have := levelBase_mono n K; omega),
      levels_eval_base arithInterpretation (rcaInput x y c) K (pNum n 0 i) (pNum_lt 0 hi),
      (levels_zero_eval x y c i hi).2,
      gpSpec_zero]
    rfl
  have hC := fun j hj => claProgram_carry x y c hK j hj
  unfold claProgram at hp hC ⊢
  rw [appendGates_eval_ge _ _ _ (3 * n) (lineF n K) (3 * i + 2) (by omega)]
  have e0 : (3 * i + 2) % 3 = 2 := by omega
  have e1 : (3 * i + 2) / 3 = i := by omega
  have n0 : ¬ (2 : ℕ) = 0 := by decide
  have n1 : ¬ (2 : ℕ) = 1 := by decide
  by_cases hi0 : i = 0
  · subst hi0
    simp only [lineF, e0, e1, n0, n1, ↓reduceDIte, binLine_eval, arithInterpretation,
      Wire.elim_gate, Wire.elim_input, ↓reduceIte, Nat.one_ne_zero]
    rw [hp, rcaInput_c, BitVec.carry_zero]
  · simp only [lineF, e0, e1, n0, n1, hi0, ↓reduceDIte, binLine_eval, arithInterpretation,
      Wire.elim_gate, ↓reduceIte, Nat.one_ne_zero]
    rw [hp, hC (i - 1) (by omega), show i - 1 + 1 = i by omega]

/-- **Sum bits**: for `n ≤ 2 ^ K`, output `i < n` is bit `i` of `(BitVec.adc x y c).2`. -/
theorem carryLookaheadAdder_sum {K : ℕ} (hK : n ≤ 2 ^ K) (i : ℕ) (hi : i < n) :
    (carryLookaheadAdder n K).eval arithInterpretation (rcaInput x y c) ⟨i, by omega⟩ =
      (BitVec.adc x y c).2.getLsbD i := by
  simp only [Circuit.eval, carryLookaheadAdder, Function.comp_apply, hi, ↓reduceDIte,
    Program.trace]
  rw [Wire.elim_gate, claProgram_sum x y c hK i hi, BitVec.adc_spec,
    BitVec.getLsbD_add_add_bool hi]
  simp

/-- **Carry out**: for `n ≤ 2 ^ K`, output `n` is the carry `(BitVec.adc x y c).1`. -/
theorem carryLookaheadAdder_carry {K : ℕ} (hK : n ≤ 2 ^ K) :
    (carryLookaheadAdder n K).eval arithInterpretation (rcaInput x y c) ⟨n, by omega⟩ =
      (BitVec.adc x y c).1 := by
  have hn : ¬ n < n := Nat.lt_irrefl n
  rw [BitVec.adc_spec]
  by_cases h0 : n = 0
  · subst h0
    simp only [Circuit.eval, carryLookaheadAdder, Function.comp_apply, hn, ↓reduceDIte,
      Program.trace, Wire.elim_input]
    rw [rcaInput_c, BitVec.carry_zero]
  · simp only [Circuit.eval, carryLookaheadAdder, Function.comp_apply, hn, h0, ↓reduceDIte,
      Program.trace, Wire.elim_gate]
    rw [claProgram_carry x y c hK (n - 1) (by omega), show n - 1 + 1 = n by omega]

/-- The gate count: `2 n` for level `0`, `3 n` per Kogge-Stone level, `3 n` for the final level.
-/
theorem carryLookaheadAdder_size (n K : ℕ) :
    (carryLookaheadAdder n K).size = 5 * n + 3 * n * K := by
  change levelBase n K + 3 * n = 5 * n + 3 * n * K
  induction K with
  | zero => simp only [levelBase]; omega
  | succ K ih => simp only [levelBase] at ih ⊢; rw [Nat.mul_succ]; omega

end CarryLookahead

/-! ## Depth as evaluation -/

section Depth

universe v

variable {σ : Signature.{v}} {m : ℕ}

/-- Depth as an interpretation in `ℕ`: a gate is one deeper than its deepest argument. -/
def depthInterpretation (σ : Signature) : Interpretation σ ℕ := fun op f =>
  Nat.succ (Fin.foldl (σ.Arity op) (fun d k => max d (f k)) 0)

/-- Gate depths are evaluation under `depthInterpretation` with inputs at depth `0`. -/
theorem Program.depths_eq_eval {g : ℕ} (p : Program σ m g) :
    p.depths = p.eval (depthInterpretation σ) (fun _ => 0) := by
  induction p with
  | empty => funext k; exact Fin.elim0 k
  | gate p line ih =>
      funext k
      simp only [Program.depths, Program.eval, ih]
      rfl

/-- A binary gate's depth is one more than its deeper argument. -/
theorem depthInterpretation_arith (op : ArithGate) (f : Fin 2 → ℕ) :
    depthInterpretation arithSignature op f = max (f 0) (f 1) + 1 := by
  simp only [depthInterpretation, arithSignature, Fin.foldl_succ_last, Fin.foldl_zero]
  simp

theorem binLine_eval_depth {m g : ℕ} (op : ArithGate) (u v : Wire m g) (x : Fin m → ℕ)
    (gates : Fin g → ℕ) :
    (binLine op u v).eval (depthInterpretation arithSignature) x gates =
      max (Wire.elim x gates u) (Wire.elim x gates v) + 1 := by
  simp only [Line.eval, binLine]
  exact depthInterpretation_arith op _

/-- A running maximum bounded by `B` everywhere stays at most `B`. -/
private theorem foldl_max_le {B : ℕ} : ∀ {k : ℕ} (f : Fin k → ℕ) (x : ℕ), x ≤ B → (∀ j, f j ≤ B) →
    Fin.foldl k (fun d j => max d (f j)) x ≤ B
  | 0, _, x, hx, _ => by simpa using hx
  | k + 1, f, x, hx, hf => by
      rw [Fin.foldl_succ_last]
      exact Nat.max_le.2 ⟨foldl_max_le (fun j => f j.castSucc) x hx fun j => hf _, hf _⟩

/-- Every value is at most the running maximum. -/
private theorem le_foldl_max : ∀ {k : ℕ} (f : Fin k → ℕ) (x : ℕ) (j : Fin k),
    f j ≤ Fin.foldl k (fun d j => max d (f j)) x
  | 0, _, _, j => Fin.elim0 j
  | k + 1, f, x, j => by
      rw [Fin.foldl_succ_last]
      refine Fin.lastCases ?_ (fun j => ?_) j
      · exact Nat.le_max_right _ _
      · exact Nat.le_trans (le_foldl_max (fun j => f j.castSucc) x j) (Nat.le_max_left _ _)

end Depth

namespace CarryLookahead

/-! ## Depth of the adder -/

/-- Depth values: evaluation under `depthInterpretation` with inputs at depth `0`. -/
local notation "dI" => depthInterpretation arithSignature

/-- **Depths after each level**: the generate gates sit at depth `2 k + 1`, the propagate gates
at depth `k + 1`. -/
theorem levels_depth {n : ℕ} : ∀ (k i : ℕ) (hi : i < n),
    (levels n k).eval dI (fun _ => 0) ⟨gNum n k i, gNum_lt k hi⟩ = 2 * k + 1 ∧
    (levels n k).eval dI (fun _ => 0) ⟨pNum n k i, pNum_lt k hi⟩ = k + 1
  | 0, i, hi => by
      constructor
      · change (appendGates Program.empty (2 * n) (line0 n)).eval _ _ ⟨0 + 2 * i, _⟩ = _
        rw [appendGates_eval_ge Program.empty _ _ (2 * n) (line0 n) (2 * i) (by omega)]
        have h2 : 2 * i % 2 = 0 := by omega
        simp only [line0, h2, ↓reduceIte, binLine_eval_depth, Wire.elim_input]
        rfl
      · change (appendGates Program.empty (2 * n) (line0 n)).eval _ _ ⟨0 + (2 * i + 1), _⟩ = _
        rw [appendGates_eval_ge Program.empty _ _ (2 * n) (line0 n) (2 * i + 1) (by omega)]
        have h2 : (2 * i + 1) % 2 = 1 := by omega
        simp only [line0, h2, Nat.one_ne_zero, ↓reduceIte, binLine_eval_depth, Wire.elim_input]
        rfl
  | k + 1, i, hi => by
      have ih := levels_depth (n := n) k
      have hq := partner_lt (k := k) hi
      have hG : ∀ b (hb : b < n), (appendGates (levels n k) (3 * n) (lineK n k)).eval dI
          (fun _ => 0) ⟨gNum n k b, by have := gNum_lt k hb; omega⟩ = 2 * k + 1 := fun b hb => by
        rw [appendGates_eval_lt _ _ _ _ _ (gNum n k b) (gNum_lt k hb)]; exact (ih b hb).1
      have hP : ∀ b (hb : b < n), (appendGates (levels n k) (3 * n) (lineK n k)).eval dI
          (fun _ => 0) ⟨pNum n k b, by have := pNum_lt k hb; omega⟩ = k + 1 := fun b hb => by
        rw [appendGates_eval_lt _ _ _ _ _ (pNum n k b) (pNum_lt k hb)]; exact (ih b hb).2
      have hT : (appendGates (levels n k) (3 * n) (lineK n k)).eval dI (fun _ => 0)
          ⟨levelBase n k + 3 * i, by omega⟩ = 2 * k + 2 := by
        rw [appendGates_eval_ge _ _ _ (3 * n) (lineK n k) (3 * i) (by omega)]
        have e0 : 3 * i % 3 = 0 := by omega
        have e1 : 3 * i / 3 = i := by omega
        simp only [lineK, e0, e1, ↓reduceDIte, binLine_eval_depth, Wire.elim_gate]
        rw [hP i hi, hG _ hq]
        omega
      constructor
      · change (appendGates (levels n k) (3 * n) (lineK n k)).eval _ _
          ⟨levelBase n k + (3 * i + 1), _⟩ = _
        rw [appendGates_eval_ge _ _ _ (3 * n) (lineK n k) (3 * i + 1) (by omega)]
        have e0 : (3 * i + 1) % 3 = 1 := by omega
        have e1 : (3 * i + 1) / 3 = i := by omega
        simp only [lineK, e0, e1, Nat.one_ne_zero, ↓reduceDIte, binLine_eval_depth,
          Wire.elim_gate, Nat.add_sub_cancel]
        rw [hG i hi, hT]
        omega
      · change (appendGates (levels n k) (3 * n) (lineK n k)).eval _ _
          ⟨levelBase n k + (3 * i + 2), _⟩ = _
        rw [appendGates_eval_ge _ _ _ (3 * n) (lineK n k) (3 * i + 2) (by omega)]
        have e0 : (3 * i + 2) % 3 = 2 := by omega
        have e1 : (3 * i + 2) / 3 = i := by omega
        have n0 : ¬ (2 : ℕ) = 0 := by decide
        have n1 : ¬ (2 : ℕ) = 1 := by decide
        simp only [lineK, e0, e1, n0, n1, ↓reduceDIte, binLine_eval_depth, Wire.elim_gate]
        rw [hP i hi, hP _ hq]
        omega

/-- The carry gates of the final level sit at depth `max (2 K + 1) (K + 2) + 1`. -/
theorem claProgram_carry_depth {n K : ℕ} (i : ℕ) (hi : i < n) :
    (claProgram n K).eval dI (fun _ => 0) ⟨levelBase n K + (3 * i + 1), by omega⟩ =
      max (2 * K + 1) (K + 2) + 1 := by
  have hL := levels_depth K i hi
  have hU : (claProgram n K).eval dI (fun _ => 0) ⟨levelBase n K + 3 * i, by omega⟩ = K + 2 := by
    unfold claProgram
    rw [appendGates_eval_ge _ _ _ (3 * n) (lineF n K) (3 * i) (by omega)]
    have e0 : 3 * i % 3 = 0 := by omega
    have e1 : 3 * i / 3 = i := by omega
    simp only [lineF, e0, e1, ↓reduceDIte, binLine_eval_depth, Wire.elim_gate,
      Wire.elim_input]
    rw [appendGates_eval_lt _ _ _ _ _ (pNum n K i) (pNum_lt K hi), hL.2]
    omega
  unfold claProgram at hU ⊢
  rw [appendGates_eval_ge _ _ _ (3 * n) (lineF n K) (3 * i + 1) (by omega)]
  have e0 : (3 * i + 1) % 3 = 1 := by omega
  have e1 : (3 * i + 1) / 3 = i := by omega
  simp only [lineF, e0, e1, Nat.one_ne_zero, ↓reduceDIte, binLine_eval_depth, Wire.elim_gate,
    Nat.add_sub_cancel]
  rw [appendGates_eval_lt _ _ _ _ _ (gNum n K i) (gNum_lt K hi), hL.1, hU]

/-- The sum gates of the final level: depth `2` for bit `0`, one above the carry gates otherwise.
-/
theorem claProgram_sum_depth {n K : ℕ} (i : ℕ) (hi : i < n) :
    (claProgram n K).eval dI (fun _ => 0) ⟨levelBase n K + (3 * i + 2), by omega⟩ =
      if i = 0 then 2 else max (2 * K + 1) (K + 2) + 2 := by
  have hp : (claProgram n K).eval dI (fun _ => 0)
      ⟨pNum n 0 i, by have := pNum_lt 0 hi; have := levelBase_mono n K; omega⟩ = 1 := by
    unfold claProgram
    rw [appendGates_eval_lt _ _ _ _ _ (pNum n 0 i)
        (by have := pNum_lt 0 hi; have := levelBase_mono n K; omega),
      levels_eval_base dI (fun _ => 0) K (pNum n 0 i) (pNum_lt 0 hi), (levels_depth 0 i hi).2]
  have hC := fun j hj => claProgram_carry_depth (n := n) (K := K) j hj
  unfold claProgram at hp hC ⊢
  rw [appendGates_eval_ge _ _ _ (3 * n) (lineF n K) (3 * i + 2) (by omega)]
  have e0 : (3 * i + 2) % 3 = 2 := by omega
  have e1 : (3 * i + 2) / 3 = i := by omega
  have n0 : ¬ (2 : ℕ) = 0 := by decide
  have n1 : ¬ (2 : ℕ) = 1 := by decide
  by_cases hi0 : i = 0
  · subst hi0
    simp only [lineF, e0, e1, n0, n1, ↓reduceDIte, binLine_eval_depth, Wire.elim_gate,
      Wire.elim_input, ↓reduceIte]
    rw [hp]
    rfl
  · simp only [lineF, e0, e1, n0, n1, hi0, ↓reduceDIte, binLine_eval_depth, Wire.elim_gate,
      ↓reduceIte]
    rw [hp, hC (i - 1) (by omega)]
    omega

/-- **Logarithmic depth**: with `K ≥ 1` levels and `n ≥ 2` bits the adder has depth `2 K + 3`;
with `K = claLevels n = Nat.log2 n + 1` that is `2 log₂ n + 5`. (The ripple-carry adder's
depth grows linearly in `n`.) -/
theorem carryLookaheadAdder_depth {n K : ℕ} (hK : 1 ≤ K) (hn : 2 ≤ n) :
    (carryLookaheadAdder n K).depth = 2 * K + 3 := by
  have hout : ∀ o : Fin (n + 1), (carryLookaheadAdder n K).outputDepths o =
      if h : o.val < n then (if o.val = 0 then 2 else 2 * K + 3) else 2 * K + 2 := by
    intro o
    simp only [Circuit.outputDepths, Function.comp_apply, Program.wireDepths,
      Program.depths_eq_eval, carryLookaheadAdder]
    by_cases ho : o.val < n
    · simp only [ho, ↓reduceDIte, Wire.elim_gate]
      rw [claProgram_sum_depth o.val ho]
      split_ifs <;> omega
    · have hn0 : ¬ n = 0 := by omega
      simp only [ho, hn0, ↓reduceDIte, Wire.elim_gate]
      rw [claProgram_carry_depth (n - 1) (by omega)]
      omega
  unfold Circuit.depth
  apply Nat.le_antisymm
  · refine foldl_max_le _ 0 (Nat.zero_le _) fun o => ?_
    rw [hout o]
    split_ifs <;> omega
  · have h1 := le_foldl_max (carryLookaheadAdder n K).outputDepths 0 ⟨1, by omega⟩
    rw [hout ⟨1, by omega⟩] at h1
    simp only [show 1 < n by omega, ↓reduceDIte, Nat.one_ne_zero, ↓reduceIte] at h1
    exact h1

/-- With `claLevels n` levels, the depth is `2 log₂ n + 5`. -/
theorem carryLookaheadAdder_depth_claLevels {n : ℕ} (hn : 2 ≤ n) :
    (carryLookaheadAdder n (claLevels n)).depth = 2 * Nat.log2 n + 5 := by
  rw [carryLookaheadAdder_depth (by simp [claLevels]) hn]
  simp only [claLevels]
  omega

end CarryLookahead

/-! ## Depth of the ripple-carry adder, for comparison -/

namespace RippleCarry

local notation "dI" => depthInterpretation arithSignature

/-- The depth of the carry into bit `i`: `0` for the carry in, `2 i + 1` afterwards. -/
def carryDepth (i : ℕ) : ℕ := if i = 0 then 0 else 2 * i + 1

/-- The depth of gate `j` of the ripple-carry adder. -/
def gateDepth (j : ℕ) : ℕ :=
  if j % 5 = 0 ∨ j % 5 = 2 then 1
  else if j % 5 = 1 ∨ j % 5 = 3 then max 1 (carryDepth (j / 5)) + 1
  else carryDepth (j / 5 + 1)

theorem gateDepth_of_mod0 {j : ℕ} (h : j % 5 = 0) : gateDepth j = 1 := by simp [gateDepth, h]
theorem gateDepth_of_mod2 {j : ℕ} (h : j % 5 = 2) : gateDepth j = 1 := by simp [gateDepth, h]
theorem gateDepth_of_mod1 {j : ℕ} (h : j % 5 = 1) :
    gateDepth j = max 1 (carryDepth (j / 5)) + 1 := by simp [gateDepth, h]
theorem gateDepth_of_mod3 {j : ℕ} (h : j % 5 = 3) :
    gateDepth j = max 1 (carryDepth (j / 5)) + 1 := by simp [gateDepth, h]
theorem gateDepth_of_mod4 {j : ℕ} (h : j % 5 = 4) : gateDepth j = carryDepth (j / 5 + 1) := by
  simp [gateDepth, h]

theorem carryWire_depth {n g i : ℕ} (hi : 5 * i ≤ g) (gates : Fin g → ℕ)
    (hgates : ∀ j (hj : j < g), gates ⟨j, hj⟩ = gateDepth j) :
    Wire.elim (fun _ => 0) gates (carryWire n g i hi) = carryDepth i := by
  unfold carryWire
  split_ifs with h
  · subst h; simp only [Wire.elim_input]; rfl
  · simp only [Wire.elim_gate]
    rw [hgates]
    have h4 : (5 * i - 1) % 5 = 4 := by omega
    have hd : (5 * i - 1) / 5 + 1 = i := by omega
    simp only [gateDepth, h4, hd]
    simp

/-- Every gate of the ripple-carry adder sits at depth `gateDepth`. -/
theorem rcaProgram_depth {n : ℕ} : ∀ (g : ℕ) (hg : g ≤ 5 * n) (j : ℕ) (hj : j < g),
    (rcaProgram n g hg).eval dI (fun _ => 0) ⟨j, hj⟩ = gateDepth j
  | 0, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | g + 1, hg, j, hj => by
      have ih := rcaProgram_depth (n := n) g (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · have : (⟨j, hj⟩ : Fin (g + 1)) = Fin.castSucc ⟨j, hj'⟩ := rfl
        rw [this, rcaProgram, Program.eval_gate_castSucc, ih]
      · have : (⟨j, hj⟩ : Fin (j + 1)) = Fin.last j := rfl
        rw [this, rcaProgram, Program.eval_gate_last]
        set prior := (rcaProgram n j (by omega)).eval dI (fun _ => 0)
        have hC := carryWire_depth (n := n) (Nat.mul_div_le j 5) prior ih
        unfold line
        split_ifs with h0 h1 h2 h3
        · rw [binLine_eval_depth]; simp only [Wire.elim_input]; simp [gateDepth, h0]
        · rw [binLine_eval_depth]
          simp only [Wire.elim_gate]
          rw [ih, hC]
          have e1 : (j - 1) % 5 = 0 := by omega
          simp only [gateDepth, e1, h1]
          simp
        · rw [binLine_eval_depth]; simp only [Wire.elim_input]; simp [gateDepth, h2]
        · rw [binLine_eval_depth]
          simp only [Wire.elim_gate]
          rw [ih, hC]
          have e1 : (j - 3) % 5 = 0 := by omega
          simp only [gateDepth, e1, h3]
          simp
        · have h4 : j % 5 = 4 := by omega
          rw [binLine_eval_depth]
          simp only [Wire.elim_gate]
          rw [ih, ih]
          have e1 : (j - 2) % 5 = 2 := by omega
          have e3 : (j - 1) % 5 = 3 := by omega
          have e4 : (j - 1) / 5 = j / 5 := by omega
          rw [gateDepth_of_mod2 e1, gateDepth_of_mod3 e3, gateDepth_of_mod4 h4, e4]
          unfold carryDepth
          split_ifs <;> omega

end RippleCarry

open RippleCarry in
/-- **The ripple-carry adder has linear depth**: `2 n + 1` for `n ≥ 1`, the length of the carry
chain. -/
theorem rippleCarryAdder_depth {n : ℕ} (hn : 1 ≤ n) : (rippleCarryAdder n).depth = 2 * n + 1 := by
  have hout : ∀ o : Fin (n + 1), (rippleCarryAdder n).outputDepths o =
      if o.val < n then max 1 (carryDepth o.val) + 1 else 2 * n + 1 := by
    intro o
    simp only [Circuit.outputDepths, Function.comp_apply, Program.wireDepths,
      Program.depths_eq_eval, rippleCarryAdder]
    by_cases ho : o.val < n
    · simp only [ho, ↓reduceDIte, Wire.elim_gate, ↓reduceIte]
      rw [rcaProgram_depth]
      have e1 : (5 * o.val + 1) % 5 = 1 := by omega
      have e2 : (5 * o.val + 1) / 5 = o.val := by omega
      simp only [gateDepth, e1, e2]
      simp
    · simp only [ho, ↓reduceDIte, ↓reduceIte]
      rw [carryWire_depth (Nat.le_refl _) _ (rcaProgram_depth (5 * n) (Nat.le_refl _))]
      have hn0 : n ≠ 0 := by omega
      simp only [carryDepth, hn0, ↓reduceIte]
  unfold Circuit.depth
  apply Nat.le_antisymm
  · refine foldl_max_le _ 0 (Nat.zero_le _) fun o => ?_
    rw [hout o]
    split_ifs with h
    · have : carryDepth o.val ≤ 2 * o.val + 1 := by unfold carryDepth; split_ifs <;> omega
      omega
    · exact Nat.le_refl _
  · have h1 := le_foldl_max (rippleCarryAdder n).outputDepths 0 ⟨n, by omega⟩
    rw [hout ⟨n, by omega⟩] at h1
    simp only [Nat.lt_irrefl, ↓reduceIte] at h1
    exact h1

end Cslib.Circuits
