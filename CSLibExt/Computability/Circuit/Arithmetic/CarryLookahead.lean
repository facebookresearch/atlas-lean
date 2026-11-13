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

/-- **Appending a block of gates.** Let $p$ be a straight-line program with $g$ gates over $m$
inputs, let $c \in \mathbb{N}$, and for each $j < c$ let $f_j$ be a line (a gate operation with
its argument wires) that reads the inputs and the first $g + j$ gates. Appending
$f_0, \dots, f_{c-1}$ to $p$ gives the program with $g + c$ gates whose first $g$ gates are
those of $p$ and whose gate $g + j$ is $f_j$ for each $j < c$. It is defined by recursion on
$c$, adding one gate at a time. -/
def appendGates {g : ℕ} (p : Program σ m g) :
    (c : ℕ) → ((j : ℕ) → j < c → Line σ m (g + j)) → Program σ m (g + c)
  | 0, _ => p
  | c + 1, f => (appendGates p c fun j h => f j (by omega)).gate (f c (by omega))

/-- **Appending gates keeps the old gate values.** Let $p$ be a program with $g$ gates over $m$
inputs, let $c \in \mathbb{N}$, and for each $j < c$ let $f_j$ be a line that reads the inputs
and the first $g + j$ gates. Under any interpretation of the gate symbols and any input values,
for every $k < g$ the value of gate $k$ of the program obtained by appending
$f_0, \dots, f_{c-1}$ to $p$ equals the value of gate $k$ of $p$. -/
theorem appendGates_eval_lt {g : ℕ} (p : Program σ m g) (i : Interpretation σ U)
    (x : Fin m → U) : ∀ (c : ℕ) (f : (j : ℕ) → j < c → Line σ m (g + j)) (k : ℕ) (hk : k < g)
      (hk' : k < g + c), (appendGates p c f).eval i x ⟨k, hk'⟩ = p.eval i x ⟨k, hk⟩
  | 0, _, _, _, _ => rfl
  | c + 1, f, k, hk, hk' => by
      have : (⟨k, hk'⟩ : Fin (g + c + 1)) = Fin.castSucc ⟨k, by omega⟩ := rfl
      rw [appendGates, this, Program.eval_gate_castSucc]
      exact appendGates_eval_lt p i x c _ k hk _

/-- **Appending one more gate keeps the earlier gate values.** Let $p$ be a program with $g$
gates over $m$ inputs, let $c \in \mathbb{N}$, and for each $j \le c$ let $f_j$ be a line that
reads the inputs and the first $g + j$ gates. Under any interpretation of the gate symbols and
any input values, for every $k < g + c$ the value of gate $k$ of the program obtained by
appending $f_0, \dots, f_c$ to $p$ equals the value of gate $k$ of the program obtained by
appending $f_0, \dots, f_{c-1}$ to $p$ (no gates when $c = 0$). -/
theorem appendGates_eval_le {g : ℕ} (p : Program σ m g) (i : Interpretation σ U)
    (x : Fin m → U) : ∀ (c : ℕ) (f : (j : ℕ) → j < c + 1 → Line σ m (g + j)) (k : ℕ)
      (hk : k < g + c),
      (appendGates p (c + 1) f).eval i x ⟨k, by omega⟩ =
        (appendGates p c fun j h => f j (by omega)).eval i x ⟨k, hk⟩
  | c, f, k, hk => by
      have : (⟨k, by omega⟩ : Fin (g + c + 1)) = Fin.castSucc ⟨k, hk⟩ := rfl
      rw [appendGates, this, Program.eval_gate_castSucc]

/-- **Values of appended gates.** Let $p$ be a program with $g$ gates over $m$ inputs, let
$c \in \mathbb{N}$, and for each $j < c$ let $f_j$ be a line that reads the inputs and the first
$g + j$ gates. Under any interpretation of the gate symbols and any input values $x$, for every
$j < c$ the value of gate $g + j$ of the program obtained by appending $f_0, \dots, f_{c-1}$ to
$p$ is the value of the line $f_j$ on $x$ and the values of gates $0, \dots, g + j - 1$ of that
same program. -/
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

/-- **Combining generate–propagate pairs.** For pairs of Booleans $(G, P)$ and $(G', P')$, their
combination is $(G \lor (P \land G'), P \land P')$.

When $(G, P)$ are the generate and propagate signals of a block of bits placed directly above a
block with signals $(G', P')$, the combination gives the signals of the joined block. -/
def combine (hi lo : Bool × Bool) : Bool × Bool := (hi.1 || (hi.2 && lo.1), hi.2 && lo.2)

theorem combine_assoc (a b d : Bool × Bool) :
    combine (combine a b) d = combine a (combine b d) := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b; obtain ⟨d1, d2⟩ := d
  cases a1 <;> cases a2 <;> cases b1 <;> cases b2 <;> cases d1 <;> cases d2 <;> rfl

/-- **Generate and propagate signals of a bit.** For bit vectors $x, y$ of width $n$ and an index
$i \in \mathbb{N}$, the generate–propagate pair of bit $i$ is $(x_i \wedge y_i,\ x_i \oplus y_i)$,
where $x_i$ and $y_i$ are bit $i$ of $x$ and $y$, taken to be false when $i \ge n$. -/
def gpBit (i : ℕ) : Bool × Bool := (x.getLsbD i && y.getLsbD i, x.getLsbD i ^^ y.getLsbD i)

/-- **Generate and propagate signals of a block.** For bit vectors $x, y$ of the same width, a
start bit $\ell$ and a length $m$, the generate–propagate pair $\mathrm{GP}(\ell, m)$ of the block
of bits $\ell, \dots, \ell + m - 1$ is defined by recursion on $m$: the empty block has
$\mathrm{GP}(\ell, 0) = (\mathrm{false}, \mathrm{true})$, and
$\mathrm{GP}(\ell, m + 1) = \mathrm{gp}(\ell + m) \circ \mathrm{GP}(\ell, m)$, where
$\mathrm{gp}(\ell + m)$ is the generate–propagate pair of bit $\ell + m$ and $\circ$ is the block
operator with its left argument placed above its right. -/
def gpRange (lo : ℕ) : ℕ → Bool × Bool
  | 0 => (false, true)
  | len + 1 => combine (gpBit x y (lo + len)) (gpRange lo len)

theorem gpRange_one (lo : ℕ) : gpRange x y lo 1 = gpBit x y lo := by
  simp only [gpRange, combine, Nat.add_zero, Bool.and_false, Bool.or_false, Bool.and_true]

/-- **Adjacent blocks compose.** Fix bit vectors $x, y$ of the same width, write
$\mathrm{GP}(\ell, m)$ for the generate–propagate pair of the block of the $m$ bits
$\ell, \dots, \ell + m - 1$, and write $h \circ l$ for the block operator with $h$ placed above
$l$. Then for all natural numbers $\ell, a, b$,
$\mathrm{GP}(\ell, a + b) = \mathrm{GP}(\ell + a, b) \circ \mathrm{GP}(\ell, a)$. -/
theorem gpRange_add (lo a : ℕ) : ∀ b : ℕ,
    gpRange x y lo (a + b) = combine (gpRange x y (lo + a) b) (gpRange x y lo a)
  | 0 => by
      obtain ⟨g1, g2⟩ := gpRange x y lo a
      simp only [gpRange, combine, Bool.false_or, Bool.true_and]
  | b + 1 => by
      rw [show a + (b + 1) = (a + b) + 1 by omega, gpRange, gpRange_add lo a b, gpRange,
        ← combine_assoc, show lo + (a + b) = lo + a + b by omega]

/-- **The carry out of a block of bits.** Let $x, y$ be $n$-bit vectors and $c$ a carry-in bit,
and for $i \in \mathbb{N}$ let $c_i$ be the carry into bit $i$ when computing $x + y + c$, that
is, $c_i$ holds exactly when $(x \bmod 2^i) + (y \bmod 2^i) + c \ge 2^i$, where $x$, $y$ are
read as natural numbers and $c$ counts as $1$ when true. For all $a, \ell \in \mathbb{N}$, if
$(G, P)$ are the generate and propagate signals of the block of bits $a, \dots, a + \ell - 1$,
then $c_{a + \ell} = G \lor (P \land c_a)$. -/
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

/-- **Lowest bit of a Kogge-Stone block.** The lowest bit of the block that bit $i$ holds after $k$
Kogge-Stone levels, $i + 1 - \min(i + 1, 2^k)$, that is, $\max(0, i + 1 - 2^k)$. -/
def lowBit (k i : ℕ) : ℕ := i + 1 - min (i + 1) (2 ^ k)

/-- **The block held after Kogge-Stone levels.** Fix bit vectors $x, y$ of the same width. For
$k, i \in \mathbb{N}$, the pair $S_k(i)$ that bit $i$ holds after $k$ Kogge-Stone levels is the
generate–propagate pair of the block of the $\min(i + 1, 2^k)$ bits ending at bit $i$, that is,
of the bits $i + 1 - \min(i + 1, 2^k), \dots, i$. -/
def gpSpec (k i : ℕ) : Bool × Bool := gpRange x y (lowBit k i) (i + 1 - lowBit k i)

theorem gpSpec_zero (i : ℕ) : gpSpec x y 0 i = gpBit x y i := by
  have : lowBit 0 i = i := by simp [lowBit]
  simp only [gpSpec, this, show i + 1 - i = 1 by omega, gpRange_one]

/-- **The Kogge-Stone step.** Fix bit vectors $x, y$ of the same width and write $S_k(i)$ for the
generate–propagate pair of the block of the $\min(i + 1, 2^k)$ bits ending at bit $i$, the pair
bit $i$ holds after $k$ Kogge-Stone levels. For all $k, i \in \mathbb{N}$: if $2^k \le i$, then
$S_{k+1}(i) = S_k(i) \circ S_k(i - 2^k)$, where $\circ$ is the block operator with its left
argument placed above its right; otherwise $S_{k+1}(i) = S_k(i)$. -/
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

/-- **Carries from the Kogge–Stone prefixes.** Let $x, y$ be $n$-bit vectors, $c$ a carry-in bit,
and $K$, $i$ natural numbers with $n \le 2^K$ and $i < n$. Let $(G, P)$ be the generate and
propagate signals that bit $i$ holds after $K$ Kogge–Stone levels, those of the block of the at
most $2^K$ bits ending at bit $i$. Then the carry into bit $i + 1$ of $x + y + c$, which is true
exactly when $(x \bmod 2^{i+1}) + (y \bmod 2^{i+1}) + c \ge 2^{i+1}$, equals
$G \lor (P \land c)$.

Since $n \le 2^K$, that block is the whole prefix of bits $0, \dots, i$. -/
theorem carry_of_gpSpec {K i : ℕ} (hK : n ≤ 2 ^ K) (hi : i < n) :
    BitVec.carry (i + 1) x y c = ((gpSpec x y K i).1 || ((gpSpec x y K i).2 && c)) := by
  have h0 : lowBit K i = 0 := by simp only [lowBit]; omega
  have := carry_add x y c 0 (i + 1)
  simp only [Nat.zero_add, BitVec.carry_zero] at this
  simp only [gpSpec, h0, Nat.sub_zero]
  exact this

/-! ## The circuit -/

/-- **Gate count of the first Kogge-Stone levels.** For an $n$-bit adder, the number $L_n(k)$ of
gates in level $0$ together with the first $k$ Kogge-Stone levels is given by $L_n(0) = 2n$ and
$L_n(k + 1) = L_n(k) + 3n$, so $L_n(k) = 2n + 3nk$. -/
def levelBase (n : ℕ) : ℕ → ℕ
  | 0 => 0 + 2 * n
  | k + 1 => levelBase n k + 3 * n

/-- **Index of the generate gate.** For $n$-bit Kogge-Stone adders, the generate signal of bit $i$
after level $0$ is held by gate $2i$, and after Kogge-Stone level $k + 1$ by gate
$2n + 3nk + 3i + 1$; here $2n + 3nk$ is the number of gates in levels $0, \dots, k$. -/
def gNum (n : ℕ) : ℕ → ℕ → ℕ
  | 0, i => 0 + 2 * i
  | k + 1, i => levelBase n k + (3 * i + 1)

/-- **Propagate gate of a bit in the Kogge–Stone adder.** For natural numbers $n$, $k$ and $i$,
$p_n(k, i)$ is the index of the gate holding the propagate signal of bit $i$ after level $k$ of
the $n$-bit carry-lookahead adder: $p_n(0, i) = 2i + 1$, and $p_n(k + 1, i) = 2n + 3nk + 3i + 2$,
where $2n + 3nk$ is the number of gates in levels $0, \dots, k$. -/
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

/-- **Kogge–Stone partner bit.** The bit combined with bit $i$ at level $k + 1$ of the Kogge–Stone
adder is bit $i - 2^k$ if $2^k \le i$, and bit $i$ itself otherwise. -/
def partner (k i : ℕ) : ℕ := if 2 ^ k ≤ i then i - 2 ^ k else i

theorem partner_lt {n k i : ℕ} (hi : i < n) : partner k i < n := by
  have := Nat.two_pow_pos k
  unfold partner; split_ifs <;> omega

/-- **Gates of level 0.** Gate $j < 2n$ of level $0$ of the $n$-bit adder of $x$ and $y$ reads the
inputs $\lfloor j/2 \rfloor$ and $n + \lfloor j/2 \rfloor$, which carry bit $\lfloor j/2 \rfloor$
of $x$ and of $y$. For even $j$ it is an AND gate, the generate signal of that bit; for odd $j$ it
is an XOR gate, its propagate signal. -/
def line0 (n j : ℕ) (hj : j < 2 * n) : Line arithSignature (2 * n + 1) (0 + j) :=
  if j % 2 = 0 then binLine .and (Wire.input ⟨j / 2, by omega⟩) (Wire.input ⟨n + j / 2, by omega⟩)
  else binLine .xor (Wire.input ⟨j / 2, by omega⟩) (Wire.input ⟨n + j / 2, by omega⟩)

/-- **Gates of a Kogge-Stone level.** Gate $j < 3n$ of Kogge-Stone level $k + 1$ of the $n$-bit
adder serves bit $i = \lfloor j/3 \rfloor$ and its partner $q$, which is $i - 2^k$ if $2^k \le i$
and $i$ otherwise. Write $G_b$ and $P_b$ for the generate and propagate gates of bit $b$ after
level $k$. If $j \equiv 0 \pmod 3$ the gate computes $P_i \wedge G_q$; if $j \equiv 1 \pmod 3$ it
computes the new generate signal $G_i \vee (P_i \wedge G_q)$ from $G_i$ and the previous gate; if
$j \equiv 2 \pmod 3$ it computes the new propagate signal $P_i \wedge P_q$. -/
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

/-- **The first Kogge-Stone levels.** For an $n$-bit adder, the program over the XOR, AND and OR
gates on $2n + 1$ inputs obtained from the empty program by appending the $2n$ gates of level
$0$ and then, in turn, the $3n$ gates of each Kogge-Stone level $1, \dots, k$. It has
$2n + 3nk$ gates. -/
def levels (n : ℕ) : (k : ℕ) → Program arithSignature (2 * n + 1) (levelBase n k)
  | 0 => appendGates .empty (2 * n) (line0 n)
  | k + 1 => appendGates (levels n k) (3 * n) (lineK n k)

/-- **Gates of the final level.** Gate $j < 3n$ of the final level of the $n$-bit adder with $K$
Kogge-Stone levels serves bit $i = \lfloor j/3 \rfloor$. Write $G_i$ and $P_i$ for the generate and
propagate gates of bit $i$ after the $K$ levels, $p_i$ for the propagate gate of bit $i$ at level
$0$, and $c$ for the carry input. If $j \equiv 0 \pmod 3$ the gate computes $P_i \wedge c$; if
$j \equiv 1 \pmod 3$ it computes the carry $c_{i+1} = G_i \vee (P_i \wedge c)$ from $G_i$ and the
previous gate; if $j \equiv 2 \pmod 3$ it computes the sum bit $p_i \oplus c_i$, where $c_0 = c$
and, for $i \ge 1$, $c_i$ is the carry gate of bit $i - 1$. -/
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

/-- **Gates of the carry-lookahead adder.** For natural numbers $n$ and $K$, the gate program of
the $n$-bit adder with $K$ Kogge–Stone levels is the straight-line program over the XOR/AND/OR
basis on $2n + 1$ inputs (the $n$ bits of one summand, the $n$ bits of the other and a carry-in
$c$) made of level $0$ and Kogge–Stone levels $1, \dots, K$, followed by a final level of $3n$
gates. For each bit $i < n$, let $G_i$ and $P_i$ be the generate and propagate gates of bit $i$
after level $K$ and $p_i$ its propagate gate at level $0$. Gate $3i$ of the final level computes
$P_i \land c$, gate $3i + 1$ computes $G_i \lor (P_i \land c)$, and gate $3i + 2$ computes
$p_i \oplus c$ when $i = 0$ and the XOR of $p_i$ with gate $3(i - 1) + 1$ of the final level
otherwise. -/
def claProgram (n K : ℕ) : Program arithSignature (2 * n + 1) (levelBase n K + 3 * n) :=
  appendGates (levels n K) (3 * n) (lineF n K)

/-- **Kogge–Stone carry-lookahead adder.** For natural numbers $n$ and $K$, the $n$-bit
carry-lookahead adder with $K$ levels is the circuit over the XOR/AND/OR basis with $2n + 1$
inputs (the bits $x_0, \dots, x_{n-1}$ of one summand, the bits $y_0, \dots, y_{n-1}$ of the
other, and a carry-in $c$) and $n + 1$ outputs, whose gates are those of the $n$-bit adder
program with $K$ Kogge–Stone levels. For $i < n$, output $i$ is the sum gate of bit $i$ in the
final level; output $n$ is the carry gate of bit $n - 1$ in the final level, or the input $c$
when $n = 0$.

When $n \le 2^K$, the outputs are the $n$ bits of $x + y + c$ and its carry out. -/
def carryLookaheadAdder (n K : ℕ) :
    Circuit arithSignature (2 * n + 1) (n + 1) where
  size := levelBase n K + 3 * n
  program := claProgram n K
  outputs o :=
    if h : o.val < n then Wire.gate ⟨levelBase n K + (3 * o.val + 2), by omega⟩
    else if h' : n = 0 then Wire.input ⟨2 * n, by omega⟩
    else Wire.gate ⟨levelBase n K + (3 * (n - 1) + 1), by omega⟩

/-- **Number of carry-lookahead levels.** For a natural number $n$, the number of Kogge–Stone
levels used for $n$ bits is $\lfloor \log_2 n \rfloor + 1$, with $\lfloor \log_2 0 \rfloor = 0$.

This number satisfies $n \le 2^{\lfloor \log_2 n \rfloor + 1}$. -/
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

/-- **Level 0 computes generate and propagate.** Let $x$ and $y$ be $n$-bit vectors and $c$ a carry
bit, and evaluate level $0$ of the adder on the bits of $x$, the bits of $y$ and $c$. For every
bit $i < n$, the gate holding the generate signal of bit $i$ carries the generate signal, and the
gate holding its propagate signal carries the propagate signal, of the block consisting of bit $i$
alone, namely $x_i \wedge y_i$ and $x_i \oplus y_i$. -/
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

/-- **Each Kogge-Stone level is correct.** Let $x$ and $y$ be $n$-bit vectors and $c$ a carry bit,
and evaluate level $0$ and the first $k$ Kogge-Stone levels of the adder on the bits of $x$, the
bits of $y$ and $c$. For every bit $i < n$, the gate holding the generate signal of bit $i$
carries the generate signal, and the gate holding its propagate signal carries the propagate
signal, of the block of the at most $2^k$ bits ending at $i$, that is, of the bits
$\max(0, i + 1 - 2^k), \dots, i$. -/
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

/-- **Level-0 gates are unchanged by later levels.** For the $n$-bit adder, every interpretation
of the XOR, AND and OR gates in a type $U$, every assignment of values in $U$ to the $2n + 1$
inputs, and every $K$, each of the $2n$ gates of level $0$ has the same value in the program with
level $0$ and $K$ Kogge-Stone levels as in the program with level $0$ alone. -/
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

/-- **The carry gates.** Let $x, y$ be $n$-bit vectors, $c$ a carry-in bit and $K$ a natural number
with $n \le 2^K$. Evaluate the gate program of the $n$-bit adder with $K$ Kogge–Stone levels in
the Boolean interpretation of the XOR/AND/OR basis, on the input made of the bits of $x$, the bits
of $y$ and $c$. Then for every $i < n$, gate $3i + 1$ of the final level holds the carry into bit
$i + 1$ of $x + y + c$, which is true exactly when
$(x \bmod 2^{i+1}) + (y \bmod 2^{i+1}) + c \ge 2^{i+1}$. -/
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

/-- **The sum gates.** Let $x, y$ be $n$-bit vectors with bits $x_i$, $y_i$, $c$ a carry-in bit
and $K$ a natural number with $n \le 2^K$. Evaluate the gate program of the $n$-bit adder with
$K$ Kogge–Stone levels in the Boolean interpretation of the XOR/AND/OR basis, on the input made
of the bits of $x$, the bits of $y$ and $c$. Then for every $i < n$, gate $3i + 2$ of the final
level is $x_i \oplus y_i \oplus c_i$, where $c_i$ is the carry into bit $i$ of $x + y + c$, true
exactly when $(x \bmod 2^i) + (y \bmod 2^i) + c \ge 2^i$. -/
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

/-- **Sum bits of the carry-lookahead adder.** Let $x, y$ be $n$-bit vectors, $c$ a carry-in bit
and $K$ a natural number with $n \le 2^K$. Evaluate the $n$-bit Kogge–Stone carry-lookahead adder
with $K$ levels in the Boolean interpretation of the XOR/AND/OR basis, on the input made of the
bits of $x$, the bits of $y$ and $c$. Then for every $i < n$, output $i$ of the adder is bit $i$
(the bit of weight $2^i$) of the sum $x + y + c$ taken modulo $2^n$. -/
theorem carryLookaheadAdder_sum {K : ℕ} (hK : n ≤ 2 ^ K) (i : ℕ) (hi : i < n) :
    (carryLookaheadAdder n K).eval arithInterpretation (rcaInput x y c) ⟨i, by omega⟩ =
      (BitVec.adc x y c).2.getLsbD i := by
  simp only [Circuit.eval, carryLookaheadAdder, Function.comp_apply, hi, ↓reduceDIte,
    Program.trace]
  rw [Wire.elim_gate, claProgram_sum x y c hK i hi, BitVec.adc_spec,
    BitVec.getLsbD_add_add_bool hi]
  simp

/-- **Carry out of the carry-lookahead adder.** Let $n, K \in \mathbb{N}$ with $n \le 2^K$, let
$x, y$ be $n$-bit vectors and let $c$ be a carry-in bit. Evaluate the $n$-bit Kogge-Stone
carry-lookahead adder with $K$ levels over the Boolean XOR/AND/OR basis on the input that lists
the bits of $x$ from least to most significant, then those of $y$ in the same order, then $c$.
Its output $n$, the last of its $n + 1$ outputs numbered from $0$, is the carry out of
$x + y + c$: it is true exactly when $x + y + c \ge 2^n$, where $x$, $y$ are read as natural
numbers and $c$ counts as $1$ when true. -/
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

/-- **Gate count of the carry-lookahead adder.** For all $n, K \in \mathbb{N}$, the $n$-bit
Kogge-Stone carry-lookahead adder with $K$ levels has exactly $5n + 3nK$ gates: $2n$ in the
first level, $3n$ in each of the $K$ Kogge-Stone levels, and $3n$ in the final level. -/
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

/-- **The depth interpretation.** For a signature $\sigma$, the depth interpretation is the
interpretation of $\sigma$ in $\mathbb{N}$ that sends an operation symbol of arity $k$, applied to
argument depths $d_0, \dots, d_{k-1}$, to $\max(0, d_0, \dots, d_{k-1}) + 1$: a gate is one deeper
than its deepest argument, and a gate without arguments has depth $1$. -/
def depthInterpretation (σ : Signature) : Interpretation σ ℕ := fun op f =>
  Nat.succ (Fin.foldl (σ.Arity op) (fun d k => max d (f k)) 0)

/-- **Gate depths are evaluation in the depth interpretation.** For every program $p$ over a
signature $\sigma$, the depth of each gate of $p$ equals the value of that gate when $p$ is
evaluated under the depth interpretation of $\sigma$ with every input set to $0$. -/
theorem Program.depths_eq_eval {g : ℕ} (p : Program σ m g) :
    p.depths = p.eval (depthInterpretation σ) (fun _ => 0) := by
  induction p with
  | empty => funext k; exact Fin.elim0 k
  | gate p line ih =>
      funext k
      simp only [Program.depths, Program.eval, ih]
      rfl

/-- **Depth of an arithmetic gate.** For each gate of the arithmetic basis (XOR, AND or OR) and all
argument depths $d_0, d_1 \in \mathbb{N}$, the depth interpretation of the arithmetic signature
assigns the gate the depth $\max(d_0, d_1) + 1$. -/
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

/-- **Depths after each level.** In the program made of level $0$ and the first $k$ Kogge-Stone
levels of the $n$-bit adder, where inputs have depth $0$ and a gate is one deeper than its deepest
argument, for every bit $i < n$ the gate holding the generate signal of bit $i$ has depth $2k + 1$
and the gate holding its propagate signal has depth $k + 1$. -/
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

/-- **Depth of the carry gates.** For all natural numbers $n$, $K$ and $i < n$, in the gate program
of the $n$-bit adder with $K$ Kogge–Stone levels, the carry gate of bit $i$ in the final level
(gate $3i + 1$ of that level) has depth $\max(2K + 1, K + 2) + 1$, where inputs have depth $0$
and each gate is one deeper than its deepest argument. -/
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

/-- **Depth of the sum gates.** For all natural numbers $n$, $K$ and $i < n$, in the gate program
of the $n$-bit adder with $K$ Kogge–Stone levels, the sum gate of bit $i$ in the final level
(gate $3i + 2$ of that level) has depth $2$ if $i = 0$ and depth $\max(2K + 1, K + 2) + 2$
otherwise, where inputs have depth $0$ and each gate is one deeper than its deepest argument. -/
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

/-- **Exact depth of the carry-lookahead adder.** For all $K \ge 1$ and $n \ge 2$, the $n$-bit
Kogge-Stone carry-lookahead adder with $K$ levels has depth exactly $2K + 3$, the depth being the
largest depth of an output with the inputs at depth $0$.

With $K = \lfloor \log_2 n \rfloor + 1$ levels this is $2 \lfloor \log_2 n \rfloor + 5$,
logarithmic in $n$, while the depth of the ripple-carry adder grows linearly in $n$. -/
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

/-- **Depth of the carry-lookahead adder with logarithmically many levels.** For every
$n \ge 2$, the $n$-bit Kogge-Stone carry-lookahead adder with $\lfloor \log_2 n \rfloor + 1$
levels has depth exactly $2 \lfloor \log_2 n \rfloor + 5$, the depth being the largest depth of
an output with the inputs at depth $0$. -/
theorem carryLookaheadAdder_depth_claLevels {n : ℕ} (hn : 2 ≤ n) :
    (carryLookaheadAdder n (claLevels n)).depth = 2 * Nat.log2 n + 5 := by
  rw [carryLookaheadAdder_depth (by simp [claLevels]) hn]
  simp only [claLevels]
  omega

end CarryLookahead

/-! ## Depth of the ripple-carry adder, for comparison -/

namespace RippleCarry

local notation "dI" => depthInterpretation arithSignature

/-- **Carry depth in the ripple-carry adder.** For $i \in \mathbb{N}$, the carry depth of bit $i$
is $0$ if $i = 0$ and $2i + 1$ if $i \ge 1$. It is used as the depth of the carry into bit $i$
of the ripple-carry adder, where the carry into bit $0$ is the carry-in input. -/
def carryDepth (i : ℕ) : ℕ := if i = 0 then 0 else 2 * i + 1

/-- **Gate-depth formula for the ripple-carry adder.** Let $c(i)$ be the carry depth of bit $i$:
$c(0) = 0$ and $c(i) = 2i + 1$ for $i \ge 1$. The formula assigns to gate $j$ of the ripple-carry
adder, for every $j \in \mathbb{N}$, the depth $1$ when $j \bmod 5$ is $0$ or $2$, the depth
$\max(1, c(\lfloor j/5 \rfloor)) + 1$ when $j \bmod 5$ is $1$ or $3$, and the depth
$c(\lfloor j/5 \rfloor + 1)$ when $j \bmod 5 = 4$. -/
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

/-- **Gate depths of the ripple-carry adder.** For natural numbers $n$, $g \le 5n$ and $j < g$,
evaluating the first $g$ gates of the $n$-bit ripple-carry adder in $\mathbb{N}$, with every
input at depth $0$ and every gate one deeper than its deepest argument, gives gate $j$ the depth
$d(j)$. Here, with $q = \lfloor j / 5 \rfloor$, $c(0) = 0$ and $c(i) = 2i + 1$ for $i \ge 1$,
$d(j) = 1$ if $j \bmod 5 \in \{0, 2\}$, $d(j) = \max(1, c(q)) + 1$ if $j \bmod 5 \in \{1, 3\}$,
and $d(j) = c(q + 1)$ if $j \bmod 5 = 4$. -/
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
/-- **The ripple-carry adder has linear depth.** For every $n \ge 1$, the $n$-bit ripple-carry
adder has depth $2n + 1$, the length of its carry chain. -/
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
