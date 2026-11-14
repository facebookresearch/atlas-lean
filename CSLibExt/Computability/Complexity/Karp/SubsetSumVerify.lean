/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.SubsetSum
public import CSLibExt.Computability.Complexity.SatVerifierSpec
public import MathlibExt.Computability.TuringMachine.BitOps
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
public import Mathlib.Tactic.Linarith

/-!
# The NP verifier for SUBSET-SUM

A witness `w` is a choice mask: number `i` of the instance is chosen iff `w[i] = true` (missing
bits are `false`). `ssCheck x w` accepts iff `x` decodes to `(as, t)` and the chosen numbers
(`pick as w`) sum to `t`.

* Pure part: `decodeSS` parses an instance block by block with the shared
  `Cslib.CookLevin.decodeNatPrefix` (canonical binary only) and inverts `encodeSS`
  (`decodeSS_eq_some`).
  `subsetSumDec_iff` characterizes SUBSET-SUM by `ssCheck` with witnesses no longer than the
  input (sublists of `as` are exactly the `pick as w` with `|w| = |as|`).
* Machine: `prog`, a `TM2` component on seven stacks over `Sym` (bits as `Sym.bit`). It reads the
  target onto `T` (most significant bit on top), then for each number pops one witness bit and
  either skips the number's block or adds it to the running sum on `A` (least significant bit on
  top) by ripple-carry addition (`addB`), building the new sum on `B` and moving it back. Each
  block is checked to be canonical as it is read (`lastF`). At the end the sum is moved onto `B`
  and compared with `T` (`cmpB`). The sums stay canonical (`addB_encodeNat`), so list equality is
  equality of numbers. `run`: it reaches `yes` iff `ssCheck x w`, within
  `16 (|x| + |w| + 1)³` steps (quadratic in fact).
-/

@[expose] public section

namespace Cslib.Complexity.Karp.SSVerify

open Turing Function MetaMathlibExt MetaMathlibExt.TM2Program Cslib.CookLevin Computability
open MetaMathlibExt.BitstringEncoding
open Cslib.Complexity.SatVerifier (Sym encodeNat_decodeNat_eq_iff encodeNat_inj)
open MetaMathlibExt.TM2Recursive (encodeNat_eq_cons encodeNat_zero)

/-! ### Parsing -/

/-- **Whether a bit string ends in false.** For a Boolean $z$ and a list of bits $p$, the value
is $z$ when $p$ is empty and the negation of the last bit of $p$ otherwise. So if $z$ records
whether the bits read so far end in false, the value records whether those bits followed by $p$
end in false.

With $z$ false the value is true exactly when $p$ is non-empty and ends in false, that is, when
$p$ is not the canonical binary code of a number, least significant bit first. -/
def lastF : Bool → List Bool → Bool
  | z, [] => z
  | _, b :: p => lastF (!b) p

theorem lastF_eq_false_iff : ∀ (z : Bool) (p : List Bool),
    lastF z p = false ↔ (p = [] ∧ z = false) ∨ p.getLast? = some true
  | z, [] => by simp [lastF]
  | z, [b] => by cases b <;> simp [lastF]
  | z, b :: c :: p => by
      rw [lastF, lastF_eq_false_iff (!b) (c :: p)]
      simp [List.getLast?_cons_cons]

/-- **Canonical binary strings are those not ending in zero.** For every bit string $p$, encoding
in binary (least significant bit first) the natural number that $p$ decodes to gives back $p$ if
and only if the trailing-zero test, started with no trailing zero, reports that $p$ does not end
in $0$; that is, $p$ is empty or its last bit is $1$. -/
theorem encodeNat_decodeNat_iff (p : List Bool) :
    encodeNat (decodeNat p) = p ↔ lastF false p = false := by
  rw [encodeNat_decodeNat_eq_iff, lastF_eq_false_iff]
  simp

theorem lastF_encodeNat (n : ℕ) : lastF false (encodeNat n) = false :=
  (encodeNat_decodeNat_iff _).1 (by rw [decode_encodeNat])

/-- `decodeNatPrefix` (one canonical binary block off the front) in `delimit` form. -/
private theorem decodeNatPrefix_eq_some' {l r : List Bool} {a : ℕ} :
    decodeNatPrefix l = some (a, r) ↔ l = delimit (encodeNat a) ++ r :=
  decodeNatPrefix_eq_some_iff l a r

/-- **Parsing number blocks, with fuel.** For a fuel $n$ and a list of bits $r$, the result is
either a list of numbers or a failure. If $r$ is empty, the result is the empty list. If $r$ is
non-empty and $n = 0$, parsing fails. If $r$ is non-empty and $n = m + 1$, one prefix-coded
number is decoded off the front of $r$: if this gives a number $a$ with remainder $r'$, the result
is $a$ followed by the result for $r'$ with fuel $m$ (failing if that fails), and otherwise
parsing fails. Here the prefix code of $a$ is the canonical binary code of $a$, least significant
bit first, with each bit $b$ written as the pair true, $b$, followed by a final false. -/
def numsAux : ℕ → List Bool → Option (List ℕ)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, b :: l => match decodeNatPrefix (b :: l) with
    | some (a, r) => (numsAux n r).map (a :: ·)
    | none => none

/-- **Decoding a SUBSET-SUM instance.** A block holding a bit string $p$ writes each bit $b$ of $p$
as the two bits $1, b$ and ends with a single $0$. The decoder reads a bit string $x$ as one block
holding the target $t$, followed by blocks holding numbers $a_1, \dots, a_n$ that run exactly to
the end of $x$, where each block must hold the canonical binary representation of its number
(least significant bit first, no trailing $0$). It returns the list $(a_1, \dots, a_n)$ together
with $t$, and fails if $x$ does not split this way. -/
def decodeSS (x : List Bool) : Option (List ℕ × ℕ) :=
  match decodeNatPrefix x with
  | some (t, r) => (numsAux r.length r).map fun as => (as, t)
  | none => none

theorem delimit_ne_nil (l : List Bool) : delimit l ≠ [] := by
  cases l <;> simp [delimit]

theorem length_le_flatMap (as : List ℕ) :
    as.length ≤ (as.flatMap fun a => delimit (encodeNat a)).length := by
  induction as with
  | nil => simp
  | cons a as ih => simp only [List.flatMap_cons, List.length_append, length_delimit,
      List.length_cons]; omega

theorem numsAux_nil (n : ℕ) : numsAux n [] = some [] := by
  cases n <;> rfl

theorem numsAux_of_decode {n : ℕ} {r r' : List Bool} {a : ℕ}
    (h : decodeNatPrefix r = some (a, r')) :
    numsAux (n + 1) r = (numsAux n r').map (a :: ·) := by
  cases r with
  | nil => simp [decodeNatPrefix, encodeNat_decodeNat_iff, undelimit] at h
  | cons b l => simp [numsAux, h]

theorem numsAux_of_decode_none {n : ℕ} {r : List Bool} (hr : r ≠ [])
    (h : decodeNatPrefix r = none) :
    numsAux (n + 1) r = none := by
  cases r with
  | nil => exact absurd rfl hr
  | cons b l => simp [numsAux, h]

theorem numsAux_eq_some : ∀ (n : ℕ) (r : List Bool) (as : List ℕ), r.length ≤ n →
    (numsAux n r = some as ↔ r = as.flatMap fun a => delimit (encodeNat a))
  | n, [], as, _ => by
      rw [numsAux_nil]
      cases as with
      | nil => simp
      | cons a as => simp [delimit_ne_nil]
  | 0, _ :: _, _, h => by simp at h
  | n + 1, b :: l, as, h => by
      constructor
      · intro hs
        cases hb : decodeNatPrefix (b :: l) with
        | none => simp [numsAux_of_decode_none (List.cons_ne_nil b l) hb] at hs
        | some ar =>
            obtain ⟨a, r⟩ := ar
            rw [numsAux_of_decode hb] at hs
            obtain ⟨as', hn, rfl⟩ := Option.map_eq_some_iff.1 hs
            have he := decodeNatPrefix_eq_some'.1 hb
            have hr : r.length ≤ n := by
              have := congrArg List.length he
              simp only [List.length_append, length_delimit] at this h
              omega
            rw [he, (numsAux_eq_some n r as' hr).1 hn, List.flatMap_cons]
      · intro he
        cases as with
        | nil => simp at he
        | cons a as =>
            rw [List.flatMap_cons] at he
            have hr : (as.flatMap fun a => delimit (encodeNat a)).length ≤ n := by
              have := congrArg List.length he
              simp only [List.length_append, length_delimit] at this h
              omega
            rw [numsAux_of_decode (decodeNatPrefix_eq_some'.2 he),
              (numsAux_eq_some n _ as hr).2 rfl,
              Option.map_some]

/-- **Decoding a SUBSET-SUM instance inverts its encoding.** For every bit string $x$, every
list $a$ of natural numbers and every natural number $t$, the SUBSET-SUM decoder returns the
instance $(a, t)$ on $x$ if and only if $x$ is the encoding of the SUBSET-SUM instance with
numbers $a$ and target $t$. -/
theorem decodeSS_eq_some {x : List Bool} {as : List ℕ} {t : ℕ} :
    decodeSS x = some (as, t) ↔ encodeSS as t = x := by
  constructor
  · intro h
    unfold decodeSS at h
    split at h
    · rename_i t' r hb
      obtain ⟨as', hn, he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      rw [decodeNatPrefix_eq_some'.1 hb, (numsAux_eq_some _ r as' le_rfl).1 hn, encodeSS]
    · simp at h
  · rintro rfl
    have hb : decodeNatPrefix (encodeSS as t) =
        some (t, as.flatMap fun a => delimit (encodeNat a)) :=
      decodeNatPrefix_eq_some'.2 rfl
    simp only [decodeSS, hb, (numsAux_eq_some _ _ as le_rfl).2 rfl, Option.map_some]

/-! ### The verifier as a pure function -/

/-- **Numbers chosen by a mask.** For a list of numbers $a_0, \dots, a_{k-1}$ and a list of bits
$w$, the list of those $a_i$ with $w_i$ true, in their original order, where positions $i$ beyond
the end of $w$ count as false. -/
def pick : List ℕ → List Bool → List ℕ
  | [], _ => []
  | a :: as, w => if w.headD false then a :: pick as w.tail else pick as w.tail

/-- **The SUBSET-SUM verifier.** For bit strings $x$ and $w$, the verifier accepts $(x, w)$ exactly
when $x$ is the encoding of a SUBSET-SUM instance with numbers $a_0, \dots, a_{n-1}$ and target
$t$, and the sum of the $a_i$ for which bit $i$ of $w$ is true equals $t$; bits beyond the end of
$w$ count as false, and bits of $w$ past position $n - 1$ are ignored. If $x$ is not the encoding
of an instance, the verifier rejects. -/
def ssCheck (x w : List Bool) : Bool :=
  match decodeSS x with
  | some (as, t) => (pick as w).sum == t
  | none => false

theorem pick_sublist : ∀ (as : List ℕ) (w : List Bool), (pick as w).Sublist as
  | [], _ => List.Sublist.slnil
  | a :: as, w => by
      unfold pick
      split
      · exact (pick_sublist as w.tail).cons_cons a
      · exact (pick_sublist as w.tail).cons a

/-- **Every sublist is selected by a mask.** If $l$ is a sublist of a list $a$ of natural numbers,
then there is a list $w$ of Booleans of the same length as $a$ such that the entries $a_i$ of $a$
with $w_i$ true, taken in order, form exactly $l$. -/
theorem exists_pick {l as : List ℕ} (h : l.Sublist as) :
    ∃ w : List Bool, w.length = as.length ∧ pick as w = l := by
  induction h with
  | slnil => exact ⟨[], rfl, rfl⟩
  | cons a _ ih =>
      obtain ⟨w, hw, hp⟩ := ih
      exact ⟨false :: w, by simp [hw], by simp [pick, hp]⟩
  | cons_cons a _ ih =>
      obtain ⟨w, hw, hp⟩ := ih
      exact ⟨true :: w, by simp [hw], by simp [pick, hp]⟩

theorem sum_pick_cons (a : ℕ) (as : List ℕ) (w : List Bool) :
    (pick (a :: as) w).sum = (if w.headD false then a else 0) + (pick as w.tail).sum := by
  simp only [pick]
  cases w.headD false <;> simp

/-- **SUBSET-SUM is characterized by its verifier.** A bit string $x$ is a yes-instance of
SUBSET-SUM if and only if there is a bit string $w$ with $|w| \le |x|$ such that the SUBSET-SUM
verifier accepts $(x, w)$. -/
theorem subsetSumDec_iff (x : List Bool) :
    subsetSumDec x = true ↔ ∃ w, w.length ≤ x.length ∧ ssCheck x w = true := by
  simp only [subsetSumDec, decide_eq_true_eq]
  constructor
  · rintro ⟨as, t, rfl, l, hl, hs⟩
    obtain ⟨w, hw, rfl⟩ := exists_pick hl
    refine ⟨w, ?_, ?_⟩
    · rw [hw, encodeSS, List.length_append]
      have := length_le_flatMap as
      omega
    · simp [ssCheck, decodeSS_eq_some.2 rfl, hs]
  · rintro ⟨w, -, hw⟩
    unfold ssCheck at hw
    split at hw
    · rename_i as t hd
      exact ⟨as, t, decodeSS_eq_some.1 hd, pick as w, pick_sublist as w, by simpa using hw⟩
    · simp at hw

/-! ### Binary addition -/

/-- **Carry bit of a full adder.** For bits $a$, $b$ and a carry-in $c$, the carry out of adding
$a$, $b$ and $c$ is $(a \wedge b) \vee (c \wedge (a \oplus b))$, which is true iff at least two of
$a$, $b$, $c$ are true. -/
def carry (a b c : Bool) : Bool := a && b || c && (a ^^ b)

/-- **Adding a carry bit.** For a carry bit $c$ and a bit string $u$ (least significant bit
first), $\mathrm{inc}(c, u)$ adds $c$ to $u$ by ripple carry: on the empty string it is $[1]$ if
$c$ is true and empty otherwise, and on a string with first bit $a$ and rest $u'$ it is the bit
$a \oplus c$ followed by $\mathrm{inc}(a \wedge c, u')$. -/
def incB : Bool → List Bool → List Bool
  | c, [] => if c then [true] else []
  | c, a :: u => (a ^^ c) :: incB (a && c) u

/-- **Ripple-carry addition of bit lists.** For a carry-in bit $c$ and bit lists $u$ and $p$, both
least significant bit first, the ripple-carry sum walks $p$. If $p$ is empty, the result is $u$ with
the carry $c$ added (a final carry becomes a new last bit). Otherwise, with $a$ the first bit of $u$
($a$ is false when $u$ is empty) and $b$ the first bit of $p$, the result is the bit
$a \oplus b \oplus c$ followed by the ripple-carry sum of the rest of $u$ and the rest of $p$ with
carry-in the carry out of $a$, $b$ and $c$. -/
def addB : Bool → List Bool → List Bool → List Bool
  | c, u, [] => incB c u
  | c, u, b :: p =>
      (u.headD false ^^ b ^^ c) :: addB (carry (u.headD false) b c) u.tail p

theorem headD_encodeNat (m : ℕ) : (encodeNat m).headD false = decide (m % 2 = 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · rw [encodeNat_eq_cons hm.ne']; rfl

theorem tail_encodeNat (m : ℕ) : (encodeNat m).tail = encodeNat (m / 2) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rfl
  · rw [encodeNat_eq_cons hm.ne']; rfl

theorem incB_encodeNat (c : Bool) (m : ℕ) : incB c (encodeNat m) = encodeNat (m + c.toNat) := by
  induction m using Nat.strong_induction_on generalizing c with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · cases c <;> decide
    · rw [encodeNat_eq_cons hm.ne', incB, ih _ (Nat.div_lt_self hm one_lt_two),
        encodeNat_eq_cons (n := m + c.toNat) (by omega)]
      congr 2 <;> cases c <;> rcases Nat.mod_two_eq_zero_or_one m with h | h <;> simp [h] <;>
        omega

/-- **Addition is correct on canonical numbers.** For every bit $c$ and all natural numbers $m$ and
$n$, the ripple-carry sum, with carry-in $c$, of the canonical binary expansions of $m$ and $n$
(least significant bit first, no trailing false bit) is the canonical binary expansion of
$m + n + c$, where $c$ counts as $1$ if true and $0$ if false. In particular the sum stays
canonical. -/
theorem addB_encodeNat (c : Bool) (m n : ℕ) :
    addB c (encodeNat m) (encodeNat n) = encodeNat (m + n + c.toNat) := by
  induction n using Nat.strong_induction_on generalizing c m with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [encodeNat_zero, addB, incB_encodeNat, Nat.add_zero]
    · rw [encodeNat_eq_cons hn.ne', addB, headD_encodeNat, tail_encodeNat,
        ih _ (Nat.div_lt_self hn one_lt_two), encodeNat_eq_cons (n := m + n + c.toNat) (by omega)]
      congr 2 <;> cases c <;> rcases Nat.mod_two_eq_zero_or_one m with h | h <;>
        rcases Nat.mod_two_eq_zero_or_one n with h' | h' <;> simp [h, h', carry] <;> omega

theorem length_incB : ∀ (c : Bool) (u : List Bool), (incB c u).length ≤ u.length + 1
  | c, [] => by cases c <;> simp [incB]
  | c, a :: u => by simpa [incB] using length_incB (a && c) u

theorem length_addB : ∀ (c : Bool) (u p : List Bool),
    (addB c u p).length ≤ u.length + p.length + 1
  | c, u, [] => by simpa [addB] using length_incB c u
  | c, u, b :: p => by
      have h₁ := length_addB (carry (u.headD false) b c) u.tail p
      have h₂ : u.tail.length ≤ u.length := by simp
      simp only [addB, List.length_cons]
      omega

/-! ### The machine -/

/-- **Stacks of the SUBSET-SUM verifier.** The verifier has seven stacks: the input $X$, the
witness $W$, the target $T$ (most significant bit on top), the running sum $A$ (least significant
bit on top), the new sum $B$ (most significant bit on top), and the scratch stacks $P$ and $Q$ of
the final comparison. -/
inductive K | X | W | T | A | B | P | Q
  deriving DecidableEq

/-- `K` is finite. -/
instance K.instFintypeEnumFix : Fintype K where
  elems := ⟨↑[K.X, .W, .T, .A, .B, .P, .Q], by decide⟩
  complete := fun x => by cases x <;> decide

/-- **Labels of the SUBSET-SUM verifier.** The verifier has the labels $\mathrm{tgt}(z)$, reading
the target; $\mathrm{next}$, starting the next number; $\mathrm{add}(c, z)$, adding a chosen
number with carry $c$; $\mathrm{skip}(z)$, skipping an unchosen number; $\mathrm{fin}(c)$,
carrying $c$ through the rest of the sum; $\mathrm{back}$, moving the new sum back;
$\mathrm{fmove}$, moving the final sum for the comparison; $\mathrm{cmp}$, comparing;
$\mathrm{yes}$, accepting; and $\mathrm{no}$, rejecting, for all bits $c$ and $z$. In
$\mathrm{tgt}(z)$, $\mathrm{add}(c, z)$ and $\mathrm{skip}(z)$ the flag $z$ records whether the
bits of the current block read so far end in $0$. -/
inductive Lab
  | tgt (z : Bool) | next | add (c z : Bool) | skip (z : Bool) | fin (c : Bool) | back | fmove
  | cmp | yes | no
  deriving DecidableEq

/-- `Lab` is finite. -/
instance Lab.instFintypeEnumFix : Fintype Lab where
  elems := ⟨↑[Lab.tgt false, .tgt true, .next, .add false false, .add false true,
    .add true false, .add true true, .skip false, .skip true, .fin false, .fin true, .back,
    .fmove, .cmp, .yes, .no], by decide⟩
  complete := by
    rintro (⟨_ | _⟩ | _ | ⟨_ | _, _ | _⟩ | ⟨_ | _⟩ | ⟨_ | _⟩ | _ | _ | _ | _ | _) <;> decide

/-- **Statements of the SUBSET-SUM verifier.** The statements of the SUBSET-SUM verifier machine
are the statements of a multi-stack Turing machine in Mathlib's TM2 model whose stacks are the
seven stacks $X$, $W$, $T$, $A$, $B$, $P$, $Q$, each over the symbol alphabet of the SAT verifier,
whose labels are the labels of the SUBSET-SUM verifier, and whose local state is a Boolean. -/
abbrev Stmt := TM2.Stmt (fun _ : K => Sym) Lab Bool

/-- **Reading one pair of a block.** For a flag $z$ (the bits read so far end in false), a
statement $\mathit{done}$ and statements $\mathit{body}(b)$ for each bit $b$: if the input stack
$X$ is empty, go to the label $\mathsf{no}$. Otherwise pop the top of $X$ as a bit, a symbol that
is not a bit counting as false. If it is false (the end marker), go to $\mathsf{no}$ when $z$ is
true and run $\mathit{done}$ otherwise. If it is true, go to $\mathsf{no}$ if $X$ is now empty,
and otherwise pop the next symbol of $X$ as a payload bit $b$ (again a non-bit counts as false)
and run $\mathit{body}(b)$. -/
def rdS (z : Bool) (done : Stmt) (body : Bool → Stmt) : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
  .pop .X (fun _ o => bitOf Sym.bit? o) <| .branch id
    (.peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .no) <|
      .pop .X (fun _ o => bitOf Sym.bit? o) <| .branch id (body true) (body false))
    (bif z then .goto fun _ => .no else done)

/-- **Adding one payload bit to the sum.** The machine statement for adding the payload bit $b$
with carry $c$: pop the top symbol of the sum stack $A$ and read it as a bit $a$ (false if $A$ is
empty or the symbol is not a bit), push the bit $a \oplus b \oplus c$ onto $B$, and go to the label
that adds a chosen number with carry the carry out of $a$, $b$ and $c$ and flag $\lnot b$ (the flag
records whether the bits of the block read so far end in false). -/
def addS (c b : Bool) : Stmt :=
  .pop .A (fun _ o => bitOf Sym.bit? o) <| .push .B (fun a => .bit (a ^^ b ^^ c)) <|
    .goto fun a => .add (carry a b c) (!b)

/-- **Carry step of the SUBSET-SUM verifier.** For a carry bit $c$, the verifier statement that
carries $c$ through the rest of the sum on stack $A$: if $A$ is empty, it sets the local variable
to true, pushes the bit $1$ onto $B$ when $c$ is true and goes to label $\mathrm{back}$; otherwise
it pops the top symbol of $A$, read as a bit $a$ (a symbol that is not a bit reads as $0$), sets
the local variable to $a$, pushes the bit $a \oplus c$ onto $B$ and goes to label
$\mathrm{fin}(a \wedge c)$. -/
def finS (c : Bool) : Stmt :=
  .peek .A (fun _ o => o.isNone) <| .branch id
    (bif c then .push .B (fun _ => .bit true) (.goto fun _ => .back) else .goto fun _ => .back)
    (.pop .A (fun _ o => bitOf Sym.bit? o) <| .push .B (fun a => .bit (a ^^ c)) <|
      .goto fun a => .fin (a && c))

/-- **Starting the next number.** The verifier's statement at the label $\mathsf{next}$. If the
input stack $X$ is empty, it goes to the label $\mathsf{fmove}$ (move the sum, then compare).
Otherwise it pops the top of the witness stack $W$ and reads it as a bit $c$, taking $c$ false
when $W$ is empty or its top is not a bit; $c$ becomes the internal state. It then goes to the
label $\mathsf{add}$ with carry false if $c$ is true, and to the label $\mathsf{skip}$ if $c$ is
false, in both cases with the flag "the bits read so far end in false" unset. -/
def nextS : Stmt :=
  .peek .X (fun _ o => o.isNone) <| .branch id (.goto fun _ => .fmove) <|
  .pop .W (fun _ o => bitOf Sym.bit? o) <|
    .goto fun c => bif c then .add false false else .skip false

/-- **The SUBSET-SUM verifier program.** The program on the stacks $X, W, T, A, B, P, Q$ over
the verifier's symbols, with Boolean internal state, given label by label. A popped symbol that
is not a bit counts as false, as does a pop from an empty stack. Reading a pair of a block off
$X$ with flag $z$ ("the bits read so far end in false") goes to $\mathsf{no}$ if $X$ is empty;
on the end marker false it goes to $\mathsf{no}$ if $z$ holds and otherwise ends the block; on
true it reads a payload bit $b$, going to $\mathsf{no}$ if $X$ has ended.

* $\mathsf{tgt}(z)$: read a pair of the target block with flag $z$; at the end of the block go
  to $\mathsf{next}$; on a payload bit $b$, push $b$ onto $T$ and go to $\mathsf{tgt}(\lnot b)$.
* $\mathsf{next}$: if $X$ is empty go to $\mathsf{fmove}$; otherwise pop a witness bit $c$ off
  $W$ (false if absent) and go to $\mathsf{add}$ with carry false if $c$, else to
  $\mathsf{skip}$, with the flag unset.
* $\mathsf{add}(c, z)$: read a pair with flag $z$; at the end of the block go to
  $\mathsf{fin}(c)$; on a payload bit $b$, pop a bit $a$ off $A$ (false if absent), push
  $a \oplus b \oplus c$ onto $B$ and go to $\mathsf{add}(c', \lnot b)$, where $c'$ is the carry
  out of $a + b + c$.
* $\mathsf{skip}(z)$: read a pair with flag $z$; at the end of the block go to $\mathsf{next}$;
  on a payload bit $b$ go to $\mathsf{skip}(\lnot b)$.
* $\mathsf{fin}(c)$: carry $c$ through the rest of $A$, pushing the result bits onto $B$, then
  go to $\mathsf{back}$.
* $\mathsf{back}$: move the bits on top of $B$ onto $A$ one by one, then go to $\mathsf{next}$.
* $\mathsf{fmove}$: move the bits on top of $A$ onto $B$ one by one, then go to $\mathsf{cmp}$.
* $\mathsf{cmp}$: compare the bit blocks on top of $B$ and $T$, using $P$ and $Q$ as scratch, and
  go to $\mathsf{yes}$ if they are equal and to $\mathsf{no}$ otherwise.
* $\mathsf{yes}$ and $\mathsf{no}$: halt. -/
def prog : Lab → TM2.Stmt (fun _ : K => Sym) Lab Bool
  | .tgt z => rdS z (.goto fun _ => .next) fun b =>
      .push .T (fun _ => .bit b) <| .goto fun _ => .tgt (!b)
  | .next => nextS
  | .add c z => rdS z (.goto fun _ => .fin c) (addS c)
  | .skip z => rdS z (.goto fun _ => .next) fun b => .goto fun _ => .skip (!b)
  | .fin c => finS c
  | .back => moveB .B .A Sym.bit? Sym.bit .back .next
  | .fmove => moveB .A .B Sym.bit? Sym.bit .fmove .cmp
  | .cmp => cmpB .B .T .P .Q Sym.bit? Sym.bit? Sym.bit Sym.bit .cmp .yes .no
  | .yes => .halt
  | .no => .halt

/-- **Start state of the SUBSET-SUM verifier.** The SUBSET-SUM verifier machine starts in its
target-reading state, with the flag recording whether the bits read so far end in false set to
false. -/
def start : Lab := .tgt false

/-! ### Stacks -/

/-- **Stack contents of the SUBSET-SUM verifier.** For lists of symbols $x$, $w$, $t$, $a$, $b$,
this assigns contents to the seven stacks of the SUBSET-SUM verifier machine: the input stack $X$
holds $x$, the witness stack $W$ holds $w$, the target stack $T$ holds $t$, the sum stacks $A$ and
$B$ hold $a$ and $b$, and the scratch stacks $P$ and $Q$ are empty. -/
def st (x w t a b : List Sym) : K → List Sym
  | .X => x
  | .W => w
  | .T => t
  | .A => a
  | .B => b
  | .P => []
  | .Q => []

section Upd

variable (x w t a b l : List Sym)

@[simp] theorem upd_X : update (st x w t a b) .X l = st l w t a b := by
  funext s; cases s <;> rfl
@[simp] theorem upd_W : update (st x w t a b) .W l = st x l t a b := by
  funext s; cases s <;> rfl
@[simp] theorem upd_T : update (st x w t a b) .T l = st x w l a b := by
  funext s; cases s <;> rfl
@[simp] theorem upd_A : update (st x w t a b) .A l = st x w t l b := by
  funext s; cases s <;> rfl
@[simp] theorem upd_B : update (st x w t a b) .B l = st x w t a l := by
  funext s; cases s <;> rfl

@[simp] theorem st_X : st x w t a b .X = x := rfl
@[simp] theorem st_W : st x w t a b .W = w := rfl
@[simp] theorem st_T : st x w t a b .T = t := rfl
@[simp] theorem st_A : st x w t a b .A = a := rfl
@[simp] theorem st_B : st x w t a b .B = b := rfl
@[simp] theorem st_P : st x w t a b .P = [] := rfl
@[simp] theorem st_Q : st x w t a b .Q = [] := rfl

end Upd

/-- **Rejection by the SUBSET-SUM verifier within a step bound.** For a natural number $n$ and a
configuration $c$ of the SUBSET-SUM verifier, $\mathrm{Rej}(n, c)$ holds when there are an
internal state $v$ and stack contents $S$ such that the verifier runs from $c$ in at most $n$
steps to the configuration with label $\mathsf{no}$, internal state $v$ and stacks $S$. -/
def Rej (n : ℕ) (c : TM2.Cfg (fun _ : K => Sym) Lab Bool) : Prop :=
  ∃ v S, RunLe prog n c ⟨some .no, v, S⟩

theorem Rej.mono {n m : ℕ} {c : TM2.Cfg (fun _ : K => Sym) Lab Bool} (h : Rej n c)
    (hnm : n ≤ m) : Rej m c :=
  let ⟨v, S, h⟩ := h; ⟨v, S, h.mono hnm⟩

theorem Rej.head {k n : ℕ} {c d : TM2.Cfg (fun _ : K => Sym) Lab Bool} (h₁ : Run prog k c d)
    (h₂ : Rej n d) : Rej (k + n) c :=
  let ⟨v, S, h⟩ := h₂; ⟨v, S, (h₁.le le_rfl).trans h⟩

/-- **Rejecting in one step.** Let $l$ be a label, $v$ a Boolean and $S$ an assignment of stack
contents. If executing the verifier's statement at label $l$ from internal state $v$ and stacks
$S$ yields the next label $\mathsf{no}$, then the verifier reaches a configuration with label
$\mathsf{no}$ from the configuration $(l, v, S)$ within one step. -/
theorem rej_one {l : Lab} {v : Bool} {S : K → List Sym}
    (h : (TM2.stepAux (prog l) v S).l = some .no) : Rej 1 ⟨some l, v, S⟩ := by
  rcases hs : TM2.stepAux (prog l) v S with ⟨l', v', S'⟩
  rw [hs] at h
  cases h
  exact ⟨v', S', (Run.single hs).le le_rfl⟩

/-! ### Reading blocks -/

/-- **Reading the target block.** Let $p$ and $s$ be lists of bits, and write $\mathrm{delimit}(p)$
for the self-delimiting encoding of $p$ (each bit $b$ written as true followed by $b$, then a
terminating false). Suppose the SUBSET-SUM verifier machine is in its target-reading state, with
flag $z$ recording whether the bits read so far end in false and any value of its local Boolean
variable, with the bits of $\mathrm{delimit}(p)$ followed by the bits of $s$ on the input stack
$X$, a list $t$ of symbols on the target stack $T$, arbitrary contents on the stacks $W$, $A$, $B$,
and the scratch stacks $P$, $Q$ empty. Then after exactly $|p| + 1$ steps the stack $X$ holds the
bits of $s$, the bits of $p$ have been pushed onto $T$ one at a time (so that $T$ holds, from the
top, the bits of $p$ in reverse order followed by $t$), the stacks $W$, $A$, $B$, $P$, $Q$ are
unchanged, the local variable is false, and the machine is in its rejecting state if either $p$
is non-empty and ends in false or $p$ is empty and $z$ is true, and in the state that starts the
next number otherwise. -/
theorem tgt_run (rest : List Bool) (w a b : List Sym) :
    ∀ (p : List Bool) (z : Bool) (t : List Sym) (v : Bool),
    Run prog (p.length + 1) ⟨some (.tgt z), v, st ((delimit p ++ rest).map .bit) w t a b⟩
      ⟨some (if lastF z p then .no else .next), false,
        st (rest.map .bit) w ((p.map .bit).reverse ++ t) a b⟩
  | [], z, t, v => Run.single (by
      cases z <;> simp [prog, rdS, TM2.stepAux, delimit, lastF, bitOf, Sym.bit?])
  | c :: p, z, t, v => by
      have h := tgt_run rest w a b p (!c) (.bit c :: t) c
      simp only [List.length_cons, lastF, List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      exact Run.head
        (by cases c <;> simp [TM2.step, prog, rdS, TM2.stepAux, delimit, bitOf, Sym.bit?]) h

/-- **Skipping a number block.** Let $p$ and $s$ be lists of bits, and write $\mathrm{delimit}(p)$
for the self-delimiting encoding of $p$ (each bit $b$ written as true followed by $b$, then a
terminating false). Suppose the SUBSET-SUM verifier machine is in the state that skips an
unchosen number block, with flag $z$ recording whether the bits read so far end in false and any
value of its local Boolean variable, with the bits of $\mathrm{delimit}(p)$ followed by the bits
of $s$ on the input stack $X$, arbitrary contents on the stacks $W$, $T$, $A$, $B$, and the
scratch stacks $P$, $Q$ empty. Then after exactly $|p| + 1$ steps the stack $X$ holds the bits of
$s$, all other stacks are unchanged, the local variable is false, and the machine is in its
rejecting state if either $p$ is non-empty and ends in false or $p$ is empty and $z$ is true, and
in the state that starts the next number otherwise. -/
theorem skip_run (rest : List Bool) (w t a b : List Sym) :
    ∀ (p : List Bool) (z : Bool) (v : Bool),
    Run prog (p.length + 1) ⟨some (.skip z), v, st ((delimit p ++ rest).map .bit) w t a b⟩
      ⟨some (if lastF z p then .no else .next), false, st (rest.map .bit) w t a b⟩
  | [], z, v => Run.single (by
      cases z <;> simp [prog, rdS, TM2.stepAux, delimit, lastF, bitOf, Sym.bit?])
  | c :: p, z, v => by
      have h := skip_run rest w t a b p (!c) c
      simp only [List.length_cons, lastF]
      exact Run.head
        (by cases c <;> simp [TM2.step, prog, rdS, TM2.stepAux, delimit, bitOf, Sym.bit?]) h

/-- **Carry phase of the SUBSET-SUM verifier.** Let $x$, $w$, $t$ and $\mathit{acc}$ be lists of
stack symbols, $u$ a list of bits, $c$ a carry bit and $v$ a Boolean, and write
$\mathrm{inc}(c, u)$ for the result of adding the carry $c$ to $u$ (least significant bit first).
Started at label $\mathrm{fin}(c)$ with variable $v$, with $x$, $w$, $t$ on the stacks $X$, $W$,
$T$, the bits of $u$ on $A$ (first bit on top), $\mathit{acc}$ on $B$ and $P$, $Q$ empty, the
verifier takes exactly $|u| + 1$ steps to reach label $\mathrm{back}$ with variable true, where
$X$, $W$, $T$ are unchanged, $A$, $P$, $Q$ are empty, and $B$ holds the bits of
$\mathrm{inc}(c, u)$ on top of $\mathit{acc}$, last bit on top. -/
theorem fin_run (x w t : List Sym) : ∀ (u : List Bool) (c : Bool) (acc : List Sym) (v : Bool),
    Run prog (u.length + 1) ⟨some (.fin c), v, st x w t (u.map .bit) acc⟩
      ⟨some .back, true, st x w t [] (((incB c u).map .bit).reverse ++ acc)⟩
  | [], c, acc, v => Run.single (by cases c <;> simp [prog, finS, TM2.stepAux, incB])
  | a :: u, c, acc, v => by
      have h := fin_run x w t u (a && c) (.bit (a ^^ c) :: acc) a
      simp only [List.length_cons, incB, List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      exact Run.head (by simp [TM2.step, prog, finS, TM2.stepAux, bitOf, Sym.bit?]) h

/-- **Adding a canonical chosen block.** Let $p$ and $\mathit{rest}$ be bit lists and $z$ a bit
such that $p$ is nonempty and ends in true, or $p$ is empty and $z$ is false (the flag $z$
records whether the bits of the block read so far end in false), and let $c$ be a bit. Start the
SUBSET-SUM verifier machine at the label that adds a chosen number with carry $c$ and flag $z$,
with any value of the local variable, the self-delimiting encoding of $p$ followed by
$\mathit{rest}$ (as bit symbols) on the input stack $X$, symbol lists $w$ on $W$ and $t$ on $T$, a
bit list $u$ (as bit symbols, least significant bit first) on the sum stack $A$, a symbol list
$\mathit{acc}$ on $B$, and the scratch stacks $P$ and $Q$ empty. Then within $|p| + |u| + 2$ steps
the machine reaches the label that moves the new sum back, with some value of the local variable,
$\mathit{rest}$ on $X$, $w$ on $W$, $t$ on $T$, $A$, $P$ and $Q$ empty, and on $B$ the ripple-carry
sum of $u$ and $p$ with carry-in $c$ (as bit symbols, most significant bit on top) above
$\mathit{acc}$. -/
theorem add_run (rest : List Bool) (w t : List Sym) :
    ∀ (p : List Bool) (c z : Bool) (u : List Bool) (acc : List Sym) (v : Bool),
    lastF z p = false →
    ∃ v', RunLe prog (p.length + u.length + 2)
      ⟨some (.add c z), v, st ((delimit p ++ rest).map .bit) w t (u.map .bit) acc⟩
      ⟨some .back, v', st (rest.map .bit) w t [] (((addB c u p).map .bit).reverse ++ acc)⟩
  | [], c, z, u, acc, v, hz => by
      obtain rfl : z = false := hz
      have h := fin_run (rest.map .bit) w t u c acc false
      refine ⟨true, (Run.head ?_ h).le (by omega)⟩
      simp [TM2.step, prog, rdS, TM2.stepAux, delimit, bitOf, Sym.bit?]
  | b :: p, c, z, u, acc, v, hz => by
      obtain ⟨v', h⟩ := add_run rest w t p (carry (u.headD false) b c) (!b) u.tail
        (.bit (u.headD false ^^ b ^^ c) :: acc) (u.headD false) hz
      refine ⟨v', ?_⟩
      simp only [addB, List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append]
      refine (((Run.head ?_ (Run.zero _)).le le_rfl).trans h).mono (by simp; omega)
      cases u <;> cases b <;>
        simp [TM2.step, prog, rdS, addS, TM2.stepAux, delimit, bitOf, Sym.bit?]

/-- **The verifier rejects a chosen block that ends in false.** Let $p$ and $\mathit{rest}$ be bit
lists and $z$ a bit such that $p$ is nonempty and ends in false, or $p$ is empty and $z$ is true
(the flag $z$ records whether the bits of the block read so far end in false). Let $c$ be a bit and
$u$ a bit list. Start the SUBSET-SUM verifier machine at the label that adds a chosen number with
carry $c$ and flag $z$, with any value of the local variable, the self-delimiting encoding of $p$
followed by $\mathit{rest}$ (as bit symbols) on the input stack $X$, any symbol lists on $W$, $T$
and $B$, $u$ (as bit symbols) on the sum stack $A$, and the scratch stacks $P$ and $Q$ empty. Then
the machine reaches the rejecting label within $|p| + 1$ steps. -/
theorem add_rej (rest : List Bool) (w t : List Sym) :
    ∀ (p : List Bool) (c z : Bool) (u : List Bool) (acc : List Sym) (v : Bool),
    lastF z p = true →
    Rej (p.length + 1) ⟨some (.add c z), v, st ((delimit p ++ rest).map .bit) w t (u.map .bit) acc⟩
  | [], c, z, u, acc, v, hz => by
      obtain rfl : z = true := hz
      exact rej_one (by simp [prog, rdS, TM2.stepAux, delimit, bitOf, Sym.bit?])
  | b :: p, c, z, u, acc, v, hz => by
      have ih := add_rej rest w t p (carry (u.headD false) b c) (!b) u.tail
        (.bit (u.headD false ^^ b ^^ c) :: acc) (u.headD false) hz
      refine (Rej.head (Run.single ?_) ih).mono (by simp only [List.length_cons]; omega)
      cases u <;> cases b <;> simp [prog, rdS, addS, TM2.stepAux, delimit, bitOf, Sym.bit?]

/-- **The verifier rejects an unterminated target block.** Let $r$ be a list of bits that does
not begin with a self-delimiting block, that is, parsing one self-delimiting block off the front
of $r$ fails. Suppose the SUBSET-SUM verifier machine is in its target-reading state, with either
value of the flag $z$ recording whether the bits read so far end in false and either value of its
local Boolean variable, with the bits of $r$ on the input stack $X$, arbitrary contents on the
stacks $W$, $T$, $A$, $B$, and the scratch stacks $P$, $Q$ empty. Then the machine reaches its
rejecting state within $|r| + 1$ steps. -/
theorem tgt_fail (w a b : List Sym) : ∀ (r : List Bool), undelimit r = none →
    ∀ (z : Bool) (t : List Sym) (v : Bool), Rej (r.length + 1)
      ⟨some (.tgt z), v, st (r.map .bit) w t a b⟩
  | [], _, z, t, v => rej_one (by simp [prog, rdS, TM2.stepAux])
  | false :: r, h, _, _, _ => by simp [undelimit] at h
  | [true], _, z, t, v => by
      refine (rej_one ?_).mono (by simp)
      simp [prog, rdS, TM2.stepAux, bitOf, Sym.bit?]
  | true :: c :: r, h, z, t, v => by
      have hr : undelimit r = none := by simpa [undelimit] using h
      have ih := tgt_fail w a b r hr (!c) (.bit c :: t) c
      refine (Rej.head (Run.single ?_) ih).mono (by simp; omega)
      cases c <;> simp [prog, rdS, TM2.stepAux, bitOf, Sym.bit?]

/-- **The verifier rejects an unterminated skipped block.** Let $r$ be a list of bits that does
not begin with a self-delimiting block, that is, parsing one self-delimiting block off the front
of $r$ fails. Suppose the SUBSET-SUM verifier machine is in the state that skips an unchosen
number block, with either value of the flag $z$ recording whether the bits read so far end in
false and either value of its local Boolean variable, with the bits of $r$ on the input stack
$X$, arbitrary contents on the stacks $W$, $T$, $A$, $B$, and the scratch stacks $P$, $Q$ empty.
Then the machine reaches its rejecting state within $|r| + 1$ steps. -/
theorem skip_fail (w t a b : List Sym) : ∀ (r : List Bool), undelimit r = none →
    ∀ (z : Bool) (v : Bool), Rej (r.length + 1) ⟨some (.skip z), v, st (r.map .bit) w t a b⟩
  | [], _, z, v => rej_one (by simp [prog, rdS, TM2.stepAux])
  | false :: r, h, _, _ => by simp [undelimit] at h
  | [true], _, z, v => by
      refine (rej_one ?_).mono (by simp)
      simp [prog, rdS, TM2.stepAux, bitOf, Sym.bit?]
  | true :: c :: r, h, z, v => by
      have hr : undelimit r = none := by simpa [undelimit] using h
      have ih := skip_fail w t a b r hr (!c) c
      refine (Rej.head (Run.single ?_) ih).mono (by simp; omega)
      cases c <;> simp [prog, rdS, TM2.stepAux, bitOf, Sym.bit?]

/-- **The verifier rejects an unterminated chosen block.** Let $r$ be a bit list from whose front no
complete self-delimiting block can be parsed, let $c$ and $z$ be bits, and let $u$ be a bit list.
Start the SUBSET-SUM verifier machine at the label that adds a chosen number with carry $c$ and
flag $z$ (the flag records whether the bits of the block read so far end in false), with any value
of the local variable, $r$ (as bit symbols) on the input stack $X$, any symbol lists on $W$, $T$
and $B$, $u$ (as bit symbols) on the sum stack $A$, and the scratch stacks $P$ and $Q$ empty. Then
the machine reaches the rejecting label within $|r| + 1$ steps. -/
theorem add_fail (w t : List Sym) : ∀ (r : List Bool), undelimit r = none →
    ∀ (c z : Bool) (u : List Bool) (acc : List Sym) (v : Bool),
    Rej (r.length + 1) ⟨some (.add c z), v, st (r.map .bit) w t (u.map .bit) acc⟩
  | [], _, c, z, u, acc, v => rej_one (by simp [prog, rdS, TM2.stepAux])
  | false :: r, h, _, _, _, _, _ => by simp [undelimit] at h
  | [true], _, c, z, u, acc, v => by
      refine (rej_one ?_).mono (by simp)
      simp [prog, rdS, TM2.stepAux, bitOf, Sym.bit?]
  | true :: b :: r, h, c, z, u, acc, v => by
      have hr : undelimit r = none := by simpa [undelimit] using h
      have ih := add_fail w t r hr (carry (u.headD false) b c) (!b) u.tail
        (.bit (u.headD false ^^ b ^^ c) :: acc) (u.headD false)
      refine (Rej.head (Run.single ?_) ih).mono (by simp; omega)
      cases u <;> cases b <;> simp [prog, rdS, addS, TM2.stepAux, bitOf, Sym.bit?]

/-! ### Moving and comparing sums -/

/-- **Moving the new sum back.** Let $\mathit{res}$ be a bit list. Start the SUBSET-SUM verifier
machine at the label that moves the new sum back, with any value of the local variable, symbol lists
$x$, $w$, $t$ on $X$, $W$, $T$, the sum stack $A$ empty, $\mathit{res}$ (as bit symbols, last bit
on top) on $B$, and the scratch stacks $P$ and $Q$ empty. Then after exactly
$|\mathit{res}| + 1$ steps the machine is at the label that starts the next number, with some value
of the local variable, $x$, $w$, $t$ unchanged, $\mathit{res}$ (as bit symbols, first bit on top)
on $A$, and $B$, $P$, $Q$ empty. -/
theorem back_run (x w t : List Sym) (res : List Bool) (v : Bool) :
    ∃ v', Run prog (res.length + 1) ⟨some .back, v, st x w t [] (res.map .bit).reverse⟩
      ⟨some .next, v', st x w t (res.map .bit) []⟩ := by
  obtain ⟨v', S', h, hB, hA, hk⟩ := moveB_run (M := prog) (self := .back) (next := .next) rfl
    (show K.B ≠ K.A by decide) res.reverse (res.map Sym.bit).reverse [] v
    (st x w t [] (res.map .bit).reverse) (by simp)
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def, List.map_reverse])
    (by simp [EndsBitBlock])
  have e : S' = st x w t (res.map .bit) [] := by
    funext k
    cases k
    case A => simpa [List.map_reverse] using hA
    case B => simpa using hB
    all_goals exact hk _ (by decide) (by decide)
  exact ⟨v', by simpa [e] using h⟩

/-- **Moving the final sum for the comparison.** Let $x$, $w$, $t$ be lists of stack symbols, $s$
a list of bits and $v$ a Boolean. Started at label $\mathrm{fmove}$ with variable $v$, with $x$,
$w$, $t$ on the stacks $X$, $W$, $T$, the bits of $s$ on $A$ (first bit on top) and $B$, $P$, $Q$
empty, the verifier takes exactly $|s| + 1$ steps to reach label $\mathrm{cmp}$, with some value
of the variable, where $X$, $W$, $T$ are unchanged, $A$, $P$, $Q$ are empty, and $B$ holds the
bits of $s$, last bit on top. -/
theorem fmove_run (x w t : List Sym) (s : List Bool) (v : Bool) :
    ∃ v', Run prog (s.length + 1) ⟨some .fmove, v, st x w t (s.map .bit) []⟩
      ⟨some .cmp, v', st x w t [] (s.map .bit).reverse⟩ := by
  obtain ⟨v', S', h, hA, hB, hk⟩ := moveB_run (M := prog) (self := .fmove) (next := .cmp) rfl
    (show K.A ≠ K.B by decide) s (s.map Sym.bit) [] v (st x w t (s.map .bit) []) (by simp)
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def]) (by simp [EndsBitBlock])
  have e : S' = st x w t [] (s.map .bit).reverse := by
    funext k
    cases k
    case A => simpa using hA
    case B => simpa using hB
    all_goals exact hk _ (by decide) (by decide)
  exact ⟨v', by simpa [e] using h⟩

/-- **Comparing the sum with the target.** Let $s$ and $\tau$ be bit lists. Start the SUBSET-SUM
verifier machine at the comparison label, with any value of the local variable, symbol lists $x$
and $w$ on $X$ and $W$, the target $\tau$ on $T$ and the sum $s$ on $B$ (both as bit symbols, last
bit on top), and the stacks $A$, $P$ and $Q$ empty. Then within $|s| + 1$ steps the machine reaches
the accepting label if $s = \tau$ and the rejecting label otherwise. -/
theorem cmp_run (x w : List Sym) (s tt : List Bool) (v : Bool) :
    ∃ v' S', RunLe prog (s.length + 1)
      ⟨some .cmp, v, st x w (tt.map .bit).reverse [] (s.map .bit).reverse⟩
      ⟨some (if s = tt then .yes else .no), v', S'⟩ := by
  obtain ⟨c, v', S', hc, -, -, h, -⟩ := cmpB_run (M := prog) (self := .cmp) (eqL := .yes)
    (neL := .no) rfl ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
    s.reverse tt.reverse (s.map Sym.bit).reverse [] (tt.map Sym.bit).reverse [] v
    (st x w (tt.map .bit).reverse [] (s.map .bit).reverse) (by simp) (by simp)
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def, List.map_reverse])
    (by simp [IsBitBlock, Sym.bit?, Function.comp_def, List.map_reverse])
    (by simp [EndsBitBlock]) (by simp [EndsBitBlock])
  simp only [List.reverse_inj] at h
  exact ⟨v', S', h.le (by simpa using hc.length_le)⟩

/-! ### The summing loop -/

/-- **The summing loop of the SUBSET-SUM verifier.** Let $N$ be a natural number and $t$ a list
of symbols. Write $\langle m \rangle$ for the canonical binary code of a natural number $m$, least
significant bit first, and put a bit list on a stack as the list of its name-bit symbols. Let $n$
and $s$ be natural numbers, $r$ and $w$ bit lists and $v$ a Boolean, with $|r| \le n$ and
$|\langle s \rangle| + |r| \le N$. Start the SUBSET-SUM verifier at the label $\mathsf{next}$
with internal state $v$, with $r$ on $X$, $w$ on $W$, $t$ on $T$, $\langle s \rangle$ on $A$,
and the stacks $B$, $P$ and $Q$ empty. Then for some internal state $v'$ and stack contents $S'$
it runs within $|r| \cdot (2N + 6) + 1$ steps to the configuration with internal state $v'$,
stacks $S'$ and label $\mathsf{fmove}$ if parsing the number blocks of $r$ with fuel $n$
succeeds, and label $\mathsf{no}$ if it fails. Moreover, if that parsing gives the list of
numbers $a$, and $\sigma$ is $s$ plus the sum of the numbers of $a$ chosen by the mask $w$, then
$|\langle \sigma \rangle| \le N$, and for some list of symbols $w'$ the stacks $S'$ hold nothing
on $X$, $w'$ on $W$, $t$ on $T$, $\langle \sigma \rangle$ on $A$, and nothing on $B$, $P$ and
$Q$. -/
theorem loop_run (N : ℕ) (t : List Sym) : ∀ (n : ℕ) (r w : List Bool) (s : ℕ) (v : Bool),
    r.length ≤ n → (encodeNat s).length + r.length ≤ N →
    ∃ v' S', RunLe prog (r.length * (2 * N + 6) + 1)
      ⟨some .next, v, st (r.map .bit) (w.map .bit) t ((encodeNat s).map .bit) []⟩
      ⟨some (if (numsAux n r).isSome then .fmove else .no), v', S'⟩ ∧
      ∀ as, numsAux n r = some as → (encodeNat (s + (pick as w).sum)).length ≤ N ∧
        ∃ w', S' = st [] w' t ((encodeNat (s + (pick as w).sum)).map .bit) []
  | n, [], w, s, v, _, hN => by
      refine ⟨true, st [] (w.map .bit) t ((encodeNat s).map .bit) [],
        (Run.single ?_).le (by simp), fun as has => ?_⟩
      · simp [prog, nextS, TM2.stepAux, numsAux_nil]
      · rw [numsAux_nil, Option.some.injEq] at has
        subst has
        simp only [List.length_nil, add_zero] at hN
        exact ⟨by simpa [pick] using hN, w.map .bit, by simp [pick]⟩
  | 0, _ :: _, _, _, _, h, _ => by simp at h
  | n + 1, b :: r₀, w, s, v, hn, hN => by
      have hne : b :: r₀ ≠ [] := List.cons_ne_nil b r₀
      generalize b :: r₀ = r at hne hn hN ⊢
      have h₁ : Run prog 1
          ⟨some .next, v, st (r.map .bit) (w.map .bit) t ((encodeNat s).map .bit) []⟩
          ⟨some (bif w.headD false then .add false false else .skip false), w.headD false,
            st (r.map .bit) (w.tail.map .bit) t ((encodeNat s).map .bit) []⟩ := by
        apply Run.single
        obtain ⟨c, r, rfl⟩ := List.exists_cons_of_ne_nil hne
        cases w with
        | nil => simp [prog, nextS, TM2.stepAux, bitOf, Sym.bit?]
        | cons c w => cases c <;> simp [prog, nextS, TM2.stepAux, bitOf, Sym.bit?]
      cases hu : undelimit r with
      | none =>
          have hr1 : 1 ≤ r.length := by
            cases r with
            | nil => exact absurd rfl hne
            | cons _ _ => simp
          have hb : decodeNatPrefix r = none := by
            simp [decodeNatPrefix, encodeNat_decodeNat_iff, hu]
          rw [numsAux_of_decode_none hne hb]
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨v', S', h₂⟩ : Rej (r.length + 1)
              ⟨some (bif w.headD false then .add false false else .skip false), w.headD false,
                st (r.map .bit) (w.tail.map .bit) t ((encodeNat s).map .bit) []⟩ := by
            cases w.headD false
            · exact skip_fail _ _ _ _ r hu false false
            · exact add_fail _ _ r hu false false (encodeNat s) [] true
          refine ⟨v', S', ((h₁.le le_rfl).trans h₂).mono ?_, by simp⟩
          nlinarith
      | some pr =>
          obtain ⟨p, r'⟩ := pr
          obtain rfl := (undelimit_eq_some_iff r p r').1 hu
          have hlen : (delimit p ++ r').length = 2 * p.length + 1 + r'.length := by
            simp only [List.length_append, length_delimit]
          by_cases hz : lastF false p = true
          · have hb : decodeNatPrefix (delimit p ++ r') = none := by
              simp [decodeNatPrefix, encodeNat_decodeNat_iff, hz]
            rw [numsAux_of_decode_none hne hb]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨v', S', h₂⟩ : Rej (p.length + 1)
                ⟨some (bif w.headD false then .add false false else .skip false), w.headD false,
                  st ((delimit p ++ r').map .bit) (w.tail.map .bit) t
                    ((encodeNat s).map .bit) []⟩ := by
              cases w.headD false
              · have h := skip_run r' (w.tail.map .bit) t ((encodeNat s).map .bit) [] p false
                  false
                rw [ite_eq_left hz] at h
                exact ⟨_, _, h.le le_rfl⟩
              · exact add_rej r' (w.tail.map .bit) t p false false (encodeNat s) [] true hz
            refine ⟨v', S', ((h₁.le le_rfl).trans h₂).mono ?_, by simp⟩
            rw [hlen]
            nlinarith
          · obtain ⟨a, rfl⟩ : ∃ a, encodeNat a = p :=
              ⟨decodeNat p, (encodeNat_decodeNat_iff p).2 (by simpa using hz)⟩
            have hb : decodeNatPrefix (delimit (encodeNat a) ++ r') = some (a, r') :=
              decodeNatPrefix_eq_some'.2 rfl
            rw [numsAux_of_decode hb, Option.isSome_map]
            have hn' : r'.length ≤ n := by omega
            cases hcw : w.headD false
            · simp only [hcw, Bool.cond_false] at h₁
              have h₂ := skip_run r' (w.tail.map .bit) t ((encodeNat s).map .bit) []
                (encodeNat a) false false
              rw [lastF_encodeNat, ite_eq_right (by simp)] at h₂
              obtain ⟨v', S', h₃, hF⟩ := loop_run N t n r' w.tail s false hn' (by omega)
              refine ⟨v', S', (((h₁.le le_rfl).trans (h₂.le le_rfl)).trans h₃).mono ?_,
                fun as has => ?_⟩
              · rw [hlen]
                nlinarith [Nat.zero_le ((encodeNat a).length * N)]
              · obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.1 has
                rw [sum_pick_cons, hcw]
                simpa using hF as' has'
            · simp only [hcw, Bool.cond_true] at h₁
              obtain ⟨v₂, h₂⟩ := add_run r' (w.tail.map .bit) t (encodeNat a) false false
                (encodeNat s) [] true (lastF_encodeNat a)
              rw [addB_encodeNat, Bool.toNat_false, Nat.add_zero, List.append_nil] at h₂
              obtain ⟨v₃, h₃⟩ := back_run (r'.map .bit) (w.tail.map .bit) t (encodeNat (s + a)) v₂
              have hres := length_addB false (encodeNat s) (encodeNat a)
              rw [addB_encodeNat, Bool.toNat_false, Nat.add_zero] at hres
              obtain ⟨v', S', h₄, hF⟩ := loop_run N t n r' w.tail (s + a) v₃ hn' (by omega)
              refine ⟨v', S',
                ((((h₁.le le_rfl).trans h₂).trans (h₃.le le_rfl)).trans h₄).mono ?_,
                fun as has => ?_⟩
              · rw [hlen]
                nlinarith [Nat.zero_le ((encodeNat a).length * N)]
              · obtain ⟨as', has', rfl⟩ := Option.map_eq_some_iff.1 has
                rw [sum_pick_cons, hcw, ite_eq_left rfl, ← Nat.add_assoc]
                exact hF as' has'

/-! ### The whole run -/

/-- **Cubic bound on the verifier's phase costs.** For natural numbers $X$, $W$, $P$, $R$ and $S$
with $P + R \le X$ and $S \le X$,
$P + 1 + (R(2X + 6) + 1) + (S + 1) + (S + 1) \le 16 (X + W + 1)^3$. -/
theorem cost_le (X W P R S : ℕ) (hP : P + R ≤ X) (hS : S ≤ X) :
    P + 1 + (R * (2 * X + 6) + 1) + (S + 1) + (S + 1) ≤ 16 * (X + W + 1) ^ 3 := by
  have h1 : R * (2 * X + 6) ≤ X * (2 * X + 6) := Nat.mul_le_mul_right _ (by omega)
  have h2 : (X + 1) ^ 2 ≤ (X + W + 1) ^ 3 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  nlinarith

/-- **The SUBSET-SUM verifier machine.** Let $x$ and $w$ be lists of bits and $v$ a Boolean, and
let $S$ assign stack contents with the bits of $x$ on $X$, the bits of $w$ on $W$ and every other
stack empty. Started at the start label with internal state $v$ and stacks $S$, the verifier
program reaches, within $16(|x| + |w| + 1)^3$ steps, a configuration with label $\mathsf{yes}$
if the SUBSET-SUM check accepts $(x, w)$, and with label $\mathsf{no}$ otherwise. -/
theorem run (x w : List Bool) (v : Bool) (St : ∀ _ : K, List Sym)
    (hX : St .X = x.map Sym.bit) (hW : St .W = w.map Sym.bit)
    (h0 : ∀ k, k ≠ .X → k ≠ .W → St k = []) :
    ∃ v' S', RunLe prog (16 * (x.length + w.length + 1) ^ 3) ⟨some start, v, St⟩
      ⟨some (if ssCheck x w then .yes else .no), v', S'⟩ := by
  have hSt : St = st (x.map Sym.bit) (w.map Sym.bit) [] [] [] := by
    funext k
    cases k <;> simp [hX, hW, h0]
  subst hSt
  cases hu : undelimit x with
  | none =>
      have hc : ssCheck x w = false := by
        simp [ssCheck, decodeSS, decodeNatPrefix, encodeNat_decodeNat_iff, hu]
      rw [hc]
      obtain ⟨v', S', h⟩ := tgt_fail (w.map .bit) [] [] x hu false [] v
      have := cost_le x.length w.length x.length 0 0 (by omega) (by omega)
      exact ⟨v', S', h.mono (by linarith)⟩
  | some pr =>
      obtain ⟨p, r⟩ := pr
      obtain rfl := (undelimit_eq_some_iff x p r).1 hu
      have hlen : (delimit p ++ r).length = 2 * p.length + 1 + r.length := by
        simp only [List.length_append, length_delimit]
      have h₁ := tgt_run r (w.map .bit) [] [] p false [] v
      simp only [List.append_nil] at h₁
      by_cases hz : lastF false p = true
      · have hc : ssCheck (delimit p ++ r) w = false := by
          simp [ssCheck, decodeSS, decodeNatPrefix, encodeNat_decodeNat_iff, hz]
        rw [hc]
        rw [ite_eq_left hz] at h₁
        have := cost_le (delimit p ++ r).length w.length p.length 0 0 (by omega) (by omega)
        exact ⟨_, _, h₁.le (by linarith)⟩
      · obtain ⟨t, rfl⟩ : ∃ t, encodeNat t = p :=
          ⟨decodeNat p, (encodeNat_decodeNat_iff p).2 (by simpa using hz)⟩
        rw [lastF_encodeNat, ite_eq_right (by simp)] at h₁
        have hd : decodeSS (delimit (encodeNat t) ++ r) =
            (numsAux r.length r).map fun as => (as, t) := by
          simp only [decodeSS, decodeNatPrefix_eq_some'.2 rfl]
        obtain ⟨v₂, S₂, h₂, hF⟩ := loop_run (delimit (encodeNat t) ++ r).length
          ((encodeNat t).map .bit).reverse r.length r w 0 false le_rfl
          (by rw [encodeNat_zero, hlen]; simp only [List.length_nil]; omega)
        cases hn : numsAux r.length r with
        | none =>
            have hc : ssCheck (delimit (encodeNat t) ++ r) w = false := by
              simp [ssCheck, hd, hn]
            rw [hc]
            rw [hn] at h₂
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h₂
            have := cost_le (delimit (encodeNat t) ++ r).length w.length (encodeNat t).length
              r.length 0 (by omega) (by omega)
            exact ⟨v₂, S₂, ((h₁.le le_rfl).trans h₂).mono (by linarith)⟩
        | some as =>
            rw [hn] at h₂
            simp only [Option.isSome_some, ↓reduceIte] at h₂
            obtain ⟨hlenS, w', rfl⟩ := hF as hn
            obtain ⟨v₃, h₃⟩ := fmove_run [] w' ((encodeNat t).map .bit).reverse
              (encodeNat (0 + (pick as w).sum)) v₂
            obtain ⟨v₄, S₄, h₄⟩ := cmp_run [] w' (encodeNat (0 + (pick as w).sum))
              (encodeNat t) v₃
            have hc : ssCheck (delimit (encodeNat t) ++ r) w = ((pick as w).sum == t) := by
              simp [ssCheck, hd, hn]
            rw [hc]
            have e : (if encodeNat (0 + (pick as w).sum) = encodeNat t then Lab.yes else .no) =
                if ((pick as w).sum == t) = true then .yes else .no := by
              simp [encodeNat_inj]
            rw [e] at h₄
            have := cost_le (delimit (encodeNat t) ++ r).length w.length (encodeNat t).length
              r.length (encodeNat (0 + (pick as w).sum)).length (by omega) hlenS
            exact ⟨v₄, S₄,
              ((((h₁.le le_rfl).trans h₂).trans (h₃.le le_rfl)).trans h₄).mono (by linarith)⟩

end Cslib.Complexity.Karp.SSVerify
