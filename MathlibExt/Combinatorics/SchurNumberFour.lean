/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/Schur/README.md` (leansolving/SqueezeBench), at commit
e2e19eef093a77882da57f348def029533ec2d5e: the statement of `schurNumber_four` (from the README's
"Known values" table), with its docstring from `WantedExt/Combinatorics/SchurNumbersWanted.lean`.
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. SqueezeBench ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: the README value, which
SqueezeBench marks as reporting only, was turned into a Batteries `theorem_wanted` declaration.
Later change (ATLAS, 2026): the statement was proved and moved from
`WantedExt/Combinatorics/SchurNumbersWanted.lean` to this `MathlibExt` module with unchanged name,
statement and docstring.

ATLAS contributed the proof, its private auxiliary definitions and lemmas, the search
certificate, and the module documentation.
-/
module

public import MathlibExt.Combinatorics.SchurNumbers
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Bitwise
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.IntervalCases

/-!
# The fourth Schur number

This file proves `schurNumber_four`: the Schur number `S(4)` equals `44`. That is, `[1, 44]`
splits into four sum-free classes, while every colouring of the natural numbers with four colours
has a monochromatic solution of `x + y = z` with `x, y, z ∈ [1, 45]`.

## Lower bound

A partition of `[1, 44]` into four sum-free classes, found by a computer search, is checked pair
by pair by the kernel (`decide +kernel`).

## Upper bound

The upper bound is a finite search, checked by the kernel against a certificate.

*Normalisation.* Since `1 + 1 = 2`, the numbers `1` and `2` get different colours, and after
permuting the colours we may assume that `1` has colour `0` and `2` has colour `1`.

*States.* A partial colouring is stored as four classes. Each class is a triple of bitmasks
`(m, r, f)`: `m` holds the members, `r` holds `64 - x` for each member `x` (so that `i - x` is a
right shift of `r`), and `f` holds the blocked numbers, those `w` for which some `x, y` in the
class satisfy `x + y = w`, `2 * w = x` or `x + w = y`. Adding `w` to the class would then create a
monochromatic solution. Adding a member `i` updates `f` by four shifts.

*Search.* At each state the checker (`check`) proceeds as follows.
* If some `w ∈ [1, 45]` is blocked in all four classes, there is nothing to do: every colouring
  that extends the state has a monochromatic solution.
* Otherwise, if some uncoloured number is blocked in exactly three classes, it takes the least
  such number. Else it reads the next number from the certificate.
* For the chosen number `i` and each colour `j` in which `i` is not blocked, it checks the state
  with `i` added to class `j`. When classes `2` and `3` are both empty the colour `3` is skipped,
  as swapping these two colours maps it to colour `2`.

The certificate lists the numbers read in the search tree, in depth-first order. The tree has
118381 nodes, but only 16222 of them read the certificate. The tree is cut into 22
chunks, each a separate kernel computation. The search above them reads the marker `0` followed
by an index `k` when it reaches the root of chunk `k`, and then checks that its state is the one
chunk `k` starts from. Each state is rebuilt from its four member masks (`stateOf`).

The certificate was produced by an external search program, which branched on a number whose
children leave the most constrained states, judged by a one-step lookahead. It records only the
branching choices, and the kernel recomputes everything else, so the program need not be
trusted.

`check_sound` proves the checker sound by induction. The chunks are checked by `decide +kernel`,
which evaluates the checker with the kernel's arithmetic on numerals (no `native_decide`).

The partition and the certificate were computed for this file; the docstring of
`schurNumber_four` gives the source of the statement.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SchurNumbersWanted

open Finset

/-! ### Lower bound -/

/-- A partition of `[1, 44]` into four sum-free classes, as a colouring: colour `j` for the `j`-th
of the three listed classes (counting from `0`), and colour `3` for every other number. On
`[1, 44]` the last class is `{9, 10, 11, 12, 14, 16, 29, 31, 34, 35, 36}`. -/
private def sumFreeColouring (n : ℕ) : Fin 4 :=
  if n ∈ ({1, 3, 5, 15, 17, 19, 26, 28, 40, 42, 44} : Finset ℕ) then 0
  else if n ∈ ({2, 7, 8, 18, 21, 24, 27, 33, 37, 38, 43} : Finset ℕ) then 1
  else if n ∈ ({4, 6, 13, 20, 22, 23, 25, 30, 32, 39, 41} : Finset ℕ) then 2 else 3

/-- The colouring `sumFreeColouring` has no monochromatic Schur triple in `[1, 44]`. -/
private theorem not_schurForces_four_44 : ¬ schurForces 4 44 := by
  have h : ∀ x ∈ Icc 1 44, ∀ y ∈ Icc 1 44, x + y ≤ 44 →
      sumFreeColouring x = sumFreeColouring y →
        sumFreeColouring y ≠ sumFreeColouring (x + y) := by
    decide +kernel
  intro hf
  obtain ⟨x, hx, y, hy, _, hz, rfl, hxy, hyz⟩ := hf sumFreeColouring
  exact h x hx y hy (mem_Icc.mp hz).2 hxy hyz

/-! ### The checker -/

/-- Bit `i` of `f`, with the operations the kernel evaluates on numerals. -/
private def tb (f i : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight f i) 1) 1

/-- The blocked mask after `i` joins a class, where `m` and `r` are the new member and reflected
masks: the old blocked mask `f`, the sums `x + i`, the differences `x - i` and `i - x` for members
`x`, and `i / 2` when `i` is even. -/
private def newF (f m r i : ℕ) : ℕ :=
  Nat.lor f (Nat.lor (Nat.lor (Nat.shiftLeft m i) (Nat.shiftRight m i))
    (Nat.lor (Nat.shiftRight r (64 - i))
      (cond (Nat.beq (i % 2) 0) (Nat.shiftLeft 1 (i / 2)) 0)))

/-- The type of the checker on a state: the masks `m, r, f` of the four classes, then the rest of
the certificate. -/
private abbrev Rec : Type :=
  ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → Option (List ℕ)

/-- Colour `3` for the number `i`: skipped when `i` is blocked in class `3`, or when classes `2`
and `3` are both empty, and otherwise checked with `rec`. -/
private def step3 (rec : Rec) (m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i : ℕ) (l : List ℕ) :
    Option (List ℕ) :=
  cond (tb f3 i || (Nat.beq m2 0 && Nat.beq m3 0)) (some l)
    (rec m0 r0 f0 m1 r1 f1 m2 r2 f2 (Nat.lor m3 (Nat.shiftLeft 1 i))
      (Nat.lor r3 (Nat.shiftLeft 1 (64 - i)))
      (newF f3 (Nat.lor m3 (Nat.shiftLeft 1 i)) (Nat.lor r3 (Nat.shiftLeft 1 (64 - i))) i) l)

/-- Colours `2` and `3` for the number `i`. -/
private def step2 (rec : Rec) (m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i : ℕ) (l : List ℕ) :
    Option (List ℕ) :=
  cond (tb f2 i) (step3 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i l)
    (Option.bind (rec m0 r0 f0 m1 r1 f1
      (Nat.lor m2 (Nat.shiftLeft 1 i)) (Nat.lor r2 (Nat.shiftLeft 1 (64 - i)))
      (newF f2 (Nat.lor m2 (Nat.shiftLeft 1 i)) (Nat.lor r2 (Nat.shiftLeft 1 (64 - i))) i)
      m3 r3 f3 l) (step3 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i))

/-- Colours `1`, `2` and `3` for the number `i`. -/
private def step1 (rec : Rec) (m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i : ℕ) (l : List ℕ) :
    Option (List ℕ) :=
  cond (tb f1 i) (step2 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i l)
    (Option.bind (rec m0 r0 f0
      (Nat.lor m1 (Nat.shiftLeft 1 i)) (Nat.lor r1 (Nat.shiftLeft 1 (64 - i)))
      (newF f1 (Nat.lor m1 (Nat.shiftLeft 1 i)) (Nat.lor r1 (Nat.shiftLeft 1 (64 - i))) i)
      m2 r2 f2 m3 r3 f3 l) (step2 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i))

/-- All four colours for the number `i`, which must lie in `[1, 45]`. -/
private def step0 (rec : Rec) (m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i : ℕ) (l : List ℕ) :
    Option (List ℕ) :=
  cond (Nat.ble 1 i && Nat.ble i 45)
    (cond (tb f0 i) (step1 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i l)
      (Option.bind (rec
        (Nat.lor m0 (Nat.shiftLeft 1 i)) (Nat.lor r0 (Nat.shiftLeft 1 (64 - i)))
        (newF f0 (Nat.lor m0 (Nat.shiftLeft 1 i)) (Nat.lor r0 (Nat.shiftLeft 1 (64 - i))) i)
        m1 r1 f1 m2 r2 f2 m3 r3 f3 l) (step1 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i)))
    none

/-- The mask of `[1, 45]`. -/
private def full : ℕ := 70368744177662

/-- The uncoloured numbers of `[1, 45]` that are blocked in exactly three classes. -/
private def three (m0 f0 m1 f1 m2 f2 m3 f3 : ℕ) : ℕ :=
  Nat.land (Nat.xor full (Nat.lor (Nat.lor m0 m1) (Nat.lor m2 m3)))
    (Nat.lor (Nat.land (Nat.land f0 f1) (Nat.xor f2 f3))
      (Nat.land (Nat.xor f0 f1) (Nat.land f2 f3)))

/-- Digit `2 ^ k % 67` of this number in base `64` is `k`, for `k < 64`: the residues
`2 ^ k % 67` are distinct, as `2` has order `66` modulo `67`. The other digits are `0`. -/
private def log2Table : ℕ :=
  List.foldr (fun d t => d + 64 * t) 0
    [0, 0, 1, 39, 2, 15, 40, 23, 3, 12, 16, 59, 41, 19, 24, 54, 4, 0, 13, 10, 17, 62, 60, 28, 42,
      30, 20, 51, 25, 44, 55, 47, 5, 32, 0, 38, 14, 22, 11, 58, 18, 53, 63, 9, 61, 27, 29,
      50, 43, 46, 31, 37, 21, 57, 52, 8, 26, 49, 45, 36, 56, 7, 48, 35, 6, 34, 33]

/-- The position of the lowest set bit of `x`, for `0 < x < 2 ^ 64`. -/
private def lowIdx (x : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight log2Table (6 * (Nat.xor x (Nat.land x (x - 1)) % 67))) 63

/-- The masks `m, r, f` of the class with member mask `m`, adding the members in increasing
order. -/
private def classOf (m : ℕ) : List ℕ :=
  let t := (List.range' 1 45).foldl (fun (t : ℕ × ℕ × ℕ) i =>
    cond (tb m i)
      (Nat.lor t.1 (Nat.shiftLeft 1 i), Nat.lor t.2.1 (Nat.shiftLeft 1 (64 - i)),
        newF t.2.2 (Nat.lor t.1 (Nat.shiftLeft 1 i)) (Nat.lor t.2.1 (Nat.shiftLeft 1 (64 - i))) i)
      t) (0, 0, 0)
  [t.1, t.2.1, t.2.2]

/-- The twelve masks of the state with the given member masks of the four classes. -/
private def stateOf (s : List ℕ) : List ℕ :=
  s.flatMap classOf

/-- A leaf of the search above the chunks: the certificate gives the index `k` of a chunk, whose
state must be the current one. -/
private def chunkLeaf (lem : List (List ℕ)) (m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 : ℕ) :
    List ℕ → Option (List ℕ)
  | [] => none
  | k :: l => cond (decide (stateOf (lem.getD k []) =
      [m0, r0, f0, m1, r1, f1, m2, r2, f2, m3, r3, f3])) (some l) none

/-- The checker, with fuel `n` (one unit per level of the search tree). On success it returns
the rest of the certificate. `lem` lists the member masks of the chunk roots. -/
private def check (lem : List (List ℕ)) : ℕ → Rec
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m0, r0, f0, m1, r1, f1, m2, r2, f2, m3, r3, f3, l =>
    cond (Nat.beq (Nat.land full (Nat.land (Nat.land f0 f1) (Nat.land f2 f3))) 0)
      (cond (Nat.beq (three m0 f0 m1 f1 m2 f2 m3 f3) 0)
        (match l with
         | [] => none
         | i :: l =>
           cond (Nat.beq i 0) (chunkLeaf lem m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 l)
             (step0 (check lem n) m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i l))
        (step0 (check lem n) m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3
          (lowIdx (three m0 f0 m1 f1 m2 f2 m3 f3)) l))
      (some l)
termination_by structural n => n

/-- The checker on a state given as a list of twelve masks. -/
private def checkState (lem : List (List ℕ)) (t : List ℕ) (l : List ℕ) : Option (List ℕ) :=
  match t with
  | [m0, r0, f0, m1, r1, f1, m2, r2, f2, m3, r3, f3] =>
    check lem 46 m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 l
  | _ => none

/-- Unpack `k` base-`64` digits of `c` (lowest first) in front of `acc`. -/
private def unpack : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, acc => acc
  | k + 1, c, acc => c % 64 :: unpack k (c / 64) acc

/-- A certificate stored with `60` base-`64` digits per numeral. -/
private def decode (cs : List ℕ) : List ℕ :=
  cs.foldr (fun c acc => unpack 60 c acc) []

/-! ### Soundness of the checker -/

/-- The colouring `c` has a monochromatic solution of `x + y = z` in `[1, 45]`. -/
private def Mono (c : ℕ → Fin 4) : Prop :=
  ∃ x ∈ Icc 1 45, ∃ y ∈ Icc 1 45, ∃ z ∈ Icc 1 45, x + y = z ∧ c x = c y ∧ c y = c z

/-- Adding `w` to a class with member mask `m` creates a solution of `x + y = z` in the class. -/
private def Blocked (m w : ℕ) : Prop :=
  (∃ x y, m.testBit x ∧ m.testBit y ∧ x + y = w) ∨ m.testBit (2 * w) ∨
    ∃ x, m.testBit x ∧ m.testBit (x + w)

/-- The masks `m, r, f` describe a class of colour `j` of the colouring `c`. -/
private structure ClassInv (c : ℕ → Fin 4) (j : Fin 4) (m r f : ℕ) : Prop where
  mem : ∀ x, m.testBit x → 1 ≤ x ∧ x ≤ 45 ∧ c x = j
  refl : ∀ t, r.testBit t → t ≤ 64 ∧ m.testBit (64 - t)
  blocked : ∀ w, 1 ≤ w → f.testBit w → Blocked m w

/-- Every colouring that extends the state has a monochromatic solution in `[1, 45]`. -/
private def Proven (m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 : ℕ) : Prop :=
  ∀ c, ClassInv c 0 m0 r0 f0 → ClassInv c 1 m1 r1 f1 → ClassInv c 2 m2 r2 f2 →
    ClassInv c 3 m3 r3 f3 → Mono c

/-- `Proven` for a state given as a list of twelve masks. -/
private def ProvenL (t : List ℕ) : Prop :=
  ∀ m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3,
    t = [m0, r0, f0, m1, r1, f1, m2, r2, f2, m3, r3, f3] →
      Proven m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3

/-- A checker on states is sound when each success proves its state. -/
private def RecSound (rec : Rec) : Prop :=
  ∀ m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 l l',
    rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 l = some l' →
      Proven m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3

private theorem tb_eq (f i : ℕ) : tb f i = f.testBit i := by
  have h1 : Nat.land (Nat.shiftRight f i) 1 = (f >>> i) % 2 := Nat.and_one_is_mod _
  have h2 : f.testBit i = (1 &&& f >>> i != 0) := rfl
  rw [tb, h1, h2, Nat.one_and_eq_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (f >>> i) with h | h <;> rw [h] <;> rfl

private theorem testBit_lor (a b w : ℕ) :
    (Nat.lor a b).testBit w = (a.testBit w || b.testBit w) :=
  Nat.testBit_or a b w

private theorem testBit_land (a b w : ℕ) :
    (Nat.land a b).testBit w = (a.testBit w && b.testBit w) :=
  Nat.testBit_and a b w

private theorem testBit_shiftLeft_one (i w : ℕ) :
    (Nat.shiftLeft 1 i).testBit w = decide (i = w) := by
  change (1 <<< i).testBit w = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem testBit_shiftLeft' (m i w : ℕ) :
    (Nat.shiftLeft m i).testBit w = (decide (w ≥ i) && m.testBit (w - i)) :=
  Nat.testBit_shiftLeft m

private theorem testBit_shiftRight' (m i w : ℕ) :
    (Nat.shiftRight m i).testBit w = m.testBit (i + w) :=
  Nat.testBit_shiftRight m

private theorem testBit_newF (f m r i w : ℕ) :
    (newF f m r i).testBit w = (f.testBit w || (decide (w ≥ i) && m.testBit (w - i)) ||
      m.testBit (i + w) || r.testBit (64 - i + w) ||
        (Nat.beq (i % 2) 0 && decide (i / 2 = w))) := by
  unfold newF
  rw [testBit_lor, testBit_lor, testBit_lor, testBit_shiftLeft', testBit_shiftRight', testBit_lor,
    testBit_shiftRight']
  cases Nat.beq (i % 2) 0
  · rw [Bool.cond_false]
    simp [Bool.or_assoc]
  · rw [Bool.cond_true, testBit_shiftLeft_one]
    simp [Bool.or_assoc]

/-- A blocked number of a class gives a monochromatic solution once it has the class's
colour. -/
private theorem mono_of_blocked {c : ℕ → Fin 4} {j : Fin 4} {m r f w : ℕ}
    (h : ClassInv c j m r f) (hw1 : 1 ≤ w) (hw : w ≤ 45) (hc : c w = j) (hb : Blocked m w) :
    Mono c := by
  rcases hb with ⟨x, y, hx, hy, rfl⟩ | h2 | ⟨x, hx, hxw⟩
  · obtain ⟨hx1, hx2, hcx⟩ := h.mem x hx
    obtain ⟨hy1, hy2, hcy⟩ := h.mem y hy
    exact ⟨x, mem_Icc.2 ⟨hx1, hx2⟩, y, mem_Icc.2 ⟨hy1, hy2⟩, x + y, mem_Icc.2 ⟨hw1, hw⟩, rfl,
      hcx.trans hcy.symm, hcy.trans hc.symm⟩
  · obtain ⟨h1, h2', hc2⟩ := h.mem _ h2
    exact ⟨w, mem_Icc.2 ⟨hw1, hw⟩, w, mem_Icc.2 ⟨hw1, hw⟩, 2 * w, mem_Icc.2 ⟨h1, h2'⟩,
      by omega, rfl, hc.trans hc2.symm⟩
  · obtain ⟨hx1, hx2, hcx⟩ := h.mem x hx
    obtain ⟨h1, h2', hc2⟩ := h.mem _ hxw
    exact ⟨x, mem_Icc.2 ⟨hx1, hx2⟩, w, mem_Icc.2 ⟨hw1, hw⟩, x + w, mem_Icc.2 ⟨h1, h2'⟩, rfl,
      hcx.trans hc.symm, hc.trans hc2.symm⟩

/-- If the checker finds `i` blocked in the class of its colour, there is a monochromatic
solution. -/
private theorem mono_of_tb {c : ℕ → Fin 4} {j : Fin 4} {m r f i : ℕ} (h : ClassInv c j m r f)
    (hi1 : 1 ≤ i) (hi45 : i ≤ 45) (hc : c i = j) (ht : tb f i = true) : Mono c :=
  mono_of_blocked h hi1 hi45 hc (h.blocked i hi1 (by rwa [tb_eq] at ht))

private theorem Blocked.mono {m m' w : ℕ} (h : Blocked m w)
    (hm : ∀ x, m.testBit x = true → m'.testBit x = true) : Blocked m' w := by
  rcases h with ⟨x, y, hx, hy, rfl⟩ | h2 | ⟨x, hx, hxw⟩
  · exact Or.inl ⟨x, y, hm x hx, hm y hy, rfl⟩
  · exact Or.inr (Or.inl (hm _ h2))
  · exact Or.inr (Or.inr ⟨x, hm x hx, hm _ hxw⟩)

/-- Adding a number `i ∈ [1, 45]` of colour `j` to a class of colour `j`. -/
private theorem ClassInv.ins {c : ℕ → Fin 4} {j : Fin 4} {m r f i : ℕ} (h : ClassInv c j m r f)
    (hi1 : 1 ≤ i) (hi45 : i ≤ 45) (hc : c i = j) :
    ClassInv c j (Nat.lor m (Nat.shiftLeft 1 i)) (Nat.lor r (Nat.shiftLeft 1 (64 - i)))
      (newF f (Nat.lor m (Nat.shiftLeft 1 i)) (Nat.lor r (Nat.shiftLeft 1 (64 - i))) i) := by
  have hm' : ∀ x, (Nat.lor m (Nat.shiftLeft 1 i)).testBit x = (m.testBit x || decide (i = x)) :=
    fun x => by rw [testBit_lor, testBit_shiftLeft_one]
  have hmi : (Nat.lor m (Nat.shiftLeft 1 i)).testBit i = true := by simp
  have hsub : ∀ x, m.testBit x = true → (Nat.lor m (Nat.shiftLeft 1 i)).testBit x = true :=
    fun x hx => by simp [hx]
  refine ⟨fun x hx => ?_, fun t ht => ?_, fun w hw1 hw => ?_⟩
  · rw [hm'] at hx
    rcases Bool.or_eq_true_iff.1 hx with hx | hx
    · exact h.mem x hx
    · obtain rfl := of_decide_eq_true hx
      exact ⟨hi1, hi45, hc⟩
  · rw [testBit_lor, testBit_shiftLeft_one] at ht
    rcases Bool.or_eq_true_iff.1 ht with ht | ht
    · obtain ⟨h1, h2⟩ := h.refl t ht
      exact ⟨h1, hsub _ h2⟩
    · obtain rfl := of_decide_eq_true ht
      refine ⟨by omega, ?_⟩
      rwa [show 64 - (64 - i) = i by omega]
  · rw [testBit_newF] at hw
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq] at hw
    rcases hw with (((hw | ⟨hwi, hw⟩) | hw) | hw) | ⟨hpar, hw⟩
    · exact (h.blocked w hw1 hw).mono hsub
    · -- `w = (w - i) + i`
      exact Or.inl ⟨w - i, i, hw, hmi, by omega⟩
    · -- `i + w` is a member
      exact Or.inr (Or.inr ⟨i, hmi, hw⟩)
    · -- `i - w` is a member, through the reflected mask
      rw [testBit_lor, testBit_shiftLeft_one] at hw
      rcases Bool.or_eq_true_iff.1 hw with hw | hw
      · obtain ⟨h1, h2⟩ := h.refl _ hw
        refine Or.inr (Or.inr ⟨i - w, hsub _ ?_, ?_⟩)
        · rwa [show 64 - (64 - i + w) = i - w by omega] at h2
        · rwa [show i - w + w = i by omega]
      · have := of_decide_eq_true hw
        omega
    · -- `w = i / 2`
      exact Or.inr (Or.inl (by rwa [show 2 * w = i by omega]))

/-- Recolouring: a class whose members all keep a common colour. -/
private theorem ClassInv.recolour {c c' : ℕ → Fin 4} {j j' : Fin 4} {m r f : ℕ}
    (h : ClassInv c j m r f) (hc : ∀ x, m.testBit x = true → c x = j → c' x = j') :
    ClassInv c' j' m r f :=
  ⟨fun x hx => by
    obtain ⟨h1, h2, h3⟩ := h.mem x hx
    exact ⟨h1, h2, hc x hx h3⟩, h.refl, h.blocked⟩

private theorem ClassInv.empty (c : ℕ → Fin 4) (j : Fin 4) : ClassInv c j 0 0 0 :=
  ⟨fun x hx => by simp at hx, fun t ht => by simp at ht, fun w _ hw => by simp at hw⟩

/-- A permutation of the colours keeps monochromatic solutions. -/
private theorem Mono.of_perm {c : ℕ → Fin 4} (e : Fin 4 ≃ Fin 4) (h : Mono fun x => e (c x)) :
    Mono c := by
  obtain ⟨x, hx, y, hy, z, hz, hxyz, h1, h2⟩ := h
  exact ⟨x, hx, y, hy, z, hz, hxyz, e.injective h1, e.injective h2⟩

/-- No number of `[1, 45]` is blocked in an empty class. -/
private theorem tb_of_empty {c : ℕ → Fin 4} {j : Fin 4} {r f i : ℕ} (h : ClassInv c j 0 r f)
    (hi1 : 1 ≤ i) : tb f i = false := by
  rw [tb_eq]
  by_contra hb
  rcases h.blocked i hi1 (by simpa using hb) with ⟨_, _, hx, _⟩ | h2 | ⟨_, hx, _⟩ <;>
    simp at *

private theorem step3_sound {rec : Rec} (hrec : RecSound rec)
    {m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i : ℕ} {l l' : List ℕ}
    (h : step3 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i l = some l') (hi1 : 1 ≤ i)
    (hi45 : i ≤ 45) {c : ℕ → Fin 4} (h0 : ClassInv c 0 m0 r0 f0) (h1 : ClassInv c 1 m1 r1 f1)
    (h2 : ClassInv c 2 m2 r2 f2) (h3 : ClassInv c 3 m3 r3 f3) (hci : c i = 3)
    (hskip : ¬ (m2 = 0 ∧ m3 = 0)) : Mono c := by
  unfold step3 at h
  cases ht : tb f3 i
  · have hs : (Nat.beq m2 0 && Nat.beq m3 0) = false := by
      cases hb : (Nat.beq m2 0 && Nat.beq m3 0)
      · rfl
      · simp only [Bool.and_eq_true, Nat.beq_eq] at hb
        exact absurd hb hskip
    rw [ht, hs] at h
    exact hrec _ _ _ _ _ _ _ _ _ _ _ _ _ _ h c h0 h1 h2 (h3.ins hi1 hi45 hci)
  · exact mono_of_tb h3 hi1 hi45 hci ht

private theorem step2_sound {rec : Rec} (hrec : RecSound rec)
    {m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i : ℕ} {l l' : List ℕ}
    (h : step2 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i l = some l') (hi1 : 1 ≤ i)
    (hi45 : i ≤ 45) {c : ℕ → Fin 4} (h0 : ClassInv c 0 m0 r0 f0) (h1 : ClassInv c 1 m1 r1 f1)
    (h2 : ClassInv c 2 m2 r2 f2) (h3 : ClassInv c 3 m3 r3 f3) (hci : c i = 2 ∨ c i = 3) :
    Mono c := by
  unfold step2 at h
  cases ht : tb f2 i <;> rw [ht] at h
  · obtain ⟨l₁, hl₁, h'⟩ := Option.bind_eq_some_iff.1 h
    have hP := hrec _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl₁
    rcases hci with hci | hci
    · exact hP c h0 h1 (h2.ins hi1 hi45 hci) h3
    · by_cases hskip : m2 = 0 ∧ m3 = 0
      · -- swap the colours `2` and `3`
        obtain ⟨rfl, rfl⟩ := hskip
        let e : Fin 4 ≃ Fin 4 := Equiv.swap 2 3
        refine Mono.of_perm e (hP (fun x => e (c x)) ?_ ?_ ?_ ?_)
        · exact h0.recolour fun x _ hx => by simp [e, hx, Equiv.swap_apply_of_ne_of_ne]
        · exact h1.recolour fun x _ hx => by simp [e, hx, Equiv.swap_apply_of_ne_of_ne]
        · refine ClassInv.ins ?_ hi1 hi45 (by simp [e, hci])
          exact h2.recolour fun x hx _ => by simp at hx
        · exact h3.recolour fun x hx _ => by simp at hx
      · exact step3_sound hrec h' hi1 hi45 h0 h1 h2 h3 hci hskip
  · rcases hci with hci | hci
    · exact mono_of_tb h2 hi1 hi45 hci ht
    · by_cases hskip : m2 = 0 ∧ m3 = 0
      · obtain ⟨rfl, rfl⟩ := hskip
        rw [tb_of_empty h2 hi1] at ht
        exact absurd ht (by decide)
      · exact step3_sound hrec h hi1 hi45 h0 h1 h2 h3 hci hskip

private theorem step1_sound {rec : Rec} (hrec : RecSound rec)
    {m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i : ℕ} {l l' : List ℕ}
    (h : step1 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i l = some l') (hi1 : 1 ≤ i)
    (hi45 : i ≤ 45) {c : ℕ → Fin 4} (h0 : ClassInv c 0 m0 r0 f0) (h1 : ClassInv c 1 m1 r1 f1)
    (h2 : ClassInv c 2 m2 r2 f2) (h3 : ClassInv c 3 m3 r3 f3) (hci : c i ≠ 0) : Mono c := by
  have hci' : c i = 1 ∨ c i = 2 ∨ c i = 3 := by
    revert hci; generalize c i = v; revert v; decide
  unfold step1 at h
  cases ht : tb f1 i <;> rw [ht] at h
  · obtain ⟨l₁, hl₁, h'⟩ := Option.bind_eq_some_iff.1 h
    rcases hci' with hci' | hci'
    · exact hrec _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl₁ c h0 (h1.ins hi1 hi45 hci') h2 h3
    · exact step2_sound hrec h' hi1 hi45 h0 h1 h2 h3 hci'
  · rcases hci' with hci' | hci'
    · exact mono_of_tb h1 hi1 hi45 hci' ht
    · exact step2_sound hrec h hi1 hi45 h0 h1 h2 h3 hci'

private theorem step0_sound {rec : Rec} (hrec : RecSound rec)
    {m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i : ℕ} {l l' : List ℕ}
    (h : step0 rec m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 i l = some l') :
    Proven m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 := by
  intro c h0 h1 h2 h3
  unfold step0 at h
  cases hr : (Nat.ble 1 i && Nat.ble i 45) <;> rw [hr] at h
  · simp at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at hr
  obtain ⟨hi1, hi45⟩ := hr
  simp only [Bool.cond_true] at h
  cases ht : tb f0 i <;> rw [ht] at h
  · obtain ⟨l₁, hl₁, h'⟩ := Option.bind_eq_some_iff.1 h
    by_cases hci : c i = 0
    · exact hrec _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl₁ c (h0.ins hi1 hi45 hci) h1 h2 h3
    · exact step1_sound hrec h' hi1 hi45 h0 h1 h2 h3 hci
  · by_cases hci : c i = 0
    · exact mono_of_tb h0 hi1 hi45 hci ht
    · exact step1_sound hrec h hi1 hi45 h0 h1 h2 h3 hci

private theorem testBit_full {w : ℕ} (hw : full.testBit w = true) : 1 ≤ w ∧ w ≤ 45 := by
  by_contra hw'
  rcases (show w = 0 ∨ 46 ≤ w by omega) with rfl | h46
  · exact absurd hw (by decide)
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide) (Nat.pow_le_pow_right
      (by omega) h46))] at hw
    exact absurd hw (by decide)

/-- A number of `[1, 45]` blocked in all four classes gives a monochromatic solution. -/
private theorem mono_of_dead {m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 : ℕ}
    (h : Nat.beq (Nat.land full (Nat.land (Nat.land f0 f1) (Nat.land f2 f3))) 0 = false) :
    Proven m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 := by
  intro c h0 h1 h2 h3
  have hne : Nat.land full (Nat.land (Nat.land f0 f1) (Nat.land f2 f3)) ≠ 0 := by
    intro h'
    rw [h', Nat.beq_refl] at h
    exact absurd h (by decide)
  obtain ⟨w, hw⟩ := Nat.exists_testBit_of_ne_zero hne
  simp only [testBit_land, Bool.and_eq_true] at hw
  obtain ⟨hwf, ⟨hw0, hw1⟩, hw2, hw3⟩ := hw
  obtain ⟨hw1', hw45⟩ := testBit_full hwf
  have hc : c w = 0 ∨ c w = 1 ∨ c w = 2 ∨ c w = 3 := by
    generalize c w = v; revert v; decide
  rcases hc with hc | hc | hc | hc
  · exact mono_of_tb h0 hw1' hw45 hc (by rwa [tb_eq])
  · exact mono_of_tb h1 hw1' hw45 hc (by rwa [tb_eq])
  · exact mono_of_tb h2 hw1' hw45 hc (by rwa [tb_eq])
  · exact mono_of_tb h3 hw1' hw45 hc (by rwa [tb_eq])

private theorem chunkLeaf_sound {lem : List (List ℕ)} (hlem : ∀ s ∈ lem, ProvenL (stateOf s))
    {m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 : ℕ} {l l' : List ℕ}
    (h : chunkLeaf lem m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 l = some l') :
    Proven m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 := by
  cases l with
  | nil => simp [chunkLeaf] at h
  | cons k l =>
    dsimp only [chunkLeaf] at h
    cases hd : decide (stateOf (lem.getD k []) = [m0, r0, f0, m1, r1, f1, m2, r2, f2, m3, r3, f3])
      <;> rw [hd] at h
    · simp at h
    have hs := of_decide_eq_true hd
    by_cases hk : k < lem.length
    · rw [List.getD_eq_getElem _ _ hk] at hs
      exact hlem _ (List.getElem_mem hk) _ _ _ _ _ _ _ _ _ _ _ _ hs
    · rw [List.getD_eq_default _ _ (by omega)] at hs
      simp [stateOf] at hs

/-- Soundness of the checker: each success proves its state. -/
private theorem check_sound {lem : List (List ℕ)} (hlem : ∀ s ∈ lem, ProvenL (stateOf s)) :
    ∀ n, RecSound (check lem n)
  | 0 => fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => by simp [check] at h
  | n + 1 => fun m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 l l' h => by
    unfold check at h
    cases hd : Nat.beq (Nat.land full (Nat.land (Nat.land f0 f1) (Nat.land f2 f3))) 0 <;>
      rw [hd] at h
    · exact mono_of_dead hd
    simp only [Bool.cond_true] at h
    cases h3 : Nat.beq (three m0 f0 m1 f1 m2 f2 m3 f3) 0 <;> rw [h3] at h
    · exact step0_sound (check_sound hlem n) h
    simp only [Bool.cond_true] at h
    cases l with
    | nil => simp at h
    | cons i l =>
      simp only at h
      cases hi : Nat.beq i 0 <;> rw [hi] at h
      · exact step0_sound (check_sound hlem n) h
      · exact chunkLeaf_sound hlem h

private theorem checkState_sound {lem : List (List ℕ)} (hlem : ∀ s ∈ lem, ProvenL (stateOf s))
    {t l : List ℕ} (h : (checkState lem t l).isSome = true) : ProvenL t := by
  intro m0 r0 f0 m1 r1 f1 m2 r2 f2 m3 r3 f3 rfl
  obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.1 h
  exact check_sound hlem 46 _ _ _ _ _ _ _ _ _ _ _ _ _ _ hl'

/-! ### The certificate -/

/-- The member masks of the four classes at the root of each chunk. -/
private def chunkMasks : List (List ℕ) := [
  [0x42, 0x84, 0x0, 0x0],
  [0x42, 0x24, 0x80, 0x0],
  [0x42, 0x4, 0xa0, 0x0],
  [0x42, 0x4, 0x80, 0x20],
  [0xa, 0x44, 0x0, 0x0],
  [0x102, 0x44, 0x8, 0x0],
  [0x2, 0x44, 0x108, 0x0],
  [0x2, 0x44, 0x8, 0x100],
  [0x122, 0x4, 0x40, 0x0],
  [0x22, 0x104, 0x40, 0x0],
  [0x22, 0x4, 0x140, 0x10],
  [0x22, 0x4, 0x50, 0x100],
  [0x82, 0x24, 0x40, 0x0],
  [0x2, 0x24, 0xc0, 0x0],
  [0x2, 0x24, 0x40, 0x80],
  [0x4002, 0x4, 0x60, 0x0],
  [0x2, 0x4004, 0x60, 0x0],
  [0x2, 0x4, 0x4060, 0x0],
  [0x2, 0x4, 0x60, 0x4000],
  [0x402, 0x4, 0x40, 0x20],
  [0x2, 0x404, 0x40, 0x20],
  [0x2, 0x4, 0x440, 0x20]]

/-- The certificate of each chunk: its branching numbers, packed by `decode`. -/
private def chunkCerts : List (List ℕ) := [
  -- 16 numerals
  [0x71251750b3563d335744d5913cc7125cc65444c7173510c334b2d850d5c84cc71159b5185133df44f34e250285,
   0x5573d45cc34c5cb11960885e34e70f51154c11320934c2592cf3206d54d632c2173cd30b11445864e3ce816444,
   0x61975c95972061246060872070c0d620b5577937835126530ce99859721555c8606954d23c485f31660f54354f,
   0x31135330e2210dc48f2600d64677193da6124554ce8d520c5cc0d74c97ce0dc48d51a7d96165dc81459839871c,
   0xdd69975a48941712249e65841c4267d85c32504d435a4da11081335365244e30849f3a164d20f3cf48365334c,
   0x3ce2c930d3d045039038d25235741624e2d149258e44c4da5124047627d751d2ce35872491675a58d2d245569f,
   0x6903d06922ce5197cd58f24925a54f50b5d58104da0d53cc39d35454399a50350e31a39f48d24d5093d0456816,
   0x59310db0c4166125083a05d53a34a070d71a4193e339f6432da7525d53a25d05df6192598da2cd75a75640949a,
   0x11935725711146041381245055645280d34d10c26748b0d540b4c468b31061944c5d98108905d684d317344250,
   0x58d48f40d64b69240f0d269d59a2d35082595955972d85cd54b4d52513d061151244f4546997118174941107da,
   0x11870364f48c65350355662049870f58d81959150d6902e06e05835844604834e255065645b59b69c2d14d145b,
   0x69440f11569068b4433cb45a5623cd45020f4934164de81754b5123135c334b49449665240b4944913d33d63d0,
   0x54d45226c49036355f6964110c840f20b4837a36d771151249252834b85951e2037115c834f348509604599214,
   0x51d58935124d41420f6d15486c82d121f58365c70c0d484f4885cd4e47cd4083432254207c868f65b6570d0490,
   0x51a31d2d40e150b5907d63137207982094a440f7d051496569134b41a92071a7db64b24d21984931e8cd34849a,
   0x1631421e81a21a4555527d55d66945543d05d860f5d63d665048f68c6d64dc6e05943df6d6],
  -- 12 numerals
  [0x25b4de34965c3dc36780b50944c4949166176173d84954a22d23d53125dc38d5a860939750965354f459210283,
   0x45c69b4d269c6cb3597135915c82d685a40d2d965534841f69511044c49438f3994d43915162d330d5183db50c,
   0x3cb51745a41b64b55121f55548d41651940d59420f2575155d77087d956276574d4142443094d15d93566d1784,
   0x86048d2c85cb25e71460b3d99202cf51385b69020b35a4174576cd81250d20f51071831e6444c85d410d4df704,
   0x2934122cf50e5db85d6948d324f69b7935d14d971b55a6cd2d120979f8d594d7162138105997525cd51c78b48f,
   0x60f60b3606205882ca35c40b3502d86514154d26502e710b28445231265c30a41a41961f59c69528411f24964d,
   0x58d41d21720b68b69075428f25135c24954f5d12116497c91172cb21130f2cf49f49122364f40c31b6604d848a,
   0x50a28834c4d475350859074b3526d441758d35229335d22220b4ca6cd35465a65440d58ba1a4cb2e4424551404,
   0x2524da55429a55a51279668828971421a3102d15046102dd50a40d28b65710a49368b6d622251711b20c35334f,
   0x3d241f68a41835230b69a55369441a550312689a5454c2d670851a35a4154d011a5c92926123da49711c3dc99a,
   0x41031a81979721a4d470960450f3d769d35668f64948f3cd1182cb2482ca28b2134123ca35278420c613744409,
   0x25e4092122565c825758d6905d811b6084d76085269985d055a4c830a756],
  -- 15 numerals
  [0x3575082d65194495513cb3916432d34d14912d848339040d5974575d22083dc5cd5d85d68184945d169424428c,
   0x35d20f4d8554a0d71d7d37094c37117173499d34574433d97574434df34e0db64f25825f34b3d68176d63c9214,
   0xde7188607585d08126a00cd39261258b4832176184924c826825335d4237c44446c84034504084492d871f2c9,
   0x1174572152107135da2dc41055f6195573ce5c334f44b2515cf3555a00d345f4444904d18104433cb4a58090d6,
   0x6d83942622d262255a6193d020a11724f9510d140b62121c9c886635c24f11026920460b6174cd71b3505517d9,
   0x8552434d050e75e6165d871d6574e38587097185a171845335b66049e8536d96a55494894a14cd6a560e7a0653,
   0x79235269e8157d748d0d57dc5e54dc35a55749058d6195d564935c6c355124d5e360e5614c92da40f2554c9558,
   0x41b7c939344d41f62524f75120f39170b3dd38f5c36837d93504087dd20e85d35545c20e4d48df0d595c38d343,
   0x6d741b45285275470351c4112cb0dd74f5db0d36942094197593d94087da7173db7157df2d32595570e371d212,
   0x28b69635d55559451d39468d5883d975058d55a59d54e51d71b51745a4946155880c941545f3da41345b71f55a,
   0x6035d45d141660a20e51875a3ce6166e374e4607085126160d079f61651945c95e80d51a7437d33546e079834e,
   0x2d154821445250f6d445269f71450d5d44986943902d25565584c849a51d49959c45245641b4485975d8297517,
   0x48d2134cb0c92dd34f4d261878d3d93c85939217dc6cf49366261a0cf61960f38d29071c69341844e75454d294,
   0x21d2623d645365834f5d15152df85491f60f28925344f4a1b116934920da35185348f4e13d25d14d2283549693,
   0x49a3915c920d5082562583493c85165d551a5cf2972594d45430d661360e7cf6a23d339120375134e7cf613],
  -- 12 numerals
  [0xd175c3085cc5c82d05ac3d8203a0c7155984582cd5512e85e47163144515c311c0dcadb4584cd2cf30440e24a,
   0x54c6e445281634e42175049a4d338c4d03445914cf0e24c85117cc3d93cc4d56117084915da4d01153114cb5d1,
   0x44d55240434b40f65738b25320c80c40d91244c34e51f4500cb71b5cc0d259c61e31335759121359844c494653,
   0x25d4dc61c8964130cd61139111084e49089541254d3986534d538f3d024f5d93932d50d53845155192d00d0811,
   0x69b4de60d71135241068d68b0d941b51a2d26d35d15d74d12c438920411970e49a41855d2540c43d35c95d1394,
   0xce11455045135210375734e6dc55855890e6dd4d05099d461c60d0c355a35044b65340d7d538f5d048b80354b,
   0x4535522d14834112c44955d65083964d240d49c7176ce45668f5896847605955d13833cd2d05da4da44e251691,
   0x3d36914163035d225265c6562d035f2525d45d349645651545648f64930d3cc4952d624d5584094cb0cb6525d0,
   0x4163da4842446505d16c43d94d255771630b5d14155d24cb51641924b10c21455a2502d05c48c940f8cb110504,
   0x3cc21849a49341a5c351521048411e1100c31194935cd3dc6967544935135c824b4525562d44553d311454f412,
   0x2d45dd81058f80f6955973cd35759c3d24c94d33dc68f3d251310f68b24825259340b5524cf71d2540d26537d9,
   0xd],
  -- 24 numerals
  [0x1564da6a16d762725634a1ce48e1537d41d348a51b3875123d748e80d2566c529340c6531cd2a33555ce4112c4,
   0x28e61b24e4d435868a1473858874d039b15015315261334e5154d82921503db95339535235a2893876c560a489,
   0x4db54724581b3db4c96c759864a40768a3931df6d32476963e285434c3473922975095aa3e414f14e1d375b407,
   0x55d8131476d730939251765c55b4955d66d258e1455092596cf3d94d491b2587d69cd6d36d43856d84df55b317,
   0x9d374f5d43244cf56231434e5d660c91e3d08998d23935d044a24764a5d62872a378f2895c758969f4ca65465d,
   0x6a36d45564076d36543db81a40535139155d64d5953596d61d53515194d13126dd69f64c6da59651131355044e,
   0x41d5137936134d471148f4d85df79445f7077de30f51f58a49780e49369495a39054579e617320493551295524,
   0x75d3917055546a139d3203516141555d634c41e5136955914161ce45858d85a4479137854cf34c29222331455c,
   0x39642144c29964c38f24829061440f1cd29315214a4135566453a03d244f5991ce65a78c40c419310396159596,
   0x71528d1db56490f6528d75536a035b35e64a3cd40f81689158e3cc55415c9147e415439141035c41879064c645,
   0xa563de81d15938f1cf39c55e54551e60e3ce38e79a4d214741455639059430f59a65a64a4954177115164d0460,
   0x35939751b75424975d1ca64d1471545913d070c98d3de49834e75834f39f5e379f29294d84c611a1859945d358,
   0x39980970755a6c955c54765e1607185975c575b6572917526d939744752045c24e89c54e24e44a5545cd7d7494,
   0x14f2915d754f45538d6e14d569538a15715f5557ca3453894516d775c6dd3513d224544f39b351a19257755287,
   0x54558a1542943ac4ca5094544545d129915138d44d34914e5d35ca7113606916cd35b3851d43cea055c5551449,
   0x25154549968d40a79b65714a45c61b51495961979564e70d3a26134a16de24d74e15d61d4db6c55541cc8168ea,
   0x24d3082577da2474cf5494573cd70d4556922605577114d63895975995915896542454585515dc4e661748a753,
   0x31f3cd4ca5d624a74f28c5498186daa054d54a24d765658d4d214721a1d34976565d34525d314d24d45229531c,
   0x15e5895945164967185952635945ca59969934e34969960e55449414721335a28a5176dd74a71744f81a2554d2,
   0x5575dd31a59971b38a4535133454d358d14d7967e06922591533ce4586926224d329435a6a271e7d952839351c,
   0x1c568f59a45359d69c4c51d85da4cf1ce5d63c934d34f5c925d1d534f45349a44914a55729174d55359125d24c,
   0x29b46a79669624d35a511a0989a62278a58c4967d73ea8566a225395a6ce29359880d3db6962a46c96655dd51c,
   0x59168a6974d271a7dc82279f50c3284d751481c7961c969f80e6923546a055761344a31871638959388d75a69b,
   0x69981231a49849a71585a71131451c39f],
  -- 14 numerals
  [0x90f5e12967a448a2e97217d43a489a4ce58e42051a29b3a6aa188e5e56942d114f85449971b71515129634c247,
   0x59b70f71051955970e50d11ea9015744e5c41208104da45114d48f3d484b6585d15244da4912d650e2cb4522e5,
   0x51348f2ce5cf4d37194913053573d63d16613da2a86a351c89a3938dd81811161a40461738d3933e139354b60d,
   0x3d939538c49a71a39765439531775c71f8126442854dc44f54c28a5d81042cf7154ca55311a49e55029081c68a,
   0x71595c31479748e59045858f30b4d27153cc9213ca45932044a48e4d04644d74964e031648451838c31480b317,
   0x3542d045844b34c3565d760d58e6db1535d948929331e82429255351a75c69da207626ce60c75465e5d15d551b,
   0x9124d288544d3db15a7d65cc4513a045631730c61682248b5d235245b5134094975173cb49541750b30d64f2d1,
   0x4cb34935924b4da44d4893d7a995532516534193591493144974cd5cf3574456d048b5d43236d115545b5cd157,
   0x76064a39858479244466115c85570a14c50a64a30e4cb25345030f4ce4d048534b8db4112ce3565974cf48b3d6,
   0x5d17d84cf45058e51315b5953cc3515178ab6a07ce34c39011d91881a8a038f71a1113d064d39c75139a35f58c,
   0x38554f2927946852cc10d52469b5c570e4cd38c61729c51a49271455a4d238d69834e41128d35450c3d550d616,
   0x59458e34c4562d06573ce48a88e59d39461960a35b3ce2942ce1544935135a85137c528e79a48d79669b41e6e3,
   0x2cc6d354d4994d62a449334e4ce2c54cd39349950f29258d39011659938b49358e5904d54c538d491394491416,
   0x7e059129331e5e04d571a60535a2925d46cb2d26113c5513],
  -- 15 numerals
  [0x5545923592452948903d395d61664e8191c94498df81024d34551659924784745175945925d6131c955428430b,
   0x54f3905989562583594d949f44749545a34e3d43583d074e38e55f6df51059225624540d4121db5a37534975d3,
   0x4ce51675664d7117d850f91939425265651d41638d3d85197924c539451924769c6de1df3d544a10d4d934f647,
   0x48a4d428a4cd39629b1544912491de29634e64950751629889145348561c6dd29548a1d41513d04dd647610592,
   0x25964e34c4041d05913d11cf6525473143937973923197629205905d53444492913574491c57921d94d21cd396,
   0x39d25526058f54d55132464f78c49438f2513ce7474998591d234925155035c5153977564987953243d480f455,
   0x34c75d31454e3a075015130c38759531d65358d41225d6136995493967562501c72527541d134475a65d1cf493,
   0x25680a64d3c75971cc75a65d3d65051103d968c4537ce25a6d551c38c31478e4cf6515926155a876159674f50e,
   0x31425224951652025d1d434554f2894479e059a4ce51265a59430e5da38d2937a68185d159a75e4a231a58e1cf,
   0x61635e50f45528438944e54525944714e25261775249c4c71ce1e051e48e28534744c285245356b1a6511e124d,
   0x3d915759269555251d59c8194cf24a3ca35754944934a4843da48c24a3c934a5123cc4971d33456173cf354149,
   0x72232575d24a3ce7dd35425461a5841d85594cd5dc59215f1454913cc25881a1161d235e3dc55a64d14d81d5a3,
   0x39638544d2936cf35579359b31439981a65265874a3de74a3999cf74a72069e35332251a5646ca61169f7cd50d,
   0x75849a11864f28d71339339878f3446d525d48d54551228c3d645c45469c51944a29159435761158a36855c29d,
   0x4d455158a8605544d55ca5cd61c4564976e089e6cc7964cc8a090e58d62134538d39974455245a7046cd5d9],
  -- 20 numerals
  [0x31648969f7502591d051044f4d468c4ce91944f55624c1d130d3495116d461d5161d339264e3d351434c2852c4,
   0x51a39028744f5c774f4c934c394610a1d41488755968d5076575ce41b66529e42051759044c7c91c9592613294,
   0x41139c44c3d764768f6504478495056963926df65d95b1ce34c24f82138c81754740950e24d44a4926d7462613,
   0x4975135093d724c45068f44d81550d48e15671654d54d3494071cd51d65039148e4d440c39045440d31b79c5d9,
   0x6d14d42494dc2508181da48d45b31a54f5579cc68a51a5d530751259459430d1da75245534c1d46d21cc489651,
   0x79f6c75d71d13cc4073c724d68e60d34e54d6134cd40751f31725748739d65b5cd3cf34e51725478d3cc41f622,
   0x6471523524115c75da1da28d55b92868d3d251344e24740e3db69a5d33903125d15ce3895d33d748e5d135224e,
   0x39c5875ca70f24c36381771768744f49c5501493d648f5d758929560d2891cc4925505502893cc28975c1c9495,
   0x38e51169c60715465539549b6998ce49629660e61924e65414f64c41d2855567557495893871ca15449614551c,
   0x29238559225d3513d08072473db15161434775774c28774e1c769c81c5cf55274d25568a3cc5c93d2510592294,
   0x64728d29f3535052da6875d865c60a51560e69d65215434a3932935d648a74551539658b50e29924960b145594,
   0x4d835969645545c28a35449331a39a8e44d275949e30535d54e49939950a24e49569238d44e6ce35455390a252,
   0x3122d132070d45454e34e90e59565b69c71925151439135a70b4897092d25117571d459c50725939a5511d8694,
   0x7144947855496dc3985c954548c59d3496165d851335428a7095dc39b51851748914b44970e4e2328309715509,
   0x65230d74c25b2953df76014c34a1491555d928555b15149b65a38b1de71568d8ca99d3967603a32ca39458e817,
   0x5d34524df79882980e71a54a4ce81a14d35b5cc6db58d28929948a24f8d52496935575974d358f69324a393311,
   0x1c94d229c54e34560c5453cb28a2555892d84d53cb3c928e3453dc4cb3d148560f3c54d53575935d636014e28e,
   0xb1c48b31d58a9dd51b7db56529859548b5ce4c779c5455d825675d2d86895c761d79d4cb2953c514f74955314b,
   0x6db2d559a79160a2ca6d859869514948e65745558b64564e4c555668758b29b2d66d35db6d914a4455454cc50e,
   0x589],
  -- 10 numerals
  [0x4d32d96dd94e3911cb3910cc5d558e65a58b1c74214a02dd7153d86d15834e27c32d60c95995875894cf294344,
   0x4036d150c28e59149a39b39830a26245f4932872e35962db4e04913c95ca1ce54b2c954e1cb6433cb1ce0d20da,
   0x3095c35598935d880f65424b4c925881f4d46db6526122cc6904946604543cf24b5d430729442274b4d0750616,
   0x3cb1c994b3a359b7cb25750c24f5098936103d950360f2d55a86a362069a44b49979d65184c6dc65461771f458,
   0x25465265450c3d82c964b4db5de1d640d0c939b5dc79f6186c981f65759489659d6137d95ce71639345d2d760e,
   0x59339b4df2571d438f4d871860b25742275e39339879b41638b30a4d91cc25a8473174993916cc1db4475937d3,
   0x64c4d264f7d36cf68c38e81838b4d32d691051144765b5182d13873093124536d02515964cf4c751630724f687,
   0x4d350c3532da4ce4972d951b3964945614646926d46cd6974903c91de4527584502916121d04574d07d031459d,
   0x60c41a2c98a07d34ca3d494a7916ce5db2da41635758b6504ca4d479745f4a37963d18d679a3962db4df4d250c,
   0x4df4914964d8ad34a645368c61331268e6512503137e03144142927dd6515572cf74e41d45242049864e6da],
  -- 15 numerals
  [0x6d826535152145850e1d87122573073034cd68e2530c949960944365a94935651b0e144d5c939984344d50b10f,
   0x5d780d6cd5cc80e5c349b34a30a1cd0d555a6d94db3983435c775b71034d1dba113076dc54359430c51361f3a1,
   0x3530c34c78d74d739c69d38b0cd31734330745029632365358c0d729b0c995769840d2dc85b44c70b94b79129f,
   0x35874d4130d158335144d39a6134536c760e45f8158585c73435180d234b69810b1d730c6c74cb3199550e1787,
   0x1c43432d11dd0d96da60944d10d3512d774d4507124de6d15c345345e61e5186c70de4585c735aa228c7250549,
   0x54b28b45358b11a59535758365534a34e24d2c971735c49338449a5564604102d33952d924965045b35970a1cc,
   0x7493553604535044897512c939d55880744d1dc0d72cb0dd1c371d4e138d5542984905532d53834c42514185cd,
   0x61734a2c724d5873505434590dd4985c95567d354324b4d954d39d84d2d335534b0d024e7e67e274381085c912,
   0x1c770928735149378d4ce0c95c94c471979374d4d24cd60e7495d1a9d35d45a1dc0c94d67072583875d149d496,
   0x31060d55648ba581cc2d46076110d04ca72770775439d7094dc72048740b8d47c73447c425969239d11b6432d6,
   0x3911044d73504d959366075979971d65a1090cb31535675552474d48974b6510df70e71b45d1d434b4071e67da,
   0x2d124b1193590d975559b5dc48935d0dd70735569434745b0d344d1c779a6d139491c71565a40e79481e347893,
   0x9872dfa9889d0d05514562d54d41d135b75c6d170d4c36d76163504975cd8212521045dc44d1d680b5c344734e,
   0x51910b3947c44d54c451979f8586d925165d9894575d86d526089d7916525d30d62d840d2dd2d135b4524041d3,
   0x65425f0c365b7144dd2dd40b719684],
  -- 6 numerals
  [0x78c4c345665755a85755258b55324780a81871755040931459548731140a59330325568f7d541f64c6433cb34e,
   0x3513d93092533554d64d124c0cb28c2c34092cf25948f1dc3d30cc44c5da5d54504cb3035914d04513095d63d0,
   0x28d1d96df4cd0cd6492913555973d24514cd3cc3476984d55ca3cd41455061b1d250d4cc7cf0c91d41d34115e0,
   0x2d05182d769524730a48c2e97134d95d91d040b6574a81c735340f69b4934246cb3094974da5db69b31385a1cf,
   0x50d30d29d1cc3d35520d74cf54c4895cf0d235040d65264b40b4875575596494922593cf3e46492d03cd6d9715,
   0x1d7593cd4d53d47d35d549c5435094cb0cf],
  -- 8 numerals
  [0x3e039c9195091cb24b42325681a1d52dc75550b1c338975c3df40e4d15d339d5d32544891ce96089c5c32cd30a,
   0xd67d685f1c92da6a12d53926121de1d349644748b25d0d564f51e6d960944e68e51980760e3c748f513598398,
   0x4d71ce24f6170cf56538b2d13d73d33cb38d4091df5510de5d97916503972d834d1c989a6036d738e8476dd351,
   0x3956d92d388b3a06d31d45502d95d561540b58b0c92545942c74433cd49a6d73d064e75a4494612625536101dd,
   0x2dd0e81d94d934d61645e6d754b1d77542cd40f78955b8226cf45d5174dc3de3e03dd4473d70c36576547581d5,
   0x5534c96c75e24c94c33962df4ce58c1d765e4da45955b61825765439c6d95c755738d2d030934c1d058b1cc4d5,
   0x44e3d445361f65b59f75174f44f74c1c34d95d639d60e39f60c3894566574ce34d7d30dd6d48d77dd6cc3d444d,
   0x50f34e39945360e30e3595ce4584d644e],
  -- 10 numerals
  [0x58950425549335c58c4973cc50c81750410f7d740f3cd30e4933574cc58c5d37133d45d641a24b58458d311288,
   0x64f4c92e04db25151b25854d71f7135587123d74037dc54b6153d851338e2cb5c951134c45d39440459674e594,
   0x71058c6dc2d23d38987195e89236e341f55d6c97d335410339b6144cc4d47133148cb59c54f5c945048e4d5396,
   0x24f2505515093dd3d758e71a3cb4d53197d840985f4d161169f71338f6d544c36071c25325f7127136954cb3d6,
   0x38f58940459551c49a6983137da3cb70e2443953895a941760c3536495cb65369d54f4d12d27d95d450f68d44f,
   0x54c4ca49128945271a4d224d2502cc71235448d5c94d640e1241112d838f38912a48b3e255d58b6582dc466614,
   0x5d12504c940d3d440b5990d42d345225355740c44b29751424f48d4d435654d2555d724390f89b35340e48c4cd,
   0x3cd31060d48c59224b2e17db61875934f7d14d64e04d455340d69588b55579a6d764b64e3495ce3553d20d9453,
   0x51c50e80a28f3cc35258a61165459a55d7e035139881331738c2914cc2575a67545d928c5095926945145c9396,
   0x31c6c93d96163923956d234e6d050a48a2573de48e11365d60a40931d54f595],
  -- 11 numerals
  [0x7935905153d661b55a4db45896358940e65f5507e024b59042171b4252172d850c64955271c55464f45240a343,
   0x40e89e81931730465965740e48f2204d85de7163964d24523d37dd30e6d85965d86c93d210b2d061a75e5d43dc,
   0x4586cf3d94d041158e2c455359021765a4124d65d074e6565d54d268a5608d128c9a330a50830855521959979b,
   0x21685e3d18e09199a571f2123997dc4255df89d4d789921069d7d375245e5d981d48e6d730969652481744f756,
   0x38f31c7d081e85e7193c851265669482281b65d5ce60a4da70e89b75a5ce6d580868864a5d521358f5146cf9a6,
   0x6564d43cb64c64a5ca3d05582583d559429a6492d32cb20b40825138c65b7165d931b5194484dd5dd51579374f,
   0x4512c975650f3845446a529729551a2987086527a85ca41210b44c35164859828f25075140a4d831525968f452,
   0x6ca25665231981549611038f2da4dc4d82d141465845a2967483d038f6963da29d51c7552da4085ca3dc589393,
   0x29538955069221440f2136933ce41e4cf45258a4503d14c840e48459d81f4d964472048a6444d93155193a3651,
   0x49258e10b5954d160f3983d27cb21644e58c78e78f55c2d369145810940a2532443ce55b25b6a1414619516396,
   0x55026d4935884d32cf8547cb4913d22593d04963c840c3884441116093d6],
  -- 10 numerals
  [0x22421441724b61755c30c5565045a178f4d02167965c92963d540d6885842162093c435229a2d62cb58c4d1383,
   0x2cd44824c20d34464a58d5096966141136127935552883c458d5975d34217166985da21375358934a2d264a5da,
   0x25764d40450441a3c834c35530928c51341096428b3125236d08e48182942c82c47515c93d855035e30444b653,
   0x7d33cb3cb70a48d5df20d54835c5d33cc45410a51928f2528907d041768f3082d079d6493ca3576595cd5dd357,
   0x7954937dc30b6cf5d47094655575da3146148914cd4116c869d24b25a4c848b5de6d920d41c25f44b7da68c4d5,
   0x51559151c5172cc74d61e6cf7c931155e21959f2da75271322058a7df8265de24c468451788518516518454619,
   0x5a03d02c92dc5d63125d641171355954f8dc58c5085cd2da21d5102d93d149321944f35159030e28448b2d5551,
   0x4d025555434f5514123952d25dc61c49360f4d171f60c24d44f75c25458f6cc4083d18166da41275951d74f254,
   0x5945cd45261b21b64f45159b60f38b25c65264f61949940b6185543943d155b6195105d648f51531934964d3d2,
   0x59f4d72d645444f48b5104dd45048e34b45a35055161631b65270f5c82cc3482c868f34b2d964e3d4316354],
  -- 11 numerals
  [0x6432d66564c358b2032d44961d469431220b3112992d220761928b51a4d42d149020964769931464749420434f,
   0xd24162175565ca795257516a158160ca21545a5c92944d08df21165a0c449041f51c45276c793ad0109594111,
   0x40311d1c9112448b041104478887c429664345d2094445d66934910d931046641155465760c49949046c6c90cc,
   0x2228605870c91d080d30d11259c5c830d5c90d36561c441959325354d4504c33142cc1152947c311d657213216,
   0x81829359b1071165c9404204913a1279720956c46221d2550d4452753a0a2641072094d340a44c21270d1e0653,
   0x4c941720a5982071078a12090c336280831888770d20321a2894482431166225d35548085962164c81190c8253,
   0x7de1165c74935082121cd64330b7d354a4582916080c744911a0d16187a02160c934d10820844449c1d3491817,
   0x25f5d829021e45a54920369a4847146c912275e7105094cc2530dc4914c91c835058a5048c751959971225350d,
   0x30c5604cc5836446880d20d04e454384710a20a8894c86891075496440d758345448365a65a28344928c25754a,
   0x6044081d22480c724a3494547d45ca59335228a51428875944a1db4932157112473599070d124761b50880958a,
   0x25731e29621521379324855451021c49420d56355428312078848a],
  -- 11 numerals
  [0x10f4d225d11f4102532173d98db5d24cf6d75544613c424f4604033d910f4db0cd6531204107552504c321828b,
   0x4d120d49c1255c86133d142c5cf44f34d3d535b5c95045837c96d371b1d174f4d41113e072c7d37903df50f0d0,
   0x55952851e4d265a58920d3103514522501c94c81107d43564c935c4a065859025d6d120d61351641d4dd3d8584,
   0x7c741c0d121021d4540c83d34103d54e240829625328451c58a3d345528929d5c759211c0d64131077563c3251,
   0x21d5a251410a6904d549929334f4037cd4c43c74047dc41f1cf4cd5990cd0ec1d375551521010a2544d0255793,
   0x54c2156955d25c40d535c31a61c4c43d90c72484504994c74d62156541d31105d44d169c35574780474a666754,
   0x55628874a25a79d6543c311469875e0c45971c95953c830748d60c31351734c11695760c29411554c594257355,
   0x81f2473084925d31155174dc4d21cd4c328c0c70d229244a1c45d428d5c9a1734755778a3042165092883d63ca,
   0x5577536878873d36c43533c445d34f0de4d46c76ec4c460828c5931d360d24d61181162431351348944d5545c7,
   0x62435d70a12778d6ca4cd3d836770480c5073e45049176080d16095c929149a35875281c10f61d7481035d2204,
   0x91e951844944710829e44311a3445d84d72491c345828474d7150e0],
  -- 6 numerals
  [0x2079126c82481094872515092546030d57434d275b1097571151130d894469540945f1c83115a46c91c41c828b,
   0xd74d33100d51cc59148a5d431741d4154d032031d51568c31a6954cc79528c5511122073474914890c9411709,
   0xcf59e74d40a3213dd35d41575140750c78c34d5563114925254904164905d4451b238595d67dd5040cc0d24cc,
   0x44f40a2894521085ab0d760d45d30855476375a1e441541141c3d054c5d73104d05545cc55c80a5d471181430d,
   0x20845270f5c82150ca4e030454d34432030844f1c74472130cd45544829258925024321a49111a5cf1041db691,
   0x1f3605c84d644d21225eae37243103164986136955d64482871cc2984602122504956922096c83082a061840c],
  -- 17 numerals
  [0x6156114896493d259224f49435858b68d59971d2df3d15da5082182175cb59274d69c81961571b6cc6562440ca,
   0x6dd5d63d25cd76291035c4a579a7a530d75134c7117a252448d9df72025d58d35779d2482d941140b45368f496,
   0x61a75260f6628107a53dd25d6947903c479a64f1114903c425a5d675140f89d6cf35d6d111a49a7525d63d475e,
   0x59125278d41450925540c4c455a79f45d40f1e340c80f49235251075751261c4098a04d810730978935c75a752,
   0x91d79a1d325ab200c934d5902cc11140d90d3c846069645635d45645d59671a40968f25d59140f3d15cc34d597,
   0x71a2cd4583cb68f4223491d579e5544df2512d37d280d8e079445135c8606e265a0c875e21c6544d63587a2918,
   0x6dc2dfa1f65a2485284836dd44b4d02475144d958724d3165593474d40c73470da68f59025449858f6505540cb,
   0x84d60d2dd45969525449a55751835a6c754d61968b7e07cb5d87e435471480b64335a24848b6874da0d5595690,
   0x4cb6192da3533d830965264c5d43cc30f31369149d6502c72173d134361b65a6d145755b44335369960b4d65cd,
   0x4c750f6d141b7895cf7c93d045d6116c324f68b8911c35541c93d350f75a0d035355a30b6cd3516905df5105d3,
   0x74d5577e07d749158860941e5877531cf11430b1dc3dd4546cf61d4db68944c6591db452696b074c790b6d8649,
   0x3c92476d764d45d60f7536083e16517031c44c448f59810d4876d111c81c6173d821b0cf9476107154d181b71f,
   0x5102094596cf0c94cf45c4434cd4d44df64d60834f2563dd35961a70f65e4436936033df1d35161081cd0db5d0,
   0x1c441f5913d30d44517035d841845c4926a27504dc8138d46d431c4526993d121a623a618194d495a58824d6d3,
   0x55759e7107d489a79f61e4113dc80f6895d610f8a18235107dd6194257174104c849870f59248f7564903d24c8,
   0x25c61e71d61e60c2574176085130d035231c2112513da2086925195906876c95035544486d879d75521d48921a,
   0x93191d04047102443470c948c35071065075876161611241058441b6a190c7922482117044dd45e1d4517],
  -- 14 numerals
  [0x4915ce20e45230b34d5d14cc6193175a470e3105165d440f5cf7de3da65c61358c21038848864844d4d630b1c9,
   0xb0f81639941a41764c60e3d12d0a0f0c43886900cf5577134e03c838c58f0de48c7532040d92246c35d581644b,
   0x48f5dd6117593d34d33da4157d14d820d39f5163196ce45d6167514d85a080b45c6d57db5dd58b30810430e448,
   0x79111359c3ce34b40e60c3cd41a3266a061130e60c5183034522e03957d221c56739c48e45b3510d83524576d6,
   0x3d61c84c33d35872075474971c34d639c4d29de40f7da59148341db2074f1d44134913d44626976485d27970e0,
   0x70e7031d90cf21050338f4561113cf89812851651141c2124535d14c76975834cf2123de71b5d63c4417592583,
   0x3878166484943e05575ce35589954448f5991d71d73cd0d939065b5d538f6cd5db34e4165116de39c6a40d141e,
   0x49a3076435973d03849045cd1032185481035a33846438201d04d24993963c84871030ce3441c73972196440ce,
   0x3c720e3070d46970cf69738d31d6940d234c5c335a31a44c34f4103e044d40f5cf48d41a4cd5c80d03cd3c8594,
   0xc73cd31e0d320b2cd4532146885516163923975d438f0d738c58734f5cd38e0cc4974506511c730d1d738c1c3,
   0x6566c83cd0d37114953d634c40748f3486554d87cd44f45a4d24cb3dc4553504117d53538d11cf51342054d519,
   0x58d0d30cb5d341630849460d4532cf7d13484931117160cd4eca245d60d43434d17cd6c791b11630f11330b9d7,
   0x6484960d221d4910c774c0d23554dd4935cd36074375335b0cc10b6dd6d10c334b82c5cc4035511cc5901cf364,
   0x1c30cf3032086d24503431c36c844f],
  -- 12 numerals
  [0x3c74572d73d110e4132c92cb6106994942cb3dc68771e55661c25a4195d250945155148b11c449a0945740e20d,
   0x3d841350b5cf4505042574512c76835da55741460f7174cb45c85560339270f4d14134872da3c751945d503489,
   0x3034a63ce40e0c724f5d37d339624e5cf3073943103d24523941d810e5956ce3d479a48725381340e3cb20f5d5,
   0x1074931cb40f74f1153e13945124d249348f4535d210e4933873d03075d97473d348739a6ce5073d14193932c9,
   0x48c1100d264448c30b30458e1c858738e4df5162d23d64cf3942d775324b1d351339424f30b6576974d24ce4cb,
   0x5112573986a148e1d124b54c4dc6113936cf7d241668e3cf55639461241f6d33982c96532c348c5924173d95d4,
   0x5c341138911010970b2504cb24424f4503871d23d16891d03df3913874175980c75177d32d324444f3875d14e1,
   0x55154f89745d59855a60e71d40e6184983903d33072db4dc2d025330b74e3110d44c441565a40f79a11c417695,
   0x64741c41c6504475222d666258b8176920d875a68e6982c73092042ce2ce89694e40f46824f45a4d01db399398,
   0x30c3c724e49c31a7124d96192e26552d650338c75368c38b1ce55d4475900c745a44348375a4c369e74c3d52d3,
   0x5191d34c32ce68c71d55d2c371c1d970f4503e471c90c74e50780b64f39524740311665a2da44724f4502cf444,
   0x7541d141350938f2534d044e1da1c938b0dd2d0551],
  -- 10 numerals
  [0x48d6d76cc44e4cc3593de64c61951839260f45549a5d975141c6cd44c48964f71b1d175c82260f3985542c3204,
   0x54731964f41e2d02d124b41164364b30e48f1c72d560f5d36516193cb3c92d738f4531d430d6191cf25564f310,
   0x5d35225543074154434135975591cb54c4d03d64d08190cf4d13d138d44935e74739e60b0cc2530ce1c33a02cf,
   0x25834e5cf7d67d22cc6d74544074092e260f1c94174183c938b1d68cc1d644e3d81de247411599555462614820,
   0x1c361d4931c70de5c938f9435097171c350f21140b2571dc6d57dc51839c5ce6573d31c97d74d451c4c930e35d,
   0x5493dd5481d35081d93c335e5ce4c92142575032d235d50b4d449980f2134d75153c35d80db724817513217489,
   0x2d255655c68c2d63591cc3492d60d65913433070c93ce6c73d44cf3838d455558b5953d65473192d65dc1d550e,
   0x3197550cd34b3072cf2c745348d61958c0c33173154cb6174da1d265a4510d650c2595912135914c94c96494c3,
   0x2074d220b5555cb3da4d548d6dd4d83984d52095562e258d1d824855558d0d369a4d148f5d344934320b50c70d,
   0xc34d14ce20e5d65ce3831ce3ce7d352b60775ba0838e]]

/-- The certificate of the search above the chunks: branching numbers, and `0, k` at the
root of chunk `k`. -/
private def rootCert : List ℕ :=
  [0x5405004c029201101000f00e3803403001cb00a0090080081470060050081000c30020010050001c6]

/-! ### Upper bound -/

/-- Each chunk of the search is checked by its own kernel computation. -/
private def checkChunk (k : ℕ) : Option (List ℕ) :=
  checkState [] (stateOf (chunkMasks.getD k [])) (decode (chunkCerts.getD k []))

private theorem chunk_ok_0 : (checkChunk 0).isSome = true := by decide +kernel

private theorem chunk_ok_1 : (checkChunk 1).isSome = true := by decide +kernel

private theorem chunk_ok_2 : (checkChunk 2).isSome = true := by decide +kernel

private theorem chunk_ok_3 : (checkChunk 3).isSome = true := by decide +kernel

private theorem chunk_ok_4 : (checkChunk 4).isSome = true := by decide +kernel

private theorem chunk_ok_5 : (checkChunk 5).isSome = true := by decide +kernel

private theorem chunk_ok_6 : (checkChunk 6).isSome = true := by decide +kernel

private theorem chunk_ok_7 : (checkChunk 7).isSome = true := by decide +kernel

private theorem chunk_ok_8 : (checkChunk 8).isSome = true := by decide +kernel

private theorem chunk_ok_9 : (checkChunk 9).isSome = true := by decide +kernel

private theorem chunk_ok_10 : (checkChunk 10).isSome = true := by decide +kernel

private theorem chunk_ok_11 : (checkChunk 11).isSome = true := by decide +kernel

private theorem chunk_ok_12 : (checkChunk 12).isSome = true := by decide +kernel

private theorem chunk_ok_13 : (checkChunk 13).isSome = true := by decide +kernel

private theorem chunk_ok_14 : (checkChunk 14).isSome = true := by decide +kernel

private theorem chunk_ok_15 : (checkChunk 15).isSome = true := by decide +kernel

private theorem chunk_ok_16 : (checkChunk 16).isSome = true := by decide +kernel

private theorem chunk_ok_17 : (checkChunk 17).isSome = true := by decide +kernel

private theorem chunk_ok_18 : (checkChunk 18).isSome = true := by decide +kernel

private theorem chunk_ok_19 : (checkChunk 19).isSome = true := by decide +kernel

private theorem chunk_ok_20 : (checkChunk 20).isSome = true := by decide +kernel

private theorem chunk_ok_21 : (checkChunk 21).isSome = true := by decide +kernel

private theorem chunks_proven : ∀ s ∈ chunkMasks, ProvenL (stateOf s) := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
  have hc : (checkChunk k).isSome = true := by
    have hk' : k < 22 := by simpa [chunkMasks] using hk
    interval_cases k
    exacts [chunk_ok_0, chunk_ok_1, chunk_ok_2, chunk_ok_3, chunk_ok_4, chunk_ok_5, chunk_ok_6,
          chunk_ok_7, chunk_ok_8, chunk_ok_9, chunk_ok_10, chunk_ok_11, chunk_ok_12,
          chunk_ok_13, chunk_ok_14, chunk_ok_15, chunk_ok_16, chunk_ok_17, chunk_ok_18,
          chunk_ok_19, chunk_ok_20, chunk_ok_21]
  have := checkState_sound (lem := []) (by simp) hc
  rwa [List.getD_eq_getElem _ _ hk] at this

/-- The search from the normalised state succeeds. -/
private theorem root_ok : (checkState chunkMasks (stateOf [2, 4, 0, 0]) (decode rootCert)).isSome =
    true := by
  decide +kernel

/-- Every colouring with `c 1 = 0` and `c 2 = 1` has a monochromatic solution in `[1, 45]`. -/
private theorem mono_of_normal {c : ℕ → Fin 4} (h1 : c 1 = 0) (h2 : c 2 = 1) : Mono c := by
  have hP := checkState_sound chunks_proven root_ok
  have hs : stateOf [2, 4, 0, 0] =
      [Nat.lor 0 (Nat.shiftLeft 1 1), Nat.lor 0 (Nat.shiftLeft 1 (64 - 1)),
        newF 0 (Nat.lor 0 (Nat.shiftLeft 1 1)) (Nat.lor 0 (Nat.shiftLeft 1 (64 - 1))) 1,
        Nat.lor 0 (Nat.shiftLeft 1 2), Nat.lor 0 (Nat.shiftLeft 1 (64 - 2)),
        newF 0 (Nat.lor 0 (Nat.shiftLeft 1 2)) (Nat.lor 0 (Nat.shiftLeft 1 (64 - 2))) 2,
        0, 0, 0, 0, 0, 0] := by
    decide +kernel
  exact hP _ _ _ _ _ _ _ _ _ _ _ _ hs c ((ClassInv.empty c 0).ins (by omega) (by omega) h1)
    ((ClassInv.empty c 1).ins (by omega) (by omega) h2) (ClassInv.empty c 2) (ClassInv.empty c 3)

/-- Every colouring of the natural numbers with four colours has a monochromatic Schur triple in
`[1, 45]`. -/
private theorem schurForces_four_45 : schurForces 4 45 := by
  intro c
  by_cases h12 : c 1 = c 2
  · exact ⟨1, by simp, 1, by simp, 2, by simp, rfl, rfl, h12⟩
  -- move the colour of `1` to `0`, then the colour of `2` to `1`
  let e₁ : Fin 4 ≃ Fin 4 := Equiv.swap (c 1) 0
  have he₁ : e₁ (c 2) ≠ 0 := by
    intro h
    exact h12 (e₁.injective (h.trans (Equiv.swap_apply_left (c 1) 0).symm)).symm
  let e₂ : Fin 4 ≃ Fin 4 := Equiv.swap (e₁ (c 2)) 1
  refine Mono.of_perm e₁ (Mono.of_perm e₂ (mono_of_normal ?_ ?_))
  · show e₂ (e₁ (c 1)) = 0
    rw [show e₁ (c 1) = 0 from Equiv.swap_apply_left _ _]
    exact Equiv.swap_apply_of_ne_of_ne he₁.symm (by decide)
  · exact Equiv.swap_apply_left _ _

/-- Forcing a monochromatic Schur triple is monotone in the range. -/
private theorem schurForces_mono_four {k N M : ℕ} (h : schurForces k N) (hNM : N ≤ M) :
    schurForces k M := by
  intro c
  obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ := h c
  have hsub : Icc 1 N ⊆ Icc 1 M := Icc_subset_Icc_right hNM
  exact ⟨x, hsub hx, y, hsub hy, z, hsub hz, hxyz⟩

/-- **The fourth Schur number.** The Schur number $S(4)$ equals $44$.

Source: S. W. Golomb and L. D. Baumert, *Backtrack programming*, J. ACM 12
(1965), 516–524; OEIS A045652; listed in SqueezeBench
`SqueezeBench/Problems/Schur/README.md`. -/
theorem schurNumber_four : schurNumber 4 = 44 := by
  have hinf : sInf {N | schurForces 4 N} = 44 + 1 :=
    (Nat.sInf_upward_closed_eq_succ_iff (fun _ _ hNM h => schurForces_mono_four h hNM) 44).2
      ⟨schurForces_four_45, not_schurForces_four_44⟩
  simp [schurNumber, hinf]

end MathlibExt.Combinatorics.SchurNumbersWanted
