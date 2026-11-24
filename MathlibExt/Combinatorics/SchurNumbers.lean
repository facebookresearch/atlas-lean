/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`SqueezeBench/Problems/Schur/Def.lean` and `SqueezeBench/Problems/Schur/README.md`
(leansolving/SqueezeBench), at commit e2e19eef093a77882da57f348def029533ec2d5e: the definitions
`schurForces` and `schurNumber` (SqueezeBench's `Forces` and `f`) and the statements of
`schurNumber_two`, `schurNumber_three` and `le_schurNumber_six` (from the README's "Known values"
table), with their docstrings from `WantedExt/Combinatorics/SchurNumbersWanted.lean`.
Copyright the SqueezeBench contributors.
Authors: P. Manrique, H. Xia, S. Szeider.
Licensed under the Apache License, Version 2.0 (the "License"); you may not use these portions
except in compliance with the License. You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License
is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
or implied. See the License for the specific language governing permissions and limitations under
the License. SqueezeBench ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). Changes made: renamed `Forces`/`f` to
`schurForces`/`schurNumber`, inlined `nMin = 1`, dropped the helper lemmas, and turned the README
values, which SqueezeBench marks as reporting only, into Batteries `theorem_wanted` declarations.
Later change (ATLAS, 2026): the statements were proved, and the two definitions and the statements
moved from `WantedExt/Combinatorics/SchurNumbersWanted.lean` to this `MathlibExt` module with
unchanged names, statements and docstrings.

ATLAS contributed the proofs, their private auxiliary definitions and lemmas, and the module
documentation.
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Interval.Finset.Nat
import MathlibExt.Combinatorics.SchurRamsey

/-!
# Schur numbers

For natural numbers `k` and `N`, `schurForces k N` says that every colouring of the natural
numbers with `k` colours has a monochromatic solution of `x + y = z` with `x, y, z ∈ [1, N]`, and
`schurNumber k` is the Schur number `S(k)`, one less than the least such `N` (and `0` for
`k = 0`). This file proves `S(2) = 4` and `S(3) = 13` by finite checks. For three colours, it
exhibits a sum-free partition of `[1, 13]` and checks that no sum-free prefix extends to length 14.
It also proves the lower bound `536 ≤ S(6)` due to Fredricksen and Sweet (see
`le_schurNumber_six`).

## Proof of the lower bound for six colours

By Schur's theorem (`MetaMathlibExt.schur_ramsey`) some `N` forces a monochromatic solution in
six colours, so the infimum in `schurNumber 6` is attained. Forcing is monotone in `N`, so it
suffices to exhibit one colouring of `[1, 536]` with six colours and no monochromatic solution.
We use the partition of `[1, 537]` into six sum-free sets listed in the proof of Theorem 1 of
Chen, Zhu and Long, restricted to `[1, 536]`. Its classes are stored as lists and turned into
bitmasks. Bit `z` of `m <<< x` is bit `z - x` of `m`, so a class with bitmask `m` that contains
`x` has no solution `x + y = z` in it exactly when `(m <<< x) &&& m = 0`. For each
`x ∈ [1, 536]` the kernel checks this for the class of `x`, and that `x` lies in that class, with
its big-number arithmetic (`decide +kernel`, no `native_decide`).

## References

* Z. Chen, L. Zhu and F. Long, *A new lower bound for the sixth Schur number: S(6) ≥ 537*,
  arXiv:2610.31362v1 (2026), proof of Theorem 1: the partition used here.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.SchurNumbersWanted

open Finset

/-- **Schur forcing property.** For natural numbers $k$ and $N$, we say that $N$ forces a
monochromatic Schur triple in $k$ colours when every colouring $c$ of the natural numbers with $k$
colours has $x, y, z \in \{1, \dots, N\}$ with $x + y = z$ and $c(x) = c(y) = c(z)$.

Solutions with $x = y$ count, so this property gives the Schur numbers, not the weak Schur
numbers. -/
def schurForces (k N : ℕ) : Prop :=
  ∀ c : ℕ → Fin k, ∃ x ∈ Icc 1 N, ∃ y ∈ Icc 1 N, ∃ z ∈ Icc 1 N,
    x + y = z ∧ c x = c y ∧ c y = c z

/-- **Schur number.** For $k \ge 1$, the Schur number $S(k)$ is $N_0 - 1$, where $N_0$ is the
least natural number $N$ that forces a monochromatic Schur triple in $k$ colours: every colouring
$c$ of the natural numbers with $k$ colours has $x, y, z \in \{1, \dots, N\}$ with $x + y = z$ and
$c(x) = c(y) = c(z)$. For $k = 0$, $S(0) = 0$.

Such an $N_0$ exists by Schur's theorem, and $S(k)$ is the largest $N$ such that
$\{1, \dots, N\}$ splits into $k$ sum-free parts, some possibly empty (OEIS A045652); the
numbers $N_0 = S(k) + 1$ form OEIS A030126. -/
noncomputable def schurNumber (k : ℕ) : ℕ :=
  if k < 1 then 0 else sInf {N | schurForces k N} - 1

/-- Forcing a monochromatic Schur triple is monotone in the range. -/
private theorem schurForces_mono {k N M : ℕ} (h : schurForces k N) (hNM : N ≤ M) :
    schurForces k M := by
  intro c
  obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ := h c
  have hsub : Icc 1 N ⊆ Icc 1 M := Icc_subset_Icc_right hNM
  exact ⟨x, hsub hx, y, hsub hy, z, hsub hz, hxyz⟩

/-- The classes `{1, 4}` and `{2, 3}` are sum-free. -/
private theorem not_schurForces_two_four : ¬ schurForces 2 4 := by
  let c (n : ℕ) : Fin 2 := if n = 1 ∨ n = 4 then 0 else 1
  have h : ∀ x ∈ Icc 1 4, ∀ y ∈ Icc 1 4, x + y ≤ 4 → c x = c y → c y ≠ c (x + y) := by
    decide
  intro hf
  obtain ⟨x, hx, y, hy, _, hz, rfl, hxy, hyz⟩ := hf c
  exact h x hx y hy (mem_Icc.mp hz).2 hxy hyz

/-- Every two-colouring of `{1, …, 5}` makes at least one of the sums
`1 + 1`, `2 + 2`, `1 + 3`, `1 + 4`, or `2 + 3` a monochromatic triple. -/
private theorem schurForces_two_five : schurForces 2 5 := by
  intro c
  have cover : ∀ a b c d e : Fin 2,
      a = b ∨ b = d ∨ (a = c ∧ c = d) ∨ (a = d ∧ d = e) ∨ (b = c ∧ c = e) := by
    decide
  rcases cover (c 1) (c 2) (c 3) (c 4) (c 5) with h | h | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩
  · exact ⟨1, by decide, 1, by decide, 2, by decide, rfl, rfl, h⟩
  · exact ⟨2, by decide, 2, by decide, 4, by decide, rfl, rfl, h⟩
  · exact ⟨1, by decide, 3, by decide, 4, by decide, rfl, h, h'⟩
  · exact ⟨1, by decide, 4, by decide, 5, by decide, rfl, h, h'⟩
  · exact ⟨2, by decide, 3, by decide, 5, by decide, rfl, h, h'⟩

/-- **The second Schur number.** The Schur number $S(2)$ equals $4$.

Source: exhaustive check; OEIS A045652; listed in leansolving/SqueezeBench
`SqueezeBench/Problems/Schur/README.md`. -/
theorem schurNumber_two : schurNumber 2 = 4 := by
  have hinf : sInf {N | schurForces 2 N} = 4 + 1 :=
    (Nat.sInf_upward_closed_eq_succ_iff (fun _ _ hNM h => schurForces_mono h hNM) 4).2
      ⟨schurForces_two_five, not_schurForces_two_four⟩
  simp [schurNumber, hinf]

/-- A partition of `[1, 13]` into three sum-free classes. -/
private theorem not_schurForces_three_thirteen : ¬ schurForces 3 13 := by
  let c (n : ℕ) : Fin 3 :=
    if n ∈ ({1, 4, 10, 13} : Finset ℕ) then 0
    else if n ∈ ({2, 3, 11, 12} : Finset ℕ) then 1 else 2
  have h : ∀ x ∈ Icc 1 13, ∀ y ∈ Icc 1 13, x + y ≤ 13 → c x = c y → c y ≠ c (x + y) := by
    decide +kernel
  intro hf
  obtain ⟨x, hx, y, hy, _, hz, rfl, hxy, hyz⟩ := hf c
  exact h x hx y hy (mem_Icc.mp hz).2 hxy hyz

/-- All three-colourings of `[1, n]` that avoid a monochromatic Schur triple, in interval order.
To append colour `a` at `n + 1`, check the summands `i + 1` and `n - i` for each `i < n`.
Their colours are entries `i` and `n - 1 - i` of the prefix. -/
private def sumFreePrefixes : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => (sumFreePrefixes n).flatMap fun p =>
      ((List.finRange 3).filter fun a => (List.range n).all fun i =>
        decide (p[i]? = some a → p[n - 1 - i]? ≠ some a)).map fun a => p ++ [a]

/-- Every three-colouring of `[1, 14]` contains a monochromatic Schur triple. -/
private theorem schurForces_three_fourteen : schurForces 3 14 := by
  intro c
  by_contra h
  have mem (n : ℕ) (hn : n ≤ 14) :
      ((List.range n).map fun i => c (i + 1)) ∈ sumFreePrefixes n := by
    induction n with
    | zero => simp [sumFreePrefixes]
    | succ n ih =>
      simp only [sumFreePrefixes, List.mem_flatMap, List.mem_map, List.mem_filter]
      refine ⟨_, ih (by omega), c (n + 1), ⟨by simp, ?_⟩, ?_⟩
      · simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
        intro i hi
        have hj : n - 1 - i < n := by omega
        simp only [List.getElem?_map, List.getElem?_range hi, List.getElem?_range hj,
          Option.map_some, ne_eq, Option.some.injEq]
        intro h₁ h₂
        refine h ⟨i + 1, ?_, n - 1 - i + 1, ?_, n + 1, ?_, by omega, h₁.trans h₂.symm, h₂⟩ <;>
          rw [mem_Icc] <;> omega
      · simp [List.range_succ]
  have empty : sumFreePrefixes 14 = [] := by decide +kernel
  simpa [empty] using mem 14 le_rfl

/-- **The third Schur number.** The Schur number $S(3)$ equals $13$.

Source: exhaustive check; OEIS A045652; listed in SqueezeBench
`SqueezeBench/Problems/Schur/README.md`. -/
theorem schurNumber_three : schurNumber 3 = 13 := by
  have hinf : sInf {N | schurForces 3 N} = 13 + 1 :=
    (Nat.sInf_upward_closed_eq_succ_iff (fun _ _ hNM h => schurForces_mono h hNM) 13).2
      ⟨schurForces_three_fourteen, not_schurForces_three_thirteen⟩
  simp [schurNumber, hinf]

/-- The six classes of the partition of `{1, …, 537}` into sum-free sets listed in the proof of
Theorem 1 of Chen, Zhu and Long (arXiv:2610.31362v1), in the paper's order: class `j` here is
the paper's colour `j + 1`. -/
private def witnessClass : ℕ → List ℕ
  | 0 => [1, 5, 12, 15, 19, 21, 23, 25, 29, 32, 39, 43, 45, 49, 95, 102, 106, 108, 112, 119, 122,
      126, 128, 130, 132, 136, 139, 146, 150, 152, 156, 163, 166, 170, 172, 174, 176, 180, 358, 362,
      364, 366, 368, 372, 375, 382, 386, 388, 392, 399, 402, 406, 408, 410, 412, 416, 419, 426, 430,
      432, 436, 443, 489, 493, 495, 499, 506, 509, 513, 515, 517, 519, 523, 526, 533, 537]
  | 1 => [2, 6, 7, 17, 18, 22, 27, 37, 41, 42, 46, 51, 66, 70, 81, 89, 90, 100, 101, 105, 109, 110,
      113, 114, 124, 125, 129, 133, 134, 144, 145, 149, 153, 157, 158, 168, 169, 192, 346, 369, 370,
      380, 381, 385, 389, 393, 394, 404, 405, 409, 413, 414, 424, 425, 428, 429, 433, 437, 438, 448,
      449, 457, 468, 472, 487, 492, 496, 497, 501, 511, 516, 520, 521, 531, 532, 536]
  | 2 => [3, 8, 9, 14, 20, 24, 26, 30, 31, 36, 47, 53, 59, 63, 65, 69, 76, 82, 86, 88, 92, 98, 104,
      115, 120, 121, 127, 131, 137, 142, 143, 148, 154, 159, 160, 165, 171, 177, 181, 182, 187, 188,
      193, 204, 334, 345, 350, 351, 356, 357, 361, 367, 373, 378, 379, 384, 390, 395, 396, 401, 407,
      411, 417, 418, 423, 434, 440, 446, 450, 452, 456, 462, 469, 473, 475, 479, 485, 491, 502, 507,
      508, 512, 514, 518, 524, 529, 530, 535]
  | 3 => [4, 10, 11, 13, 16, 28, 33, 34, 35, 40, 55, 57, 79, 93, 94, 96, 99, 111, 116, 117, 118,
      123, 135, 138, 140, 141, 147, 155, 161, 162, 164, 167, 179, 185, 203, 335, 353, 359, 371, 374,
      376, 377, 383, 391, 397, 398, 400, 403, 415, 420, 421, 422, 427, 439, 442, 444, 445, 459, 481,
      483, 498, 503, 504, 505, 510, 522, 525, 527, 528, 534]
  | 4 => [38, 44, 48, 50, 52, 54, 56, 58, 60, 61, 62, 64, 67, 68, 71, 72, 73, 74, 75, 77, 78, 80,
      83, 84, 85, 87, 91, 97, 103, 107, 173, 189, 196, 197, 201, 209, 212, 236, 302, 326, 329, 337,
      341, 342, 349, 365, 431, 435, 441, 447, 451, 453, 454, 455, 458, 460, 461, 463, 464, 465, 466,
      467, 470, 471, 474, 476, 477, 478, 480, 482, 484, 486, 488, 490, 494, 500]
  | 5 => [151, 175, 178, 183, 184, 186, 190, 191, 194, 195, 198, 199, 200, 202, 205, 206, 207, 208,
      210, 211, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229,
      230, 231, 232, 233, 234, 235, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249,
      250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268,
      269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287,
      288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 303, 304, 305, 306, 307,
      308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 327,
      328, 330, 331, 332, 333, 336, 338, 339, 340, 343, 344, 347, 348, 352, 354, 355, 360, 363, 387]
  | _ => []

/-- The bitmask of `witnessClass i`: bit `x` is set exactly when `x` lies in the class. -/
private def witnessMask (i : ℕ) : ℕ :=
  (witnessClass i).foldr (fun x m => 1 <<< x ||| m) 0

/-- The witness colouring: `x` gets the first class whose bitmask contains it, and the last
colour if there is none. -/
private def witnessColouring (x : ℕ) : Fin 6 :=
  if (witnessMask 0).testBit x then 0 else
  if (witnessMask 1).testBit x then 1 else
  if (witnessMask 2).testBit x then 2 else
  if (witnessMask 3).testBit x then 3 else
  if (witnessMask 4).testBit x then 4 else 5

/-- The check at `x`: for the bitmask `m` of the class of `x`, bit `x` of `m` is set, and no
`y` in the class has `x + y` in the class. -/
private def witnessCheck (x : ℕ) : Bool :=
  (witnessMask (witnessColouring x)).testBit x &&
    ((witnessMask (witnessColouring x) <<< x) &&& witnessMask (witnessColouring x)) == 0

/-- The check holds at every `x ∈ [1, 536]`; the kernel evaluates it. -/
private theorem witnessCheck_range : (List.range' 1 536).all witnessCheck = true := by
  decide +kernel

/-- The witness colouring has no monochromatic Schur triple in `[1, 536]`. -/
private theorem not_schurForces_six_536 : ¬ schurForces 6 536 := by
  intro h
  obtain ⟨x, hx, y, hy, z, hz, hxyz, hcxy, hcyz⟩ := h witnessColouring
  have hcheck {w : ℕ} (hw : w ∈ Icc 1 536) : witnessCheck w = true := by
    rw [mem_Icc] at hw
    exact List.all_eq_true.1 witnessCheck_range w (List.mem_range'_1.2 ⟨hw.1, by omega⟩)
  have hX := hcheck hx
  have hY := hcheck hy
  have hZ := hcheck hz
  simp only [witnessCheck, Bool.and_eq_true, beq_iff_eq] at hX hY hZ
  rw [← hcxy] at hY
  rw [← hcyz, ← hcxy] at hZ
  have hbit := congrArg (fun n => Nat.testBit n z) hX.2
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit, hZ.1, Bool.and_true,
    show z - x = y by omega, hY.1] at hbit
  simp [show x ≤ z by omega] at hbit

/-- **Lower bound for the sixth Schur number.** The Schur number $S(6)$ is at least $536$.

Source: H. Fredricksen and M. M. Sweet, *Symmetric sum-free partitions and
lower bounds for Schur numbers*, Electron. J. Combin. 7 (2000), R32; listed in
SqueezeBench `SqueezeBench/Problems/Schur/README.md`. -/
theorem le_schurNumber_six : 536 ≤ schurNumber 6 := by
  have hne : {N | schurForces 6 N}.Nonempty := by
    obtain ⟨S, hS⟩ := MetaMathlibExt.schur_ramsey 6 (by omega)
    refine ⟨S, fun c => ?_⟩
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hsum⟩ := hS c
    exact ⟨x, hx, y, hy, z, hz, hsum, hxy, hxy.symm.trans hxz⟩
  have h537 : 537 ≤ sInf {N | schurForces 6 N} :=
    Nat.le_of_not_lt fun hlt =>
      not_schurForces_six_536 (schurForces_mono (Nat.sInf_mem hne) (by omega))
  rw [schurNumber, ite_eq_right (by omega)]
  omega

end MathlibExt.Combinatorics.SchurNumbersWanted
