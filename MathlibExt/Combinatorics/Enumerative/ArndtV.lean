/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# The map V on compositions

The pairwise map `arndtV` induces a permutation of the compositions of each natural number.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The map $V$ on lists.** The map $V$ sends a list $(c_1, c_2, \dots)$ of natural
numbers to the concatenation of the images of its consecutive pairs $(c_1, c_2)$, $(c_3, c_4)$,
and so on, where $1^j$ denotes $j$ parts equal to $1$: a pair $(a, b)$ with $b \le a$ goes to
$(1^{a - b}, 2b)$; a pair $(a, b)$ with $b > a$ goes to $(1^{a + b - 2k - 1}, 2k + 1)$, where
$k = \lfloor (b - a + 1)/2 \rfloor$ is the integer $k \ge 1$ with $2k - 1 \le b - a < 2k + 1$;
and a final unpaired entry $a$ goes to $1^a$. The empty list goes to itself. The exponent
$a + b - 2k - 1$ is read as $0$ when it is negative, which happens only when $a = 0$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 3 and its proof. -/
def arndtV : List ℕ → List ℕ
  | [] => []
  | [a] => List.replicate a 1
  | a :: b :: rest =>
      (if b ≤ a then List.replicate (a - b) 1 ++ [2 * b]
        else List.replicate (a + b - 2 * ((b - a + 1) / 2) - 1) 1 ++
          [2 * ((b - a + 1) / 2) + 1]) ++
        arndtV rest

/-- **Values of the map $V$.** The map $V$ sends $(2, 3)$ to $(1, 1, 3)$, $(1, 4)$ to $(5)$,
$(4, 1)$ to $(1, 1, 1, 2)$, $(1, 3, 1)$ to $(1, 3, 1)$ and $(2, 2, 1)$ to $(4, 1)$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 6. -/
theorem arndtV_examples :
    arndtV [2, 3] = [1, 1, 3] ∧ arndtV [1, 4] = [5] ∧ arndtV [4, 1] = [1, 1, 1, 2] ∧
      arndtV [1, 3, 1] = [1, 3, 1] ∧ arndtV [2, 2, 1] = [4, 1] := by
  decide

namespace arndtV

/-- Decode a run of ones together with its terminating part, using the parity of that part
to recover the input pair. A final run of ones recovers an unpaired part. -/
private def decode (ones : ℕ) : List ℕ → List ℕ
  | [] => if ones = 0 then [] else [ones]
  | x :: xs =>
    if x = 1 then decode (ones + 1) xs
    else if x % 2 = 0 then (ones + x / 2) :: (x / 2) :: decode 0 xs
    else
      let a := ones / 2 + 1
      a :: (ones + x - a) :: decode 0 xs

private theorem decode_replicate (r ones : ℕ) (xs : List ℕ) :
    decode ones (List.replicate r 1 ++ xs) = decode (ones + r) xs := by
  induction r generalizing ones with
  | zero => simp
  | succ r ih =>
    simp [List.replicate_succ, decode, ih, Nat.succ_add, Nat.add_assoc]

private theorem decode_arndtV (xs : List ℕ) (h : 0 ∉ xs) :
    decode 0 (arndtV xs) = xs := by
  induction xs using arndtV.induct with
  | case1 => simp [arndtV, decode]
  | case2 a =>
    have ha : a ≠ 0 := by simpa [eq_comm] using h
    rw [arndtV, ← List.append_nil (List.replicate a 1), decode_replicate]
    simp [decode, ha]
  | case3 a b rest ih =>
    simp only [List.mem_cons, not_or] at h
    have hrest := ih h.2.2
    rw [arndtV]
    split <;> rename_i hab
    · have hm : 2 * b ≠ 1 := by omega
      simp [List.append_assoc, decode_replicate, decode, hm, hrest]
      omega
    · let k := (b - a + 1) / 2
      let r := a + b - 2 * k - 1
      have hk : k ≠ 0 := by dsimp [k]; omega
      -- The run length is either 2a - 2 or 2a - 1, so it determines the first part.
      have ha : r / 2 + 1 = a := by dsimp [r, k]; omega
      have hb : r + (2 * k + 1) - a = b := by dsimp [r, k]; omega
      change decode 0 ((List.replicate r 1 ++ [2 * k + 1]) ++ arndtV rest) = _
      simp [List.append_assoc, decode_replicate, decode, hk, ha, hb, hrest]

private theorem valid (xs : List ℕ) (h : 0 ∉ xs) :
    0 ∉ arndtV xs ∧ (arndtV xs).sum = xs.sum := by
  induction xs using arndtV.induct with
  | case1 => simp [arndtV]
  | case2 a => simp [arndtV, List.mem_replicate]
  | case3 a b rest ih =>
    simp only [List.mem_cons, not_or] at h
    obtain ⟨hpos, hsum⟩ := ih h.2.2
    rw [arndtV]
    split <;> simp [List.mem_replicate, hpos, hsum] <;> omega

end arndtV

/-- **The map $V$ permutes compositions.** For every natural number $n$, the map $V$ sends
compositions of $n$ to compositions of $n$, and it is a permutation of the set of compositions
of $n$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 3 (`integers-2026-A64-thm-3`). -/
theorem exists_perm_composition_blocks_eq_arndtV (n : ℕ) :
    ∃ σ : Equiv.Perm (Composition n), ∀ c, (σ c).blocks = arndtV c.blocks := by
  have noZero {c : Composition n} : 0 ∉ c.blocks := fun h => (Nat.lt_irrefl 0) (c.blocks_pos h)
  let f (c : Composition n) : Composition n :=
    have hv := arndtV.valid c.blocks noZero
    ⟨arndtV c.blocks, fun h => Nat.pos_of_ne_zero fun he => hv.1 (he ▸ h),
      hv.2.trans c.blocks_sum⟩
  have hf : Function.Injective f := by
    intro c d h
    apply Composition.ext
    have hblocks := congrArg (fun x : Composition n => arndtV.decode 0 x.blocks) h
    simpa only [f, arndtV.decode_arndtV _ noZero] using hblocks
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun _ => rfl⟩

end

end MetaMathlibExt
