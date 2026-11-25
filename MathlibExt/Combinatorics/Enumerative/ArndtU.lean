/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# The map U on compositions

The pairwise map `arndtU` of Hopkins and Tangboonduangjit sends compositions of `n` to
compositions of `n` and induces a permutation of them
(`exists_perm_composition_blocks_eq_arndtU`). The proof decodes the image: on a composition every
pair becomes a run of ones closed by a part at least `2`, whose parity tells which case of the map
applies, and a final run of ones is the unpaired last part.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **The map $U$ on lists.** The map $U$ sends a list $(c_1, c_2, \dots)$ of natural
numbers to the concatenation of the images of its consecutive pairs $(c_1, c_2)$, $(c_3, c_4)$,
and so on, where $1^j$ denotes $j$ parts equal to $1$: a pair $(a, b)$ with $b < a$ goes to
$(1^{a - b - 1}, 2b + 1)$; a pair $(a, b)$ with $b \ge a$ goes to $(1^{a + b - 2k}, 2k)$, where
$k = \lfloor (b - a)/2 \rfloor + 1$ is the integer $k \ge 1$ with $2k - 2 \le b - a < 2k$; and a
final unpaired entry $a$ goes to $1^a$. The empty list goes to itself. The exponent
$a + b - 2k$ is read as $0$ when it is negative, which happens only when $a = 0$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 2 and its proof. -/
def arndtU : List ℕ → List ℕ
  | [] => []
  | [a] => List.replicate a 1
  | a :: b :: rest =>
      (if b < a then List.replicate (a - b - 1) 1 ++ [2 * b + 1]
        else List.replicate (a + b - 2 * ((b - a) / 2 + 1)) 1 ++ [2 * ((b - a) / 2 + 1)]) ++
        arndtU rest

/-- **Values of the map $U$.** The map $U$ sends $(2, 3)$ to $(1, 1, 1, 2)$, $(1, 4)$ to
$(1, 4)$, $(3, 2)$ to $(5)$, $(1, 1, 1, 2)$ to $(2, 1, 2)$ and $(1, 3, 1)$ to $(4, 1)$.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Table 3. -/
theorem arndtU_examples :
    arndtU [2, 3] = [1, 1, 1, 2] ∧ arndtU [1, 4] = [1, 4] ∧ arndtU [3, 2] = [5] ∧
      arndtU [1, 1, 1, 2] = [2, 1, 2] ∧ arndtU [1, 3, 1] = [4, 1] := by
  decide

namespace arndtU

/-- Decode a run of `ones` ones together with its terminating part `x ≥ 2`. An odd `x = 2b + 1`
comes from a pair `(ones + b + 1, b)`. An even `x` comes from a pair `(a, ones + x - a)` with
`a = ones / 2 + 1`, since the run has length `2a - 2` or `2a - 1`. A final run of ones recovers
an unpaired part. -/
private def decode (ones : ℕ) : List ℕ → List ℕ
  | [] => if ones = 0 then [] else [ones]
  | x :: xs =>
    if x = 1 then decode (ones + 1) xs
    else if x % 2 = 1 then (ones + x / 2 + 1) :: (x / 2) :: decode 0 xs
    else
      let a := ones / 2 + 1
      a :: (ones + x - a) :: decode 0 xs

private theorem decode_replicate (r ones : ℕ) (xs : List ℕ) :
    decode ones (List.replicate r 1 ++ xs) = decode (ones + r) xs := by
  induction r generalizing ones with
  | zero => simp
  | succ r ih =>
    simp [List.replicate_succ, decode, ih, Nat.succ_add, Nat.add_assoc]

private theorem decode_arndtU (xs : List ℕ) (h : 0 ∉ xs) :
    decode 0 (arndtU xs) = xs := by
  induction xs using arndtU.induct with
  | case1 => simp [arndtU, decode]
  | case2 a =>
    have ha : a ≠ 0 := by simpa [eq_comm] using h
    rw [arndtU, ← List.append_nil (List.replicate a 1), decode_replicate]
    simp [decode, ha]
  | case3 a b rest ih =>
    simp only [List.mem_cons, not_or] at h
    have hrest := ih h.2.2
    rw [arndtU]
    split <;> rename_i hab
    · -- The terminating part `2b + 1` is odd and at least `3`.
      have hb : b ≠ 0 := Ne.symm h.2.1
      have hodd : (2 * b + 1) % 2 = 1 := by omega
      have hdiv : (2 * b + 1) / 2 = b := by omega
      have ha : a - b - 1 + b + 1 = a := by omega
      simp [List.append_assoc, decode_replicate, decode, hb, hodd, hdiv, ha, hrest]
    · let k := (b - a) / 2 + 1
      let r := a + b - 2 * k
      have hm : 2 * k ≠ 1 := by omega
      -- The run length is either `2a - 2` or `2a - 1`, so it determines the first part.
      have ha : r / 2 + 1 = a := by dsimp [r, k]; omega
      have hb : r + 2 * k - a = b := by dsimp [r, k]; omega
      change decode 0 ((List.replicate r 1 ++ [2 * k]) ++ arndtU rest) = _
      simp [List.append_assoc, decode_replicate, decode, hm, ha, hb, hrest]

private theorem valid (xs : List ℕ) (h : 0 ∉ xs) :
    0 ∉ arndtU xs ∧ (arndtU xs).sum = xs.sum := by
  induction xs using arndtU.induct with
  | case1 => simp [arndtU]
  | case2 a => simp [arndtU, List.mem_replicate]
  | case3 a b rest ih =>
    simp only [List.mem_cons, not_or] at h
    obtain ⟨hpos, hsum⟩ := ih h.2.2
    rw [arndtU]
    split <;> simp [List.mem_replicate, hpos, hsum] <;> omega

end arndtU

/-- **The pairwise map U permutes compositions.** For every natural number $n$ there is a
permutation $\sigma$ of the compositions of $n$ such that, for every composition $c$ of $n$, the
list of parts of $\sigma(c)$ is $U(c)$, the result of applying the pairwise map $U$ to the list
of parts of $c$. In particular, $U$ sends compositions of $n$ to compositions of $n$ and permutes
them.

Source: Brian Hopkins and Aram Tangboonduangjit, *Arndt and De Morgan Compositions*, INTEGERS 26
(2026), Article A64, Theorem 2 (`integers-2026-A64-thm-2`). -/
theorem exists_perm_composition_blocks_eq_arndtU (n : ℕ) :
    ∃ σ : Equiv.Perm (Composition n), ∀ c, (σ c).blocks = arndtU c.blocks := by
  have noZero {c : Composition n} : 0 ∉ c.blocks := fun h => (Nat.lt_irrefl 0) (c.blocks_pos h)
  let f (c : Composition n) : Composition n :=
    have hv := arndtU.valid c.blocks noZero
    ⟨arndtU c.blocks, fun h => Nat.pos_of_ne_zero fun he => hv.1 (he ▸ h),
      hv.2.trans c.blocks_sum⟩
  have hf : Function.Injective f := by
    intro c d h
    apply Composition.ext
    have hblocks := congrArg (fun x : Composition n => arndtU.decode 0 x.blocks) h
    simpa only [f, arndtU.decode_arndtU _ noZero] using hblocks
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun _ => rfl⟩

end

end MetaMathlibExt
