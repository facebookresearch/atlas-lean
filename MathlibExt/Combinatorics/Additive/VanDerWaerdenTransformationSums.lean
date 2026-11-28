/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Additive.VanDerWaerdenSymmetricFunctions
import Mathlib.Combinatorics.HalesJewett

/-!
# Van der Waerden vanishing for transformation sums

Every finite family of transformed sums over `ZMod n` vanishes simultaneously on
arbitrarily many consecutive blocks of a common length greater than one.
-/

namespace MetaMathlibExt

/-- **Vanishing of families of sums of transformed entries.** Let $n$ be a positive integer, $d$ a
natural number and $g_1, \dots, g_d : \mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$ maps.
Then the family over $\mathbb{Z}/n\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to the vector
$\left(\sum_i g_1(b_i), \dots, \sum_i g_d(b_i)\right) \in (\mathbb{Z}/n\mathbb{Z})^d$ is
vanishing, where a block counts as vanishing when all $d$ coordinates of this vector are zero.

The source assumes $d > 0$; for $d = 0$ the statement is trivial.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 6
(`integers-2026-A25-thm-6`). -/
public theorem isVanishingFamily_transformation_sums {n d : ℕ} (hn : 0 < n)
    (g : Fin d → ZMod n → ZMod n) :
    IsVanishingFamily (fun (l : ℕ) (b : Fin l → ZMod n) (t : Fin d) => ∑ i, g t (b i)) := by
  intro m _ a
  have : NeZero n := ⟨hn.ne'⟩
  let prefixSum (k : ℕ) (t : Fin d) := ∑ i ∈ Finset.range k, g t (a i)
  -- Restrict to even endpoints so the progression has step at least two.
  obtain ⟨step, hstep, start, color, hmono⟩ := Combinatorics.exists_mono_homothetic_copy
    (Finset.range (m + 1)) (fun k => prefixSum (k * 2))
  have boundary (j : ℕ) (hj : j ≤ m) :
      prefixSum (start * 2 + j * (step * 2)) = color := by
    have h := hmono j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    simpa [nsmul_eq_mul, Nat.add_mul, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.add_comm] using h
  refine ⟨step * 2, by omega, start * 2, ?_⟩
  intro j hj
  funext t
  -- Each coordinate of the block sum is the difference of two equal prefix sums.
  change ∑ i : Fin (step * 2), g t (a (start * 2 + j * (step * 2) + i)) = 0
  rw [Fin.sum_univ_eq_sum_range (fun i => g t (a (start * 2 + j * (step * 2) + i))),
    ← Finset.sum_range_add_sub_sum_range (fun i => g t (a i))]
  change prefixSum (start * 2 + j * (step * 2) + step * 2) t -
    prefixSum (start * 2 + j * (step * 2)) t = 0
  rw [Nat.add_assoc, ← Nat.succ_mul, boundary (j + 1) hj, boundary j hj.le, sub_self]

end MetaMathlibExt
