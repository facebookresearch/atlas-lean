/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedFrobeniusTriangular

/-! # Tests for explicit triangular Frobenius numbers -/

open MetaMathlibExt

-- Enumerate triples for the whole window on the *original* generators. For each pair of
-- first and second coefficients, the third generator is larger than the window width,
-- so at most one third coefficient contributes. Add its represented integer to the histogram.
private def windowCounts (a b c g : ℕ) : Array ℕ :=
  (List.range ((g + a) / a + 1)).foldl (fun counts x =>
    (List.range ((g + a - x * a) / b + 1)).foldl (fun counts y =>
      let base := x * a + y * b
      let z := (g - base + c - 1) / c
      let m := base + z * c
      if g ≤ m && m ≤ g + a then counts.modify (m - g) (· + 1) else counts) counts)
    (Array.replicate (a + 1) 0)

private def checksRow (n s g L atCutoff : ℕ) : Bool :=
  let t (j : ℕ) := j * (j + 1) / 2
  4 * (g + 1) == (n + 1) * (n + 2) * L &&
    match (windowCounts (t n) (t (n + 1)) (t (n + 2)) g).toList with
    | [] => false
    | count :: rest => count == atCutoff && count ≤ s && rest.length == t n &&
      rest.all (fun c => s < c)

-- Check the least index in each parity branch, and the additional even boundary n = 14
-- at level 11. At the two level-20 boundaries the cutoff count is 19, not 20.
#guard checksRow 12 11 4913 108 11
#guard checksRow 14 11 7439 124 11
#guard checksRow 15 11 8975 132 11
#guard checksRow 14 12 7559 126 12
#guard checksRow 17 12 12824 150 12
#guard checksRow 12 13 5186 114 13
#guard checksRow 15 13 9383 138 13
#guard checksRow 12 14 5459 120 14
#guard checksRow 15 14 9791 144 14
#guard checksRow 18 15 17099 180 15
#guard checksRow 15 15 10199 150 15
#guard checksRow 20 16 23099 200 16
#guard checksRow 17 16 14534 170 16
#guard checksRow 18 17 17669 186 17
#guard checksRow 15 17 10607 156 17
#guard checksRow 20 18 24485 212 18
#guard checksRow 17 18 15560 182 18
#guard checksRow 20 19 25178 218 19
#guard checksRow 23 19 37199 248 19
#guard checksRow 18 20 18809 198 19
#guard checksRow 21 20 28841 228 19

-- A client can extract the first row and solve its equation for the cutoff.
example : IsGenFrobeniusNumber (triangularTriple 14) 11 7439 := by
  obtain ⟨g, hg, heq⟩ := (isGenFrobeniusNumber_triangularTriple_eleven_to_twenty 14).1
    (Or.inr (by decide))
  have : g = 7439 := by omega
  simpa only [this] using hg
