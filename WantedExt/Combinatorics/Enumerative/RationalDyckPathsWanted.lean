/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Logic.Equiv.Defs

/-!
# Rational Dyck paths and `Q`-bonacci paths

Statements from Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*,
Journal of Integer Sequences 28 (2025), Article 25.3.2 (arXiv:2409.20210). The
paths are Mathlib's `DyckWord`s of height at most `2`. Such a path `P ≠ ε` of
semilength `n` factorizes as `U X₁ ⋯ X_{n-1} D` with each `Xᵢ` a `1`-peak `UD`
or a `0`-valley `DU`, and the source's factorization
`P = U (UD)^{p₁} (DU)^{v₁} ⋯ (UD)^{p_k} (DU)^{v_k} D` reads the maximal runs of
this block word. Here the block word is a `List Bool` (`true` for `UD`), its
maximal runs are `boolRuns`, and the parameters `r, s` of `q = r/s` are natural
numbers.
-/

namespace MetaMathlibExt

@[expose] public section

open DyckStep

/-- A Dyck word has height at most `2` when no prefix has more than two more `U`s
than `D`s.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 2. -/
public def IsDyckHeightAtMostTwo (p : DyckWord) : Prop :=
  ∀ i ≤ p.toList.length, (p.toList.take i).count U ≤ (p.toList.take i).count D + 2

/-- Height at most `2` is decidable.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 2. -/
public instance : DecidablePred IsDyckHeightAtMostTwo := fun p => by
  unfold IsDyckHeightAtMostTwo
  infer_instance

/-- The block word of a Dyck word of height at most `2` and semilength `n`: for
`i < n - 1`, entry `i` is `true` when the steps `2i+1, 2i+2` form a `1`-peak `UD`
and `false` when they form a `0`-valley `DU`.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 3, factorization (1). -/
public def dyckHeightTwoBlockWord (p : DyckWord) : List Bool :=
  (List.range (p.semilength - 1)).map fun i => decide (p.toList[2 * i + 1]? = some U)

/-- The maximal runs of a Boolean word, as (letter, length) pairs from left to
right.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 3 (blocks of maximal
length of consecutive `1`-peaks and `0`-valleys). -/
public def boolRuns : List Bool → List (Bool × ℕ)
  | [] => []
  | b :: l =>
    match boolRuns l with
    | [] => [(b, 1)]
    | (c, m) :: rest => if b = c then (c, m + 1) :: rest else (b, 1) :: (c, m) :: rest

/-- The source's example `U (UD) (DU)^2 (UD)^2 (DU)^2 D` has runs
`p₁ = 1, v₁ = 2, p₂ = 2, v₂ = 2`.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 3, Example. -/
public theorem boolRuns_example :
    boolRuns [true, false, false, true, true, false, false] =
      [(true, 1), (false, 2), (true, 2), (false, 2)] := by
  decide

/-- The number of `0`-valleys immediately after run `i`: the length of run
`i + 1` if it is a `false` run, and `0` otherwise.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Section 3 (`vᵢ` after `pᵢ`). -/
public def runFollowingValleys (R : List (Bool × ℕ)) (i : ℕ) : ℕ :=
  match R[i + 1]? with
  | some (false, v) => v
  | _ => 0

/-- The run condition of `R̃^{r/s}` (Definition 3): every block of `p` consecutive
`1`-peaks has `p ≤ r` and is followed by `v` consecutive `0`-valleys with
`p s ≤ r v`, i.e. `v ≥ ⌈p s / r⌉`.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 3. -/
public def IsTildeRationalRuns (r s : ℕ) (R : List (Bool × ℕ)) : Prop :=
  ∀ i < R.length, (R.getD i (false, 0)).1 = true →
    (R.getD i (false, 0)).2 ≤ r ∧ (R.getD i (false, 0)).2 * s ≤ r * runFollowingValleys R i

/-- The run condition of `Q^{r/s}` (Definition 4): every block of `p` consecutive
`1`-peaks has `p ≤ r`; every block but the last is followed by `v` consecutive
`0`-valleys with `p s ≤ r v`; the last block (`p_k`, `v_k`) needs this only when
`p_k < r` and `v_k ≠ 0`.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 4. -/
public def IsQBonacciRuns (r s : ℕ) (R : List (Bool × ℕ)) : Prop :=
  ∀ i < R.length, (R.getD i (false, 0)).1 = true →
    (R.getD i (false, 0)).2 ≤ r ∧
      ((R.getD i (false, 0)).2 * s ≤ r * runFollowingValleys R i ∨
        ((∀ j < R.length, i < j → (R.getD j (false, 0)).1 = false) ∧
          ((R.getD i (false, 0)).2 = r ∨ runFollowingValleys R i = 0)))

/-- The `R̃` run condition is decidable.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 3. -/
public instance (r s : ℕ) : DecidablePred (IsTildeRationalRuns r s) := fun R => by
  unfold IsTildeRationalRuns
  infer_instance

/-- The `Q` run condition is decidable.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 4. -/
public instance (r s : ℕ) : DecidablePred (IsQBonacciRuns r s) := fun R => by
  unfold IsQBonacciRuns
  infer_instance

/-- The source's examples for `q = 4/5`: `U (UD) (DU)^2 (UD)^2 (DU)^2 D` is not in
`Q^{4/5}`, while `U (UD) (DU)^2 (UD)^4 (DU)^2 D` (last block `p₂ = 4 = r`) and
`U (UD) (DU)^2 (UD)^3 D` (`p₂ = 3 < r`, `v₂ = 0`) are.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Example after Definition 4. -/
public theorem isQBonacciRuns_examples :
    ¬ IsQBonacciRuns 4 5 (boolRuns [true, false, false, true, true, false, false]) ∧
      IsQBonacciRuns 4 5
        (boolRuns [true, false, false, true, true, true, true, false, false]) ∧
      IsQBonacciRuns 4 5 (boolRuns [true, false, false, true, true, true]) := by
  decide

/-- `R̃_n^{r/s}`: the Dyck paths of semilength `n` and height at most `2` whose
blocks satisfy Definition 3.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 3. -/
public def tildeRationalDyckPaths (r s n : ℕ) : Finset {p : DyckWord // p.semilength = n} :=
  Finset.univ.filter fun p =>
    IsDyckHeightAtMostTwo p.1 ∧ IsTildeRationalRuns r s (boolRuns (dyckHeightTwoBlockWord p.1))

/-- `Q_n^{r/s}`: the `Q`-bonacci paths, i.e. the Dyck paths of semilength `n` and
height at most `2` whose blocks satisfy Definition 4.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definition 4. -/
public def qBonacciDyckPaths (r s n : ℕ) : Finset {p : DyckWord // p.semilength = n} :=
  Finset.univ.filter fun p =>
    IsDyckHeightAtMostTwo p.1 ∧ IsQBonacciRuns r s (boolRuns (dyckHeightTwoBlockWord p.1))

/-- Small values for `q = 3/2` (here `t = 0` and `s ≠ t r + 1`):
`|Q_4^{3/2}| = 7` but `|R̃_5^{3/2}| = 6`.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Definitions 3 and 4. -/
public theorem card_qBonacciDyckPaths_three_two_four :
    (qBonacciDyckPaths 3 2 4).card = 7 ∧ (tildeRationalDyckPaths 3 2 5).card = 6 := by
  decide +kernel

/-- If `s = t r + 1` with `t ∈ ℕ` (and `r ≥ 1`), then `Q_n^{r/s}` and
`R̃_{n+t+1}^{r/s}` are in bijection for every `n ≥ 0`.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Proposition 6
(`jis-2025-25.3.2-prop-6`). -/
public theorem_wanted nonempty_equiv_qBonacci_tildeRational {r s t : ℕ} (hr : 0 < r)
    (hs : s = t * r + 1) (n : ℕ) :
    Nonempty (qBonacciDyckPaths r s n ≃ tildeRationalDyckPaths r s (n + t + 1))

/-- For coprime `r, s ≥ 1` and `t = ⌊(s - 1)/r⌋` (so `t r + 1 ≤ s ≤ (t + 1) r`, the
source's choice of `t`), the sets `R̃_{n+t+1}^{r/s}` and `Q_n^{r/s}` are in
bijection for every `n` if and only if `s = t r + 1`.

Source: Barcucci, Bernini, Bilotta, and Pinzani, *Rational Dyck Paths*, Journal
of Integer Sequences 28 (2025), Article 25.3.2, Proposition 7
(`jis-2025-25.3.2-prop-7`). -/
public theorem_wanted forall_nonempty_equiv_qBonacci_tildeRational_iff {r s : ℕ} (hr : 0 < r)
    (hs : 0 < s) (hrs : Nat.Coprime r s) :
    (∀ n : ℕ, Nonempty (tildeRationalDyckPaths r s (n + (s - 1) / r + 1) ≃
      qBonacciDyckPaths r s n)) ↔ s = (s - 1) / r * r + 1

end

end MetaMathlibExt
