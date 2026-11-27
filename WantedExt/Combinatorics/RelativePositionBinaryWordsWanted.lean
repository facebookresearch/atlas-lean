/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.List.TFAE
public import Mathlib.Data.Stream.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Topology.Instances.EReal.Lemmas
public import MathlibExt.Combinatorics.InfiniteWord.FibonacciWord
public import MathlibExt.Combinatorics.InfiniteWord.ThueMorse
public import MathlibExt.Combinatorics.Words.AntitoneRelativePosition
public import MathlibExt.Combinatorics.Words.BoundedRunPositions
public import MathlibExt.Combinatorics.Words.ClonedWordPositions
public import MathlibExt.Combinatorics.Words.EquilibriousWord
public import MathlibExt.Combinatorics.Words.FibonacciIccanobiF
public import MathlibExt.Combinatorics.Words.GoldenEigenvector
public import MathlibExt.Combinatorics.Words.LetterPositionReconstruction
public import MathlibExt.Combinatorics.Words.MonotoneRelativePosition
public import MathlibExt.Combinatorics.Words.PeriodicRelativePosition
public import MathlibExt.Combinatorics.Words.PisaEigenvector
public import MathlibExt.Combinatorics.Words.PisaRelativePosition
public import MathlibExt.Combinatorics.Words.RelativePositionBinaryWords
public import MathlibExt.Combinatorics.Words.RelativePositionFrequency
public import MathlibExt.Combinatorics.Words.RelativePositionIncrements
public import MathlibExt.Combinatorics.Words.RelativePositionInjective

/-!
# Relative position in binary words (Coons–Ramsey–Strungaru)

Statements from Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position
in Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5
(arXiv:2410.12173, TeX source read for the definitions).

Conventions. An infinite binary word `w = ℓ₀ ℓ₁ ℓ₂ ⋯` is a function `ℕ → Bool`, with the
letter `a` encoded as `true` and `b` as `false`. The paper's `𝒲` (both letters occur
infinitely often) is `BothLettersInfinite`, and `a𝒲` adds `w 0 = true`. The paper's
functions on `ℕ = {1, 2, …}` are functions `ℕ → _` used only at `n ≥ 1`; the difference
sequence is `Δs(n) = s(n+1) - s(n)`. "Increasing" in the paper means non-decreasing.
The reflection `w̄` is `fun i => !w i`, the prefix operator `Pre_u(w) = u w` is Mathlib's
`u ++ₛ w`, the cloning substitution `φ_k(w)` is `fun i => w (i / k)`, and the counting function
`#_α(m)` counts the letters `α` among the first `m` letters `ℓ₀ ⋯ ℓ_{m-1}`.
The Fibonacci word `f = abaab⋯` is `fun i => !fibInf i` (`fibInf` encodes `a` as `false`), so
`f̄ = fibInf`, and `ϱ_F^n(a)` is `(fibWord n).map (!·)`. The Thue–Morse word `t = abba⋯` is
`fun i => !thueMorse i`. A one-sided fixed point of a substitution `ϱ` is a word `w` with
`IsSubstitutionImage ϱ w w`, and the substitution matrix of `ϱ` has entries
`M₁₁ = |ϱ(a)|_a`, `M₁₂ = |ϱ(b)|_a`, `M₂₁ = |ϱ(a)|_b`, `M₂₂ = |ϱ(b)|_b`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Characterization of the position functions.** Let $p$ be a function from the natural
numbers to the natural numbers. There is an infinite word $w$ over the letters $a$ and $b$ that
starts with $a$, in which both letters occur infinitely often, and whose position function for
$a$ satisfies $p_a(n) = p(n)$ for all $n \ge 1$, if and only if $p(n) < p(n+1)$ for all $n \ge 1$,
$p(1) = 0$, and $p(n+1) - p(n) > 1$ for infinitely many $n \ge 1$. Likewise, there is an infinite
word over $a$ and $b$ that starts with $a$, in which both letters occur infinitely often, and
whose position function for $b$ satisfies $p_b(n) = p(n)$ for all $n \ge 1$, if and only if
$p(n) < p(n+1)$ for all $n \ge 1$, $p(1) > 0$, and $p(n+1) - p(n) > 1$ for infinitely many
$n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 4
(`jis-2025-25.1.5-lem-4`). -/
public theorem_wanted exists_word_letterPosition_eq_iff (p : ℕ → ℕ) :
    ((∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → letterPosition w true n = p n) ↔
      (∀ n, 1 ≤ n → p n < p (n + 1)) ∧ p 1 = 0 ∧
        {n | 1 ≤ n ∧ 1 < p (n + 1) - p n}.Infinite) ∧
    ((∃ w, BothLettersInfinite w ∧ w 0 = true ∧ ∀ n, 1 ≤ n → letterPosition w false n = p n) ↔
      (∀ n, 1 ≤ n → p n < p (n + 1)) ∧ 0 < p 1 ∧
        {n | 1 ≤ n ∧ 1 < p (n + 1) - p n}.Infinite)

/-- **Monotonicity of the relative position function and runs of letters.** Let $w$ be an
infinite word over $\{a, b\}$ that starts with $a$ and in which both letters occur infinitely
often, let $r$ be its relative position function, and write $\Delta r(n) = r(n+1) - r(n)$. A
factor of $w$ is a block of consecutive letters. (a) If $r(n) < r(n+1)$ for all $n \ge 1$, then
$bb$ is not a factor of $w$. (b) If $bb$ is not a factor of $w$, then $r(n) \le r(n+1)$ for all
$n \ge 1$. (c) For every $k \ge 0$, if $b^k$ is a factor of $w$, then there is $n \ge 0$ with
$\Delta r(n+j) \le 0$ for all $1 \le j \le k - 1$. (d) For every $k \ge 0$, if $a^k$ is a factor
of $w$, then there is $n \ge 0$ with $\Delta r(n+j) \ge 0$ for all $1 \le j \le k - 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 14
(`jis-2025-25.1.5-lem-14`). -/
public theorem_wanted relativePosition_monotonicity_runs {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    let r := relativePosition w
    ((∀ n, 1 ≤ n → r n < r (n + 1)) → ¬ ∃ i, w i = false ∧ w (i + 1) = false) ∧
      ((¬ ∃ i, w i = false ∧ w (i + 1) = false) → ∀ n, 1 ≤ n → r n ≤ r (n + 1)) ∧
      (∀ k, (∃ i, ∀ j < k, w (i + j) = false) →
        ∃ n, ∀ j, 1 ≤ j → j ≤ k - 1 → r (n + j + 1) - r (n + j) ≤ 0) ∧
      (∀ k, (∃ i, ∀ j < k, w (i + j) = true) →
        ∃ n, ∀ j, 1 ≤ j → j ≤ k - 1 → 0 ≤ r (n + j + 1) - r (n + j))

/-- **Periodicity of a word and of the gaps between occurrences of its letters.** Let
$w = w_0 w_1 w_2 \cdots$ be an infinite binary word over $\{a, b\}$ that starts with $a$ and in
which both letters occur infinitely often. Let $p_\alpha(n)$ be the position (counted from $0$)
of the $n$-th occurrence of the letter $\alpha$ in $w$, and $\Delta p_\alpha(n) =
p_\alpha(n+1) - p_\alpha(n)$. Call a sequence $s$ periodic if there is $q > 0$ with
$s(n + q) = s(n)$ for all $n \ge 1$. The following are equivalent: $w$ is periodic, that is,
$w_{i+q} = w_i$ for some $q > 0$ and all $i \ge 0$; $\Delta p_a$ is periodic; $\Delta p_a$ and
$\Delta p_b$ are both periodic. Moreover, if $w = u^\omega$ for a nonempty finite word $u$ with
$k$ letters $a$ and $j$ letters $b$, then $\Delta p_a(n + k) = \Delta p_a(n)$ and
$\Delta p_b(n + j) = \Delta p_b(n)$ for all $n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 16
(`jis-2025-25.1.5-lem-16`). -/
public theorem_wanted periodic_iff_letterPosition_diff_periodic {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    let dpa := fun n => letterPosition w true (n + 1) - letterPosition w true n
    let dpb := fun n => letterPosition w false (n + 1) - letterPosition w false n
    let Per := fun f : ℕ → ℕ => ∃ q, 0 < q ∧ ∀ n, 1 ≤ n → f (n + q) = f n
    ((∃ q, 0 < q ∧ ∀ i, w (i + q) = w i) ↔ Per dpa) ∧ (Per dpa ↔ Per dpa ∧ Per dpb) ∧
      ∀ u : List Bool, 0 < u.length → (∀ i, w i = u.getD (i % u.length) false) →
        (∀ n, 1 ≤ n → dpa (n + u.count true) = dpa n) ∧
          ∀ n, 1 ≤ n → dpb (n + u.count false) = dpb n

/-- **Reflection of binary words and relative position.** Let $\mathcal{W}$ be the set of
infinite words over $\{a, b\}$ in which both letters occur infinitely often, and let
$a\mathcal{W}$ and $b\mathcal{W}$ be its words that begin with $a$ and with $b$. For a word $w$
let $\bar w$ be its reflection, obtained by exchanging $a$ and $b$ at every position, and let
$r_w(n) = p_b(n) - p_a(n)$ be its relative position function, where $p_a(n)$ and $p_b(n)$ are
the positions of the $n$-th $a$ and the $n$-th $b$ in $w$. Then (a) the map $w \mapsto \bar w$
sends $a\mathcal{W}$ onto $b\mathcal{W}$ and $b\mathcal{W}$ onto $a\mathcal{W}$; and (b) for all
$w, w' \in \mathcal{W}$, $\bar w = w'$ if and only if $r_w(n) = -r_{w'}(n)$ for every $n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 11
(`jis-2025-25.1.5-prop-11`). -/
public theorem_wanted reflection_image_and_relativePosition :
    ((fun w : ℕ → Bool => fun i => !w i) '' {w | BothLettersInfinite w ∧ w 0 = true} =
        {w | BothLettersInfinite w ∧ w 0 = false}) ∧
      ((fun w : ℕ → Bool => fun i => !w i) '' {w | BothLettersInfinite w ∧ w 0 = false} =
        {w | BothLettersInfinite w ∧ w 0 = true}) ∧
      ∀ w w' : ℕ → Bool, BothLettersInfinite w → BothLettersInfinite w' →
        ((fun i => !w i) = w' ↔ ∀ n, 1 ≤ n → relativePosition w n = -relativePosition w' n)

/-- **Periodicity of the gaps between the $b$'s.** Let $w$ be an infinite binary word over the
letters $a$ and $b$ in which both letters occur infinitely often, let $p_b(n)$ be the position
(counting from $0$) of the $n$-th $b$ in $w$, and let $\Delta p_b(n) = p_b(n+1) - p_b(n)$. Let
$D_a$ delete the first $a$ of a word, and let $v = D_a^{p_b(1)}(w)$, the word $w$ with its initial
run of $a$'s deleted. Then there is $q > 0$ with $\Delta p_b(n + q) = \Delta p_b(n)$ for all
$n \ge 1$ if and only if there is $q > 0$ such that, for every $i \ge 0$, the letters of $v$ at
positions $i + q$ and $i$ are equal.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 19
(`jis-2025-25.1.5-lem-19`). -/
public theorem_wanted letterPosition_diff_periodic_iff_deleteFirst_periodic {w : ℕ → Bool}
    (hw : BothLettersInfinite w) :
    (∃ q, 0 < q ∧ ∀ n, 1 ≤ n → letterPosition w false (n + q + 1) - letterPosition w false (n + q) =
        letterPosition w false (n + 1) - letterPosition w false n) ↔
      ∃ q, 0 < q ∧ ∀ i,
        (fun v => deleteFirst v true)^[letterPosition w false 1] w (i + q) =
          (fun v => deleteFirst v true)^[letterPosition w false 1] w i

/-- **Prepending an equilibrious word is undone by deletion.** Let $u$ be a finite word in the
letters $a$ and $b$ of length $2k$. Then $u$ is equilibrious, that is, $a$ and $b$ occur equally
often in $u$, if and only if $D^k(uw) = w$ for every infinite binary word $w$ in which both
letters occur infinitely often, where $D$ deletes the first $b$ and the first $a$ of a word.

Here $a$ and $b$ play the roles of the letters $0$ and $1$ in the definition of equilibrious
words.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 21
(`jis-2025-25.1.5-lem-21`). -/
public theorem_wanted isEquilibriousWord_iff_deletion_iterate_prepend (u : List Bool) {k : ℕ}
    (hu : u.length = 2 * k) :
    IsEquilibriousWord (u.map fun x => if x then 0 else 1) ↔
      ∀ w, BothLettersInfinite w → deletion^[k] (u ++ₛ w) = w

/-- **Prepending an equilibrious word shifts the position functions.** Let $u$ be a finite word
over $\{a, b\}$ of length $2k$ that is equilibrious (it contains as many letters $a$ as letters
$b$), and let $w$ be an infinite binary word in which both letters occur infinitely often. For a
word $v$, write $p_{\alpha,v}(n)$ for the position (counted from $0$) of the $n$-th occurrence of
the letter $\alpha$ in $v$, and $r_v(n) = p_{b,v}(n) - p_{a,v}(n)$. Then for every $n \ge 1$ the
concatenation $uw$ satisfies $p_{a,uw}(n+k) = p_{a,w}(n) + 2k$, $p_{b,uw}(n+k) = p_{b,w}(n) + 2k$
and $r_{uw}(n+k) = r_w(n)$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 22
(`jis-2025-25.1.5-lem-22`). -/
public theorem_wanted letterPosition_prepend_equilibrious (u : List Bool) {k : ℕ}
    (hu : u.length = 2 * k) (hequi : IsEquilibriousWord (u.map fun x => if x then 0 else 1))
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (n : ℕ) (hn : 1 ≤ n) :
    letterPosition (u ++ₛ w) true (n + k) = letterPosition w true n + 2 * k ∧
      letterPosition (u ++ₛ w) false (n + k) = letterPosition w false n + 2 * k ∧
      relativePosition (u ++ₛ w) (n + k) = relativePosition w n

open Filter in
/-- **Upper and lower densities of a letter from its position function.** Let $w$ be an infinite
binary word in which both letters occur infinitely often and let $\alpha$ be a letter. Write
$\#_\alpha(m)$ for the number of occurrences of $\alpha$ among the first $m$ letters of $w$, and
$p_\alpha(n)$ for the position (counted from $0$) of the $n$-th occurrence of $\alpha$. Then
$\limsup_{m \to \infty} \#_\alpha(m)/m = \limsup_{n \to \infty} n/p_\alpha(n)$ and
$\liminf_{m \to \infty} \#_\alpha(m)/m = \liminf_{n \to \infty} n/p_\alpha(n)$.

Both sequences are bounded, so these are the classical upper and lower limits in $\mathbb{R}$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 29
(`jis-2025-25.1.5-cor-29`). -/
public theorem_wanted limsup_liminf_letterCount_div {w : ℕ → Bool} (hw : BothLettersInfinite w)
    (α : Bool) :
    limsup (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop =
        limsup (fun n : ℕ => (n : ℝ) / letterPosition w α n) atTop ∧
      liminf (fun m : ℕ => (letterCount w α m : ℝ) / m) atTop =
        liminf (fun n : ℕ => (n : ℝ) / letterPosition w α n) atTop

open Filter Topology in
/-- **Letter frequencies and the growth of the position functions.** Let $w$ be an infinite
binary word over the letters $a$ and $b$ in which both letters occur infinitely often, and let
$0 < d < 1$. For a letter $\alpha$, let $\#_\alpha(m)$ be the number of letters $\alpha$ among the
first $m$ letters of $w$, and let $p_\alpha(n)$ be the position (counting from $0$) of the $n$-th
occurrence of $\alpha$ in $w$. Then the following are equivalent: $\#_b(m)/m \to d$ as
$m \to \infty$; $\#_a(m)/m \to 1 - d$; $p_b(n)/n \to 1/d$ as $n \to \infty$;
$p_a(n)/n \to 1/(1 - d)$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 30
(`jis-2025-25.1.5-thm-30`). -/
public theorem_wanted letter_frequency_tfae {w : ℕ → Bool} (hw : BothLettersInfinite w) {d : ℝ}
    (hd₀ : 0 < d) (hd₁ : d < 1) :
    [Tendsto (fun m : ℕ => (letterCount w false m : ℝ) / m) atTop (𝓝 d),
      Tendsto (fun m : ℕ => (letterCount w true m : ℝ) / m) atTop (𝓝 (1 - d)),
      Tendsto (fun n : ℕ => (letterPosition w false n : ℝ) / n) atTop (𝓝 (1 / d)),
      Tendsto (fun n : ℕ => (letterPosition w true n : ℝ) / n) atTop (𝓝 (1 / (1 - d)))].TFAE

open Filter Topology in
/-- **The frequency of $b$ from the growth of the relative position.** Let $w$ be an infinite
binary word in which both letters $a$ and $b$ occur infinitely often, let $r$ be its relative
position function, and suppose that $r(n)/n$ converges to $L$ in the extended real line
$[-\infty, \infty]$. Let $\#_b(m)$ be the number of letters $b$ among the first $m$ letters of
$w$. Then $\#_b(m)/m$ converges, and its limit, the frequency of $b$ in $w$, is $0$ if
$L = \infty$, $1$ if $L = -\infty$, $1/2$ if $L = 0$, and
$(2 + L - \sqrt{4 + L^2})/(2L)$ if $L$ is a nonzero real number.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 33
(`jis-2025-25.1.5-prop-33`). -/
public theorem_wanted frequency_of_tendsto_relativePosition_div {w : ℕ → Bool}
    (hw : BothLettersInfinite w) {L : EReal}
    (hL : Tendsto (fun n : ℕ => (((relativePosition w n : ℝ) / n : ℝ) : EReal)) atTop (𝓝 L)) :
    let freqB := fun m : ℕ => (letterCount w false m : ℝ) / m
    (L = ⊤ → Tendsto freqB atTop (𝓝 0)) ∧ (L = ⊥ → Tendsto freqB atTop (𝓝 1)) ∧
      (L = 0 → Tendsto freqB atTop (𝓝 (1 / 2))) ∧
      ∀ x : ℝ, L = x → x ≠ 0 →
        Tendsto freqB atTop (𝓝 ((2 + x - Real.sqrt (4 + x ^ 2)) / (2 * x)))

open Filter Topology in
/-- **Mean values of the position functions.** Let $w$ be an infinite word over $\{a, b\}$ in
which both letters occur infinitely often, with letter position functions $p_a$, $p_b$ and
relative position function $r$, and consider the sequences $r(n)/n$, $p_b(n)/n$ and $p_a(n)/n$
in the extended reals $[-\infty, \infty]$. If one of the three sequences converges, then so do
the other two. If $p_b(n)/n \to p$ and $p_a(n)/n \to q$, then $1/p + 1/q = 1$, where
$1/\infty = 0$. If $r(n)/n \to x$ with $x$ real, then
$p_b(n)/n \to (2 + x + \sqrt{4 + x^2})/2$ and $p_a(n)/n \to (2 - x + \sqrt{4 + x^2})/2$. If
$r(n)/n \to \infty$, then $p_b(n)/n \to \infty$ and $p_a(n)/n \to 1$; if $r(n)/n \to -\infty$,
then $p_b(n)/n \to 1$ and $p_a(n)/n \to \infty$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 34
(`jis-2025-25.1.5-thm-34`). -/
public theorem_wanted relativePosition_letterPosition_mean_values {w : ℕ → Bool}
    (hw : BothLettersInfinite w) :
    let R := fun n : ℕ => (((relativePosition w n : ℝ) / n : ℝ) : EReal)
    let P := fun n : ℕ => (((letterPosition w false n : ℝ) / n : ℝ) : EReal)
    let Q := fun n : ℕ => (((letterPosition w true n : ℝ) / n : ℝ) : EReal)
    ((∃ x, Tendsto R atTop (𝓝 x)) ↔ ∃ y, Tendsto P atTop (𝓝 y)) ∧
      ((∃ x, Tendsto R atTop (𝓝 x)) ↔ ∃ z, Tendsto Q atTop (𝓝 z)) ∧
      (∀ y z, Tendsto P atTop (𝓝 y) → Tendsto Q atTop (𝓝 z) → y⁻¹ + z⁻¹ = 1) ∧
      (∀ x : ℝ, Tendsto R atTop (𝓝 x) →
        Tendsto P atTop (𝓝 (((2 + x + Real.sqrt (4 + x ^ 2)) / 2 : ℝ) : EReal)) ∧
          Tendsto Q atTop (𝓝 (((2 - x + Real.sqrt (4 + x ^ 2)) / 2 : ℝ) : EReal))) ∧
      (Tendsto R atTop (𝓝 ⊤) → Tendsto P atTop (𝓝 ⊤) ∧ Tendsto Q atTop (𝓝 1)) ∧
      (Tendsto R atTop (𝓝 ⊥) → Tendsto P atTop (𝓝 1) ∧ Tendsto Q atTop (𝓝 ⊤))

open Filter Topology in
/-- **Letter frequencies of a substitution image.** Let $\mu$ be a substitution sending the
letters $a$ and $b$ to nonempty finite words, extended to words by concatenation, such that both
$a$ and $b$ occur in $\mu(a)\mu(b)$. For a word $x$ and a letter $\alpha$ write $\#_\alpha(x, m)$
for the number of letters $\alpha$ among the first $m$ letters of $x$; for a finite word $u$
write $|u|$ for its length and $|u|_\alpha$ for the number of letters $\alpha$ in it. Let $w$ be
an infinite binary word in which both letters occur infinitely often, let $v = \mu(w)$, suppose
that $\#_a(w, m)/m \to f$ for a real number $f$, and let $L = |\mu(a)|\,f + |\mu(b)|\,(1 - f)$.
Then

$$\frac{\#_a(v, m)}{m} \to \frac{|\mu(a)|_a\,f + |\mu(b)|_a\,(1 - f)}{L}, \qquad
\frac{\#_b(v, m)}{m} \to \frac{|\mu(a)|_b\,f + |\mu(b)|_b\,(1 - f)}{L}.$$

The paper allows erasing substitutions, but then the formula fails: for $\mu(a)$ empty,
$\mu(b) = ab$ and $w$ with $b$ exactly at the perfect squares, the frequency of $a$ in $w$ is $1$
and $\mu(w) = (ab)^\omega$ has frequency of $a$ equal to $1/2$, while $L = 0$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 35
(`jis-2025-25.1.5-thm-35`). -/
public theorem_wanted frequency_substitution_image (μ : Bool → List Bool)
    (hμa : μ true ≠ []) (hμb : μ false ≠ [])
    (hab : true ∈ μ true ++ μ false ∧ false ∈ μ true ++ μ false)
    {w : ℕ → Bool} (hw : BothLettersInfinite w) {v : ℕ → Bool} (hv : IsSubstitutionImage μ w v)
    {f : ℝ} (hf : Tendsto (fun m : ℕ => (letterCount w true m : ℝ) / m) atTop (𝓝 f)) :
    let L := (μ true).length * f + (μ false).length * (1 - f)
    Tendsto (fun m : ℕ => (letterCount v true m : ℝ) / m) atTop
        (𝓝 (((μ true).count true * f + (μ false).count true * (1 - f)) / L)) ∧
      Tendsto (fun m : ℕ => (letterCount v false m : ℝ) / m) atTop
        (𝓝 (((μ true).count false * f + (μ false).count false * (1 - f)) / L))

open Polynomial in
/-- **Integer matrices with a metallic-mean eigenvector.** Let $k \ge 1$ be an integer, let
$\tau_k = (k + \sqrt{k^2 + 4})/2$ and $\tau_k' = (k - \sqrt{k^2 + 4})/2$, and let $M$ be a
$2 \times 2$ integer matrix. Then $(\tau_k, 1)^T$ is a right eigenvector of $M$ over $\mathbb{R}$
if and only if $M$ has rows $(km + n, m)$ and $(m, n)$ for some integers $m, n$. For such $M$ the
characteristic polynomial of $M$ is $(X - (n + m\tau_k))(X - (n + m\tau_k'))$, so the eigenvalues
of $M$ are $n + m\tau_k$ and $n + m\tau_k'$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 66
(`jis-2025-25.1.5-lem-66`). -/
public theorem_wanted metallic_eigenvector_iff (k : ℕ) (hk : 1 ≤ k)
    (M : Matrix (Fin 2) (Fin 2) ℤ) :
    let τ : ℝ := (k + Real.sqrt (k ^ 2 + 4)) / 2
    let τ' : ℝ := (k - Real.sqrt (k ^ 2 + 4)) / 2
    ((∃ c : ℝ, (M.map (Int.cast : ℤ → ℝ)).mulVec ![τ, 1] = c • ![τ, 1]) ↔
        ∃ m n : ℤ, M = !![k * m + n, m; m, n]) ∧
      ∀ m n : ℤ, M = !![k * m + n, m; m, n] →
        (M.map (Int.cast : ℤ → ℝ)).charpoly = (X - C ((n : ℝ) + m * τ)) * (X - C ((n : ℝ) + m * τ'))

/-- **Position differences in the Fibonacci word.** Let $f = \ell_0 \ell_1 \ell_2 \cdots =
abaab\cdots$ be the Fibonacci word, the infinite Fibonacci word with each $0$ written as $a$
and each $1$ as $b$. Let $p_a(n)$ and $p_b(n)$ be the positions (counted from $0$) of the
$n$-th $a$ and the $n$-th $b$ in $f$, and let $r(n) = p_b(n) - p_a(n)$. Then for every $n \ge 1$:
$p_a(n+1) - p_a(n)$ is $2$ if $\ell_{n-1} = a$ and $1$ if $\ell_{n-1} = b$;
$p_b(n+1) - p_b(n)$ is $3$ if $\ell_{n-1} = a$ and $2$ if $\ell_{n-1} = b$; and $r(n) = n$.

The printed statement gives the codings $(1, 2)$ and $(2, 3)$ instead, which are false:
$p_a$ takes the values $0, 2, 3, 5, \ldots$, so $p_a(2) - p_a(1) = 2$ while $f$ starts with
$a$. The codings above are the ones derived in the paper's proof.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 38
(`jis-2025-25.1.5-thm-38`). -/
public theorem_wanted fibonacciWord_letterPosition_diff :
    let f := (fun i => !fibInf i)
    (∀ n, 1 ≤ n → letterPosition f true (n + 1) - letterPosition f true n =
        if f (n - 1) then 2 else 1) ∧
      (∀ n, 1 ≤ n → letterPosition f false (n + 1) - letterPosition f false n =
        if f (n - 1) then 3 else 2) ∧
      ∀ n, 1 ≤ n → relativePosition f n = n

/-- **Relative position of the deleted Fibonacci word.** Let $f = abaababaabaab\cdots$ be the
Fibonacci word, the fixed point of $a \mapsto ab$, $b \mapsto a$. Let $D(f)$ be the word obtained
from $f$ by deleting its first $b$ and then the first $a$ of the result, and for an infinite
word $v$ over $\{a, b\}$ let $r_v(n) = p_b(n) - p_a(n)$, where $p_a(n)$ and $p_b(n)$ are the
positions of the $n$-th $a$ and the $n$-th $b$ in $v$. Then $r_{D(f)}(n) = n + 1$ for every
$n \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 43
(`jis-2025-25.1.5-thm-43`). -/
public theorem_wanted relativePosition_deletion_fibonacciWord (n : ℕ) (hn : 1 ≤ n) :
    relativePosition (deletion (fun i => !fibInf i)) n = n + 1

/-- **Relative position of iterated deletions of the Fibonacci word.** Let
$f = abaababaabaab\cdots$ be the Fibonacci word, the fixed point of $a \mapsto ab$,
$b \mapsto a$. Let $D$ be the operator on infinite words over $\{a, b\}$ that deletes the first
$b$ and then the first $a$ of the result, and for such a word $v$ let
$r_v(n) = p_b(n) - p_a(n)$, where $p_a(n)$ and $p_b(n)$ are the positions of the $n$-th $a$ and
the $n$-th $b$ in $v$. Then for every natural number $k$ there is an $N$ such that
$r_{D^k(f)}(n) = n + k$ for all $n > N$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 44
(`jis-2025-25.1.5-thm-44`). -/
public theorem_wanted relativePosition_deletion_iterate_fibonacciWord (k : ℕ) :
    ∃ N, ∀ n, N < n → relativePosition (deletion^[k] (fun i => !fibInf i)) n = n + k

/-- **The Fibonacci switch.** Let $f = abaab\cdots$ be the Fibonacci word, the infinite
Fibonacci word with each $0$ written as $a$ and each $1$ as $b$, and let $\mu$ be the
substitution $a \mapsto aab$, $b \mapsto ab$. Then $D(f)$ is the image $\mu(f)$ of $f$ under
$\mu$, where $D$ deletes the first $b$ and the first $a$ of a word.

In the paper's description, $\mu(f)$ is the word obtained from $f$ by replacing each level-2
supertile $aba$ by $aab$ and keeping each $ab$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 45
(`jis-2025-25.1.5-thm-45`). -/
public theorem_wanted fibonacci_switch :
    IsSubstitutionImage (fun x => if x then [true, true, false] else [true,
        false]) (fun i => !fibInf i)
      (deletion (fun i => !fibInf i))

/-- **Gap codings single out the Fibonacci word among words starting with $a$.** Let
$w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite binary word over the letters $a$ and $b$ in which
both letters occur infinitely often and $\ell_0 = a$. For a letter $\alpha$ let $p_\alpha(n)$ be
the position (counting from $0$) of the $n$-th occurrence of $\alpha$ in $w$ and
$\Delta p_\alpha(n) = p_\alpha(n+1) - p_\alpha(n)$. Call $\Delta p_a$ and $\Delta p_b$ codings of
$w$ if there are maps $\sigma_a, \sigma_b$ from $\{a, b\}$ to the natural numbers with
$\Delta p_a(n) = \sigma_a(\ell_{n-1})$ and $\Delta p_b(n) = \sigma_b(\ell_{n-1})$ for all
$n \ge 1$, and injective codings if moreover $\sigma_a$ and $\sigma_b$ are injective. Let
$f = abaab\cdots$ be the infinite Fibonacci word written with $a$ for $0$ and $b$ for $1$. Then
$\Delta p_a$ and $\Delta p_b$ are codings of $w$ if and only if $w = f$ or $w = (ab)^\omega$, and
they are injective codings of $w$ if and only if $w = f$.

The second part drops the paper's word "aperiodic": for $(ab)^\omega$ the sequences $\Delta p_a$
and $\Delta p_b$ are constant, so they are not injective codings, and the characterization holds
for every such $w$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 46
(`jis-2025-25.1.5-thm-46`). -/
public theorem_wanted letterPosition_diff_codings_iff_fibonacci {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    ((∃ σa σb : Bool → ℕ, ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
        w = (fun i => !fibInf i) ∨ w = fun i => decide (i % 2 = 0)) ∧
      ((∃ σa σb : Bool → ℕ, Function.Injective σa ∧ Function.Injective σb ∧
        ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
        w = (fun i => !fibInf i))

/-- **Gap codings single out the reflected Fibonacci word among words starting with $b$.** Let
$w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite binary word over the letters $a$ and $b$ in which
both letters occur infinitely often and $\ell_0 = b$. For a letter $\alpha$ let $p_\alpha(n)$ be
the position (counting from $0$) of the $n$-th occurrence of $\alpha$ in $w$ and
$\Delta p_\alpha(n) = p_\alpha(n+1) - p_\alpha(n)$. Call $\Delta p_a$ and $\Delta p_b$ codings of
$w$ if there are maps $\sigma_a, \sigma_b$ from $\{a, b\}$ to the natural numbers with
$\Delta p_a(n) = \sigma_a(\ell_{n-1})$ and $\Delta p_b(n) = \sigma_b(\ell_{n-1})$ for all
$n \ge 1$, and injective codings if moreover $\sigma_a$ and $\sigma_b$ are injective. Let
$\bar f = babba\cdots$ be the infinite Fibonacci word written with $b$ for $0$ and $a$ for $1$
(the Fibonacci word $f = abaab\cdots$ with $a$ and $b$ exchanged). Then $\Delta p_a$ and
$\Delta p_b$ are codings of $w$ if and only if $w = \bar f$ or $w = (ba)^\omega$, and they are
injective codings of $w$ if and only if $w = \bar f$.

The second part drops the paper's word "aperiodic": for $(ba)^\omega$ the sequences $\Delta p_a$
and $\Delta p_b$ are constant, so they are not injective codings.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 48
(`jis-2025-25.1.5-cor-48`). -/
public theorem_wanted letterPosition_diff_codings_iff_fibonacci_reflect {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = false) :
    ((∃ σa σb : Bool → ℕ, ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
        w = fibInf ∨ w = fun i => decide (i % 2 = 1)) ∧
      ((∃ σa σb : Bool → ℕ, Function.Injective σa ∧ Function.Injective σb ∧
        ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
        w = fibInf)

/-- **The Fibonacci word and its reflection are the words isomorphic to their gap sequences.**
Let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite binary word over the letters $a$ and $b$ in
which both letters occur infinitely often. For a letter $\alpha$ let $p_\alpha(n)$ be
the position (counting from $0$) of the $n$-th occurrence of $\alpha$ in $w$ and
$\Delta p_\alpha(n) = p_\alpha(n+1) - p_\alpha(n)$. Call $\Delta p_a$ and $\Delta p_b$ codings of
$w$ if there are maps $\sigma_a, \sigma_b$ from $\{a, b\}$ to the natural numbers with
$\Delta p_a(n) = \sigma_a(\ell_{n-1})$ and $\Delta p_b(n) = \sigma_b(\ell_{n-1})$ for all
$n \ge 1$, and injective codings if moreover $\sigma_a$ and $\sigma_b$ are injective. Let
$f = abaab\cdots$ be the infinite Fibonacci word written with $a$ for $0$ and $b$ for $1$, and
$\bar f$ the word $f$ with $a$ and $b$ exchanged. Then $\Delta p_a$ and $\Delta p_b$ are injective
codings of $w$ if and only if $w = f$ or $w = \bar f$.

The paper's word "aperiodic" is dropped, as in Theorem 46 and Corollary 48.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 49
(`jis-2025-25.1.5-cor-49`). -/
public theorem_wanted letterPosition_diff_isomorphic_iff_fibonacci {w : ℕ → Bool}
    (hw : BothLettersInfinite w) :
    (∃ σa σb : Bool → ℕ, Function.Injective σa ∧ Function.Injective σb ∧
        ∀ n, 1 ≤ n →
        letterPosition w true (n + 1) - letterPosition w true n = σa (w (n - 1)) ∧
          letterPosition w false (n + 1) - letterPosition w false n = σb (w (n - 1))) ↔
      w = (fun i => !fibInf i) ∨ w = fibInf

/-- **The iccanobiF iterates approximate $abf$ and $baf$.** Let $f = abaab\cdots$ be the
Fibonacci word, the infinite Fibonacci word with each $0$ written as $a$ and each $1$ as $b$,
and let $\varrho_F'$ be the iccanobiF substitution $a \mapsto ba$, $b \mapsto a$, extended to
finite words by concatenation. For every $n \ge 0$, the word $(\varrho_F')^{2n}(a)$ is a prefix
of the infinite word $abf$ and $(\varrho_F')^{2n}(b)$ is a prefix of $baf$, and for every $N$
there is an $n$ such that $(\varrho_F')^{2n}(a)$ and $(\varrho_F')^{2n}(b)$ both have length at
least $N$. Moreover, the relative position functions of $abf$ and $baf$ satisfy
$r_{abf}(1) = 1$, $r_{baf}(1) = -1$ and $r_{abf}(n) = r_{baf}(n) = n - 1$ for every $n \ge 2$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 53
(`jis-2025-25.1.5-thm-53`). -/
public theorem_wanted iccanobiF_fixed_points :
    let f := (fun i => !fibInf i)
    let it := fun (n : ℕ) (x : Bool) => (fun u : List Bool => u.flatMap fun x => if x then [false,
        true] else [true])^[2 * n] [x]
    (∀ n i, i < (it n true).length → (it n true).getD i false = ([true, false] ++ₛ f) i) ∧
      (∀ n i, i < (it n false).length → (it n false).getD i false = ([false, true] ++ₛ f) i) ∧
      (∀ N, ∃ n, N ≤ (it n true).length ∧ N ≤ (it n false).length) ∧
      relativePosition ([true, false] ++ₛ f) 1 = 1 ∧
      relativePosition ([false, true] ++ₛ f) 1 = -1 ∧
      ∀ n, 2 ≤ n → relativePosition ([true, false] ++ₛ f) n = n - 1 ∧
        relativePosition ([false, true] ++ₛ f) n = n - 1

/-- **Relative positions of the Fibonacci word with an equilibrious word prepended.** Let
$f = abaab\cdots$ be the infinite Fibonacci word with $0$ read as $a$ and $1$ as $b$, let $j \ge 0$,
let $u$ be a finite word over $\{a, b\}$ of length $2j$ in which $a$ and $b$ occur equally often
(an equilibrious word), and let $r$ be the relative position function of the concatenation $uf$.
Then $r(n) = n - j$ for all $n > j$. If moreover $u = (ab)^j$, then $r(n) = 1$ for all
$1 \le n \le j$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 55
(`jis-2025-25.1.5-thm-55`). -/
public theorem_wanted relativePosition_prepend_equilibrious_fibonacci (u : List Bool) {j : ℕ}
    (hu : u.length = 2 * j) (hequi : IsEquilibriousWord (u.map fun x => if x then 0 else 1)) :
    (∀ n, j < n → relativePosition (u ++ₛ (fun i => !fibInf i)) n = n - j) ∧
      (u = (List.replicate j [true, false]).flatten →
        ∀ n, 1 ≤ n → n ≤ j → relativePosition (u ++ₛ (fun i => !fibInf i)) n = 1)

/-- **Position identities for the extended Pisa substitution.** Let $k \ge 1$, $l \ge 0$ and
$m \ge 1$ be natural numbers, let $\sigma$ be the substitution $a \mapsto a^k b a^l$,
$b \mapsto a^m$, and let $w$ be a one-sided fixed point of $\sigma$ (so $\sigma(w) = w$) that
begins with $a$. For an infinite word $v$ over $\{a, b\}$ and $n \ge 1$, let $p_a(n)$ and
$p_b(n)$ be the positions (counted from $0$) of the $n$-th $a$ and the $n$-th $b$ in $v$, and let
$r(n) = p_b(n) - p_a(n)$. Then for $v = w$ and every $n \ge 1$,
$$p_b(n) = m\,p_a(n) + (k + l + 1 - m)n + m - l - 1$$
and
$$r(n) = (m - 1)p_a(n) + (k + l + 1 - m)n + m - l - 1.$$
Moreover, every infinite word $v$ over $\{a, b\}$ in which both letters occur infinitely often
and whose functions $r$ and $p_a$ satisfy the second identity for all $n \ge 1$ equals $w$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 57
(`jis-2025-25.1.5-thm-57`). -/
public theorem_wanted pisa_letterPosition_identity (k l m : ℕ) (hk : 1 ≤ k) (hm : 1 ≤ m)
    {w : ℕ → Bool} (hfix : IsSubstitutionImage (fun x : Bool => if x then List.replicate k true ++
        [false] ++ List.replicate l true else List.replicate m true) w w)
    (h₀ : w 0 = true) :
    (∀ n, 1 ≤ n → (letterPosition w false n : ℤ) =
        m * letterPosition w true n + (k + l + 1 - m : ℤ) * n + m - l - 1) ∧
      (∀ n, 1 ≤ n → relativePosition w n =
        (m - 1 : ℤ) * letterPosition w true n + (k + l + 1 - m : ℤ) * n + m - l - 1) ∧
      ∀ w' : ℕ → Bool, BothLettersInfinite w' →
        (∀ n, 1 ≤ n → relativePosition w' n =
          (m - 1 : ℤ) * letterPosition w' true n + (k + l + 1 - m : ℤ) * n + m - l - 1) →
        w' = w

open Filter Topology in
/-- **Letter frequencies and mean positions of primitive fixed points.** Let $\varrho$ be a
substitution on the letters $a, b$ with substitution matrix $M$, where $M_{11} = |\varrho(a)|_a$,
$M_{12} = |\varrho(b)|_a$, $M_{21} = |\varrho(a)|_b$ and $M_{22} = |\varrho(b)|_b$ ($|v|_x$ is
the number of letters $x$ in $v$). Suppose $\varrho$ is primitive (some power of $M$ has all
entries positive), and let $u > 0$ and $\lambda$ be real numbers with
$M (u, 1)^T = \lambda (u, 1)^T$. Let $w$ be a one-sided fixed point of $\varrho$ (so
$\varrho(w) = w$) in which both letters occur infinitely often. Let $N_a(n)$ and $N_b(n)$ be the
numbers of letters $a$ and $b$ among the first $n$ letters of $w$, let $p_a(n)$ and $p_b(n)$ be
the positions of the $n$-th $a$ and the $n$-th $b$ in $w$, and let $r(n) = p_b(n) - p_a(n)$.
Then, as $n \to \infty$, $N_a(n)/n \to u/(u + 1)$, $N_b(n)/n \to 1/(u + 1)$,
$p_a(n)/n \to 1 + 1/u$, $p_b(n)/n \to u + 1$ and $r(n)/n \to u - 1/u$, and each of these five
limits lies in the subfield $\mathbb{Q}(\lambda)$ of $\mathbb{R}$.

A positive eigenvector of a primitive matrix belongs to its Perron–Frobenius eigenvalue, so
$(u, 1)^T$ is a right Perron–Frobenius eigenvector of $M$ and $\lambda$ is its eigenvalue.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 32
(`jis-2025-25.1.5-lem-32`). -/
public theorem_wanted primitive_fixed_point_mean_values (ϱ : Bool → List Bool) (hprim : ∃ p, ∀ i j,
    0 < ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
    (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) ^ p) i j)
    {u c : ℝ} (hu : 0 < u)
        (heig : ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
        (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![u, 1] =
        c • ![u, 1])
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (hfix : IsSubstitutionImage ϱ w w) :
    Tendsto (fun n : ℕ => (letterCount w true n : ℝ) / n) atTop (𝓝 (u / (u + 1))) ∧
      Tendsto (fun n : ℕ => (letterCount w false n : ℝ) / n) atTop (𝓝 (1 / (u + 1))) ∧
      Tendsto (fun n : ℕ => (letterPosition w true n : ℝ) / n) atTop (𝓝 (1 + 1 / u)) ∧
      Tendsto (fun n : ℕ => (letterPosition w false n : ℝ) / n) atTop (𝓝 (u + 1)) ∧
      Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (u - 1 / u)) ∧
      ∀ x ∈ ({u / (u + 1), 1 / (u + 1), 1 + 1 / u, u + 1, u - 1 / u} : Set ℝ),
        x ∈ IntermediateField.adjoin ℚ {c}

open Filter Topology in
/-- **Relative position asymptotic to $n$ and the golden ratio.** Let $\varrho$ be a substitution
on the letters $a, b$ with substitution matrix $M$, where $M_{11} = |\varrho(a)|_a$,
$M_{12} = |\varrho(b)|_a$, $M_{21} = |\varrho(a)|_b$ and $M_{22} = |\varrho(b)|_b$ ($|v|_x$ is
the number of letters $x$ in $v$), and suppose $\varrho$ is primitive (some power of $M$ has all
entries positive). Let $w$ be a one-sided fixed point of $\varrho$ (so $\varrho(w) = w$) in which
both letters occur infinitely often, let $p_a(n)$ and $p_b(n)$ be the positions of the $n$-th $a$
and the $n$-th $b$ in $w$, and let $r(n) = p_b(n) - p_a(n)$. Then $r(n)/n \to 1$ as
$n \to \infty$ if and only if $(\varphi, 1)^T$ is an eigenvector of $M$, where
$\varphi = (1 + \sqrt 5)/2$ is the golden ratio.

Since $(\varphi, 1)^T$ is positive, this is the same as being a right Perron–Frobenius
eigenvector of $M$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Lemma 41
(`jis-2025-25.1.5-lem-41`). -/
public theorem_wanted primitive_relativePosition_div_tendsto_one_iff (ϱ : Bool → List Bool)
    (hprim : ∃ p, ∀ i j, 0 < ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
        (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) ^ p) i j)
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (hfix : IsSubstitutionImage ϱ w w) :
    Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 1) ↔
      ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
          (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec
          ![Real.goldenRatio, 1] = c • ![Real.goldenRatio, 1]

open Filter Topology in
/-- **Frequency and position criteria for an eigenvector of a primitive substitution.** Let
$j \ge 1$ and $m \ge 1$ be natural numbers with $m \ne j + 1$, and let
$\tau = (j + \sqrt{j^2 + 4m})/2$. Let
$\varrho$ be a substitution on the letters $a, b$ with substitution matrix $M$, where
$M_{11} = |\varrho(a)|_a$, $M_{12} = |\varrho(b)|_a$, $M_{21} = |\varrho(a)|_b$ and
$M_{22} = |\varrho(b)|_b$ ($|v|_x$ is the number of letters $x$ in $v$). Suppose $\varrho$ is
primitive (some power of $M$ has all entries positive), and let $w$ be a one-sided fixed point
of $\varrho$ (so $\varrho(w) = w$). Let $N_a(n)$ and $N_b(n)$ be the numbers of letters $a$ and
$b$ among the first $n$ letters of $w$, let $p_a(n)$ and $p_b(n)$ be the positions (counted from
$0$) of the $n$-th $a$ and the $n$-th $b$ in $w$, and let $r(n) = p_b(n) - p_a(n)$. Then the
following are equivalent, all limits taken as $n \to \infty$:
(i) $N_a(n)/n \to (\tau - m)/(j + 1 - m)$;
(ii) $N_b(n)/n \to (j + 1 - \tau)/(j + 1 - m)$;
(iii) $p_a(n)/n \to 1 + (\tau - j)/m$;
(iv) $p_b(n)/n \to \tau + 1$;
(v) $r(n)/n \to ((m - 1)\tau + j)/m$;
(vi) $p_a(n)/n$ converges to some real number $q$ and $r(n)/n \to (m - 1)q + j + 1 - m$;
(vii) $(\tau, 1)^T$ is an eigenvector of $M$.

The hypothesis $m \ne j + 1$ is added to the paper's statement: for $m = j + 1$ one has
$\tau = j + 1 = m$, so (i) and (ii) read $0/0$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 62
(`jis-2025-25.1.5-prop-62`). -/
public theorem_wanted pisa_frequency_tfae (j m : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m) (hjm : m ≠ j + 1)
    (ϱ : Bool → List Bool) (hprim : ∃ p, ∀ i j, 0 <
        ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
        (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) ^ p) i j)
    {w : ℕ → Bool} (hfix : IsSubstitutionImage ϱ w w) :
    let τ : ℝ := (j + Real.sqrt (j ^ 2 + 4 * m)) / 2
    [Tendsto (fun n : ℕ => (letterCount w true n : ℝ) / n) atTop (𝓝 ((τ - m) / (j + 1 - m))),
      Tendsto (fun n : ℕ => (letterCount w false n : ℝ) / n) atTop (𝓝 ((j + 1 - τ) / (j + 1 - m))),
      Tendsto (fun n : ℕ => (letterPosition w true n : ℝ) / n) atTop (𝓝 (1 + (τ - j) / m)),
      Tendsto (fun n : ℕ => (letterPosition w false n : ℝ) / n) atTop (𝓝 (τ + 1)),
      Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (((m - 1) * τ + j) / m)),
      ∃ q : ℝ, Tendsto (fun n : ℕ => (letterPosition w true n : ℝ) / n) atTop (𝓝 q) ∧
        Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 ((m - 1) * q + (j + 1 - m))),
      ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
          (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![τ,
          1] = c • ![τ, 1]].TFAE

/-- **Words with linear relative position function.** For integers $k, l, m \ge 0$ write
$\sigma_{k,l,m}$ for the substitution $a \mapsto a^k b a^l$, $b \mapsto a^m$, and for a binary
word $v$ let $r_v(n) = p_{b,v}(n) - p_{a,v}(n)$, where $p_{\alpha,v}(n)$ is the position (counted
from $0$) of the $n$-th occurrence of the letter $\alpha$ in $v$.
(a) For every $j \ge 1$, the word $v = (a^j b^j)^\omega$ has $r_v(n) = j$ for all $n \ge 1$.
(b) For integers $0 \le j < k$, every fixed point $w$ of $\sigma_{k-j,j,1}$ that starts with $a$
has $r_w(n) = kn - j$ for all $n \ge 1$.
(c) For every $k \ge 1$, if $w$ is a fixed point of $\sigma_{1,k-1,1}$ that starts with $a$ and
$D(w)$ is the word $w$ with its first $a$ and its first $b$ deleted, then $r_{D(w)}(n) = kn + 1$
for all $n \ge 1$.

The paper writes $k \ge 0$ in (c), but $\sigma_{1,k-1,1}$ needs $k \ge 1$.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 64
(`jis-2025-25.1.5-thm-64`). -/
public theorem_wanted linear_relativePosition_examples :
    (∀ j, 1 ≤ j → ∀ n, 1 ≤ n →
        relativePosition (fun i => decide (i % (2 * j) < j)) n = j) ∧
      (∀ k j : ℕ, j + 1 ≤ k → ∀ w : ℕ → Bool,
        IsSubstitutionImage (fun x : Bool => if x then List.replicate (k - j) true ++ [false] ++
            List.replicate j true else List.replicate 1 true) w w → w 0 = true →
        ∀ n, 1 ≤ n → relativePosition w n = k * n - j) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ w : ℕ → Bool,
        IsSubstitutionImage (fun x : Bool => if x then List.replicate 1 true ++ [false] ++
            List.replicate (k - 1) true else List.replicate 1 true) w w → w 0 = true →
        ∀ n, 1 ≤ n → relativePosition (deletion w) n = k * n + 1

/-- **Eventually linear relative position functions with positive slope.** Let $k \ge 1$, $q$
and $c$ be integers with $0 \le c \le k - 1$, and put $j = qk - c$. Let $w$ be an infinite word
over $\{a, b\}$ that starts with $a$ and is a fixed point of the Pisa substitution
$\sigma_{k-c,c,1}$, given by $a \mapsto a^{k-c} b a^c$ and $b \mapsto a$. For an infinite word $v$
write $r_v$ for its relative position function, and let $D$ be the deletion operator, which
deletes the first $b$ and then the first $a$ of a word. (a) If $q \ge 0$, then
$r_{D^q(w)}(n) = kn + j$ for all sufficiently large $n$. (b) If $q < 0$, then for every finite
word $u$ over $\{a, b\}$ of length $-2q$ in which $a$ and $b$ occur equally often (an
equilibrious word), $r_{uw}(n) = kn + j$ for all sufficiently large $n$.

The paper takes $w$ to be the fixed point of $\sigma_{1,k-1,1}$ for every $c$, which is false
unless $c = k - 1$: for $k = 2$ and $j = 2$ ($q = 1$, $c = 0$) that fixed point has
$r_{D(w)}(n) = 2n + 1$ (Theorem 64(c)), not $2n + 2$. The substitution $\sigma_{k-c,c,1}$ is the
one Theorem 64(b) provides ($r_w(n) = kn - c$), from which $D$ (with $r_{D(w)}(n) = r_w(n+1)$
for words that start with $ab$ or $ba$ and contain both letters infinitely often) and
equilibrious prefixes (Lemma 22) shift the index by $q$, giving every progression $kn + j$ with
$k \ge 1$; for $c = k - 1$ it is the paper's $\sigma_{1,k-1,1}$. The paper writes $k \ge 0$, but
the range $0 \le c \le k - 1$ is then empty.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Proposition 65
(`jis-2025-25.1.5-prop-65`). -/
public theorem_wanted relativePosition_eventually_eq_linear (k r : ℕ) (hk : 1 ≤ k) (hr : r < k)
    (q j : ℤ) (hj : j = q * k - r) (w : ℕ → Bool)
    (hw : IsSubstitutionImage (fun x : Bool => if x then List.replicate (k - r) true ++ [false] ++
        List.replicate r true else List.replicate 1 true) w w)
    (hw0 : w 0 = true) :
    (0 ≤ q → ∀ᶠ n in Filter.atTop, relativePosition (deletion^[q.toNat] w) n = k * n + j) ∧
      (q < 0 → ∀ u : List Bool, u.length = 2 * (-q).toNat →
        IsEquilibriousWord (u.map fun x => if x then 0 else 1) →
          ∀ᶠ n in Filter.atTop, relativePosition (u ++ₛ w) n = k * n + j)

open Filter Topology in
/-- **Primitive substitutions with asymptotically linear relative position.** Let $\varrho$ be a
substitution on the letters $a, b$ with substitution matrix $M$, where $M_{11} = |\varrho(a)|_a$,
$M_{12} = |\varrho(b)|_a$, $M_{21} = |\varrho(a)|_b$ and $M_{22} = |\varrho(b)|_b$ ($|v|_x$ is
the number of letters $x$ in $v$). Suppose $\varrho$ is primitive (some power of $M$ has all
entries positive), and let $w$ be a one-sided fixed point of $\varrho$ (so $\varrho(w) = w$) in
which both letters occur infinitely often. Let $p_a(n)$ and $p_b(n)$ be the positions of the
$n$-th $a$ and the $n$-th $b$ in $w$, let $r(n) = p_b(n) - p_a(n)$, let $k \ge 1$ be a natural
number and let $\tau = (k + \sqrt{k^2 + 4})/2$. With all limits taken as $n \to \infty$:
(a) the following are equivalent: $r(n)/n \to k$; $(\tau, 1)^T$ is an eigenvector of $M$;
$M$ has rows $(km + t, m)$ and $(m, t)$ for some natural numbers $m \ge 1$ and $t \ge 0$.
(b) the following are equivalent: $r(n)/n \to -k$; $(1, \tau)^T$ is an eigenvector of $M$;
$M$ has rows $(t, m)$ and $(m, km + t)$ for some natural numbers $m \ge 1$ and $t \ge 0$.
(c) the following are equivalent: $r(n)/n \to 0$; $(1, 1)^T$ is an eigenvector of $M$;
$M_{11} + M_{12} = M_{21} + M_{22}$.

These vectors are positive, so being an eigenvector of the primitive matrix $M$ is the same as
being its right Perron–Frobenius eigenvector.

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 67
(`jis-2025-25.1.5-thm-67`). -/
public theorem_wanted primitive_asymptotically_linear_classification (ϱ : Bool → List Bool)
    (hprim : ∃ p, ∀ i j, 0 < ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
        (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) ^ p) i j)
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (hfix : IsSubstitutionImage ϱ w w)
    (k : ℕ) (hk : 1 ≤ k) :
    let τ : ℝ := (k + Real.sqrt (k ^ 2 + 4)) / 2
    [Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (k : ℝ)),
        ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![τ,
            1] = c • ![τ, 1],
        ∃ m n : ℕ, 1 ≤ m ∧ (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) = !![k * m + n, m; m, n]].TFAE ∧
      [Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 (-(k : ℝ))),
        ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![1,
            τ] = c • ![1, τ],
        ∃ m n : ℕ, 1 ≤ m ∧ (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) = !![n, m; m, k * m + n]].TFAE ∧
      [Tendsto (fun n : ℕ => (relativePosition w n : ℝ) / n) atTop (𝓝 0),
        ∃ c : ℝ, ((!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ).map (Nat.cast : ℕ → ℝ)).mulVec ![1,
            1] = c • ![1, 1],
        (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) 0 0 +
            (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) 0 1 =
            (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) 1 0 +
            (!![(ϱ true).count true, (ϱ false).count true; (ϱ true).count false,
            (ϱ false).count false] : Matrix (Fin 2) (Fin 2) ℕ) 1 1].TFAE

/-- **Characterization of the Thue–Morse word by its relative positions.** Let
$w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite word over $\{a, b\}$ that starts with $a$ and in
which both letters occur infinitely often, and let $r$ be its relative position function. Then
$r(n) = 1$ when $\ell_{n-1} = a$ and $r(n) = -1$ when $\ell_{n-1} = b$, for all $n \ge 1$, if and
only if $w$ is the Thue–Morse word $t = abbabaab\cdots$ (the Thue–Morse sequence with $0$ read as
$a$ and $1$ as $b$).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 70
(`jis-2025-25.1.5-thm-70`). -/
public theorem_wanted relativePosition_self_coding_iff_thueMorse {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    (∀ n, 1 ≤ n → relativePosition w n = if w (n - 1) then 1 else -1) ↔ w = (fun i => !thueMorse i)

/-- **Characterization of the Thue–Morse word among words starting with $abba$.** Let
$w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite word over $\{a, b\}$ that begins with $abba$ and in
which both letters occur infinitely often, and let $r$ be its relative position function. Then
there is an injective map $\sigma \colon \{a, b\} \to \mathbb{Z}$ with $r(n) = \sigma(\ell_{n-1})$
for all $n \ge 1$ if and only if $w$ is the Thue–Morse word $t = abbabaab\cdots$ (the Thue–Morse
sequence with $0$ read as $a$ and $1$ as $b$).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Corollary 71
(`jis-2025-25.1.5-cor-71`). -/
public theorem_wanted relativePosition_isomorphic_iff_thueMorse {w : ℕ → Bool}
    (hw : BothLettersInfinite w) (h₀ : w 0 = true) (h₁ : w 1 = false) (h₂ : w 2 = false)
    (h₃ : w 3 = true) :
    (∃ σ : Bool → ℤ, Function.Injective σ ∧ ∀ n, 1 ≤ n → relativePosition w n = σ (w (n - 1))) ↔
      w = (fun i => !thueMorse i)

/-- **Characterization of the cloned Thue–Morse words by their relative positions.** Let $k > 1$
be an integer, let $w = \ell_0 \ell_1 \ell_2 \cdots$ be an infinite word over $\{a, b\}$ that starts
with $a$ and in which both letters occur infinitely often, and let $r$ be its relative position
function. Then $r(n) = k$ when $\ell_{n-1} = a$ and $r(n) = -k$ when $\ell_{n-1} = b$, for all
$n \ge 1$, if and only if $w = \varphi_k(t)$, the word whose letter at position $i$ is
$t_{\lfloor i/k \rfloor}$, where $t = abbabaab\cdots$ is the Thue–Morse word (the Thue–Morse
sequence with $0$ read as $a$ and $1$ as $b$).

Source: Michael Coons, Christopher Ramsey and Nicolae Strungaru, *Relative Position in
Binary Substitutions*, Journal of Integer Sequences 28 (2025), Article 25.1.5, Theorem 72
(`jis-2025-25.1.5-thm-72`). -/
public theorem_wanted relativePosition_self_coding_iff_clone_thueMorse (k : ℕ) (hk : 1 < k)
    {w : ℕ → Bool} (hw : BothLettersInfinite w) (h₀ : w 0 = true) :
    (∀ n, 1 ≤ n → relativePosition w n = if w (n - 1) then (k : ℤ) else -k) ↔
      w = fun i => !thueMorse (i / k)

end

end MetaMathlibExt
