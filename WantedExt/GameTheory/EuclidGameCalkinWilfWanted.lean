/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.GameTheory.EuclidGameCalkinWilf
public import MathlibExt.GameTheory.SmithRemoteness

namespace MetaMathlibExt

@[expose] public section

/-- **Number of P-positions of Euclid in a row of the Calkin–Wilf tree.** Let $L_k$ be the
number of P-positions of Euclid in row $k$ of the Calkin–Wilf tree. Then $L_0 = 1$, $L_1 = 0$,
$L_{k+2} = L_{k+1} + 2L_k$ for every $k$, and $3L_k = 2^k + 2(-1)^k$ for every $k$, that is,
$L_k = 2^k/3 + 2(-1)^k/3$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 4.6. -/
public theorem_wanted count_euclidPPosition_calkinWilfRow :
    (calkinWilfRow 0).countP (fun p => euclidPPosition p.1 p.2) = 1 ∧
      (calkinWilfRow 1).countP (fun p => euclidPPosition p.1 p.2) = 0 ∧
      (∀ k, (calkinWilfRow (k + 2)).countP (fun p => euclidPPosition p.1 p.2) =
        (calkinWilfRow (k + 1)).countP (fun p => euclidPPosition p.1 p.2) +
          2 * (calkinWilfRow k).countP (fun p => euclidPPosition p.1 p.2)) ∧
      ∀ k, 3 * ((calkinWilfRow k).countP (fun p => euclidPPosition p.1 p.2) : ℤ) =
        2 ^ k + 2 * (-1) ^ k

/-- **The Fibonacci arches.** Let $F_j$ be the Fibonacci numbers with $F_0 = F_1 = 1$ and
$F_{j+2} = F_{j+1} + F_j$. Call a pair $(a, b)$ of natural numbers a P-position when the Euclid
P-position test returns true at $(a, b)$, read it as the vertex $a/b$ of the Calkin–Wilf tree, and
let $s(a/b) = a/(a+b)$ be its son and $d(a/b) = (a+b)/b$ its daughter; write $s^k$ and $d^k$ for
the $k$-fold iterates. Let $n \ge 1$ and $k \ge 0$, and let $V = F_{2n-1}/F_{2n-2}$. Then $V$ is a
P-position, its son's daughter $d(s(V))$ is $F_{2n+1}/F_{2n}$, and its daughter's son $s(d(V))$
is $F_{2n}/(F_{2n} + F_{2n-2})$. The vertex $L = d(s^k((F_{2n+1} - F_{2n})/F_{2n}))$ is a
P-position whose numerator is $F_{2n+1} + kF_{2n-1}$ and whose denominator is
$F_{2n+1} + (k-1)F_{2n-1}$, and the vertex $R = s(d^k(F_{2n}/F_{2n-2}))$ is the P-position
$(F_{2n} + kF_{2n-2})/(F_{2n} + (k+1)F_{2n-2})$.

Here $L$ and $R$ are level $k$ (level $0$ the top) of the left and right branches of the arch
topped by $d(s(V))$ and $s(d(V))$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 5.2. -/
public theorem_wanted fibonacci_arch_positions (n k : ℕ) (hn : 1 ≤ n) :
    let F : ℕ → ℕ := fun j => Nat.fib (j + 1)
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let V := (F (2 * n - 1), F (2 * n - 2))
    let L := t (s^[k] (F (2 * n + 1) - F (2 * n), F (2 * n)))
    let R := s (t^[k] (F (2 * n), F (2 * n - 2)))
    euclidPPosition V.1 V.2 = true ∧ t (s V) = (F (2 * n + 1), F (2 * n)) ∧
      s (t V) = (F (2 * n), F (2 * n) + F (2 * n - 2)) ∧
      ((L.1 : ℤ) = F (2 * n + 1) + k * F (2 * n - 1) ∧
        (L.2 : ℤ) = F (2 * n + 1) + (k - 1) * F (2 * n - 1) ∧ euclidPPosition L.1 L.2 = true) ∧
      (R = (F (2 * n) + k * F (2 * n - 2), F (2 * n) + (k + 1) * F (2 * n - 2)) ∧
        euclidPPosition R.1 R.2 = true)

/-- **Positions of a Calkin–Wilf row with maximal optimal play in Euclid.** For every $k \ge 0$,
the number of positions in row $k$ of the Calkin–Wilf tree whose Smith remoteness in the Euclid
game is $k$ equals $2^{k/2}$ if $k$ is even and $2^{(k+1)/2}$ if $k$ is odd.

Smith remoteness is the length of optimal play when the winner hurries and the loser delays.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.1. -/
public theorem_wanted count_max_remoteness_calkinWilfRow (k : ℕ) :
    ((calkinWilfRow k).filter fun p =>
        SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from p) = k).length =
      if Even k then 2 ^ (k / 2) else 2 ^ ((k + 1) / 2)

/-- **Maximal-remoteness paths alternate in pairs.** In the Calkin–Wilf tree the vertex $a/b$ has
son $a/(a+b)$ and daughter $(a+b)/b$. Let $w = (w_0, \dots, w_{\ell-1})$ be a sequence of steps,
each "son" or "daughter", and let $a/b$ be the vertex reached from the root $1/1$ by following
$w$. If the Smith remoteness of the position $(a, b)$ of Euclid equals $\ell$, then
$w_{2i} \ne w_{2i+1}$ for every $i$ with $2i + 1 < \ell$; that is, steps $2i+1$ and $2i+2$ are
one son step and one daughter step, in either order.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.2. -/
public theorem_wanted max_remoteness_path_alternates (w : List Bool)
    (hw : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from
      w.foldl (fun q b => if b then (q.1 + q.2, q.2) else (q.1, q.1 + q.2)) (1, 1)) = w.length)
    (i : ℕ) (hi : 2 * i + 1 < w.length) :
    w[2 * i]! ≠ w[2 * i + 1]!

/-- **Golden-ratio bounds for N-positions of maximal remoteness above 1.** Let $\varphi$ be the
golden ratio. If the pair $(m, n)$, read as the fraction $m/n$, lies in row $k$ of the Calkin–Wilf
tree, $n < m$, the position $(m, n)$ of Euclid is not a P-position, and its Smith remoteness in
Euclid equals $k$, then $\varphi < m/n < \varphi + 1$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.3. -/
public theorem_wanted golden_bounds_of_max_remoteness_N (k m n : ℕ) (hk : (m, n) ∈ calkinWilfRow k)
    (hmn : n < m) (hN : euclidPPosition m n = false)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    Real.goldenRatio < (m : ℝ) / n ∧ (m : ℝ) / n < Real.goldenRatio + 1

/-- **Golden-ratio bounds for N-positions of maximal remoteness below 1.** Let $\varphi$ be the
golden ratio. If the pair $(m, n)$, read as the fraction $m/n$, lies in row $k$ of the Calkin–Wilf
tree, $m < n$, the position $(m, n)$ of Euclid is not a P-position, and its Smith remoteness in
Euclid equals $k$, then $1/(\varphi + 1) < m/n < 1/\varphi$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 6.4. -/
public theorem_wanted golden_bounds_of_max_remoteness_N_symm (k m n : ℕ)
    (hk : (m, n) ∈ calkinWilfRow k) (hmn : m < n) (hN : euclidPPosition m n = false)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    1 / (Real.goldenRatio + 1) < (m : ℝ) / n ∧ (m : ℝ) / n < 1 / Real.goldenRatio

/-- **Golden-ratio bounds for P-positions of maximal remoteness.** Let $\varphi$ be the golden
ratio. If the pair $(m, n)$, read as the fraction $m/n$, lies in row $k$ of the Calkin–Wilf tree,
$m \ne n$, the position $(m, n)$ of Euclid is a P-position, and its Smith remoteness in Euclid
equals $k$, then $(\varphi + 2)/(\varphi + 1) < m/n < \varphi$ or
$1/\varphi < m/n < (\varphi + 1)/(\varphi + 2)$.

The hypothesis $m \ne n$ corrects the printed statement, which fails at the root $1/1$ (a
P-position with $0$ moves in row $0$, and $1$ lies in neither interval).

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.5. -/
public theorem_wanted golden_bounds_of_max_remoteness_P (k m n : ℕ)
    (hk : (m, n) ∈ calkinWilfRow k) (hmn : m ≠ n) (hP : euclidPPosition m n = true)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    ((Real.goldenRatio + 2) / (Real.goldenRatio + 1) < (m : ℝ) / n ∧
        (m : ℝ) / n < Real.goldenRatio) ∨
      (1 / Real.goldenRatio < (m : ℝ) / n ∧
        (m : ℝ) / n < (Real.goldenRatio + 1) / (Real.goldenRatio + 2))

/-- **Continued fractions with maximal optimal play in Euclid.** For natural numbers
$a_0, \dots, a_r$ write $[a_0, \dots, a_r]$ for the continued fraction
$a_0 + 1/(a_1 + 1/(\cdots + 1/a_r))$, and $1^j$ for a block of $j$ ones; read a positive rational
$u/v$ in lowest terms as the position $(u, v)$ of the Euclid game. Let $n \ge 1$, $i$ and $k$ be
natural numbers. If the position of $[1^{n-1}, 2]$ lies in row $k$ of the Calkin–Wilf tree, its
Smith remoteness is $k$. If the position of $[1^{n-1}, 3]$ lies in row $k$, its Smith remoteness
is less than $k$. If $1 \le i \le n - 2$ and the position of $[1^i, 2, 1^{n-2-i}, 2]$ lies in
row $k$, its Smith remoteness is $k$ when $i \equiv n \pmod 2$ and less than $k$ when
$i \not\equiv n \pmod 2$.

Proposition 6.6 also identifies these pairs as the ones taking the most steps in the Euclidean
algorithm, a result of Hopkins and Tangboonduangjit; that half is not part of this statement.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.6. -/
public theorem_wanted continued_fraction_max_remoteness (n i k : ℕ) (hn : 1 ≤ n) :
    let cf : List ℕ → ℚ := fun l => l.foldr (fun a x => (a : ℚ) + x⁻¹) 0
    let pos : ℚ → euclidGame.Pos := fun q => (q.num.toNat, q.den)
    let rem := SpragueGrundy.smithRemoteness euclidGame
    let A := cf (List.replicate (n - 1) 1 ++ [2])
    let B := cf (List.replicate (n - 1) 1 ++ [3])
    let C := cf (List.replicate i 1 ++ [2] ++ List.replicate (n - 2 - i) 1 ++ [2])
    (((pos A).1, (pos A).2) ∈ calkinWilfRow k → rem (pos A) = k) ∧
      (((pos B).1, (pos B).2) ∈ calkinWilfRow k → rem (pos B) < k) ∧
      (1 ≤ i → i ≤ n - 2 → ((pos C).1, (pos C).2) ∈ calkinWilfRow k →
        (i % 2 = n % 2 → rem (pos C) = k) ∧ (i % 2 ≠ n % 2 → rem (pos C) < k))

end

end MetaMathlibExt
