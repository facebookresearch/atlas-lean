/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Image

/-!
# Connell sequences

This file formalizes Definition 1 from Grady D. Bullington, *The Connell Sum Sequence*:
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Bullington/bullington7.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Row lengths of the Connell triangle.** For natural numbers $r$ and $j$, the length of
row $j$ is $1 + r(j - 1)$, where $j - 1$ is read as $0$ when $j = 0$. For $j \ge 1$ this is the
number of entries in row $j$ of the Connell $(m, r)$ triangle for every $m$; the source numbers
rows from one, and the value at $j = 0$ is a convention. -/
def connellRowLength (r j : ℕ) : ℕ :=
  1 + r * (j - 1)

/-- **First entries of the rows of the Connell triangle.** For natural numbers $m$ and $r$, the
numbers $s_j$ are defined by $s_0 = s_1 = 1$ and $s_{j+1} = s_j + m(\ell_j - 1) + 1$ for
$j \ge 1$, where $\ell_j = 1 + r(j - 1)$ is the length of row $j$. For $j \ge 1$, $s_j$ is the
first entry of row $j$ of the Connell $(m, r)$ triangle: each row starts one above the last
entry $s_j + m(\ell_j - 1)$ of the row before. The source numbers rows from one, and the value
$s_0 = 1$ is a convention. -/
def connellRowStart (m r : ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | j + 2 =>
      connellRowStart m r (j + 1) + m * (connellRowLength r (j + 1) - 1) + 1

/-- **Entries of the Connell triangle.** For natural numbers $m$, $r$, $j$ and $k$, the entry with
zero-based index $k$ in row $j$ of the Connell $(m, r)$ triangle is $s_j + mk$, where $s_j$ is the
first entry of row $j$. The formula is used for every $k$, also at or beyond the row length. -/
def connellEntry (m r j k : ℕ) : ℕ :=
  connellRowStart m r j + m * k

/-- **Rows of the Connell triangle.** For natural numbers $m$, $r$ and $j$, row $j$ of the
Connell $(m, r)$ triangle is the finite set of the numbers $s_j + mk$ with $0 \le k < \ell_j$, where
$s_j$ is the first entry of row $j$ and $\ell_j = 1 + r(j - 1)$ is its length, with $j - 1$ read
as $0$ when $j = 0$. -/
def connellRowEntries (m r j : ℕ) : Finset ℕ :=
  (Finset.range (connellRowLength r j)).image (connellEntry m r j)

/-- **Connell parameters.** A pair of natural numbers $(m, r)$ with $m \ge 2$ and $r \ge 1$; these
are the admissible parameters of a Connell $(m, r)$ sequence. -/
structure ConnellParameters where
  m : ℕ
  r : ℕ
  two_le_m : 2 ≤ m
  pos_r : 0 < r

/-- **Next position in the Connell triangle.** For a natural number $r$, the position following
row $j$, zero-based column $k$, is row $j$, column $k + 1$ if $k + 1 < 1 + r(j - 1)$ (the length
of row $j$, with $j - 1$ read as $0$ when $j = 0$), and row $j + 1$, column $0$ otherwise. -/
def connellNext (r : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 + 1 < connellRowLength r p.1 then (p.1, p.2 + 1) else (p.1 + 1, 0)

/-- **Position of a term in the Connell triangle.** For a natural number $r$, the position
$p_n = (j_n, k_n)$ (row $j_n$, zero-based column $k_n$) of index $n \ge 0$ is defined by
$p_0 = (1, 0)$ and $p_{n+1} = (j_n, k_n + 1)$ if $k_n + 1 < 1 + r(j_n - 1)$ (the length of row
$j_n$, with $j_n - 1$ read as $0$ when $j_n = 0$), and $p_{n+1} = (j_n + 1, 0)$ otherwise. -/
def connellPosition (r : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => connellNext r (connellPosition r n)

/-- **Connell sequence.** For natural numbers $m \ge 2$ and $r \ge 1$, the Connell $(m, r)$
sequence $(a_n)_{n \ge 0}$ reads the Connell triangle row by row: row $j \ge 1$ has
$\ell_j = 1 + r(j - 1)$ entries $s_j, s_j + m, \dots, s_j + m(\ell_j - 1)$, where $s_1 = 1$ and
$s_{j+1} = s_j + m(\ell_j - 1) + 1$. Thus $a_n = s_j + mk$, where row $j$, zero-based column $k$
is the position reached from row $1$, column $0$ after $n$ steps, each step moving one column
right within a row and from the last entry of a row to the first entry of the next. -/
def connellSequence (p : ConnellParameters) (n : ℕ) : ℕ :=
  let pos := connellPosition p.r n
  connellEntry p.m p.r pos.1 pos.2

end MetaMathlibExt
