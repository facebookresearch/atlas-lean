# Erdős Problem 650: matching integers to distinct multiples

For a natural number $m$, let
$f(m)$ be the largest natural number $r$ such that for every natural number $N$, every set
$A \subseteq \{1, \dots, N\}$ with exactly $m$ elements and every real $x \ge 1$, there are
distinct $a_1, \dots, a_r \in A$ and distinct natural numbers $b_1, \dots, b_r$ in the open
interval $(x, x + 2N)$ with $a_i \mid b_i$ for every $i$. Then $f(m) = \min(m,
\lceil 2\sqrt{m}\,\rceil)$ for every natural number $m$; it is not the case that
$f(m) \le \sqrt{m}$ for every natural number $m$; $\sqrt{m} \le f(m)$ for every natural number
$m$; and $f(m^2) \le 2m$ for every natural number $m$.

Solved by Erdős–Surányi [ErSu59], Erdős–Selfridge [Er78], [Er86c] and van Doorn–Li–Tang [VLT26].

## Sources

- [VLT26] W. van Doorn, Y. Li and Q. Tang, Optimal bounds for an Erdős problem on matching integers to distinct multiples, arXiv:2603.28636 (2026), https://arxiv.org/abs/2603.28636; W. van Doorn, Lean formalization of Erdős Problem 650 (Aristotle-assisted), https://github.com/Woett/Lean-files/blob/c100ed4a4429e987a9555ee428a1aa524a46e16d/ErdosProblem650.lean.
