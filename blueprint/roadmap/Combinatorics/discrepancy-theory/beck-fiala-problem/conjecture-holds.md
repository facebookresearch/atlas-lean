# Linear Beck–Fiala systems have discrepancy $O(\sqrt{t})$

There is a real constant $C > 0$
such that the following holds for all natural numbers $n$, $m$ and $t \ge 1$. Let
$S_1, \dots, S_n$ be subsets of $\{1, \dots, m\}$ such that each $S_i$ has at most $t$ elements,
each element of $\{1, \dots, m\}$ lies in at most $t$ of the sets $S_i$, and $S_i$ and $S_{i'}$
have at most one common element whenever $i \ne i'$. Then there are signs
$\varepsilon_1, \dots, \varepsilon_m \in \{1, -1\}$ such that
$\left|\sum_{j \in S_i} \varepsilon_j\right| \le C\sqrt{t}$ for every $i$.

Guo, Fang and Lu prove that every $0/1$ matrix with at most $t$ nonzero entries in each column
has discrepancy less than $3\sqrt{2\pi t}$ (arXiv:2609.11189, Corollary 1.2 of their Komlós
bound, Theorem 1.1; Karingula and Lovett give an elementary proof of the Komlós bound with
constant 36, arXiv:2609.20979). Linear systems with $t$-sparse rows and columns are a special
case.

## Sources

- Shengtao Guo, Ethan X. Fang and Junwei Lu, Vector balancing via directional total variation, arXiv:2609.11189 (2026), https://arxiv.org/abs/2609.11189. Moved from `OpenConjectures/Combinatorics/LinearBeckFiala`.
