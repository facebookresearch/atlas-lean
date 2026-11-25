# Hahn decomposition of a finite signed measure

Let $s$ be a finite signed measure on a measurable space $X$, that is, a countably additive function
from the measurable sets to $\mathbb{R}$. Then there are disjoint measurable sets $P$ and $N$ with $P \cup N = X$
such that $s(E) \ge 0$ for every measurable set $E \subseteq P$ and $s(E) \le 0$ for every measurable set
$E \subseteq N$.

## Idea

Take $P$ where $s$ is as large as possible. With $a = \sup\{s(E) : E \text{ measurable}\}$, which is finite, choose
$E_j$ with $s(E_j) \ge a - 2^{-j}$; then $P = \bigcap_k \bigcup_{j \ge k} E_j$ has $s(P) = a$, and this maximality
forces $s(E) \ge 0$ for measurable $E \subseteq P$ and $s(E) \le 0$ for measurable $E \subseteq X \setminus P$. The
decomposition is unique up to sets that are null for $s$, that is, sets whose measurable subsets all have measure $0$,
and it yields the Jordan decomposition $s^+(E) = s(E \cap P)$, $s^-(E) = -s(E \cap N)$. The theorem also holds for
signed measures that take one of the values $\pm\infty$.

## Statements

- [Hahn decomposition of a finite signed measure](exists-is-compl-positive-negative.md)

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, result 9.23 (version read: the open-access PDF dated 12 June 2026).
