# General reduction lemma

Let $A \subseteq \{1, \dots, n\}$ be nonempty with least element
$a$, and let $p$ be a reduced position of Slow$A$-Nim $\mathrm{SN}(n, A)$ with largest stack
height $M$ and total $\Sigma(p) = \sum_i p_i$. Let $S$ be a set of $\ell \in A$ stacks, each
holding at least one token, and suppose that the position obtained from $p$ by removing one token
from each stack of $S$ is not reduced. Then $a M \le \Sigma(p)$ and, writing
$r = \Sigma(p) - a M$, either (R1) $\ell > a$, every stack of height $M$ lies in $S$, and
$r < \ell - a$; or (R2) some stack of height $M$ is not in $S$, and $r < \ell$.

The hypothesis that $p$ is reduced is implicit in the source, whose proof uses $r \ge 0$.

## Sources

- Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 4.
