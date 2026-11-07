# The reduction chops at the largest reduced height

Let $A \subseteq \{1, \dots, n\}$ and
let $p$ be a position of Slow$A$-Nim on $n$ stacks, with largest stack height $M = \max_i p_i$
($M = 0$ when $n = 0$). For $m \in \mathbb{N}$ write $\mathrm{ctt}(p, m)$ for the position whose
stack $i$ has height $\min(p_i, m)$. If $m \le M$, the position $\mathrm{ctt}(p, m)$ is reduced,
and $\mathrm{ctt}(p, m')$ is not reduced for any $m'$ with $m < m' \le M$, then the reduction of
$p$ is $r(p) = \mathrm{ctt}(p, m)$.

## Sources

- Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 3.
