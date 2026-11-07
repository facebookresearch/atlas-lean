# Existence of seeds for generalized taxicab numbers

Fix natural numbers $m \ge 1$ and
$t \ge 1$, and let $T(n, m, t)$ be, for each natural number $n$, either a natural number or
undefined, such that for all natural numbers $n$ and $v$, $T(n, m, t)$ is defined and equals $v$
exactly when $v$ is the least natural number with at least $t$ representations as a sum of exactly
$n$ positive $m$-th powers, representations being counted as unordered multisets of summands.
Then there is a positive integer $s_0$ such that $T(s_0, m, t)$ is defined, say equal to $v_0$,
and $T(s_0 + k, m, t) = v_0 + k$ for every natural number $k$; moreover, $s_0$ is the least
positive integer $s$ for which $T(s, m, t)$ is defined and $T(s + k, m, t) = T(s, m, t) + k$ for
every natural number $k$.

## Sources

- Jeffrey H. Dinitz, Richard A. Games, and Robert L. Roth, “Seeds for Generalized Taxicab Numbers”, Journal of Integer Sequences 22 (2019), Article 19.3.3, Theorem line 229, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Dinitz/dinitz8.tex>. Proves `Wanted` entry `generalized_taxicab_seed_exists`.
