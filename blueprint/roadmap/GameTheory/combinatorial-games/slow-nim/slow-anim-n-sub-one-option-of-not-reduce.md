# Options with reduction in Slow {n - 1}-Nim

Let $n \ge 2$, $k = n - 1$ and $A = \{k\}$.
Let $p$ be a reduced position of Slow$A$-Nim on $n$ stacks, with $s = (p_1 + \dots + p_n) \bmod 2k$,
$o$ odd stacks, and maximum $M = \max_i p_i$ attained by $\alpha$ stacks. Let $p'$ be obtained
from $p$ by playing on a set $S$ of $k$ stacks, each holding at least one token in $p$, and
suppose that $p'$ is not reduced. Write $r = r(p')$ for its reduction,
$s' = (r_1 + \dots + r_n) \bmod 2k$ and $o'$ for the number of odd stacks of $r$. Then $M$ is
even if $s < k$ and odd if $s \ge k$. If $s \not\equiv 0 \pmod k$, then $r_i = \max(p_i - 1, 0)$
for every stack $i$, $o' = n - o$, and $s' = s + k - 1$ if $s < k$, $s' = s - (k + 1)$ if
$s > k$. If $s \equiv 0 \pmod k$, then $r_i = \max(p_i - 2, 0)$ for the stacks with $p_i = M$
and $r_i = \max(p_i - 1, 0)$ for the others; moreover, if $s = 0$ then
$\alpha \le \min(n - o, n - 2)$, $s' = k - 1 - \alpha$ and $o' = n - o - \alpha$, and if $s = k$
then $\alpha \le \min(o, n - 2)$, $s' = 2k - 1 - \alpha$ and $o' = n - o + \alpha$.

Stacks are labelled, so the paper's canonical-form display of $r(p')$ is written stackwise.

## Sources

- Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 6.
