# Options without reduction in Slow {n - 1}-Nim

Let $n \ge 2$, $k = n - 1$ and $A = \{k\}$,
so that a move removes one token from each of exactly $k$ nonempty stacks. Let $p$ be a reduced
position of Slow$A$-Nim on $n$ stacks, with $s = (p_1 + \dots + p_n) \bmod 2k$ and $o$ odd stacks.
Let $p'$ be obtained from $p$ by playing on a set $S$ of $k$ stacks, each holding at least one
token in $p$, and let $j$ be the stack not in $S$. If $p'$ is reduced, then
$s' = (p'_1 + \dots + p'_n) \bmod 2k$ equals $s + k$ when $s < k$ and $s - k$ when $s \ge k$, and
the number $o'$ of odd stacks of $p'$ is $n - o + 1$ if $p_j$ is odd and $n - o - 1$ if $p_j$ is
even.

The closing remark of Lemma 5 that both values of $o'$ are legal when $0 < o < n$ is omitted: it
fails for $n = 3$ at $p = (0, 1, 1)$, whose only move omits the empty stack.

## Sources

- Matthieu Dufour and Silvia Heubach, *On the 𝒫-Positions of Some Infinite Families of Slow`A`-Nim*, INTEGERS 26 (2026), Article G3, Lemma 5.
