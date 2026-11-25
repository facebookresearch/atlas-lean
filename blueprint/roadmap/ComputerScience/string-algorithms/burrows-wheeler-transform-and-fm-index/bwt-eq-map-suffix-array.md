# The transform from the suffix array

Let $t = t_0 \cdots t_{n-1}$ be a text over a linearly ordered alphabet, let $u = t\bot$ be $t$
followed by a sentinel $\bot$ smaller than every letter, so $u_n = \bot$, and let $SA$ be the
suffix array of $u$. Then the Burrows–Wheeler transform of $t$ is the list of length $n + 1$ whose
entry at row $r$ is $u_{(SA[r] + n) \bmod (n + 1)}$: the letter of $u$ cyclically before position
$SA[r]$, which is the sentinel for the row with $SA[r] = 0$.
