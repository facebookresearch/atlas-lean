# Lower bound for the first anti-recurrence number

Let $a = (a_1, \dots, a_k)$ be a linear
form with positive integer coefficients, of trace $\tau = a_1 + \dots + a_k$, and let $A_1$ be its
first anti-recurrence number. Then $\tau + (k - 1)k/2 \le A_1$, and the inequality is strict if
and only if $a_j > 1$ for some $j$ with $2 \le j \le k$.

This corrects the printed strictness condition ("$k > 2$ and not anti-bonacci"), which fails for
$a = (2, 1, 1)$: there $A_1 = 2 + 2 + 3 = 7 = \tau + 3$. The correction follows the paper's
proof, $A_1 = \tau + \sum_j (j - 1) a_j$. The paper's hypothesis $k > 1$ is not needed.

## Sources

- Robbert Fokkink and Gandhar Joshi, *Anti-Recurrence Sequences*, INTEGERS 26 (2026), Article A24, Lemma 4 (`integers-2026-A24-lem-4`).
