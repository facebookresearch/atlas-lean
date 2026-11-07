# Metered parking functions with meter $n - 1$ and more cars than spots

Let $k > 0$ and
$f : \{0, \dots, n+k-1\} \to \{0, \dots, n-1\}$, and let $\pi_0, \dots, \pi_{n-1}$ be the
$(n-1)$-metered outcome of the first $n$ preferences $(f(0), \dots, f(n-1))$ on $n$ spots, where
$\pi_c$ is the spot in which car $c$ parks, if it parks. Then $f$ is an $(n-1)$-metered parking
function if and only if $(f(0), \dots, f(n-1))$ is a parking function and, for every
$i \in \{0, \dots, k-1\}$, car $i \bmod n$ parks in this outcome and $f(n + i) \le \pi_{i \bmod n}$.

The outcome is read periodically: the later preferences $f(n), f(n+1), \dots$ are compared with
$\pi_0, \dots, \pi_{n-1}, \pi_0, \dots$ in turn.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Theorem 6 (`integers-2025-A73-thm-6`).
