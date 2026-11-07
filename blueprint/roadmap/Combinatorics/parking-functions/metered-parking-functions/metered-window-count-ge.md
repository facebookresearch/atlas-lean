# Window condition for metered parking functions

Number the cars $1, \dots, m$ and the
spots $1, \dots, n$, and let $a_k$ be the preferred spot of car $k$. If $(a_1, \dots, a_m)$ is a
$t$-metered $(m, n)$-parking function, then for every $i$ with $1 \le i \le n$ and every $j$ with
$1 \le j \le m - t$ (truncated subtraction, so there is no such $j$ when $m \le t$),

$$t + 1 + i \le \#\{k : j \le k \le j + t,\ a_k \le i\} + n,$$

that is, at least $t + 1 - n + i$ of the cars $j, \dots, j + t$ prefer one of the spots
$1, \dots, i$.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Proposition 1 (`integers-2025-A73-prop-1`).
