# Staffing a loss system with a blocking target

Let $a = \lambda/\mu > 0$ and let $B(c, a) = (a^c/c!)/\sum_{k \le c} a^k/k!$ be the Erlang-B value. Then $1/B(c, a) = \sum_{j=0}^{c} \frac{c!}{(c-j)!}\,a^{-j}$, so $B(c, a)$ is strictly decreasing in $c$ and tends to $0$. Consequently, for a finite nonempty set $C$ of allowed server counts, a target $0 \le \varepsilon \le 1$ and a cost $\kappa c$ with $\kappa > 0$: the set $\{c \in C : B(c, a) \le \varepsilon\}$ is either empty, in which case the staffing problem is infeasible, or consists of all allowed $c$ from its least element $c^*$ on, and $c^*$ is the unique optimal staffing level. For $a = 0$, $B(0, 0) = 1$ and $B(c, 0) = 0$ for $c \ge 1$.

Proof. Divide the denominator by $a^c/c!$ and write $j = c - k$; each term $c!/((c-j)!a^j)$ is nondecreasing in $c$ and a new positive term appears, so $1/B$ strictly increases. It is at least $c/a$, which tends to infinity.

## Depends on

- [Stationarity of the Erlang loss distribution and the Erlang-B recursion](stationary-law-of-the-erlang-loss-system.md): the Erlang-B value $B(c, a)$.

## Expansion

- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
