# Binary search for the boundary of a predicate

Let $p$ be a test that is true or false on each natural number and let $lo, hi \in \mathbb{N}$.
The binary search $\beta(p, lo, hi)$ is defined by recursion on $hi - lo$: if $lo < hi$, let
$m = \lfloor (lo + hi)/2 \rfloor$; if $p(m)$ is true then $\beta(p, lo, hi) = \beta(p, m + 1, hi)$,
and otherwise $\beta(p, lo, hi) = \beta(p, lo, m)$. If $lo \ge hi$, then $\beta(p, lo, hi) = lo$.

When $lo \le hi$ and $p$ holds on an initial segment of $\{lo, \dots, hi - 1\}$, the result is the
first index of that range at which $p$ is false, or $hi$ if there is none.
