# Metered parking function

Let $m, n, t \in \mathbb{N}$, number the $n$ spots
$0, \dots, n-1$, and let $f : \{0, \dots, m-1\} \to \{0, \dots, n-1\}$ give the preferred spot of
each of $m$ cars. In the $t$-metered scheme the cars arrive in the order $0, 1, \dots, m-1$, and
car $i$ parks in the least spot $s$ with $f(i) \le s \le n - 1$ that is not occupied by any of the
(at most $t$) cars that arrived just before car $i$; it fails to park if there is no such spot.
Then $f$ is a $t$-metered parking function if every car parks.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Section 1 (definition of `t`-metered parking functions).
