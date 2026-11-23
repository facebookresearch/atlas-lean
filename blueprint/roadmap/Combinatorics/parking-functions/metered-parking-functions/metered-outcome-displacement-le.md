# Displacement bound in the metered scheme

Let $t$, $m$, $n$ be natural numbers, let
$f : \{0, \dots, m - 1\} \to \{0, \dots, n - 1\}$ be a preference function and let $i < m$ be a
car. Under the $t$-metered parking scheme on $n$ spots, if car $i$ parks in spot $s$ then
$s \le f(i) + t$, that is, its displacement is at most $t$; and if car $i$ fails to park then
$f(i) + t \ge n$.

In the source's one-based numbering, with preference $a_i = f(i) + 1$, a car that fails to park
has $a_i \ge n - t + 1$.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Proposition 5.
