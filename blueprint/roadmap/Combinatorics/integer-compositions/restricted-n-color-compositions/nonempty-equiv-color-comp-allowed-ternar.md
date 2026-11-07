# Bijection between n-color compositions with colors b, b+1 and ternary strings

For all
natural numbers $b \ge 1$ and $n \ge 1$, there is a bijection between $\mathrm{CCo}_{b,b+1}(n)$,
the $n$-color compositions of $n$ using only the colors $b$ and $b+1$, and the set of strings of
length $n-1$ over the alphabet $\{0, 1, 2\}$ such that, when the string is cut at each of its
$0$s, every resulting segment (including the possibly empty segments before the first $0$, after
the last $0$, and between adjacent $0$s) either consists only of $1$s and has length at least
$b-1$, or consists only of $2$s and has length at least $b$.

The paper states the condition as: no subword $12$ or $21$, runs of $1$s of length at least
$b-1$, runs of $2$s of length at least $b$, and successive $0$s separated by at least $b-1$
digits. The segment form above also constrains the segments before the first and after the last
$0$; without that, the string $0$ would be a counterexample at $n = 2$, $b = 3$.

## Sources

- Brian Hopkins and Hua Wang, "Allowing or Prohibiting Two Consecutive Colors in `n`-Color Compositions", Theorem 2.
