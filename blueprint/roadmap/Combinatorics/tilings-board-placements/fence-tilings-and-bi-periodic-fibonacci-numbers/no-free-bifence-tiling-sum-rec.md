# Recurrence for weighted tilings with no free bifence

Let $a$ and $b$ be nonzero elements
of a field, and let $R_n$ be the weighted number of tilings of an $n$-board by half-squares and
$(1/2, 1/2)$-fences with no free bifence, where a half-square has weight $a$ in an odd cell and
$b$ in an even cell (cells numbered $1, \dots, n$). For every $n \ge 2$,

$$R_n = \frac{b}{a}(ab + 1) R_{n-1} + ab\, R_{n-2}$$

if $n$ is even, and

$$R_n = \frac{a}{b}(ab + 1) R_{n-1} + ab\, R_{n-2}$$

if $n$ is odd.

The initial values are $R_0 = 1$ and $R_1 = a^2$.

## Sources

- Nassima Belaggoun and Hacène Belbachir, *Combinatorial Identities for the Bi-Periodic Fibonacci Numbers Squared*, The Fibonacci Quarterly 62 (2024), Article belaggoun01132024, Lemma 3.13.
