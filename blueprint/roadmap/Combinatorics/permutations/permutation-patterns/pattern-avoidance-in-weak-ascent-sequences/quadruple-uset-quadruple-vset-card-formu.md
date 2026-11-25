# Sum formulas for $|U_{n,1}|$ and $|V_{n,1}|$ (Proposition 2)

For every natural number
$n$ let $f(n, a) = \min(n - 3 - a, \lfloor (a - 1)/2 \rfloor)$ and

$$
S(n) = \sum_{a=2}^{n-4} \sum_{k=1}^{f(n,a)} \left( \binom{a-2}{2k} 2^{a-2k-2} +
\binom{a-2}{2k-1} 2^{a-2k-1} \right) (n - k - a - 2).
$$

Then for every $n \ge 1$

$$
|U_{n,1}| = \sum_{k=1}^{\lfloor n/3 \rfloor - 1} \left( \binom{n-k-4}{2k} 2^{n-3k-4} +
\binom{n-k-4}{2k-1} 2^{n-3k-3} \right)
$$

and

$$
|V_{n,1}| = \sum_{a=2}^{n-4} 2^{a-2} (n - a - 3) + S(n),
$$

and for every $n \ge 4$

$$
|V_{n,1}| = 2^{n-4} - n + 3 + S(n).
$$

A sum whose upper limit is below its lower limit is empty, and an exponent such as
$n - 3k - 4$ is negative only where the binomial coefficient multiplying it is $0$; such a
term is $0$. The last formula is stated only for $n \ge 4$: at $n = 3$ the expression
$2^{n-4} - n + 3$ equals $1/2$, while $\sum_{a=2}^{n-4} 2^{a-2} (n - a - 3)$ is $0$.

## Sources

- David Callan and Toufik Mansour, *Ascent Sequences and Weak Ascent Sequences Avoiding a Quadruple of Length-3 Patterns*, INTEGERS 25 (2025), Article A80, Proposition 2.
