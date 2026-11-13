# Sums of squares and products of trinomial coefficients with even index

Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$. For
every $n \in \mathbb{N}$ let $c_n = \binom{n}{n/2}_2$ if $n$ is even and $c_n = 0$ if $n$ is odd.
Then

$$\sum_{k=0}^{n} \binom{n}{2k}_2^2 = \frac{1}{2}\binom{2n}{2n}_2 + \frac{1}{2}\binom{n}{n}_2$$

and

$$\sum_{k=0}^{\lfloor n/2 \rfloor} \binom{n}{n-2k}_2 \binom{n}{2k}_2 =
\frac{1}{2}\binom{2n}{n}_2 + \frac{1}{2} c_n.$$

For odd $n$ the paper's $\binom{n}{n/2}_2$ is read as $0$: the floor reading fails, e.g. at
$n = 1$ the left side is $1$ while $\frac{1}{2}\binom{2}{1}_2 + \frac{1}{2}\binom{1}{0}_2 = 3/2$.

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 26 (`jis-2025-25.3.5-thm-26`).
