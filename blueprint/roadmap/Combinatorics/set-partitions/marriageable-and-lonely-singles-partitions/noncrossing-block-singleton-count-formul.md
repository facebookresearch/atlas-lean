# Counting noncrossing partitions with no or one singleton block

Write $NC_{n,m,k}$ for the
number of noncrossing partitions of $\{0, \dots, n-1\}$ with $m$ blocks of which $k$ are
singletons, and extend the binomial coefficient $\binom{a}{b}$ to all integers $a$, $b$ by setting
it to $0$ when $a < 0$ or $b < 0$. For all natural numbers $n$ and $m$: if $(n, m) \ne (0, 0)$,
then the following holds in $\mathbb{Q}$, where $1/0$ is taken to be $0$ (the denominator
vanishes only for $m = n + 1$, where $\binom{n}{m} = 0$):

$$NC_{n,m,0} = \frac{1}{n-m+1} \binom{n}{m} \binom{n-m-1}{m-1};$$

and if $(n, m) \ne (1, 1)$, then

$$NC_{n,m,1} = \binom{n}{m-1} \binom{n-m-1}{m-2}.$$

## Sources

- Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 24 (`jis-2025-25.1.1-prop-24`).
