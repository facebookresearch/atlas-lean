# Lower bound for the number of marriageable singles partitions

Extend the binomial
coefficient $\binom{a}{b}$ to all integers $a$, $b$ by setting it to $0$ when $a < 0$ or $b < 0$,
and for every natural number $N$ let

$$S(N) = \sum_{m=0}^{\lfloor N/2 \rfloor} \frac{1}{N-m+1} \binom{N}{m} \binom{N-m-1}{m-1}.$$

For every $n \ge 3$, the number $M_n$ of noncrossing partitions of $\{0, \dots, n-1\}$ that are
marriageable singles partitions satisfies

$$M_n \ge \sum_{i=1}^{n-1} \sum_{j=i+1}^{n} S(n+i-j-1)\, S(j-i-1).$$

For $N \ge 1$, $S(N)$ is the number of noncrossing partitions of an $N$-element set with no
singleton block; with the convention above, $S(0) = 0$.

## Sources

- Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 27 (`jis-2025-25.1.1-prop-27`).
