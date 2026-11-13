# Lower bound for the number of lonely singles partitions

For every $n \ge 2$, the number
$L_n$ of lonely singles partitions of $\{0, \dots, n-1\}$ satisfies

$$
L_n \ge \sum_{m=1}^{\lfloor n/2 \rfloor} \frac{1}{n-m+1} \binom{n}{m} \binom{n-m-1}{m-1} +
\sum_{m=2}^{\lfloor (n+1)/2 \rfloor} \binom{n}{m-1} \binom{n-m-1}{m-2},
$$

where a binomial coefficient $\binom{a}{b}$ with $a < 0$ or $b < 0$ is taken to be $0$.

## Sources

- Julien Rouyer and Alain Ninet, *Two New Integer Sequences Related to Crossroads and Catalan Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.1, Proposition 26 (`jis-2025-25.1.1-prop-26`).
