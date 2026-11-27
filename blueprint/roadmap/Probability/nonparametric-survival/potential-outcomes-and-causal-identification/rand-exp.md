# Expectation of a statistic under complete randomization

For a finite population of $N$ units, $n_1 \in \mathbb{N}$ and a real statistic $f$ of the treated set, the expectation of $f$ under complete randomization is

$$\mathbb{E}_{n_1}[f] = \binom{N}{n_1}^{-1} \sum_{|S| = n_1} f(S),$$

the average of $f$ over the $\binom{N}{n_1}$ sets of $n_1$ units, so that the treated set is uniform among them. For $n_1 > N$ there is no such set and the value is $0$ by convention.
