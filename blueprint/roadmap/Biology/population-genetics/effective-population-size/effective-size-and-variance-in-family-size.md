# Effective population size and the variance in family size

Let a population of $N \ge 1$ (an integer) monoecious diploid parents produce the $2N$ gene copies of the
next generation (of $N$ diploids), parent $i$ contributing $n_i \ge 0$ gametes (integers), with
$\sum_i n_i = 2N$, each gamete carrying either of its parent's two gene copies with probability $1/2$,
independently, and let the gametes be paired at random into offspring (so selfing is possible). Write
$V_n = \frac1N \sum_i (n_i - 2)^2$ for the variance of the contributions. Given the contributions,
two distinct gene copies of the offspring generation, chosen at random, come from the same parent with
probability

$$P = \frac{\sum_i n_i (n_i - 1)}{2N (2N - 1)} = \frac{V_n + 2}{2 (2N - 1)} ,$$

using $\sum_i n_i^2 = N (V_n + 4)$, and they are then copies of the same parental gene with probability
$1/2$. Defining the effective size by $P = 1/N_e$ (the value $1/N$ of a Wright–Fisher population of $N$
diploids) gives

$$N_e = \frac{4N - 2}{V_n + 2} .$$

For equal contributions ($V_n = 0$), $N_e = 2N - 1$, which is at least $N$ and exceeds $N$ for
$N > 1$; when $V_n$ equals
$2 - 2/N$, its expected value under Wright–Fisher sampling, $N_e = N$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.7, "Variation in fitness", equations (VI-50)–(VI-54), pp. 271–272.
