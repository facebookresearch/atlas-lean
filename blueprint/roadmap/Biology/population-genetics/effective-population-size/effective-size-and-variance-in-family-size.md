# Effective population size and the variance in family size

Let $N \ge 1$ (an integer) monoecious diploid parents produce the $2N$ gene copies of the next
generation (of $N$ diploids). Each gene copy $c$ of the offspring generation comes from a gamete of
one parent, $\mathrm{parent}(c)$, and parent $i$ contributes $n_i = \#\{c : \mathrm{parent}(c) = i\}$
gametes. A vector $(n_i)$ of integers $n_i \ge 0$ arises in this way from some assignment of the
gene copies to parents if and only if $\sum_i n_i = 2N$. The gametes are then paired into the
offspring (at random, so selfing is possible); the pairing plays no part below. Write
$V_n = \frac1N \sum_i (n_i - 2)^2$ for the variance of the contributions.

Given the assignment, an ordered pair of distinct gene copies of the offspring generation, chosen
uniformly at random among the $2N (2N - 1)$ such pairs, comes from the same parent with probability

$$P = \frac{\sum_i n_i (n_i - 1)}{2N (2N - 1)} = \frac{V_n + 2}{2 (2N - 1)} ,$$

using $\sum_i n_i^2 = N (V_n + 4)$. If each gamete carries either of its parent's two gene copies
with probability $1/2$, independently of the other gametes and of the choice of the pair, the two
gene copies are copies of the same parental gene with probability $P/2$. Defining the effective size
by $P = 1/N_e$ gives

$$N_e = \frac{4N - 2}{V_n + 2} .$$

The contributions are equal, $n_i = 2$ for every $i$, exactly when $V_n = 0$, and then
$N_e = 2N - 1$, which is at least $N$ and exceeds $N$ for $N > 1$. When $V_n = 2 - 2/N$,
$N_e = N$.

Under Wright–Fisher sampling, in which each of the $2N$ gene copies chooses its parent uniformly
at random and independently of the others (the assignment uniform over all $N^{2N}$ possibilities),
$V_n$ has expected value $2 - 2/N$, the value at which $N_e = N$, and $P$ has expected value $1/N$.

## Sources

- J. Felsenstein, *Theoretical Evolutionary Genetics* (GENOME 562 course text, University of Washington, version of December 2019), <https://felsenst.github.io/pgbook/pgbook.pdf>, Section VI.7, "Varying population size and offspring number", subsection "Variation in fitness", equations (VI-50)–(VI-54), pp. 271–272.
