# Unbiasedness of observed cell means in a factorial design

Let $U$ be a finite population of $N$ units. For cell sizes $n_0, \dots, n_3$, complete randomization over the four cells is the uniform measure on the assignments $f : U \to \{0,1,2,3\}$ with exactly $n_c$ units in cell $c$; it is the zero measure when no such assignment exists. Suppose $n_c > 0$ for every $c$ and $\sum_c n_c = N$. Then for every $y : U \to \mathbb{R}$ and every cell $c$, the observed mean $\bar y_c(f) = \frac{1}{n_c} \sum_{i : f(i) = c} y_i$ of cell $c$ has expectation the population mean:

$$\mathbb{E}\big[\bar y_c\big] = \frac1N \sum_{i \in U} y_i.$$

## Sources

- T. Dasgupta, N. S. Pillai and D. B. Rubin, "Causal inference from $2^K$ factorial designs using the potential outcomes model", arXiv:1211.2481, Section 3.1, equations (1) and (2).
