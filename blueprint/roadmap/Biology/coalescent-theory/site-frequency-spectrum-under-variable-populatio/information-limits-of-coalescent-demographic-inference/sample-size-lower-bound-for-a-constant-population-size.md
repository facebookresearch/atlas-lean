# Sample-size lower bound for estimating a constant population size from coalescent trees

Under the standard coalescent with constant population size $N$, while $k$ lineages remain each pair coalesces at rate $1/N$, so the $n-1$ inter-coalescence times of a genealogy of $n$ sampled individuals are independent exponentials with rates $\binom{k}{2}/N$, $k = n, \dots, 2$.

Fix $\eta > 0$. Let $H_1$ be the hypothesis that the size is the constant $N$ on $[0,\infty)$ and $H_2$ that it is the constant $(1+\eta)N$. Suppose $L$ i.i.d. coalescent trees on $n$ individuals are observed, with each hypothesis having prior probability $1/2$.

**Theorem.** For every classifier the Bayes error is at least $(1 - \Upsilon)/2$, where

$$\Upsilon^2 \le 2L\Big(1 - \Big(\frac{2\sqrt{1+\eta}}{2+\eta}\Big)^{n-1}\Big) \le \frac{L\,(n-1)\,\eta^2}{4}.$$

Hence, to estimate a constant population size within relative error $\eta$ with constant success probability, the total number of coalescent events observed must satisfy

$$L\,(n-1) \gtrsim \eta^{-2}.$$

Adding individuals to a tree helps only through the $n-1$ coalescence times it contributes, exactly as additional independent loci do.

## Expansion

Rescaling all coalescence times of a tree by the population size shows the tree under $H_2$ is the tree under $H_1$ stretched by the factor $1+\eta$. Each of the $n-1$ independent exponential inter-coalescence times contributes the same Hellinger affinity $\int \sqrt{f_\lambda f_{\lambda/(1+\eta)}} = 2\sqrt{1+\eta}/(2+\eta)$, independently of its rate. Affinities multiply over the $n-1$ intervals and the $L$ trees; the total-variation bound via Hellinger distance and the inequality $1 - x^{m} \le m(1-x)$ with $1 - 2\sqrt{1+\eta}/(2+\eta) \le \eta^2/8$ give the stated bounds.

## Sources

- Junhyong Kim, Elchanan Mossel, Miklós Z. Rácz, Nathan Ross, "Can one hear the shape of a population history?", *Theoretical Population Biology* 100 (2015), 26–38, <https://doi.org/10.1016/j.tpb.2014.12.002>; preprint arXiv:1402.2424, <https://doi.org/10.48550/arXiv.1402.2424>. Numbering of the arXiv version: Theorem 3.2 and Section 3.2.
