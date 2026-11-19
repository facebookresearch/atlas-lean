# Neutral Wright–Fisher transition matrix

For a natural number $M$, the neutral Wright–Fisher transition matrix $P_M$ on $\{0, \dots, M\}$ has the entries

$$P_M(i, j) = \binom{M}{j} \Bigl(\frac{i}{M}\Bigr)^{j} \Bigl(1 - \frac{i}{M}\Bigr)^{M - j},$$

with the convention $i/0 = 0$: row $i$ is the binomial law $\mathrm{Bin}(M, i/M)$ of the number of copies of $A$ among $M$ draws with replacement. It is a stochastic matrix. The model needs $M \ge 1$; for $M = 0$ it is the one-state chain.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004), ch. 3.
