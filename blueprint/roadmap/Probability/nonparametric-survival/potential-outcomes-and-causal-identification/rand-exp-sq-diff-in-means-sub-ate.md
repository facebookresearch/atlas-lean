# Variance of the difference in means under complete randomization

For a finite population of $N$ units with potential outcomes $y_{0i}, y_{1i}$, $1 \le n_1 \le N - 1$ and $n_0 = N - n_1$, the [difference in means](diff-in-means.md) satisfies, under [complete randomization](rand-exp.md),

$$\mathbb{E}_{n_1}\big[(\hat\tau - \tau)^2\big] = \frac{S_1^2}{n_1} + \frac{S_0^2}{n_0} - \frac{S_\tau^2}{N},$$

where $S_1^2$, $S_0^2$ and $S_\tau^2$ are the [population variances](pop-var.md) of $y_1$, of $y_0$ and of the unit-level effects $\tau_i = y_{1i} - y_{0i}$.

## Sources

- Jerzy Splawa-Neyman, *On the application of probability theory to agricultural experiments. Essay on principles. Section 9* (1923), translated by D. M. Dabrowska and T. P. Speed, Statist. Sci. 5 (1990), no. 4, 465–472, DOI 10.1214/ss/1177012031.
