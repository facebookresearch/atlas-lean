# Expectation of Neyman's variance estimator under complete randomization

For a finite population of $N$ units with potential outcomes $y_{0i}, y_{1i}$ and $2 \le n_1 \le N - 2$ (at least two treated and two control units), [Neyman's variance estimator](neyman-var.md) satisfies, under [complete randomization](rand-exp.md),

$$\mathbb{E}_{n_1}[\hat V] = \frac{S_1^2}{n_1} + \frac{S_0^2}{N - n_1},$$

with $S_1^2$, $S_0^2$ the [population variances](pop-var.md) of $y_1$ and $y_0$: the sample variances are unbiased for the population variances under sampling without replacement.
