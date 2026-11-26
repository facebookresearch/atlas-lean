# Lincoln–Petersen and Chapman capture–recapture estimators

In a closed population of size $N$, mark $n_1$ individuals, then draw a second sample of $n_2$ without replacement and let $m$ be the number of marked individuals in it, so that $m$ is hypergeometric given $(n_1, n_2)$. The Lincoln–Petersen estimator is $n_1 n_2/m$, and Chapman's estimator is

$$\hat N_C = \frac{(n_1 + 1)(n_2 + 1)}{m + 1} - 1;$$

the Lincoln–Petersen estimator is biased in small samples and the Chapman estimator is less biased (Mark and recapture, Wikipedia). In fact Chapman's estimator is exactly unbiased whenever $n_1 + n_2 \ge N$: using $\frac{1}{m+1}\binom{n_1}{m} = \frac{1}{n_1+1}\binom{n_1+1}{m+1}$ and Vandermonde's convolution,

$$E\Bigl[\frac{(n_1+1)(n_2+1)}{m+1}\Bigr] = (N + 1) - (n_2 + 1)\, \frac{\binom{N - n_1}{n_2 + 1}}{\binom{N}{n_2}},$$

and the last binomial coefficient vanishes exactly when $n_1 + n_2 \ge N$, while for $n_1 + n_2 < N$ the displayed term is the (negative) bias of $\hat N_C$. The Lincoln–Petersen estimator is infinite on $\{m = 0\}$, which has positive probability exactly when $n_1 + n_2 \le N$, so it then has infinite mean.

## Expansion

1. The model: the hypergeometric law of $m$ and the two estimators.
2. Chapman's identity for $E[(n_1+1)(n_2+1)/(m+1)]$ and its exact unbiasedness for $n_1 + n_2 \ge N$.
3. The exact bias for $n_1 + n_2 < N$.
4. The support of $m$ and the infinite mean of the Lincoln–Petersen estimator when $n_1 + n_2 \le N$.
5. Variance approximations and the exact moments of the posterior for the population size studied by Webster and Kemp, as separate statements.

## Sources

- Mark and recapture, Wikipedia, sections on the Lincoln–Petersen and Chapman estimators. <https://en.wikipedia.org/wiki/Mark_and_recapture>
- A. J. Webster and R. Kemp, Estimating omissions from searches, 2013, Introduction. <https://arxiv.org/abs/1205.1150>
- Original result: D. G. Chapman, Some properties of the hypergeometric distribution with applications to zoological sample censuses, Univ. California Publ. Statist. 1 (1951), 131–160. The estimator follows Mark and recapture, Wikipedia, and Webster and Kemp (2013).
