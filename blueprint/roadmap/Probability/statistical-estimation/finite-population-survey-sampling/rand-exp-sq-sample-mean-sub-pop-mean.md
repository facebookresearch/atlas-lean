# Variance of the sample mean under simple random sampling

Let $U$ be a finite population of $N$ units with real values $y : U \to \mathbb{R}$, and let $1 \le n \le N$. Under simple random sampling without replacement every $n$-element subset $S \subseteq U$ is drawn with probability $1/\binom{N}{n}$; write $\mathbb{E}_n[f] = \binom{N}{n}^{-1} \sum_{|S| = n} f(S)$ for the expectation of a statistic $f$ of the sample. Write $\bar y_S = \frac1n \sum_{i \in S} y_i$ for the sample mean and $\bar Y = \frac1N \sum_{i \in U} y_i$ for the population mean. Let $S_y^2 = \frac{1}{N-1} \sum_{i \in U} (y_i - \bar Y)^2$ be the population variance with divisor $N - 1$, taken to be $0$ when $N = 1$. Then the variance of the sample mean carries the finite population correction $1 - n/N$:

$$\mathbb{E}_n\big[(\bar y_S - \bar Y)^2\big] = \Big(1 - \frac{n}{N}\Big) \frac{S_y^2}{n}.$$

In the census case $n = N$ both sides are $0$.

## Sources

- Penn State STAT 506, *Sampling Theory and Methods*, Lesson 1, Section 1.3, "Estimating Population Mean and Total under SRS".
- S. K. Thompson, *Sampling*, Section 2.6.
