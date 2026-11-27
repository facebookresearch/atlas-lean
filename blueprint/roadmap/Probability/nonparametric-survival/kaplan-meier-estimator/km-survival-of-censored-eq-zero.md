# Kaplan–Meier estimate without censoring is the empirical survival

For [grouped right-censored data](censored-data.md) with no censoring ($c_j = 0$ for every $j$) and sample size $n > 0$, for every $t \in \mathbb{R}$,

$$\hat S(t) = \frac{1}{n} \sum_{j : t_j > t} d_j,$$

the fraction $\#\{\text{observations} > t\}/n = 1 - F_n(t)$ of the empirical survival function.
