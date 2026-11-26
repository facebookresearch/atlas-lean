# Hoeffding's variance formula

Let $\mu$ be a probability measure on a measurable space $\alpha$, $m \le n$, and let $h : \alpha^m \to \mathbb{R}$ be a symmetric kernel ($h(y_{\sigma(1)}, \dots, y_{\sigma(m)}) = h(y)$ for every permutation $\sigma$) that is square-integrable for $\mu^{\otimes m}$. If $X_1, \dots, X_n$ are i.i.d. with law $\mu$, the [U-statistic](u-statistic.md) $U_n$ satisfies

$$\operatorname{Var}(U_n) = \binom{n}{m}^{-1} \sum_{c=1}^{m} \binom{m}{c} \binom{n - m}{m - c} \operatorname{Var}\big(h_c(X_1, \dots, X_c)\big),$$

where $h_c$ is the [Hoeffding projection](hoeffding-proj.md).

## Sources

- Wassily Hoeffding, *A class of statistics with asymptotically normal distribution*, Ann. Math. Statist. 19 (1948), no. 3, 293–325, DOI 10.1214/aoms/1177730196, §5.
