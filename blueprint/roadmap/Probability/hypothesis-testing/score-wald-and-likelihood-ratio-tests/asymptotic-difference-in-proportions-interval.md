# Asymptotic normality of the difference of two sample proportions

Let $X \sim \mathrm{Bin}(m, p_1)$ and $Y \sim \mathrm{Bin}(n, p_2)$ be independent with $p_1, p_2 \in (0, 1)$, and let $m, n \to \infty$ with $m/(m+n) \to \kappa \in (0, 1)$. Put $\hat p_1 = X/m$, $\hat p_2 = Y/n$, $V = \hat p_1(1 - \hat p_1)/m + \hat p_2(1 - \hat p_2)/n$, and $Z = (\hat p_1 - \hat p_2 - (p_1 - p_2))/\sqrt V$ when $V > 0$, $Z = 0$ when $V = 0$. Then $Z$ converges in distribution to $N(0, 1)$, since $P(V = 0) \to 0$, and for $0 < \alpha < 1$ the Wald interval $\hat p_1 - \hat p_2 \pm z_{1-\alpha/2}\sqrt V$ has coverage tending to $1 - \alpha$. The coverage is asymptotic, not exact.

## Proof depends on

- [Slutsky's theorem (ratio form)](../../statistical-estimation/asymptotic-normality-of-maximum-likelihood/div-of-tendsto-in-measure-const.md): the ratio of the asymptotically normal numerator and the consistent standard error.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Central limit theorem for the standardized difference of two independent binomial proportions with $m/(m+n) \to \kappa \in (0,1)$.
- Consistency of $mV$-type variance estimators by the law of large numbers.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
