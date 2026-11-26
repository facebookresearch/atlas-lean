# Volterra identity for the unit exponential survival function and its hazard measure

For a measure $F$ on $\mathbb R$, its hazard measure is

$$\Lambda_F(B) = \int_B \frac{dF(s)}{F([s, \infty))},$$

the measure with density $s \mapsto F([s, \infty))^{-1} \in [0, \infty]$ with respect to $F$, where $1/0 = \infty$.

Let $\mu_0$ be the exponential distribution with rate $1$, $\Lambda_0 = \Lambda_{\mu_0}$ its hazard measure, and $S(s) = e^{-s}$. For all $0 \le a \le b$,

$$\frac{1}{S(b)} - \frac{1}{S(a)} = \int_{(a, b]} \frac{d\Lambda_0(s)}{S(s)}.$$

## Sources

- R. D. Gill and S. Johansen, A survey of product-integration with a view toward application in survival analysis, Ann. Statist. 18 (1990), 1501–1555.
