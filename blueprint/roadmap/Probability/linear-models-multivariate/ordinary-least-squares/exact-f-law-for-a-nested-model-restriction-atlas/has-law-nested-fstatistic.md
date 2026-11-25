# Exact F law of the nested-model statistic

Consider $y = X\beta + \varepsilon$ with $n$ observations, an unrestricted design $X$ with $p$ columns and a restricted design $X_0$ with $p_0$ columns, both of full column rank ($X^{\mathsf T} X$ and $X_0^{\mathsf T} X_0$ invertible), with the column space of $X_0$ contained in that of $X$ and $p_0 < p < n$. Let $\sigma > 0$ and suppose $\sigma^{-1}\varepsilon$ is standard Gaussian on $\mathbb R^n$. Under the null hypothesis $X\beta = X_0\beta_0$ for some $\beta_0$, the statistic

$$F = \frac{(\mathrm{RSS}_0 - \mathrm{RSS})/(p - p_0)}{\mathrm{RSS}/(n - p)},$$

where $\mathrm{RSS}$ and $\mathrm{RSS}_0$ are the least-squares residual sums of squares for $X$ and $X_0$, has Snedecor's $F$ distribution with $(p - p_0, n - p)$ degrees of freedom.
