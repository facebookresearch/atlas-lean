# Pure differential privacy implies zCDP with half the squared parameter

Every $\varepsilon$-differentially private mechanism is $\dfrac{\varepsilon^2}{2}$-zCDP. Conversely, for every $\rho > 0$, $\rho$-zCDP does not imply $(\varepsilon,0)$-DP for any finite $\varepsilon$ (the Gaussian mechanism with $\Delta^2/(2\sigma^2) = \rho$ for a query of sensitivity $\Delta > 0$ is a counterexample), so zCDP is strictly weaker than pure differential privacy. At $\rho = 0$ the two notions agree: $0$-zCDP forces $M(x)$ and $M(x')$ to have the same law for neighbouring $x, x'$, which is $(0,0)$-DP.

## Proof sketch

For an $\varepsilon$-DP pair the privacy loss $L$ takes values in $[-\varepsilon, \varepsilon]$ and, under $P$, satisfies $\mathbb{E}_P[e^{-L}] = 1$; among laws on $[-\varepsilon, \varepsilon]$ with this constraint the mean is largest for the two-point law on $\{-\varepsilon, \varepsilon\}$, so the mean of $L$ under $P$ (the Kullback–Leibler divergence) is at most $\varepsilon(e^{\varepsilon}-1)/(e^{\varepsilon}+1) \le \varepsilon^2/2$. Hoeffding's lemma applied to the bounded log-likelihood ratio then bounds $\mathbb{E}_P[e^{(\alpha - 1)L}] \le e^{\alpha(\alpha-1)\varepsilon^2/2}$, which is $D_\alpha \le \alpha\varepsilon^2/2$ for every $\alpha > 1$. For $\rho > 0$ and $\Delta > 0$ the Gaussian mechanism has finite $\sigma$ and unbounded privacy loss, so it is not $(\varepsilon,0)$-DP. If $\rho = 0$, then $D_\alpha = 0$ for all $\alpha > 1$, so neighbouring output laws are equal.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)
- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance](gaussian-mechanism-zcdp.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Propositions 1.4 and 3.3.
