# Pure differential privacy implies zCDP with half the squared parameter

Every $\varepsilon$-differentially private mechanism is $\dfrac{\varepsilon^2}{2}$-zCDP. Conversely, $\rho$-zCDP does not imply $(\varepsilon,0)$-DP for any finite $\varepsilon$ (the Gaussian mechanism is a counterexample), so zCDP is strictly weaker than pure differential privacy.

## Proof sketch

For an $\varepsilon$-DP pair the privacy loss $L$ takes values in $[-\varepsilon, \varepsilon]$ and, under $P$, has mean (the Kullback–Leibler divergence) at most $\varepsilon(e^{\varepsilon}-1)/(e^{\varepsilon}+1) \le \varepsilon^2/2$; Hoeffding's lemma applied to the bounded log-likelihood ratio, together with the identity $\mathbb{E}_Q[e^{-L}] = 1$, bounds $\mathbb{E}_P[e^{(\alpha - 1)L}] \le e^{\alpha(\alpha-1)\varepsilon^2/2}$, which is $D_\alpha \le \alpha\varepsilon^2/2$. The Gaussian mechanism has unbounded privacy loss, so it is not $(\varepsilon,0)$-DP.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)
- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [The Gaussian mechanism satisfies zCDP with parameter sensitivity squared over twice the variance](gaussian-mechanism-zcdp.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Propositions 1.4 and 3.3.
