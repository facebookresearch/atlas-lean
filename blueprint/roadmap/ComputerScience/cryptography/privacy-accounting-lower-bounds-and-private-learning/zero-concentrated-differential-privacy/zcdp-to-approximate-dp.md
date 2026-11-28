# Conversion from zCDP to approximate differential privacy

If a mechanism is $\rho$-zCDP with $\rho > 0$, then for every $0 < \delta < 1$ it is $(\varepsilon, \delta)$-differentially private with

$$
\varepsilon = \rho + 2\sqrt{\rho \log(1/\delta)} .
$$

If $\rho = 0$, the output laws on neighbouring inputs are equal, so the mechanism is $(0, 0)$-DP; for $\delta \ge 1$ every mechanism is trivially $(0, \delta)$-DP. Consequently, for $\varepsilon_0 > 0$ and $0 < \delta < 1$, $k \ge 1$ adaptively composed $\varepsilon_0$-DP mechanisms are $\big(k\varepsilon_0^2/2 + \varepsilon_0\sqrt{2k\log(1/\delta)}, \delta\big)$-DP, recovering advanced composition with a simple proof.

## Proof sketch

For neighbours, the privacy loss $L$ satisfies $\mathbb{E}_P[e^{(\alpha - 1)L}] = e^{(\alpha-1)D_\alpha} \le e^{(\alpha-1)\alpha\rho}$. By Markov's inequality $\Pr_P[L > \varepsilon] \le e^{(\alpha-1)(\alpha\rho - \varepsilon)}$, and the standard argument shows that $(\varepsilon,\delta)$-DP holds with $\delta$ at most this tail. For $\rho > 0$ and $\varepsilon > \rho$, which holds for the stated $\varepsilon$ because $\log(1/\delta) > 0$, the choice $\alpha = (\varepsilon + \rho)/(2\rho) > 1$ gives $\delta = e^{-(\varepsilon - \rho)^2/(4\rho)}$, which is the stated $\varepsilon$. If $\rho = 0$, then $D_\alpha = 0$ for every $\alpha > 1$ and the laws coincide. The composition corollary combines this with the pure-DP conversion and additivity, at $\rho = k\varepsilon_0^2/2 > 0$.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)
- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [Adaptive composition and post-processing of zCDP](zcdp-composition-and-post-processing.md)
- [Pure differential privacy implies zCDP with half the squared parameter](pure-dp-implies-zcdp.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Proposition 1.3 and Lemma 3.5.
