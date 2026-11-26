# Rényi-moment bound for bounded privacy loss

Let $\varepsilon > 0$ and let $P, Q$ be discrete probability distributions on the same set whose likelihood ratio satisfies $e^{-\varepsilon} \le P(r)/Q(r) \le e^{\varepsilon}$ for every $r$. Then for every $\alpha > 1$ the order-$\alpha$ Rényi moment satisfies

$$
\sum_r P(r)\Bigl(\frac{P(r)}{Q(r)}\Bigr)^{\alpha - 1} \le \frac{\sinh(\alpha\varepsilon) - \sinh((\alpha - 1)\varepsilon)}{\sinh(\varepsilon)},
$$

with equality when the likelihood ratio takes only the values $e^{-\varepsilon}$ and $e^{\varepsilon}$. Consequently $D_\alpha(P \Vert Q) \le \alpha\varepsilon^2/2$ for every $\alpha > 1$.

## Proof sketch

Write the likelihood ratio at each point as the mean of a random variable $A$ with values in $\{e^{-\varepsilon}, e^{\varepsilon}\}$. Jensen's inequality bounds the moment $\mathbb{E}_{r \sim Q}[(P(r)/Q(r))^{\alpha}]$ by $\mathbb{E}[A^{\alpha}]$, and $\mathbb{E}[A] = 1$ fixes the law of $A$, which gives the displayed value. For $\alpha\varepsilon \le 2$, the inequality $\sinh(x) - \sinh(y) \le \sinh(x - y)\, e^{xy/2}$ for $0 \le y < x \le 2$ gives $D_\alpha(P \Vert Q) \le \alpha\varepsilon^2/2$; for $\alpha\varepsilon > 2$ the bound exceeds $\varepsilon \ge D_\infty(P \Vert Q) \ge D_\alpha(P \Vert Q)$.

## Depends on

- [Rényi divergence and Rényi differential privacy](renyi-differential-privacy.md)

## Sources

- Mark Bun and Thomas Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", Theory of Cryptography (TCC 2016-B, Part I), 2016; arXiv:1605.02065v2, Proposition 3.3 and its proof, and Lemma B.1.
