# Rényi-moment bound for bounded privacy loss

Let $P, Q$ be discrete distributions whose likelihood ratio lies in $[e^{-\varepsilon}, e^{\varepsilon}]$ everywhere (with $\sum P \le \sum Q$ for subdistributions). Then for every $\alpha \ge 1$, with $s = \varepsilon(\alpha - 1)$, the Rényi moment satisfies

$$
\sum_r P(r)\Bigl(\frac{P(r)}{Q(r)}\Bigr)^{\alpha - 1} \le \exp\Bigl(\tanh(\varepsilon/2)\, s + \frac{s^2}{2}\Bigr),
$$

so for $\alpha > 1$, $D_\alpha(P \Vert Q) \le \varepsilon \tanh(\varepsilon/2) + (\alpha - 1)\varepsilon^2/2$. This is the per-round bound behind advanced composition.

## Proof sketch

The privacy loss $L = \log(P/Q)$ under $P$ lies in $[-\varepsilon, \varepsilon]$ and has mean at most $\varepsilon\tanh(\varepsilon/2)$ (because $\mathbb{E}_P[e^{-L}] \le 1$); Hoeffding's lemma bounds its moment generating function.

## Depends on

- [Rényi divergence and Rényi differential privacy](renyi-differential-privacy.md)

## Sources

- Cynthia Dwork and Aaron Roth, "The Algorithmic Foundations of Differential Privacy", Foundations and Trends in Theoretical Computer Science, 2014.
- Mark Bun and Thomas Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", Theory of Cryptography (TCC 2016-B, Part I), 2016.
