# Larsen's static lower bound for polynomial evaluation

Let $|\mathbb{F}| \ge n^{1+\varepsilon}$ for a constant $\varepsilon > 0$. Every static cell-probe structure for evaluating polynomials of degree at most $n$ over $\mathbb{F}$ that uses $S$ cells of $w$ bits has query time $t = \Omega\!\left(\frac{\log |\mathbb{F}|}{\log(S w / (n \log |\mathbb{F}|))}\right)$. In particular, with linear space $S w = O(n \log |\mathbb{F}|)$ the query time is $\Omega(\log |\mathbb{F}|)$, and with $|\mathbb{F}| = n^{O(1)}$ this is the first static lower bound of $\Omega(\log n)$ for linear space.

## Proof sketch

Take $P$ uniformly random, so $H(P) = (n+1)\log_2|\mathbb{F}|$. A cell sample of $\Delta = \Theta(n \log|\mathbb{F}| / w)$ cells resolves $|\mathbb{F}| (\Delta/2S)^t$ queries; if this exceeds $n+1$, the resolved evaluations determine $P$, while the sample has only $\Delta(w + \log S) < H(P)$ bits once constants are chosen, contradicting the encoding bound. Thus $|\mathbb{F}|(\Delta/2S)^t \le n+1$, which rearranges to the stated bound.

## Depends on

- [Static polynomial evaluation problem](static-polynomial-evaluation.md)
- [Encoding bound for cell samples](cell-sample-encoding-bound.md)

## Proof depends on

- [Static polynomial evaluation problem](static-polynomial-evaluation.md)
- [Encoding bound for cell samples](cell-sample-encoding-bound.md)

## Sources

- Kasper Green Larsen, "Higher Cell Probe Lower Bounds for Evaluating Polynomials", FOCS (2012).
