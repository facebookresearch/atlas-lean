# Larsen's static lower bound for polynomial evaluation

Let $n^{1+\varepsilon} \le |\mathbb{F}| \le n^{O(1)}$ for a constant $\varepsilon > 0$, and let cells have $w = \Theta(\log n)$ bits, Larsen's standard setting. Every static cell-probe structure for evaluating polynomials of degree at most $n$ over $\mathbb{F}$ that uses $S$ cells of $w$ bits has query time $t = \Omega\!\left(\frac{\log |\mathbb{F}|}{\log(S w / (n \log |\mathbb{F}|))}\right)$, with the logarithm in the denominator read as at least a positive constant (Theorem 1). The bound holds also for the expected query time of randomized structures with any constant error probability $\delta < 1/2$. Some bound on $w$ is needed, since a single cell of $w \ge (n+1)\log_2|\mathbb{F}|$ bits holds all coefficients. In particular, with linear space $S = O(n \log |\mathbb{F}| / w)$ the query time is $\Omega(\log |\mathbb{F}|)$, which is $\Omega(\log d)$ for a problem with $d = |\mathbb{F}|$ queries, above the previous best $\Omega(\log d/\log\log d)$ static bound of Pătraşcu and Thorup.

## Proof sketch

For a deterministic structure, take $P$ uniformly random, so $H(P) = (n+1)\log_2|\mathbb{F}|$. A cell sample of $\Delta = \Theta(n \log|\mathbb{F}| / w)$ cells resolves $|\mathbb{F}| (\Delta/2S)^t$ queries; if this exceeds $n+1$, the resolved evaluations determine $P$, while the sample has only $\Delta(w + \log S) < H(P)$ bits once constants are chosen, contradicting the encoding bound. Thus $|\mathbb{F}|(\Delta/2S)^t \le n+1$, which rearranges to the stated bound since $|\mathbb{F}| \ge n^{1+\varepsilon}$. Larsen's Lemma 1 handles randomized structures by also bounding the resolved queries that err.

## Depends on

- [Static polynomial evaluation problem](static-polynomial-evaluation.md)
- [Static cell-probe structure with space $S$ and query time $t$](static-cell-probe-structure.md)

## Proof depends on

- [Cell-sampling lemma](cell-sampling-lemma.md)
- [Encoding bound for cell samples](cell-sample-encoding-bound.md)

## Sources

- Kasper Green Larsen, "Higher Cell Probe Lower Bounds for Evaluating Polynomials", FOCS (2012).
