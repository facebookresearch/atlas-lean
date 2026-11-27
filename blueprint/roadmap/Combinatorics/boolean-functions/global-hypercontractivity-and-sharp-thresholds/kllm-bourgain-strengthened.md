# Bourgain's sharp-threshold theorem with global hypercontractivity

For every $\alpha \in (0, 1/2]$ there is a constant $C_\alpha > 0$, depending only on $\alpha$, such that the following holds for every $K > 0$, every $0 < p \le 1/2$ and every monotone $\mathcal{A} \subseteq \{0,1\}^n$ with $\mu_p(\mathcal{A}) \in [\alpha, 1 - \alpha]$: if the total influence satisfies $p\, I_p[\mathcal{A}] \le K$, then there is $S \subseteq [n]$ with $|S| \le C_\alpha K$ such that

$$
\mu_p\bigl(\mathcal{A}_{S \to \mathbf{1}}\bigr) \ge \mu_p(\mathcal{A}) + e^{-C_\alpha K}.
$$

This is Keevash, Lifshitz, Long and Minzer's Theorem 1.4. Bourgain's theorem, as they recall it, gives a set of $O(K)$ coordinates with the weaker boost $e^{-O(K^2)}$; the bound $e^{-O(K)}$ is sharp up to the constant in the exponent, by Ben-Or and Linial's anti-tribes example.

## Proof sketch

Keevash, Lifshitz, Long and Minzer prove that every Boolean $f$ with $p\, I[f] \le K\mu_p(f)(1 - \mu_p(f))$ has a set $S$ of $O(K)$ coordinates with generalized influence $I_S(f) \ge e^{-O(K)}$ (their Theorem 5.7): if all generalized influences of small sets were tiny, global hypercontractivity applied to the derivatives of $f$ would make the low-degree Fourier weight $\|f^{\le r}\|_2^2 - \mu_p(f)^2$ small, while $p\, I[f] \le K\mu_p(f)(1-\mu_p(f))$ makes the weight above level $r$ small, contradicting $\|f\|_2^2 - \mu_p(f)^2 = \mu_p(f)(1 - \mu_p(f))$. For monotone $f$, if $\mu_p(f_{J \to 1}) \le \mu_p(f) + \delta$ for every $J$ with $|J| \le r$, then $I_S(f) \le 8^{r}\delta$ for every nonempty $S$ with $|S| \le r$ (their Lemma 4.3); applied with $\delta$ below the influence bound, this turns a large generalized influence into a boost of the measure.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Proof depends on

- [Keevash–Lifshitz–Long–Minzer: hypercontractivity for global functions](kllm-global-hypercontractivity.md)
- [Globalness is equivalent to small generalized influences](global-vs-generalized-influence.md)

## Sources

- J. Bourgain, "On sharp thresholds of monotone properties" (appendix to E. Friedgut, "Sharp thresholds of graph properties, and the k-sat problem"), Journal of the American Mathematical Society 12 (1999) 1017-1054.
- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024) 245-279, arXiv:1906.05568, Theorem 1.4, Lemma 4.3 and Theorem 5.7.
