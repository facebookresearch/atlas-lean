# Coupled distance of SGM along a fixed index sequence

Let every loss $\ell(\cdot, z)$ be convex, differentiable and $L$-Lipschitz on a real Hilbert space, with $\beta$-Lipschitz gradient, and let $0 \le \alpha_t \le 2/\beta$. Let $S$ and $S'$ be samples that differ only in their $k$-th example, and run the stochastic gradient method from the same $w_0$ on $S$ and on $S'$ with the same index sequence $\iota$. Then after $t$ steps

$$
\lVert w_t - w'_t \rVert \le \sum_{s < t,\ \iota(s) = k} 2\, \alpha_s L .
$$

Proof: by induction with the [growth recursion](norm-sub-le-min-mul-add-two-mul.md). When $\iota(s) \ne k$, both runs apply the same gradient update, which is [non-expansive](../../../../Analysis/convex-analysis-and-variations/gradient-descent/norm-gradient-step-sub-le.md); when $\iota(s) = k$, both updates are [$\alpha_s L$-bounded](../../../../Analysis/convex-analysis-and-variations/gradient-descent/norm-smul-gradient-le.md) and the distance grows by at most $2\alpha_s L$.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, proof of Theorem 3.8 (Lemma 2.5 with Lemmas 3.3 and 3.7.2), along a fixed realization of the indices.
