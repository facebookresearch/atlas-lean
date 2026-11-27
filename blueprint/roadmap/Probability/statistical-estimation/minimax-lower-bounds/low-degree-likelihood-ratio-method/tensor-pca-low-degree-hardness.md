# Low-degree hardness of tensor principal component analysis

Let $p \ge 3$ and consider the spiked tensor model in which $\mathbb{Q}$ is the law of an order-$p$ tensor $W$ with i.i.d. standard Gaussian entries and $\mathbb{P}$ is the law of $Y = \lambda x^{\otimes p} + W$, with $x$ uniform on $\{\pm 1\}^n$. Detection is information-theoretically possible once $\lambda \gg n^{(1-p)/2}$ (up to logarithmic factors), whereas, for constants $0 < A_p < B_p$ depending only on $p$ (KWB Theorem 3.3), the low-degree advantage satisfies $\|L^{\le D}\| = O(1)$ whenever $\lambda \le A_p n^{-p/4} D^{(2-p)/4}$ for all large $n$, and $\|L^{\le D}\| = \omega(1)$ whenever $\lambda \ge B_p n^{-p/4} D^{(2-p)/4}$, $D = \omega(1)$ and $D \le 2n/p$ for all large $n$; polynomial-time spectral and sum-of-squares algorithms succeed for $\lambda \gg n^{-p/4}$ up to logarithmic factors. Under the low-degree conjecture this predicts a statistical-computational gap of a polynomial factor $n^{(p-2)/4}$. For $D = n^{\delta}$ with a fixed $0 < \delta < 1$, which meets both side conditions, taking degree-$D$ polynomials as a proxy for time $\exp(\tilde O(n^{\delta}))$ predicts that such algorithms succeed when $\lambda \ge B_p n^{-p/4 - \delta(p-2)/4}$ and fail when $\lambda \le A_p n^{-p/4 - \delta(p-2)/4}$, up to the logarithmic factors of the proxy.

## Proof sketch

By the additive Gaussian lemma, $\|L^{\le D}\|^2 = \sum_{d \le D}\frac{\lambda^{2d}}{d!}\mathbb{E}[\langle x, x'\rangle^{pd}]$, where $\langle x, x'\rangle$ is a sum of $n$ independent signs. Bounding $\mathbb{E}[\langle x,x'\rangle^{pd}] \le (Cpd\,n)^{pd/2}$ by moment bounds for Rademacher sums, the $d$-th term is at most $\big(C\lambda^2 n^{p/2}d^{p/2 - 1}\big)^d$, which is summable when $\lambda^2 \ll n^{-p/2}D^{1 - p/2}$, that is, $\lambda \ll n^{-p/4}D^{(2-p)/4}$.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)
- [Low-degree conjecture](low-degree-conjecture.md)

## Proof depends on

- [Low-degree advantage of the additive Gaussian model](additive-gaussian-low-degree-advantage.md)

## Sources

- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
