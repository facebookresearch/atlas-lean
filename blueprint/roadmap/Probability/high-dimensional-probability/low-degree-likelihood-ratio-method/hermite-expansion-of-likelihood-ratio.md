# Hermite expansion of the Gaussian likelihood ratio

Let $h_k$ be the probabilists' Hermite polynomials and $h_\alpha(y) = \prod_i h_{\alpha_i}(y_i)$ for multi-indices $\alpha \in \mathbb{N}^N$; the functions $h_\alpha/\sqrt{\alpha!}$ form an orthonormal basis of $L^2(\mathcal{N}(0, I_N))$. In the additive Gaussian model with prior $\mathcal{X}$, the likelihood ratio is $L(y) = \mathbb{E}_{X}\big[\exp(\langle X, y\rangle - \|X\|^2/2)\big]$, and its coefficients in this basis are

$$
\Big\langle L, \frac{h_\alpha}{\sqrt{\alpha!}} \Big\rangle = \frac{\mathbb{E}_X[X^\alpha]}{\sqrt{\alpha!}}, \qquad X^\alpha = \prod_i X_i^{\alpha_i}.
$$

Hence $L^{\le D} = \sum_{|\alpha| \le D}\mathbb{E}_X[X^\alpha]\,h_\alpha/\alpha!$.

## Proof sketch

Use the generating function $\exp(xy - x^2/2) = \sum_{k \ge 0} h_k(y)x^k/k!$ in each coordinate and take the expectation over $X$ (exchanging sum and expectation by dominated convergence when the prior has enough exponential moments), which gives $L = \sum_\alpha \mathbb{E}[X^\alpha]h_\alpha/\alpha!$; orthonormality of $h_\alpha/\sqrt{\alpha!}$ yields the coefficients.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)

## Sources

- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
