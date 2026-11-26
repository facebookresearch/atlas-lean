# Low-degree advantage of the additive Gaussian model

In the **additive Gaussian model**, $\mathbb{Q}_n$ is the law of $Z \sim \mathcal{N}(0, I_N)$ and $\mathbb{P}_n$ is the law of $Y = X + Z$ with $X$ drawn from a prior $\mathcal{X}_n$ on $\mathbb{R}^N$ independent of $Z$. Then

$$
\|L_n^{\le D}\|^2 = \sum_{d=0}^{D} \frac{1}{d!}\,\mathbb{E}_{X, X' \sim \mathcal{X}_n}\big[\langle X, X'\rangle^d\big], \qquad \|L_n\|^2 = \mathbb{E}_{X, X'}\big[e^{\langle X, X'\rangle}\big],
$$

where $X, X'$ are independent draws from the prior. Hence the low-degree advantage is a truncated exponential moment of the overlap of two independent signals.

## Proof sketch

Expand $L_n(Y) = \mathbb{E}_X[\exp(\langle X, Y\rangle - \|X\|^2/2)]$ in the orthonormal basis of normalized multivariate Hermite polynomials $h_\alpha/\sqrt{\alpha!}$ of $L^2(\mathcal{N}(0,I))$: the generating function of Hermite polynomials gives coefficients $\mathbb{E}_X[X^\alpha]/\sqrt{\alpha!}$. The projection onto degree at most $D$ keeps $|\alpha| \le D$, and $\sum_{|\alpha| = d}\mathbb{E}[X^\alpha]^2/\alpha! = \mathbb{E}[\langle X, X'\rangle^d]/d!$ by the multinomial theorem applied to independent copies.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)

## Proof depends on

- [Hermite expansion of the Gaussian likelihood ratio](hermite-expansion-of-likelihood-ratio.md)

## Sources

- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
