# Hermite expansion of the Gaussian likelihood ratio

Let $h_k$ be the probabilists' Hermite polynomials and $h_\alpha(y) = \prod_i h_{\alpha_i}(y_i)$ for multi-indices $\alpha \in \mathbb{N}^N$; the functions $h_\alpha/\sqrt{\alpha!}$ form an orthonormal basis of $L^2(\mathcal{N}(0, I_N))$. In the additive Gaussian model with prior $\mathcal{X}$, the likelihood ratio is $L(y) = \mathbb{E}_{X}\big[\exp(\langle X, y\rangle - \|X\|^2/2)\big]$. Assume $\mathbb{E}_{X, X'}[e^{\langle X, X'\rangle}] < \infty$ for independent $X, X' \sim \mathcal{X}$, which is equivalent to $L \in L^2(\mathcal{N}(0, I_N))$ (KWB Definition 1.14 projects within $L^2$); a prior with Cauchy coordinates violates it, and then even $\langle L, h_\alpha\rangle = \mathbb{E}_{Y \sim \mathbb{P}}[h_\alpha(Y)]$ is undefined for $|\alpha| = 1$, although the density formula for $L$ still holds. Under this assumption $X$ has finite moments of all orders, the coefficients of $L$ in this basis are

$$
\Big\langle L, \frac{h_\alpha}{\sqrt{\alpha!}} \Big\rangle = \frac{\mathbb{E}_X[X^\alpha]}{\sqrt{\alpha!}}, \qquad X^\alpha = \prod_i X_i^{\alpha_i},
$$

and $L = \sum_\alpha \mathbb{E}_X[X^\alpha]\,h_\alpha/\alpha!$ in $L^2$. Hence $L^{\le D} = \sum_{|\alpha| \le D}\mathbb{E}_X[X^\alpha]\,h_\alpha/\alpha!$.

## Proof sketch

Since $L$ and $h_\alpha$ lie in $L^2$, the coefficient $\langle L, h_\alpha\rangle = \mathbb{E}_{Y \sim \mathbb{P}}[h_\alpha(Y)]$ is finite, so $Y = X + Z$, and hence $X$, has all moments. By Fubini it equals $\mathbb{E}_X\big[\mathbb{E}_Z h_\alpha(X + Z)\big] = \mathbb{E}_X[X^\alpha]$, using $\mathbb{E}_{z \sim \mathcal{N}(0,1)}[h_k(x + z)] = x^k$, which follows from the generating function $\exp(ty - t^2/2) = \sum_{k \ge 0} h_k(y)t^k/k!$ at $y = x + z$. Completeness and orthonormality of $h_\alpha/\sqrt{\alpha!}$ give the expansion.

## Depends on

- [Low-degree likelihood ratio and low-degree advantage](low-degree-likelihood-ratio.md)

## Sources

- D. Kunisky, A. S. Wein, A. S. Bandeira, "Notes on Computational Hardness of Hypothesis Testing: Predictions Using the Low-Degree Likelihood Ratio", Mathematical Analysis, its Applications and Computation, Springer (2022), arXiv:1907.11636.
