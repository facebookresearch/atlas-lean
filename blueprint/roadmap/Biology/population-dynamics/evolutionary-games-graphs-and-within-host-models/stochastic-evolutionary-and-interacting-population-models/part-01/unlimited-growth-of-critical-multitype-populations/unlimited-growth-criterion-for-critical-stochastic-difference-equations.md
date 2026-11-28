# Unlimited growth criterion for critical stochastic difference equations

Let $(\mathbf X_n)$ be random row vectors in $\mathbb R_+^d$ satisfying

$$\mathbf X_{n+1} = \mathbf X_n M + g(\mathbf X_n) + \xi_n, \qquad n \in \mathbb N,$$

where $M$ is a non-negative primitive $d\times d$ matrix with Perron root $\rho = 1$ (the **critical** case), $g : \mathbb R_+^d \to \mathbb R_+^d$ satisfies $\|g(\mathbf x)\| = o(\|\mathbf x\|)$, and $E(\xi_n \mid \mathcal F_n) = 0$ for the natural filtration. Let $u$ and $v$ be the right and left Perron eigenvectors normalized by $vu = u^\top u = 1$, and assume $\sigma^2(\mathbf X_n) = E((\xi_n u)^2 \mid \mathcal F_n)$ is a function of $\mathbf X_n$. Write $\mathbf y = \mathbf x(I - uv)$ for the component transverse to the Perron direction.

**Assumptions.** (A1) For some $\alpha \in (-1,1)$ and constants $c_1, d_1 > 0$,

$$g(\mathbf x)u = c_1 (\mathbf x u)^{\alpha} + h_1(\mathbf y) + f_1(\mathbf x), \qquad \sigma^2(\mathbf x) = d_1 (\mathbf x u)^{1+\alpha} + h_2(\mathbf y) + f_2(\mathbf x),$$

with $|h_1(\mathbf y)| \le c_2\|\mathbf y\|^\alpha$ (and $h_1 \equiv 0$ if $\alpha \le 0$), $|h_2(\mathbf y)| \le d_2\|\mathbf y\|^{1+\alpha}$, $f_1 = o((\mathbf x u)^\alpha)$ and $f_2 = o((\mathbf x u)^{1+\alpha})$. (A2) $E(\|\xi_n\|^{2+\delta} \mid \mathcal F_n) \le A_1 \sigma^{2+\delta}(\mathbf X_n)$ for some $\delta, A_1 > 0$. (A3) For every $C > 0$ some $n$ has $P(\mathbf X_n u \ge C) > 0$. (A4) $g(\mathbf x)u$ is bounded away from $0$ on $\{a < \mathbf x u < b\}$ for $s_1 < a < b$. (A5) $\sigma^2$ is bounded on bounded sets.

**Theorem (Adam, Theorem 2.1).** Assume (A1) and (A2).

1. If $c_1 < d_1/2$, then $P(\|\mathbf X_n\| \to \infty) = 0$.
2. If $c_1 > d_1/2$ and (A3), (A4), (A5) hold, then $P(\|\mathbf X_n\| \to \infty) > 0$.

This extends the one-dimensional Lamperti–Kersting criterion: growth is decided by comparing twice the drift along the Perron direction with the conditional variance, roughly $\lim 2r\, g(rv)u / \sigma^2(rv)$ against $1$, because $M$ preserves the component along $v$ and contracts the others.

## Expansion

The proof follows Kersting's one-dimensional argument applied to the scalar projection $\mathbf X_n u$. If $c_1 < d_1/2$, a second-order expansion shows that $\log(\mathbf X_n u)$ is a supermartingale over blocks of $k$ steps once $\mathbf X_n u$ is large (Lemma 2.1), which rules out escape to infinity. If $c_1 > d_1/2$, the function $L(x) = 1/\log x$ evaluated at $\mathbf X_n u$ is a supermartingale over such blocks (Lemma 2.2), giving escape with positive probability. The transverse component $\mathbf Y_n$ is controlled because $M$ contracts it geometrically, so its contributions to the conditional drift and variance are of lower order (Lemmas 4.1 to 4.3).

## Sources

- E. Adam, *Criterion of unlimited growth for critical multidimensional stochastic models*, arXiv:1502.04046 (2015). <https://doi.org/10.48550/arXiv.1502.04046>. Published version: Advances in Applied Probability 48(4) (2016), 972–988, <https://doi.org/10.1017/apr.2016.61>; locators above refer to the arXiv version.
