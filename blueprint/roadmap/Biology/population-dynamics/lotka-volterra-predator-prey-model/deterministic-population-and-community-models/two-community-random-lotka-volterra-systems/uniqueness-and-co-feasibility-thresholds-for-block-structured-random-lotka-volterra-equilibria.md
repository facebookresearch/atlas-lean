# Uniqueness and co-feasibility thresholds for block-structured random Lotka–Volterra equilibria

Consider $n$ species in two communities $\mathcal I_1,\mathcal I_2$ of proportions $\beta_1=n_1/n$ and $\beta_2=1-\beta_1$, with Lotka–Volterra dynamics

$$
\dot x_k=x_k\big(1-x_k+(B\mathbf x)_k\big),\qquad B=\frac1{\sqrt n}\begin{pmatrix}s_{11}A_{11}&s_{12}A_{12}\\ s_{21}A_{21}&s_{22}A_{22}\end{pmatrix},
$$

where the $A_{ij}$ have i.i.d. standard Gaussian entries and $\mathbf s=(s_{ij})$ is the $2\times2$ matrix of within- and between-community interaction strengths.

**Unique globally stable equilibrium.** If

$$
\big\|\big((\mathbf s\circ\mathbf s)+(\mathbf s\circ\mathbf s)^\top\big)\mathrm{diag}(\boldsymbol\beta)\big\|_\infty<1,
$$

where $\|X\|_\infty=\max_k\sum_\ell|X_{k\ell}|$ and $(\mathbf s\circ\mathbf s)_{ij}=s_{ij}^2$, that is $\max\{2s_{11}^2\beta_1+(s_{12}^2+s_{21}^2)\beta_2,\ (s_{12}^2+s_{21}^2)\beta_1+2s_{22}^2\beta_2\}<1$, then almost surely $(I-B)+(I-B)^\top$ is eventually positive definite, so $-I+B$ is Lyapunov diagonally stable. By the Takeuchi–Adachi theorem the associated linear complementarity problem has a unique solution $\mathbf x^*$, which is the unique globally stable equilibrium (some species may be at zero).

This corrects Theorem 2 of the source, which prints the condition $\left\|\mathrm{diag}(\boldsymbol{\beta}) \left((\mathbf{s} \circ \mathbf{s})+(\mathbf{s} \circ \mathbf{s})^{\top}\right) \right\|_\infty < 1$, with $\mathrm{diag}(\boldsymbol\beta)$ on the left. Its proof bounds the spectrum of $H=B+B^\top$ by $2\|S\|_\infty^{1/2}$, where the row sums of the variance profile $S$ of $H$ are the two entries of the maximum above. With $\beta_1=0.1$, $s_{11}^2=4.3$, $s_{12}^2=0.95$, $s_{21}^2=0.05$ and $s_{22}^2=0.01$ the printed quantity is $0.96<1$, but the source's quadratic vector equation (12) puts the spectral edge of $H$ near $2.28>2$.

**Co-feasibility threshold.** Let $\mathbf s=\mathbf s_n\to0$, let $\mathbf x_n=(I-B_n)^{-1}\mathbf 1$ be the interior equilibrium, and set $s_n^*=1/\sqrt{2\log n}$.

- If eventually $\|(\mathbf s_n\circ\mathbf s_n)\boldsymbol\beta^\top\|_\infty\ge(1+\varepsilon)(s_n^*)^2$ for some $\varepsilon>0$, then $\mathbb P(\min_kx_k>0)\to0$.
- If eventually $\|(\mathbf s_n\circ\mathbf s_n)\boldsymbol\beta^\top\|_\infty\le(1-\varepsilon)(s_n^*)^2$, then $\mathbb P(\min_kx_k>0)\to1$.

So all species of both communities coexist exactly when the largest community-wise effective interaction variance $\max_i\sum_j\beta_js_{ij}^2$ is below $1/(2\log n)$. This generalizes the single-community threshold $\sigma\sqrt{2\log n}=1$.

## Proof sketch

Positive definiteness of the symmetric part follows from the block variance profile: the spectral norm of $(B+B^\top)$ is asymptotically at most $2\|S\|_\infty^{1/2}$, where $S$ is its variance profile, whose row sums are $2s_{11}^2\beta_1+(s_{12}^2+s_{21}^2)\beta_2$ on the first community and $(s_{12}^2+s_{21}^2)\beta_1+2s_{22}^2\beta_2$ on the second, which gives the stated $\ell^\infty$ condition. For feasibility, $x_k=1+(B\mathbf x)_k$, and for small $\mathbf s_n$ each $(B\mathbf x)_k$ is approximately Gaussian with variance $\sum_j\beta_js_{ij}^2$ for $k$ in community $i$. The minimum of $n$ such Gaussians is about $-\sqrt{2\log n}$ times the largest standard deviation. That is why feasibility switches at $(s_n^*)^2$.

## Related topics

- [Lotka–Volterra predator–prey model](../../README.md)

## Sources

- Maxime Clenet, François Massol and Jamal Najim, "Impact of a block structure on the Lotka-Volterra model", *Peer Community Journal* 4 (2024), e86, <https://doi.org/10.24072/pcjournal.460>. Preprint version: arXiv:2311.09470 (2023), Section 2 (model (eq:LV2), (eq:mat_int), Definition 1, Theorems 1–2) and Section 4 (Theorem 3, Eqs. (eq:fea_fixed), (eq:mat_int_fea)), <https://doi.org/10.48550/arXiv.2311.09470>.
