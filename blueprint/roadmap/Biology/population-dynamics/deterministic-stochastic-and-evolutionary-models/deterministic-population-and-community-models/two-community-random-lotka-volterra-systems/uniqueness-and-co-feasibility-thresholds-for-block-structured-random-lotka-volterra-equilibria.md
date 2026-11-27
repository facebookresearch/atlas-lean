# Uniqueness and co-feasibility thresholds for block-structured random Lotka–Volterra equilibria

Consider $n$ species in two communities $\mathcal I_1,\mathcal I_2$ of proportions $\beta_1=n_1/n$ and $\beta_2=1-\beta_1$, with Lotka–Volterra dynamics

$$
\dot x_k=x_k\big(1-x_k+(B\mathbf x)_k\big),\qquad B=\frac1{\sqrt n}\begin{pmatrix}s_{11}A_{11}&s_{12}A_{12}\\ s_{21}A_{21}&s_{22}A_{22}\end{pmatrix},
$$

where the $A_{ij}$ have i.i.d. standard Gaussian entries and $\mathbf s=(s_{ij})$ is the $2\times2$ matrix of within- and between-community interaction strengths.

**Unique globally stable equilibrium.** If

$$
\big\|\mathrm{diag}(\boldsymbol\beta)\big((\mathbf s\circ\mathbf s)+(\mathbf s\circ\mathbf s)^\top\big)\big\|_\infty<1,
$$

then almost surely $(I-B)+(I-B)^\top$ is eventually positive definite, so $-I+B$ is Lyapunov diagonally stable. By the Takeuchi–Adachi theorem the associated linear complementarity problem has a unique solution $\mathbf x^*$, which is the unique globally stable equilibrium (some species may be at zero).

**Co-feasibility threshold.** Let $\mathbf s=\mathbf s_n\to0$, let $\mathbf x_n=(I-B_n)^{-1}\mathbf 1$ be the interior equilibrium, and set $s_n^*=1/\sqrt{2\log n}$.

- If eventually $\|(\mathbf s_n\circ\mathbf s_n)\boldsymbol\beta^\top\|_\infty\ge(1+\varepsilon)(s_n^*)^2$ for some $\varepsilon>0$, then $\mathbb P(\min_kx_k>0)\to0$.
- If eventually $\|(\mathbf s_n\circ\mathbf s_n)\boldsymbol\beta^\top\|_\infty\le(1-\varepsilon)(s_n^*)^2$, then $\mathbb P(\min_kx_k>0)\to1$.

So all species of both communities coexist exactly when the largest community-wise effective interaction variance $\max_i\sum_j\beta_js_{ij}^2$ is below $1/(2\log n)$. This generalizes the single-community threshold $\sigma\sqrt{2\log n}=1$.

## Proof sketch

Positive definiteness of the symmetric part follows from the block variance profile: the spectral norm of $(B+B^\top)$ is controlled by the row sums of the variance profile, which gives the stated $\ell^\infty$ condition. For feasibility, $x_k=1+(B\mathbf x)_k$, and for small $\mathbf s_n$ each $(B\mathbf x)_k$ is approximately Gaussian with variance $\sum_j\beta_js_{ij}^2$ for $k$ in community $i$. The minimum of $n$ such Gaussians is about $-\sqrt{2\log n}$ times the largest standard deviation. That is why feasibility switches at $(s_n^*)^2$.

## Related topics

- [Lotka–Volterra predator–prey model](../../../lotka-volterra-predator-prey-model/README.md)

## Sources

- Maxime Clenet, François Massol and Jamal Najim, "Impact of a block structure on the Lotka-Volterra model", *Peer Community Journal* 4 (2024), e86, <https://doi.org/10.24072/pcjournal.460>. Preprint version: arXiv:2311.09470 (2023), Section 2 (model (eq:LV2), (eq:mat_int), Definition 1, Theorems 1–2) and Section 4 (Theorem 3, Eqs. (eq:fea_fixed), (eq:mat_int_fea)), <https://doi.org/10.48550/arXiv.2311.09470>.
