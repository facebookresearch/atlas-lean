# Bulk-surface oligomerization model with recruitment feedback and its mass conservation

**Model.** A cell occupies a bounded domain $\Omega$ with smooth boundary (plasma membrane) $\Gamma = \partial\Omega$. A cytosolic ligand with concentration $u(x,t)$, $x \in \Omega$, diffuses freely and binds the membrane, forming surface monomers $a_1$ that diffuse laterally and aggregate by monomer attachment into oligomers $a_j$ of size $j \le N$ on $\Gamma$. The largest oligomers recruit further ligand (positive feedback), so the membrane flux is

$$
f(u, a_1, a_N) = (k_0 + k_b a_N)\, u - k_d a_1,
$$

with basal binding rate $k_0$, recruitment rate $k_b$ and unbinding rate $k_d$, all positive. The dynamics are

$$
\begin{aligned}
\partial_t u &= D_u \nabla^2 u \ \text{ in } \Omega, \qquad -D_u\, \mathbf{n}\cdot\nabla u = (k_0 + k_b a_N) u - k_d a_1 \ \text{ on } \Gamma,\\
\partial_t a_1 &= D_1 \Delta_\Gamma a_1 + (k_0 + k_b a_N) u - k_d a_1 - 2 k_m a_1^2 + 2 k_2 a_2 - k_g a_1 \sum_{l=2}^{N-1} a_l + \sum_{j=3}^{N} k_j a_j,\\
\partial_t a_2 &= D_2 \Delta_\Gamma a_2 + k_m a_1^2 - k_g a_1 a_2 - k_2 a_2 + k_3 a_3,\\
\partial_t a_j &= D_j \Delta_\Gamma a_j + k_g a_1 a_{j-1} - k_g a_1 a_j - k_j a_j + k_{j+1} a_{j+1}, \qquad 3 \le j \le N - 1,\\
\partial_t a_N &= D_N \Delta_\Gamma a_N + k_g a_1 a_{N-1} - k_N a_N,
\end{aligned}
$$

where $\Delta_\Gamma$ is the Laplace–Beltrami operator, $k_m$ the dimerization rate, $k_g$ the common attachment rate for larger oligomers and $k_j$ the rate at which a $j$-mer releases a monomer (a reversible Smoluchowski aggregation scheme).

**Proposition (mass conservation).** For classical solutions, the total number of ligand molecules

$$
M(t) = \int_\Omega u(x,t)\, dx + \sum_{j=1}^{N} j \int_\Gamma a_j(x,t)\, ds
$$

is constant in time: $M(t) = M_0$ for all $t \ge 0$.

**Well-mixed cytosol limit.** If cytosolic diffusion is fast ($D_u \to \infty$) and $u$ is initially uniform, then $u = u(t)$ is spatially constant and conservation gives the nonlocal closure $u(t) = |\Omega|^{-1}\big[M_0 - \sum_j j \int_\Gamma a_j\, ds\big]$, which turns the model into a nonlocal reaction–diffusion system posed on the membrane alone.

## Expansion

Differentiating $M$, the bulk term gives $\int_\Omega D_u\nabla^2 u = \int_\Gamma D_u\, \mathbf{n}\cdot\nabla u = -\int_\Gamma f$ by the divergence theorem and the flux boundary condition. On the closed surface $\Gamma$ every Laplace–Beltrami term integrates to zero, and in $\sum_j j\, \partial_t a_j$ the oligomerization terms telescope: each attachment $A_{j-1} + A_1 \to A_j$ removes $j-1$ and $1$ monomer units and adds $j$, and each release reverses this. What remains is exactly $+\int_\Gamma f$ from the $a_1$ equation, which cancels the bulk loss.

## Sources

- Lucas M. Stolerman, Michael Getz, Stefan G. Llewellyn Smith, Michael Holst, Padmini Rangamani, "Stability Analysis of a Bulk–Surface Reaction Model for Membrane Protein Clustering", Bulletin of Mathematical Biology 82 (2020), 30, <https://doi.org/10.1007/s11538-020-00703-4>. Published version of arXiv:1908.05214, cited next; locators there refer to the arXiv version.
- L. M. Stolerman, M. Getz, S. G. Llewellyn Smith, M. Holst, "Stability Analysis of a Bulk-Surface Reaction Model for Membrane-Protein Clustering," arXiv 2019. Section 2 (model assumptions and governing equations), Proposition 2.1 (mass conservation), Section 2 subsection "System Reduction when $D_u \to \infty$". <https://doi.org/10.48550/arXiv.1908.05214>
