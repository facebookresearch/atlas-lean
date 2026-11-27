# Order-1/N Dirichlet approximation of the stationary Wright–Fisher chain

**Model.** A haploid population of fixed size $N$ carries $K$ allele types. Given type frequencies $u=(u_1,\dots,u_{K-1})$ (with $u_K=1-\sum_{i<K}u_i$), each offspring picks a parent uniformly and then mutates to type $j$ with probability $p_j$ independently of the parent's type (parent-independent mutation), so the next generation's frequencies $y$ have the multinomial transition probabilities

$$P_u(y)=\binom{N}{Ny_1,\dots,Ny_{K-1}}\prod_{j}\Big(u_j\big(1-\textstyle\sum_{i=1}^Kp_i\big)+p_j\Big)^{Ny_j}.$$

Assume $p_i=\beta_i/(2N)$ for fixed $\boldsymbol\beta=(\beta_1,\dots,\beta_K)$ with all $\beta_i>0$. The finite chain is irreducible and aperiodic; let $U$ have its stationary distribution and let $Z\sim\mathrm{Dirichlet}(\beta_1,\dots,\beta_K)$, the stationary law of the limiting Wright-Fisher diffusion with mutation.

**Metric.** $\mathcal{M}_4$ is the class of $h:\mathbb{R}^{K-1}\to\mathbb{R}$ with $\sup|D^{a}h|\le1$ for all multi-indices with $1\le\|a\|_1\le4$, and $d_{\mathcal{M}_4}(U,Z)=\sup_{h\in\mathcal{M}_4}|\mathbb{E}h(U)-\mathbb{E}h(Z)|$; this class is convergence determining.

**Statement.** There is $C(\boldsymbol\beta,K)$ independent of $N$ with

$$d_{\mathcal{M}_4}(U,Z)\le C(\boldsymbol\beta,K)\Big(\frac1N+\frac{1+N^2}{N^{\beta_K/2}}\Big)\qquad\text{for all }N .$$

In particular the rate is $O(1/N)$ when $\beta_K$ is large enough (the paper notes $\beta_K/2\ge6$ suffices), improving the earlier $O(1/\sqrt N)$ bound; the second term is an artefact of a one-sided interpolation near the boundary $x_K=0$.

## Depends on

- [Finite-type Fleming-Viot process and the K-allele Wright-Fisher diffusion](../../diffusion-theory/fleming-viot-processes/finite-type-fleming-viot-k-allele-wright-fisher.md)

## Expansion

The Dirichlet law is characterized by $\mathbb{E}\,\mathcal{G}_Zf(Z)=0$ for the Wright-Fisher diffusion generator $\mathcal{G}_Zf=\tfrac12\sum_{i,j}x_i(\delta_{ij}-x_j)\partial_{ij}f+\tfrac12\sum_i(\beta_i-sx_i)\partial_if$, $s=\sum\beta_i$. Solving the Stein equation $\mathcal{G}_Zf_h=h-\mathbb{E}h(Z)$ gives $|\mathbb{E}h(U)-\mathbb{E}h(Z)|=|\mathbb{E}\mathcal{G}_Zf_h(U)|$. The prelimit comparison writes $\mathbb{E}[\mathcal{G}_U Af_h(U)]=0$ for the chain's generator acting on a smooth interpolation $Af_h$ of $f_h$ from the lattice $\delta\mathbb{Z}^{K-1}$, $\delta=1/N$, which reproduces cubic polynomials exactly; a Taylor expansion of $\mathcal{G}_U$ to fourth order matches $\mathcal{G}_Z$ up to terms of order $\delta$ times fourth derivatives of $f_h$, which are bounded (Stein factors). The interpolation needs room on one side, so the region within $O(1/\sqrt N)$ of the face $x_K=0$ is handled separately using the $\mathrm{Beta}(\beta_K,s-\beta_K)$ marginal of $Z_K$, producing the $N^{-\beta_K/2}$ term.

## Sources

- Anton Braverman and Han L. Gan, "Steady-state Dirichlet approximation of the Wright-Fisher model using the prelimit generator comparison approach of Stein’s method", Adv. Appl. Probab. 57 (2025), 1321–1359, <https://doi.org/10.1017/apr.2025.13>. Numbering follows the arXiv version, arXiv:2312.10831 (2023): Section 1 (model (1.1), assumption (1.3) and Theorem 1.1), Section 2 (proof) and Appendix A (the interpolator $A$), <https://doi.org/10.48550/arXiv.2312.10831>.
