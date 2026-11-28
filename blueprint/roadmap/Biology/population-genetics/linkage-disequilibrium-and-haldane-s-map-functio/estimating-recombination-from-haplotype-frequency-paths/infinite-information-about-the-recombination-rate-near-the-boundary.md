# Infinite information about the recombination rate near the simplex boundary

**Setting.** Use the two-locus Wright–Fisher diffusion $X(t)=(X_{ij}(t))$ with recombination rate $\rho\ge0$ and mutation rates $\theta_A/2$, $\theta_B/2$ at the two loci, and the observed information

$$I_T=\int_0^T\sum_{i=1}^K\sum_{j=1}^L\frac{\big(X_{ij}(t)-X_{i\cdot}(t)X_{\cdot j}(t)\big)^2}{X_{ij}(t)}\,dt$$

for estimating $\rho$ from the path on $[0,T]$ (see the depended-on article).

**Theorem.** Suppose that

$$\rho+\frac{\theta_A}{2}+\frac{\theta_B}{2}<\frac12,$$

that mutation is parent-independent (each mutation matrix has identical rows), and that $X(0)$ lies in the interior of the simplex. Then for every $T>0$,

$$\mathbb P(I_T=\infty)>0 .$$

Consequently, with positive probability the recombination rate is learned without error in finite time by the corrected maximum likelihood estimator.

## Expansion

The integrand of $I_T$ is locally integrable in the interior of the simplex, so infinite information can only come from the boundary. It suffices that some haplotype frequency $X_{ij}$ hits $0$ before time $T$ while the linkage disequilibrium $D_{ij}$ stays bounded away from $0$, and that $\int_0^{T_\varepsilon}X_{ij}(t)^{-1}\,dt$ diverges as $\varepsilon\to0$, where $T_\varepsilon$ is the hitting time of level $\varepsilon$. Under parent-independent mutation the drift of $X_{ij}$ is

$$\mu_{ij}=\rho\,(X_{i\cdot}X_{\cdot j}-X_{ij})+\tfrac{\theta_A}{2}(X_{\cdot j}P^A_i-X_{ij})+\tfrac{\theta_B}{2}(X_{i\cdot}P^B_j-X_{ij}),$$

and on a neighbourhood of the initial point it is dominated by $\frac{\vartheta}{2}(P-X_{ij})$ for some $\vartheta<1$ with $\rho+\theta_A/2+\theta_B/2<\vartheta/2$. A comparison theorem for one-dimensional SDEs puts $X_{ij}$ below a one-locus mutation-only Wright–Fisher diffusion $Z$ with this drift. Because $\vartheta<1$, the boundary $0$ is accessible for $Z$ and $\int_0^{T_\varepsilon(Z)}Z(t)^{-1}dt$ diverges as $\varepsilon\to0$; the event that $X_{ij}$ reaches $0$ before $T$ while the disequilibrium stays away from $0$ and the comparison remains valid has positive probability.

## Depends on

- [Maximum likelihood estimator of the recombination rate from a continuously observed Wright–Fisher path](maximum-likelihood-estimator-of-the-recombination-rate-from-a-wright-fisher-path.md)

## Proof depends on

- [Comparison theorem for one-dimensional stochastic differential equations](../../../../Probability/stochastic-calculus/stochastic-differential-equations/comparison-theorem-for-one-dimensional-sdes.md)
- [Accessible endpoints give almost sure exit with finite mean exit time](../../diffusion-theory/selection-duality-and-general-one-dimensional-di/finite-accessibility-integrals-at-both-endpoints.md)

## Sources

- Robert C. Griffiths and Paul A. Jenkins, "An estimator for the recombination rate from a continuously observed diffusion of haplotype frequencies", *Journal of Mathematical Biology* 86 (2023), 98, <https://doi.org/10.1007/s00285-023-01931-7>. Numbering as in the preprint arXiv:2212.07747v2, <https://arxiv.org/abs/2212.07747v2>: Section 3.2, Theorem 3.
