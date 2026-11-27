# Expected allelic frequency spectrum of a splitting tree at a fixed time

**Model.** A **splitting tree** is a branching population in which individuals have i.i.d. lifetimes with law $\mathbb P_V$ on $(0,\infty]$ (not necessarily exponential) and give birth to single offspring at constant rate $b$ during life. Let $\Lambda = b\,\mathbb P_V$, let $\psi(x) = x - \int_{(0,\infty]}(1 - e^{-rx})\,\Lambda(dr)$, and let the **scale function** $W$ be defined by $\int_0^\infty e^{-xr}W(r)\,dr = 1/\psi(x)$ for $x$ larger than the largest root $\alpha$ of $\psi$; then $W(t) = \mathbb E[N_t \mid N_t > 0]$ for the population size $N_t$ of a tree founded by one individual $t$ units of time ago. Neutral mutations occur along each lifetime at the points of a Poisson process of rate $\theta$, each creating a new allele (infinitely-many-alleles model). Let $W_\theta$ be the scale function of the **clonal** splitting tree, in which lifetimes are killed at their first mutation; it is given by

$$W_\theta(x) = e^{-\theta x}\,W(x) + \theta\int_0^x W(y)\,e^{-\theta y}\,dy, \qquad x \ge 0.$$

Let $A_\theta(k,t)$ be the number of derived alleles carried by exactly $k$ individuals alive at time $t$, $Z_0(t)$ the number of individuals carrying the ancestral allele, and $\mathbb P^\star$, $\mathbb E^\star$ the law conditioned on survival up to time $t$.

**Theorem.** For every $t \ge 0$ and $k \ge 1$,

$$\mathbb E^\star A_\theta(k,t) = W(t)\int_0^t \theta e^{-\theta x}\,\frac{1}{W_\theta(x)^2}\Big(1 - \frac{1}{W_\theta(x)}\Big)^{k-1}dx,$$

$$\mathbb P^\star\big(Z_0(t) = k\big) = W(t)\,\frac{e^{-\theta t}}{W_\theta(t)^2}\Big(1 - \frac{1}{W_\theta(t)}\Big)^{k-1},$$

and, conditionally on the population size, $\mathbb E\big(Z_0(t) \mid N_t = n\big) = n\,e^{-\theta t}$. In the supercritical case ($\alpha > 0$), $e^{-\alpha t}\,\mathbb E A_\theta(k,t) \to \frac{\alpha\,U_k}{b\,\psi'(\alpha)}$ with $U_k = \int_0^\infty \theta e^{-\theta x}\,W_\theta(x)^{-2}\big(1 - W_\theta(x)^{-1}\big)^{k-1}dx$.

These are exact finite-time formulas, valid for any lifetime law and any age of the population, rather than limits as $t \to \infty$.

## Expansion

The genealogy of the individuals alive at time $t$ is a **coalescent point process**: the coalescence times between consecutive individuals are i.i.d. with $\mathbb P(H > x) = 1/W(x)$, stopped at the first value exceeding $t$, so the population size is geometric. Mutations fall on the branches of this comb as Poisson points of rate $\theta$. Scanning the individuals from left to right, the next individual carrying no mutation besides those of a reference lineage forms a renewal sequence whose excursion lengths and heights $(B^\theta_i, H^\theta_i)$ are i.i.d., with generating function $1/(1 - \mathbb E[\gamma^{B^\theta}; H^\theta \le x]) = W_\theta(x;\gamma)$ related to $W$ by the displayed integral identity (Theorem 3.1). Counting, for each mutation at height $x$, the size of the clonal family it founds, whose law is expressed through $W_\theta(x)$, and integrating over the mutation's position gives the formula for $A_\theta(k,t)$; the factor $W(t)$ comes from conditioning on survival. The ancestral class is the clonal family of the root lineage.

## Sources

- Nicolas Champagnat, Amaury Lambert, "Splitting trees with neutral Poissonian mutations I: Small families", *Stochastic Processes and their Applications* 122 (2012), 1003–1033, <https://doi.org/10.1016/j.spa.2011.11.002>; preprint arXiv:1009.0680, <https://doi.org/10.48550/arXiv.1009.0680>. Numbering of the arXiv version: Section 2 (model, scale functions), Theorem 3.1, Theorem 3.4, Proposition 4.1, Corollaries 4.3 and 4.4, Proposition 5.1.
