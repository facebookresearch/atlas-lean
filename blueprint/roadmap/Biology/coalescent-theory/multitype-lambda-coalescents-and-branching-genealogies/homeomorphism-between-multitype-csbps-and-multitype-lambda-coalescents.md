# Homeomorphism between multitype CSBPs and multitype Λ-coalescents

A **multitype continuous-state branching process** (MCSBP) on $\mathbb{R}_+^d$ has characteristic triplet $(B, c, \mu)$: a drift matrix $B$ with $b_{ij} \ge 0$ for $i \ne j$, diffusion coefficients $c \in \mathbb{R}_+^d$, and jump measures $\mu_1, \dots, \mu_d$ on $\mathbb{R}_+^d\setminus\{0\}$ with the usual integrability. A multitype Λ-coalescent is described by its pair $(\rho, \mathcal{Q})$ of type-switch/binary-merger rates and multiple-merger measures on $[0,1]^d$. For $z \in (0,\infty)^d$ let $T_z(w) = \big(w_1/(w_1 + z_1), \dots, w_d/(w_d + z_d)\big)$ and $\mathbf{T}_z\mu$ the pushforward; $T_1$ is the case $z = (1,\dots,1)$.

**Theorem 3.1 (homeomorphism).** Fix $a \in \mathbb{R}^d$ and $T > 0$. Let $\mathcal{B}$ be the space of MCSBPs with triplets in the parameter class $\mathbf{\Psi}^{\mathrm{branch}}_a$ and $\mathcal{C}$ the space of multitype Λ-coalescents whose measures put no mass on $[0,1]^d\setminus[0,1)^d$, both with the Prohorov topology of weak convergence on Skorokhod path space on $[0,T]$. Then $\mathcal{B}$ and $\mathcal{C}$ are homeomorphic via the explicit parameter map
$$H(B, c, \mu) = (\rho, \mathcal{Q}), \qquad \rho_{ii} = 2c_i, \quad \rho_{ij} = b_{ji}\ (i \ne j), \quad \mathcal{Q}_i = \mathbf{T}_1\mu_i,$$
with inverse $c_i = \rho_{ii}/2$, $b_{ij} = \rho_{ji}$, $\mu_i = \mathbf{T}_1^{-1}\mathcal{Q}_i$.

The map has a genealogical meaning: running two independent MCSBPs and following the relative frequency of one of them in each colony through a sequential sampling ("culling") procedure produces, in the limit (Theorem 3.2), a multitype Λ-Wright–Fisher process whose moment dual is the image coalescent. Thus the coalescent $H(B,c,\mu)$ is the local genealogy of the branching population: Feller diffusion becomes binary merging, offspring migration $b_{ji}$ becomes lineage type switching, and a jump of size $w$ becomes a merger capturing a fraction $w/(w+z)$ of each colony.

**Multitype Beta coalescents.** Applying $H_z$ to multitype $\alpha$-stable branching processes defines multitype Beta coalescents with parameters $(\alpha, \eta, z)$ (Section 3), extending the one-type fact that the Beta$(2-\alpha,\alpha)$ coalescent is the genealogy of an $\alpha$-stable CSBP; when $\alpha_i \in [1,2)$, large mergers can only involve lineages of a single type.

## Depends on

- [Moment duality of the multitype Λ-Wright–Fisher process](moment-duality-of-the-multitype-lambda-wright-fisher-process.md)
- [The Beta-coalescent measure on the unit interval](../multiple-merger-coalescents/merger-rates-and-beta-coalescents/beta-lambda.md)

## Expansion

The proof first shows that $H$ is a homeomorphism between the parameter spaces with suitable topologies (convergence of triplets in terms of characteristic exponents, convergence of coalescent pairs in terms of the measures $\mathcal{Q}_i$ weighted by $u_j^{1+\delta_{ij}}$), then that convergence of parameters is equivalent to weak convergence of the processes on path space, so the parameter homeomorphism lifts. The genealogical interpretation comes from the culling construction: sampling individuals one at a time from the two populations, with total mass fixed at $z$, discretizes the frequency process; its generator converges to the multitype Λ-Wright–Fisher generator with parameters $H_z(B,c,\mu)$, and the moment duality identifies the coalescent. This extends the one-type correspondence between CSBPs and Λ-coalescents with no atom at $1$.

## Sources

- A. González Casanova, N. Kurt, I. Nuñez, J. L. Pérez, "From multitype branching to multitype coalescents and back: Genealogies, duality and examples", arXiv:2501.00329 (2025), Definition 2.1, Theorems 2.5, 2.6, 3.1 and 3.2, and the multitype Beta coalescents of Section 3, <https://doi.org/10.48550/arXiv.2501.00329>.
