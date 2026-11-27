# Migration between patches slows neutral extinction in a two-patch Wright–Fisher metacommunity

**Model.** Two habitat patches (forest patches joined by a corridor) host $N_1=N$ and $N_2=dN$ plants, $0<d\le1$, of two neutral species $\alpha,\beta$. Let $x=(x_1,x_2)\in\mathcal{D}=[0,1]^2$ be the frequencies of $\alpha$ in the two patches. With time step $\delta t=1/N$, one step is a deterministic exchange followed by independent Wright–Fisher resampling in each patch:

$$x_1\mapsto(1-\kappa d\,\delta t)x_1+\kappa d\,\delta t\,x_2,\qquad x_2\mapsto\kappa\,\delta t\,x_1+(1-\kappa\,\delta t)x_2,$$

then $Nx_1\sim\mathrm{Bin}(N,x_1)$ and $dNx_2\sim\mathrm{Bin}(dN,x_2)$ independently, where $\kappa>0$ is the exchange rate. The states $(0,0)$ and $(1,1)$ (one species lost from the metacommunity) are absorbing.

**Theorem.** With $M=\begin{pmatrix}d&-d\\-1&1\end{pmatrix}$ define

$$L_du(x)=\frac{x_1(1-x_1)}{2}\,u_{x_1x_1}+\frac{x_2(1-x_2)}{2d}\,u_{x_2x_2}-\kappa\,Mx\cdot\nabla u .$$

1. *(Hydrodynamic limit.)* For $f\in C^2(\mathcal{D})$ vanishing at $(0,0)$ and $(1,1)$, the expectations $u_N(t,x)$ of $f$ along the chain converge uniformly on $[0,T]\times\mathcal{D}$ to the solution of $\partial_tu=L_du$, $u(0)=f$; $L_d$ satisfies parabolic and elliptic comparison principles.
2. *(Extinction time, conditional.)* Let $\tau_N$ be the polynomial interpolating the mean extinction times of the chain on the grid. If $\tau_N$ converges as $N\to\infty$ (an assumption the source makes and does not prove), the limit is the solution $\tau$ of $-L_d\tau=1$ vanishing at $(0,0)$ and $(1,1)$, which is unique by the elliptic comparison principle.
3. *(Corridors slow extinction, conditional.)* Assume, in addition to the convergence in item 2, that $\tau$ is smooth up to the boundary of $\mathcal D$ except at $(0,0)$ and $(1,1)$, so that the comparison principle applies to it (a regularity the source admits without proof). Let $H(z)=-2\big(z\ln z+(1-z)\ln(1-z)\big)$ and $z=(x_1+dx_2)/(1+d)$. The mean extinction time of a single merged patch of capacity $(1+d)N$, $\underline\tau=(1+d)H(z)$, is a subsolution, so $\underline\tau\le\tau$: splitting the community into two patches linked by migration never shortens the mean time to loss of a species.
4. *(Limits, conditional.)* Under the same assumptions, for fixed $d$, $\tau_{d,\kappa}(x)\to+\infty$ as $\kappa\to0$ at every $x\ne(0,0),(1,1)$; for fixed $\kappa$, $\tau\to H(x_1)$ as $d\to0$, the one-patch value.

## Depends on

- [Neutral Wright–Fisher transition matrix](../../wright-fisher-markov-chain/wright-fisher.md)

## Proof depends on

## Expansion

The migration step is a stochastic matrix $I-\frac{\kappa}{N}M$, contributing the drift $-\kappa Mx$ at rate $N$, while the Bernstein (binomial) resampling contributes the Wright–Fisher variances $x_i(1-x_i)/N_i$ per step; the two scale together when $\delta t=1/N$. The mean absorption time solves $N(I-\tilde P_N)T_N=\mathbf{1}$, the discrete analogue of $-L_d\tau=1$. For item 3, a direct computation gives

$$-L_d\underline\tau=\frac{x_1(1-x_1)+d\,x_2(1-x_2)}{(1+d)\,z(1-z)}\le1$$

by concavity of $x(1-x)$, and the elliptic comparison principle turns the subsolution into a lower bound.

## Sources

- Gauthier Delvoye, Olivier Goubet and Frédéric Paccaut, "Comparison principles and applications to mathematical modelling of vegetal meta-communities", arXiv:2004.01417 (2020), Section 2 (model), Theorems 3.1, 3.10, 4.1 and 4.3, Remark 4.2 and Propositions 4.4–4.5 (locators follow arXiv v3), <https://doi.org/10.48550/arXiv.2004.01417>; published in *Mathematics in Engineering* 4(5) (2022), <https://doi.org/10.3934/mine.2022035>.
