# Invasion-rate classification of attracting subcommunities in random environments

**Model.** Species densities $X(t)\in\mathbb{R}_+^n$ and an auxiliary variable $Y(t)\in\mathbb{R}^{\kappa_0}$ (feedbacks, stage structure, environment) evolve in discrete time driven by i.i.d. environments $\xi(t)$:

$$X_i(t+1)=X_i(t)\,F_i\big(X(t),Y(t),\xi(t)\big),\qquad Y(t+1)=G\big(X(t),Y(t),\xi(t)\big),$$

on the state space $\mathcal S=\mathbb R^n_+\times\mathbb R^{\kappa_0}$, under the source's Assumption 2.1:
- (A1) each $F_i(z,\xi)$ is continuous in $z=(x,y)$ for every $\xi$, measurable in $(z,\xi)$, and strictly positive;
- (A2) $G$ is continuous in $z$ and measurable in $(z,\xi)$;
- (A3) there are $V:\mathcal S\to\mathbb R_+$ and constants $\gamma_1,\gamma_3,C>0$, $\rho\in(0,1)$ such that for all $z\in\mathcal S$: $V(x,y)\ge|x|^{\gamma_1}+1$; $V(z)\to\infty$ as $|z|\to\infty$; and $\mathbb E\big[V\big(x\circ F(z,\xi(1)),G(z,\xi(1))\big)\,h(z,\xi(1))\big]\le\rho V(z)+C$, where $\circ$ is the entrywise product and $h(z,\xi)=\max_i\max\{F_i(z,\xi),1/F_i(z,\xi)\}^{\gamma_3}$.

The extinction results (1)–(2) also use the source's Assumption 2.2: there are $\varphi:\mathcal S\to(0,\infty)$ and constants $C,\delta_\varphi>0$ with $\mathbb E_zV(Z(1))\le V(z)-\varphi(z)+C$ and $\mathbb E_z\big(V(Z(1))-PV(z)\big)^2+\mathbb E\big|\log F(z,\xi(1))-\mathbb E\log F(z,\xi(1))\big|^2\le\delta_\varphi\varphi(z)$ for all $z\in\mathcal S$, where $P$ is the transition operator of $Z$. For an ergodic invariant probability measure $\mu$ of $Z=(X,Y)$ supported on the boundary, the **invasion rate** of species $i$ is

$$r_i(\mu)=\int\!\!\int \ln F_i(z,\xi)\,\mu(dz)\,\mathbb{P}(d\xi),$$

and $r_i(\mu)=0$ for every species $i$ present in the support of $\mu$. For $I\subseteq\{1,\dots,n\}$ let $\mathcal{M}^{I,+}$ be the ergodic measures under which exactly the species of $I$ are present, and $\mathcal{M}^{I,\partial}$ those living on the boundary of the face $\{x_j=0,\ j\notin I\}$.

**Attracting subcommunities.** Let $E_1$ be the family of sets $I$ such that $\mathcal{M}^{I,+}\ne\emptyset$ and
1. $\max_{i\notin I} r_i(\mu)<0$ for all $\mu\in\mathrm{Conv}(\mathcal{M}^{I,+})$ (no outsider can invade the community $I$ at stationarity), and
2. if $I\ne\emptyset$, $\max_{i\in I} r_i(\nu)>0$ for all $\nu\in\mathrm{Conv}(\mathcal{M}^{I,\partial})$ (the subcommunity $I$ is persistent on its own face).

**Theorem.**

*(1)* For every $I\in E_1$, $I\ne\{1,\dots,n\}$, there is $\alpha_I>0$ such that for every compact $K$ in the interior $\mathcal S^I_+$ of the face of $I$ (all species of $I$ positive),

$$\lim_{\operatorname{dist}(z,K)\to 0,\ z\in\mathcal S_+}\ \mathbb{P}_z\Big\{\lim_{t\to\infty}\tfrac1t\ln X_i(t)\le-\alpha_I,\ i\notin I\Big\}=1:$$

started from an interior state $z\in\mathcal S_+$ (all species positive) near the community $I$, the outsiders go extinct exponentially fast with probability close to one.

*(2)* If every $J\notin E_1$ satisfies $\max_i r_i(\nu)>0$ for all $\nu\in\mathcal{M}^{J,+}$, and the union of the $E_1$ faces is accessible, then from every interior state

$$\sum_{I\in E_1}p_{z,I}=1,$$

where $p_{z,I}$ is the probability that the empirical occupation measures concentrate on $\mathrm{Conv}(\mathcal{M}^{I,+})$ and each outsider $j\notin I$ decays at a rate $r_j(\mu)$ for some such $\mu$. Thus almost surely the community ends up at one of the attracting subcommunities in $E_1$, and the extinct species are exactly those outside it.

The same classification holds in continuous time for Kolmogorov-type stochastic differential equations, with the invasion rates defined as the corresponding stationary averages of the per-capita log-growth drift.

## Expansion

Condition 1 makes the face of $I$ a stochastic attractor: near it, $\ln X_j$ for $j\notin I$ is a random walk whose drift is an average of negative invasion rates. Condition 2 is the persistence criterion restricted to the face, which keeps the species of $I$ away from their own extinction set, so the stationary measures of $I$ are the only places where the outsiders' drift is evaluated. Under the accessibility and non-degeneracy hypotheses, every non-attracting face is repelling, so the process cannot linger there; the occupation measures must eventually settle on one attracting face, which gives the partition of probability among the $E_1$ outcomes.

## Sources

- Alexandru Hening, Dang H. Nguyen and Peter Chesson, "A general theory of coexistence and extinction for stochastic ecological communities", arXiv:2007.09025 (2020), Assumptions 2.1–2.2, Proposition 2.1, Definition 2.1, Theorems 2.5–2.6 (discrete time) and Theorems 3.4–3.5 (continuous time), <https://doi.org/10.48550/arXiv.2007.09025>.
