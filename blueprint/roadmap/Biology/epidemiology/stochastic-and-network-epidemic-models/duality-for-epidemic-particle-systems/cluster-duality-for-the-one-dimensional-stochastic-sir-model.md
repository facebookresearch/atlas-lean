# Cluster duality for the one-dimensional stochastic SIR model

**Model.** On $\mathbb{Z}$ each site is susceptible ($S$), infectious ($I$) or recovered ($R$). An infectious site infects each susceptible nearest neighbour at rate $\beta$ ($IS \to II$ and $SI \to II$) and recovers at rate $\gamma$ ($I \to R$); recovered sites stay recovered. Write $\eta^a_x = \mathbf{1}\{\eta_x = a\}$. For an initial law $\nu$ define the cluster functions

$$
G^\nu(r,n,t) = \Bigl\langle \eta^I_{r-1}(t)\prod_{j=0}^{n-1}\eta^S_{r+j}(t)\,\eta^I_{r+n}(t)\Bigr\rangle_\nu,\qquad
J^\nu(r,n,t) = \Bigl\langle \eta^R_{r-1}(t)\prod_{j=0}^{n-1}\eta^S_{r+j}(t)\,\eta^I_{r+n}(t)\Bigr\rangle_\nu,
$$

the probabilities of a run of $n$ susceptibles bounded by two infectious sites, or by a recovered site on the left and an infectious one on the right.

**Statement.** The SIR process is dual, with duality function

$$
d\bigl(\eta,(r,n,i)\bigr) = \bigl[\eta^I_{r-1}\mathbf{1}_{i=G} + \eta^R_{r-1}\mathbf{1}_{i=J}\bigr]\prod_{j=0}^{n-1}\eta^S_{r+j}\,\eta^I_{r+n}, \qquad d(\eta,\partial) = 0,
$$

to a biased random walk on two layers $\mathbb{Z}\times\mathbb{N}\times\{G,J\}$ with a trap $\partial$, with transitions

$$
(r,n,i) \to (r,n+1,i) \ \text{at rate } \beta, \quad (r,n,G) \to (r-1,n+1,G) \ \text{at rate } \beta, \quad (r,n,J) \to (r,n,G) \ \text{at rate } \gamma, \quad (r,n,G) \to \partial \ \text{at rate } 2\gamma .
$$

Consequences: for translation-invariant $\nu$,

$$
G^\nu(n,t) = e^{-2(\gamma+\beta)t}\sum_{\ell\ge 0}\frac{(2\beta t)^\ell}{\ell!}G^\nu(n+\ell,0),
$$

and $J^\nu$ solves $\dot J(n) = -(\gamma+\beta)J(n) + \beta J(n+1) + \gamma G(n)$; for a deterministic, non-translation-invariant initial configuration $\eta$,

$$
G^\eta(r,n,t) = e^{-2(\gamma+\beta)t}\sum_{0 \le a \le b}\binom{b}{a}2^{-b}\frac{(2\beta t)^b}{b!}\,G^\eta(r-a,n+b,0),
$$

with an analogous closed formula for $J^\eta$. These give the time decay of susceptible clusters for arbitrary initial states.

## Expansion

Apply the SIR generator to $d(\cdot,(r,n,G))$. The cluster $I\,S^n\,I$ starting at $r-1$ is reached from the longer clusters $I\,S^{n+1}\,I$ at $r-2$ or at $r-1$ when the extra susceptible next to a border is infected (rate $\beta$ each), and it is destroyed when either border recovers (total rate $2\gamma$); this is the $G$-layer dynamics, with the trap absorbing the destroyed cluster. For $R\,S^n\,I$ only the right border can infect inward (rate $\beta$, no shift), and the cluster is also fed by $I\,S^n\,I$ whose left border recovers (rate $\gamma$), which is the $J \to G$ transition read in the dual direction. Because the dual is a walk whose number of steps by time $t$ is Poisson, the duality relation $\mathbb{E}_\eta[d(\eta_t,\xi)] = \mathbb{E}_\xi[d(\eta,\xi_t)]$ yields the explicit series. Unlike the factorized duality of the contact process, this duality function is nonlocal: a product over a whole cluster.

## Sources

- Chiara Franceschini, Ellen Saada, Gunter M. Schütz and Sonia Velasco, "Duality for some models of epidemic spreading", Stochastic Processes and their Applications 191 (2026), 104773, <https://doi.org/10.1016/j.spa.2025.104773>; numbering as in arXiv:2408.15613: Section 4, Theorem 3, Proposition 7, Theorems 4 and 5.
