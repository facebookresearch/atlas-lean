# Offspring law of colors in the branching–coalescing network model

**Model.** Start from one lineage carrying a color (a group of lineages close enough to hybridize). In continuous time: each lineage splits into two at rate $1$; each lineage dies at rate $\alpha>0$; each pair of lineages **of the same color** merges at rate $2\beta>0$ (hybridization, so the hybridization rate decreases with phylogenetic distance); each lineage acquires a new, never-seen color at rate $\mu>0$ (speciation-like divergence after which hybridization with the old color is impossible). The resulting time-embedded network $\mathscr G$ decomposes into a Galton–Watson tree $\mathscr T$ of colors, each color decorated by the subnetwork of its lineages; within one color the number of lineages is a *logistic branching process* jumping $k\to k+1$ at rate $k$ and $k\to k-1$ at rate $k(\alpha+\mu)+k(k-1)\beta$.

**Theorem.** Let $M$ be the number of new colors produced by one color over its lifetime (the offspring law of $\mathscr T$), and $\rho_k=\alpha+\mu+(k-1)\beta$. Then

$$\mathbb E[M]=\mu\sum_{j\ge1}\prod_{k=1}^j\frac1{\rho_k},$$

and its generating function is the continued fraction

$$g(z)=\cfrac{\alpha+\mu z}{1+\rho_1-\cfrac{\alpha+\beta+\mu z}{1+\rho_2-\cfrac{\alpha+2\beta+\mu z}{1+\rho_3-\ddots}}},$$

which is meromorphic on $\mathbb C$ with radius of convergence $R>1$ at $0$ and a pole at $R$. In particular $M$ has exponential moments, the network is finite almost surely iff $\mathbb E[M]\le1$, and the extinction probability is the smallest fixed point of $g$ in $[0,1]$. The Malthusian growth rate $\lambda$ of the number of colors solves $\mu\,\mathbb E\big[\int_0^\infty X_te^{-\lambda t}dt\big]=1$ (with $X$ the logistic process), has the sign of $\mathbb E[M]-1$, and $e^{-\lambda t}Z_t\to W$ a.s. and in $L^2$ on survival when $\mathbb E[M]>1$.

## Expansion

Each color evolves independently once created, so colors form a Crump–Mode–Jagers process whose reproduction point process is the set of mutation times of the color, with intensity $\mu\,\mathbb E[X_t]\,dt$. Hence $\mathbb E[M]=\mu\,\mathbb E\int_0^\infty X_tdt$, and the expected total lineage time of the birth–death chain $X$ started from $1$ follows from its stationary-type measure $\prod_k1/\rho_k$, giving the series. The continued fraction comes from a first-step analysis of the logistic chain with the mutation count marked by $z$: a measure change $\mathbb E_\mu[f(X)s^M]=\mathbb E_{s\mu}[f(X)e^{(s-1)\mu L}]$, $L=\int X_tdt$, turns the generating function into a ratio of solutions of a three-term recursion. Strong within-color coalescence ($\beta$ large) keeps colors small, so $\mathbb E[M]\approx\mu/(\alpha+\mu)$, while weak coalescence lets colors grow and produce many new colors.

## Sources

- François Bienvenu and Jean-Jil Duchamps, "A branching process with coalescence to model random phylogenetic networks", Electronic Journal of Probability 29 (2024), 1–48, <https://doi.org/10.1214/24-ejp1088>; numbering as in arXiv:2211.02407: Section 1.2 (model), Propositions 2.1, 2.8 and 2.9, Theorem 2.5 and Corollary 2.7.
