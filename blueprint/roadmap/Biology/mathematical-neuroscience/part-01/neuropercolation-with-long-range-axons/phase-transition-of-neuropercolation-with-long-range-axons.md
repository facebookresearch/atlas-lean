# Phase transition of neuropercolation with long-range axons

**Model.** The cortical neuropil is modelled as a random graph $G$ on the discrete torus $\mathbb Z_N^2$, an $(N+1)\times(N+1)$ grid with periodic boundary and $N^2$ vertices. It has two kinds of edges. Short edges join lattice neighbours. Long edges, which stand for long axons, are added independently: a pair of vertices at lattice distance $d>1$ is joined with probability

$$p_d=\frac{c}{N\,d},$$

for a constant $c>0$. The number of long edges at a vertex is then asymptotically Poisson with mean $\lambda=4c\ln2$. Each vertex $v$ carries a state $\chi_v(t)\in\{0,1\}$. Initially each vertex is active independently with probability $p_0$, and states then update synchronously by the threshold rule

$$\chi_v(t+1)=\mathbf 1\Big(\sum_{u\in N(v)}\chi_u(t)\ge k\Big),$$

where $N(v)$ is the closed neighbourhood of $v$ in $G$ ($v$ together with its neighbours) and $k\in\{0,\dots,5\}$ is the activation threshold. Let $A(t)$ be the set of active vertices and $\hat\rho_t=|A(t)|/N^2$ the true active fraction.

**Mean-field approximation.** In the mean-field approximation of the activation process (Janson et al., Section 5), each vertex samples a new set of neighbours at every step, so the state is described by the mean-field density $\rho_t$ alone: $\rho_0=p_0$ and, given $\rho_t$,

$$N^2\rho_{t+1}=\mathrm{Bin}\bigl(N^2\rho_t,\,f^+(\rho_t)\bigr)+\mathrm{Bin}\bigl(N^2(1-\rho_t),\,f^-(\rho_t)\bigr)$$

(source Eq. (5.1)), where $f^+(x)$ (resp. $f^-(x)$) is the probability that an active (resp. inactive) vertex, whose $4$ lattice neighbours and long-edge neighbours are each independently active with probability $x$, has at least $k$ active vertices in its closed neighbourhood. As $N\to\infty$, $\rho_t$ becomes deterministic with $\rho_{t+1}=\bar f_k(\rho_t)$, where $\bar f_k(x)=\mathbb P[\mathrm{Bin}(Y+5,x)\ge k]$ with $Y\sim\mathrm{Po}(\lambda)$ is the mean-field map for $\rho_t$.

**Theorem (mean-field phase transition).** In the mean-field approximation of the activation process, there is a critical initial activation probability $p_c=p_c(k,\lambda)$ such that for fixed $p_0$, with high probability as $N\to\infty$, every vertex is eventually active if $p_0>p_c$, and every vertex is eventually inactive if $p_0<p_c$. Explicitly:

1. $p_c=0$ for $k\le1$;
2. $p_c=x_k(\lambda)$ for $k=2,3,4$, where $x_k(\lambda)\in(0,1)$ is the nontrivial solution of $x=\bar f_k(x)$;
3. for $k=5$, $p_c=x_5(\lambda)$, the nontrivial solution of $x=\bar f_5(x)$ in $(0,1)$, if $\lambda>\ln5$, and $p_c=1$ if $\lambda\le\ln5$.

These values describe the mean-field approximation only. For the true process $\hat\rho_t$, Janson et al. prove (Proposition 1) that, with high probability, $p_c=o(1)$ for $0\le k\le2$ and $p_c=1-o(1)$ for $3\le k\le5$, for every $\lambda\ge0$.

## Expansion

This is a bootstrap-type percolation (threshold activation) process on a lattice coupled to a sparse random graph, so local clusters can trigger distant ones. For small $\lambda$ the critical probability stays close to that of the purely local system. As $\lambda$ grows it decreases: long axons lower the initial activity needed for system-wide ignition. That is the mechanism the source offers for brain dynamics poised near criticality and for abrupt, roughly 100 ms recurrent phase transitions in cortical EEG. Kozma, Baars and Geld restate the theorem with $p_d=c/(Nd^\alpha)$ for a general exponent $\alpha$ and the open neighbourhood, and write the critical value as $p_c$ in the same symbol as the long-edge probability; the theorem is proved for $\alpha=1$ and the closed neighbourhood, and its threshold is in the initial activation density, with $\lambda$ fixing the long-edge density.

## Sources

- R. Kozma, B. J. Baars, N. Geld, "Evolutionary advantages of stimulus-driven EEG phase transitions in the upper cortical layers", *Frontiers in Systems Neuroscience* 15 (2021) 784404, Section 3.1, Eqs. (1)–(2), Proposition 6 and Figure 1, <https://doi.org/10.3389/fnsys.2021.784404>, PMCID PMC8692947.
- S. Janson, R. Kozma, M. Ruszinkó, Y. Sokolov, "A modified bootstrap percolation on a random graph coupled with a lattice", *Discrete Applied Mathematics* 258 (2019) 152–165, Eq. (1.2) with $\alpha=1$, the Poisson approximation of long-edge degrees ($\lambda=4c\ln2$), rule (3.1), map (5.11), Proposition 2 and Theorem 2, the original source of the theorem restated by Kozma, Baars and Geld, <https://arxiv.org/abs/1507.07997>.
