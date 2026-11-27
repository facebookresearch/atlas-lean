# Invasion threshold of cooperative parasites on random geometric graphs

**Model.** Hosts sit at the points of a Poisson process of intensity $N$ on $[0,1]^n$; two hosts are linked if their max-norm distance is at most $r_N=\tfrac12N^{(\beta-1)/n}$ for some $\beta\in(0,1)$, so an interior host has about $d_N=(2r_N)^nN=N^\beta$ neighbours. The host nearest the centre is infected in generation $0$. In each generation every parasite moves along a uniformly chosen edge to a neighbouring host. A host attacked by **at least two** parasites simultaneously is infected, dies, and releases $v_N$ new parasites; a host attacked by a single parasite survives and kills the parasite; parasites arriving at empty vertices die. Let $\bar I_g$ be the number of hosts infected up to generation $g$ and $E_u=\{\exists g:\bar I_g\ge u\cdot\#\text{hosts}\}$, $0<u\le1$.

A *discrete-time branching process with cooperation* has $Z_g=\sum_{i\le Z_{g-1}}X_{g,i}+\sum_{1\le j<i\le Z_{g-1}}Y_{g,i,j}$ with i.i.d. offspring $X\sim\mathcal L_o$ and pairwise cooperation offspring $Y\sim\mathcal L_c$. Let $\pi(a)>0$ be the survival probability of the one with $\mathcal L_o=\mathrm{Poi}(a^2/2)$ and $\mathcal L_c=\mathrm{Poi}(a^2)$.

**Theorem.**
1. *Invasion probability.* If $v_N=o(\sqrt{d_N})$ then $\mathbb P(E_u)\to0$. If $v_N\sim a\sqrt{d_N}$ with $0<a<\infty$ then

$$\pi\big(a/\sqrt{2^n}\big)\le\liminf_{N}\mathbb P(E_u)\le\limsup_N\mathbb P(E_u)\le\pi(a).$$

If $\sqrt{d_N}=o(v_N)$ then $\mathbb P(E_u)\to1$.
2. *Invasion time.* If $v_N\sim a\sqrt{d_N}$ and $T=\inf\{g:\bar I_g=\#\text{hosts}\}$, then conditionally on $T<\infty$, with probability tending to one,

$$\Big\lfloor\frac1{2r_N}\Big\rfloor\le T\le\Big\lceil\frac1{2r_N}\Big\rceil+O\big(\max(\log\log N,\ \varepsilon_N/r_N^2)\big),\qquad \varepsilon_N=N^{\frac{\beta/2-1}{n}+\delta}.$$

## Expansion

With $k$ infected hosts each releasing $v_N$ parasites into a neighbourhood of $d_N$ hosts, the expected number of hosts hit by two parasites from *different* sources is of order $k^2v_N^2/d_N$, and by two from the same source of order $kv_N^2/d_N$; so $v_N\asymp\sqrt{d_N}$ is the critical scale at which both pairwise (cooperation) and single-source infections contribute $O(1)$ new infections, and early spread is a branching process with cooperation. Because cooperation offspring grow quadratically in population size, $\pi(a)>0$ for every $a>0$, unlike for configuration-model host networks. The bounds come from couplings with the corresponding process on a complete graph: the upper bound treats the initial neighbourhood as fully connected, the lower bound restricts to a sub-cube in which all hosts are mutually linked, which costs the factor $2^n$ in the number of shared neighbours. Once a small polynomial number of hosts is infected, the epidemic sweeps the graph ball by ball, one graph distance per generation, giving the invasion time $\approx 1/(2r_N)$.

## Sources

- Vianney Brouard, Cornelia Pokalyuk, Marco Seiler and Hung Tran, "Spatial invasion of cooperative parasites", Theoretical Population Biology 159 (2024), 35–58, <https://doi.org/10.1016/j.tpb.2024.07.001>; numbering as in arXiv:2308.07397: Definitions 2.1 and 2.3, Theorem 2.4 and Theorem 2.7.
