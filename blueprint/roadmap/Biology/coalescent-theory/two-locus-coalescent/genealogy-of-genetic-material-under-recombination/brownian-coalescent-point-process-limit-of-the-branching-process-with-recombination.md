# Brownian coalescent point process limit of the branching process with recombination

**Model.** Fix a focal ancestor in a large Wright–Fisher population of size $N$ with a chromosome of genetic length $R/N$ per meiosis (one crossover per meiosis with probability $R/N$, at a uniform position $U$ on $(0,R)$). While few individuals carry its genetic material, the carriers form the *branching process with recombination*: each carrier of an interval $I \subset (0,R)$ has approximately Poisson-many children; a child without a crossover inherits all of $I$ or none of it with probability $1/2$ each, and a child with a crossover at $U \in I$ inherits the part of $I$ to the left or to the right of $U$ with probability $1/2$ each. Let $\mathbb{P}_R$ start from one individual carrying $(0,R)$, let $T_n$ be the set of carriers at generation $n$, $Z_n = |T_n|$, $d_T(u,v)$ the number of generations back to the most recent common ancestor of $u,v$, and $\mu_n = \sum_{u\in T_n}\delta_{(u,|I_u|)}$.

**Proposition (survival).** $\lim_{N\to\infty} \mathbb{P}_R(Z_N > 0)/N$ exists and

$$\lim_{R\to\infty}\lim_{N\to\infty} \frac{R\,\mathbb{P}_R(Z_N>0)}{N\log R} = 1.$$

**Theorem (genealogy).** Let $F_R(x) = \log\big((R-1)x+1\big)/\log R$ on $[0,1]$ and define the time-changed genealogical distance $\bar d^R_n(u,v) = 1 - F_R\big(1 - d_T(u,v)/n\big)$. For fixed $t > 0$, conditional on survival to generation $\lfloor Nt\rfloor$,

$$\lim_{R\to\infty}\lim_{N\to\infty}\Big[T_{\lfloor Nt\rfloor},\ \bar d^R_{\lfloor Nt\rfloor},\ \frac{\mu_{\lfloor Nt\rfloor}}{tN\log R}\Big] = \big[(0,Y),\ d_P,\ \mathrm{Leb}\otimes\mathrm{Exp}(t)\big]$$

in distribution for the marked Gromov-weak topology. Here $[(0,Y), d_P]$ is the *Brownian coalescent point process*: $k$ points sampled from it have pairwise coalescence depths $H_{ij} = \max\{H_i,\ldots,H_{j-1}\}$ (for $i<j$, after a uniform relabeling) with $H_1,\ldots,H_{k-1}$ i.i.d. uniform on $(0,1)$; and the interval lengths carried by sampled carriers are asymptotically i.i.d. exponential with mean $1/t$, independent of the genealogy. The same limit holds jointly when distances are measured along the ancestry of the carried genetic material.

## Expansion

The key tool is a $k$-spine (many-to-few) decomposition: sums over $k$-tuples of distinct carriers at generation $N$ equal $h(x)N^{k-1}k!$ times an expectation under a size-biased law in which $k$ spines branch off one another at i.i.d. times, where $h(I) \propto |I|$ is harmonic for the near-critical process. Along a spine, the carried interval shrinks by recombination like a pure-jump process whose rescaled value is Gamma distributed; branch times of the spines are i.i.d. with distribution function $F_R$, which becomes uniform after the time change. Moment convergence of polynomials of the marked metric measure space, plus a moment-growth bound, identifies the limit as the Brownian CPP with independent exponential marks.

## Sources

- Félix Foutel-Rodier and Emmanuel Schertzer, "Convergence of genealogies through spinal decomposition with an application to population genetics", Probab. Theory Related Fields 187 (2023), 697–751, <https://doi.org/10.1007/s00440-023-01223-7>. Numbering follows the arXiv version, arXiv:2201.12412 (2022): Proposition 1 (survival asymptotics, after Baird et al.), Theorem 1, Theorem 2, Theorem 3 (spinal decomposition) and Corollary 1 (Brownian CPP moments), <https://doi.org/10.48550/arXiv.2201.12412>.
