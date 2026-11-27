# Brownian coalescent point process limit of the branching process with recombination

**Model.** Fix a focal ancestor in a large Wright–Fisher population of size $N$ with a chromosome of genetic length $R/N$ per meiosis (one crossover per meiosis with probability $R/N$, at a uniform position $U$ on $(0,R)$). While few individuals carry its genetic material, the carriers form the *branching process with recombination*: each carrier of an interval $I \subset (0,R)$ has approximately Poisson-many children; a child without a crossover inherits all of $I$ or none of it with probability $1/2$ each, and a child with a crossover at $U \in I$ inherits the part of $I$ to the left or to the right of $U$ with probability $1/2$ each. Let $\mathbb{P}_R$ start from one individual carrying $(0,R)$, let $T_n$ be the set of carriers at generation $n$, $Z_n = |T_n|$, $d_T(u,v)$ the number of generations back to the most recent common ancestor of $u,v$, and $\mu_n = \sum_{u\in T_n}\delta_{(u,|I_u|)}$.

**Proposition (survival).** $\lim_{N\to\infty} \mathbb{P}_R(Z_N > 0)/N$ exists and

$$\lim_{R\to\infty}\lim_{N\to\infty} \frac{R\,\mathbb{P}_R(Z_N>0)}{N\log R} = 1.$$

**Theorem (genealogy).** Let $F_R(x) = \log\big((R-1)x+1\big)/\log R$ on $[0,1]$ and define the time-changed genealogical distance $\bar d^R_n(u,v) = 1 - F_R\big(1 - d_T(u,v)/n\big)$. For fixed $t > 0$, conditional on survival to generation $\lfloor Nt\rfloor$,

$$\lim_{R\to\infty}\lim_{N\to\infty}\Big[T_{\lfloor Nt\rfloor},\ \bar d^R_{\lfloor Nt\rfloor},\ \frac{\mu_{\lfloor Nt\rfloor}}{tN\log R}\Big] = \big[(0,Y),\ d_P,\ \mathrm{Leb}\otimes\mathrm{Exp}(t)\big]$$

in distribution for the marked Gromov-weak topology, where $\mathrm{Exp}(t)$ is the exponential law with mean $1/t$. Here $[(0,Y), d_P]$ is the *Brownian coalescent point process*: let $P$ be a Poisson point process on $(0,\infty)\times(0,1)$ with intensity $dt\otimes x^{-2}\,dx$, set $d_P(x,y) = \sup\{z : (t,z)\in P,\ x\le t\le y\}$ for $x\le y$, and let $Y$ be an exponential random variable with mean $1$, independent of $P$. Its moments are explicit: for every $k\ge1$ and bounded continuous $\phi$,

$$\mathbb{E}\int_{(0,Y)^k}\phi\big(d_P(x_i,x_j);\ i,j\le k\big)\,dx_1\cdots dx_k = k!\,\mathbb{E}\big[\phi\big(H_{\sigma_i\sigma_j};\ i,j\le k\big)\big],$$

where $H_{ij} = H_{ji} = \max\{H_i,\ldots,H_{j-1}\}$ for $i<j$, the variables $H_1,\ldots,H_{k-1}$ are i.i.d. uniform on $(0,1)$, and $\sigma$ is an independent uniform permutation of $\{1,\ldots,k\}$. The mark component says that the interval lengths carried by sampled carriers are asymptotically i.i.d. exponential with mean $1/t$, independent of the genealogy.

**Theorem (genealogy and chromosomic distance).** For each $u \in T_n$ pick a reference point $M_u$ uniformly on $I_u$, and define the rescaled chromosomic distance $\bar D^R_n(u,v) = \log\big(|M_u - M_v| \vee 2\big)/\log R$. For fixed $t>0$, conditional on survival to generation $\lfloor Nt\rfloor$,

$$\lim_{R\to\infty}\lim_{N\to\infty}\Big[T_{\lfloor Nt\rfloor},\ \bar d^R_{\lfloor Nt\rfloor},\ \bar D^R_{\lfloor Nt\rfloor},\ \frac{\mu_{\lfloor Nt\rfloor}}{tN\log R}\Big] = \big[(0,Y),\ d_P,\ d_P,\ \mathrm{Leb}\otimes\mathrm{Exp}(t)\big]$$

in distribution for the marked Gromov-weak topology on marked bi-metric measure spaces. In the limit the rescaled genealogical and chromosomic distances coincide.

## Expansion

The key tool is a $k$-spine (many-to-few) decomposition: sums over $k$-tuples of distinct carriers at generation $N$ equal $h(x)N^{k-1}k!$ times an expectation under a size-biased law in which $k$ spines branch off one another at i.i.d. times, where $h(I) \propto |I|$ is harmonic for the near-critical process. Along a spine, the carried interval shrinks by recombination like a pure-jump process whose rescaled value is Gamma distributed; branch times of the spines are i.i.d. with distribution function $F_R$, which becomes uniform after the time change. Moment convergence of polynomials of the marked metric measure space, plus a moment-growth bound, identifies the limit as the Brownian CPP with independent exponential marks.

## Sources

- Félix Foutel-Rodier and Emmanuel Schertzer, "Convergence of genealogies through spinal decomposition with an application to population genetics", Probab. Theory Related Fields 187 (2023), 697–751, <https://doi.org/10.1007/s00440-023-01223-7>. Numbering follows the arXiv version, arXiv:2201.12412 (2022): Proposition 1 (survival asymptotics, after Baird et al.), Theorem 1, Theorem 2, Theorem 3 (spinal decomposition) and Corollary 1 (Brownian CPP moments), <https://doi.org/10.48550/arXiv.2201.12412>.
