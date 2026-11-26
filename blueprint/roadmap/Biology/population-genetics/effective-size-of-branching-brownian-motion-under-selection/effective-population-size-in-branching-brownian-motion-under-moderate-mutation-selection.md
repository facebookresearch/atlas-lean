# Effective population size N^(1−c) in branching Brownian motion under moderate mutation–selection

**Model.** Fix $c \in (0,1)$. For each $N$ consider dyadic branching Brownian motion on $[0, L]$ with drift $+\beta_N$, $\beta_N \in (0,1)$, branching rate $1/2$, reflection at $0$ and killing at $L$. Positions model the load of deleterious mutations: drift toward $L$ is mutation accumulation and killing at $L$ is selection. For each $\beta$ the killing point $L = L(\beta)$ is chosen to make the system **critical**: the principal eigenvalue of the particle density equation $\partial_t u = \tfrac12 \partial_{yy}u - \beta\partial_y u + \tfrac12 u$ (zero flux at $0$, $u(L) = 0$) is $0$, with eigenfunction built from $v_1(x) = \sin(\gamma(L - x))$, $\gamma = \sqrt{1-\beta^2}$. Here $\beta_N$ is chosen so that

$$L(\beta_N) = c\log N + 6\log\log N,$$

so the particle cloud has width of order $c\log N$ (the moderate mutation–selection regime). Let $h$ be the reproductive value, $\mathbb{E}_x[Z(t)] \approx h(x)$, and $\tilde h$ the stable configuration (left Perron–Frobenius eigenvector), normalized by $\int_0^L \tilde h = \int_0^L h\tilde h = 1$. The reproductive variance $\Sigma^2 = \int_0^L h^2 \tilde h$ satisfies $\Sigma^2 / N^{c} \to \sigma^2$ for a constant $\sigma = \sigma(c) > 0$. Let $Z(t)$ be the number of particles.

**Theorem.** Let $t > 0$ and $x > 0$, and start from one particle at $x$.
1. *(Kolmogorov estimate.)* $\big| N\,\mathbb{P}_x\big(Z(tN^{1-c}) > 0\big) - \frac{2}{\sigma^2 t} h(x)\big| \to 0$.
2. *(Yaglom law.)* Conditionally on $Z(tN^{1-c}) > 0$, $\;Z(tN^{1-c})/N \Rightarrow \frac{\sigma^2 t}{2}\,\mathcal{E}$, with $\mathcal{E}$ a mean-one exponential.
3. *(Genealogy.)* Conditionally on survival to $tN^{1-c}$, the genealogical distances between $k$ sampled particles, divided by $N^{1-c}$, converge to those of $k$ uniform samples from a Brownian coalescent point process of height $T = \sigma^2 t/2$: with $U_1, \dots, U_{k-1}$ i.i.d. uniform on $[0,T]$, the distance between the $i$-th and $j$-th leaves (after a uniform random relabeling) is $\max\{U_i, \dots, U_{j-1}\}$. Equivalently, the whole metric measure tree converges Gromov-weakly to the Brownian CPP.

So demographic fluctuations and the genealogy are those of a critical Feller diffusion (only binary mergers, Kingman-like after time change) on the **polynomial** time scale $N^{1-c}$: the effective population size scales as $N^{1-c}$, not $N$ or $\log^3 N$.

## Expansion

A particle's descendants survive long only if it reaches the low-load region near $0$, where $h$ is largest; conditional on surviving, a spine of ancestors spends its time distributed as $h\tilde h$. Each branching along the spine contributes offspring variance weighted by $h^2$, so the effective variance is $\Sigma^2 \sim \sigma^2 N^c$ and a population of $N$ particles has coalescence time $N/\Sigma^2 \sim N^{1-c}$. The many-to-few formula reduces $k$-point genealogical moments to $k$-spine computations, which converge to the moments of the Brownian CPP; the method of moments in the Gromov-weak topology then identifies the limit tree. Unlike the fully pulled regime ($c = 1$, Bolthausen–Sznitman genealogy on $\log^3 N$ scale), at moderate selection the mergers are binary and concentrated near the reflecting boundary.

## Sources

- Florin Boenkost and Julie Tourniaire, "Power-law scaling of the effective population size in a branching particle system for moderate mutation-selection", arXiv:2404.17527 (2024), Section 1 (criticality and the regime $L(\beta_N) = c\log N + 6\log\log N$), Proposition 1.3, Theorems 1–4, Proposition 2.7, <https://doi.org/10.48550/arXiv.2404.17527>.
