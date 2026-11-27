# Waiting for k mutations in a spatial model with increasing mutation rates

**Model.** Cells occupy the $d$-dimensional torus $\mathcal{T} = [0,L]^d$ of volume $N = L^d$; initially every point has type $0$. Type-$(i-1)$ points acquire an $i$-th mutation at rate $\mu_i$ per unit volume (a Poisson process in space-time), and every mutation then spreads deterministically as a ball growing at speed $\alpha$, taking over points of lower type (a continuum limit of the biased voter / spatial Moran model; also the polynuclear growth model). Let $\sigma_k$ be the first time some point has type $k$. All parameters may depend on $N$, and the rates are asymptotically increasing: $\mu_1 \lesssim \mu_2 \lesssim \cdots$. Let $\gamma_d$ be the volume of the unit ball in $\mathbb{R}^d$ and

$$\beta_k = \Big(N \alpha^{(k-1)d}\prod_{i=1}^k \mu_i\Big)^{-1/((k-1)d+k)}, \qquad \kappa_j = (\mu_j \alpha^d)^{-1/(d+1)}.$$

**Theorem.** As $N \to \infty$:

1. *(Slow mutation.)* If $\mu_1 \ll \alpha/N^{(d+1)/d}$ and $\mu_i/\mu_1 \to c_i \in (0,\infty]$ for $i \le k$, then $N\mu_1 \sigma_k \Rightarrow W_1 + \cdots + W_k$ with independent $W_i \sim \mathrm{Exp}(c_i)$ ($W_i = 0$ if $c_i = \infty$): each mutation sweeps the torus before the next appears.
2. *(Fast later mutations.)* If $\mu_1 \gg \alpha/N^{(d+1)/d}$ and $\mu_2 \gg (N\mu_1)^{d+1}/\alpha^d$, then $N\mu_1\sigma_k \Rightarrow \mathrm{Exp}(1)$ for every $k \ge 2$: the first mutation is rate-limiting and the rest follow almost immediately inside its ball.
3. *(Nucleation regime.)* If $\mu_1 \gg \alpha/N^{(d+1)/d}$ and $\mu_k \ll 1/(\alpha^d \beta_{k-1}^{d+1})$, then for $t > 0$

    $$\mathbb{P}(\sigma_k > \beta_k t) \to \exp\Big(-\frac{\gamma_d^{k-1}(d!)^{k-1}}{((k-1)d+k)!}\, t^{(k-1)d+k}\Big).$$

4. *(Mixed regime.)* If $\mu_1 \gg \alpha/N^{(d+1)/d}$, $2 \le l < k$ and $\mu_{l+1} \gg 1/(\alpha^d\beta_l^{d+1})$, then $\mathbb{P}(\sigma_k > \beta_l t)$ has the same limit with $k$ replaced by $l$: once $l$ mutations have nucleated, the remaining ones appear on a faster scale.

**Distance between successive driver mutations.** Under the separation of scales $\mu_2 \ll \mu_3 \ll \cdots \ll \mu_k$ and the hypotheses of part 2 (or, with $\mu_{l+1} \ll \mu_{l+2} \ll \cdots \ll \mu_k$, those of part 4 with $l \le j$), the distance $D_{j,k}$ between the first type-$j$ and the first type-$k$ mutation satisfies, for $1 \le j < k$ and $s > 0$,

$$\mathbb{P}\Big(\frac{D_{j,k}}{\alpha\kappa_{j+1}} \le s\Big) \to \int_0^\infty \gamma_d\, (t\wedge s)^d \exp\Big(-\frac{\gamma_d t^{d+1}}{d+1}\Big)dt,$$

the law of the radius at which the first type-$(j+1)$ point appears inside a growing type-$j$ ball, which sets the size of the premalignant field.

## Expansion

A type-$j$ ball born at time $0$ has volume $\gamma_d(\alpha t)^d$ at time $t$, so the first type-$(j+1)$ mutation inside it arrives at a time $T$ with $\mathbb{P}(T > t) = \exp(-\mu_{j+1}\gamma_d\alpha^d t^{d+1}/(d+1))$; $\kappa_{j+1}$ is its time scale, and the new mutation is uniformly placed in the ball of radius $\alpha T$, giving the distance law. Integrating nested ball volumes over $k$ successive nucleation times gives the exponent $(k-1)d + k$ and the constant $\gamma_d^{k-1}(d!)^{k-1}/((k-1)d+k)!$ in part 3, as in the Armitage–Doll multistage model with spatial growth replacing clonal expansion. Increasing rates make later steps faster, which is why the regimes are cut by comparing $\mu_{l+1}$ with $1/(\alpha^d\beta_l^{d+1})$.

## Sources

- Brian Chao and Jason Schweinsberg, "A spatial mutation model with increasing mutation rates", Journal of Applied Probability 60 (2023), 1157–1180, <https://doi.org/10.1017/jpr.2022.120>; numbering as in arXiv:2108.09590: Section 2 (notation, $\beta_k$, $\kappa_j$), Theorems 1–6.
