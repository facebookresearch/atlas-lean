# Seed-bank Cannings graphs and the delayed Kingman and Xi limits

**Model.** A haploid population of constant size $N$ lives on the vertex set $\mathbb{Z} \times [N]$ (generation, label). Each generation carries exchangeable reproductive weights $\bar W^N_g = (W^N_v)_{v}$, i.i.d. over generations with law $\mathcal{W}^N$ (a Cannings mechanism). Each individual $v$ independently draws a delay $J^N_v \sim \mu^N$ on $\{1, \dots, m_N\}$ and picks its parent in generation $g(v) - J^N_v$ with probability proportional to the weights there: $\mathbb{P}(U^N_v = k \mid J^N_v = j, \bar W) = W^N_{(g(v)-j, k)}$. Parents more than one generation back model dormant seeds. The resulting directed graph (each vertex pointing to its parent) is the *seed-bank random di-graph*. Write $\beta_N = \mathbb{E}[J^N_v]$, $c_N = N\,\mathbb{E}[(W^N_v)^2]$, $d_N = N\,\mathbb{E}[(W^N_v)^3]$, and let the *window process* $\bar B^N_g$ count the ancestral lineages of a sample crossing generation $g$ back in time, sorted by the generation they point to.

**Theorem.**
1. *(Duality.)* On a single graph, the forward type-frequency process $\bar X^N_g$ (frequencies of a type in the last $m_N$ generations) and the ancestral process are sampling duals, and the window process and $\bar X^N$ are moment duals, for every finite $N$.
2. *(Kingman limit with delay.)* If $\mu^N(1) > 0$ and, for some $\varepsilon > 0$, $c_N/\beta_N^2 \to 0$, $N^{\varepsilon}\tau_N c_N \to 0$ (with $\tau_N$ the mixing time of the delay chain), $(1/4)^{N^\varepsilon}\beta_N^2 \to 0$ and $d_N/(\beta_N c_N) \to 0$, then $|\bar B^N_{\lfloor t\beta_N^2/c_N \rfloor}|$ converges in finite-dimensional distributions to the block-counting process of Kingman's coalescent.
3. *($\Xi$ limit with delay.)* If $\beta_N \to \beta < \infty$ and the ancestral process of the Cannings model driven by $\mathcal{W}^N$, sped up by $1/c_N$, converges to the block-counting process of a $\Xi$-coalescent, then $|\bar B^N_{\lfloor t/c_N\rfloor}|$ converges to the block-counting process of the $\Xi^\beta$-coalescent, where $\Xi^\beta$ is the image of $\Xi$ under $\boldsymbol y \mapsto \boldsymbol y/\beta$ on the simplex $\Delta$.
4. *(Forward limit.)* If $m_N \le m$ and the delay laws' stationary distributions $\nu^N \to \nu$, then under item 2 (time $t\beta_N^2/c_N$) or item 3 (time $t/c_N$) all $m$ coordinates of $\bar X^N$ converge to a common process $X_t$ started at $X_0 = \sum_i \nu(i)x_i$: the Wright–Fisher diffusion in the Kingman case, and the moment dual of the $\Xi^\beta$-coalescent block counts in the $\Xi$ case.

## Depends on

- [Merger rates of a coalescent with simultaneous multiple collisions](../../../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Expansion

A weak seed bank (bounded delays) does not change the shape of genealogies, only their clock: two lineages can coalesce only when they point to the same generation, which happens with probability of order $1/\beta_N^2$ per generation at stationarity, so Kingman time is stretched by $\beta_N^2$. With skewed reproduction a single large family occupies a fraction $y$ of one generation, but lineages are spread over generations, so only a fraction $y/\beta$ of them land in it; this thins every paintbox block by $1/\beta$, which is the $\Xi \to \Xi^\beta$ transformation and smooths multiple mergers. Building forward and backward processes on one random graph gives the dualities pathwise.

## Sources

- Adrián González Casanova, Lizbeth Peñaloza and Arno Siri-Jégousse, "Seed bank Cannings graphs: How dormancy smoothes random genetic drift", ALEA Lat. Am. J. Probab. Math. Stat. 20 (2023), 1165, <https://doi.org/10.30757/ALEA.v20-43>. Numbering follows the arXiv version, arXiv:2210.05819 (2022): Definitions 1–4, Propositions 3–4, Theorems 1–3 and the definition of $\Xi^\beta$ (Section 2), <https://doi.org/10.48550/arXiv.2210.05819>.
