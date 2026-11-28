# Longest pendant and interior edges of a Sevast'yanov branching tree

**Model.** Let $(T, L)$ be a random element of $(0,\infty) \times \mathbb Z_{\ge 0}$, with $T$ and $L$ possibly dependent. Starting from one individual, each individual $u$ lives for time $T_u$ and at death gives birth to $L_u$ children, the pairs $(T_u, L_u)$ being i.i.d. copies of $(T, L)$ (a Sevast'yanov process; Bellman-Harris when $T$ and $L$ are independent). Assume

$$\mathbb P(T = 0) = \mathbb P(T = \infty) = 0, \qquad \mathbb E(L) \in (1, \infty),$$

so the population survives with positive probability. Let $\alpha > 0$ be the Malthusian parameter, $\mathbb E(L e^{-\alpha T}) = 1$, assume $\mathbb E(e^{-\alpha T} L \log_+ L) < \infty$, and let $Z_\infty$ be the limit of the Malthusian martingale (positive on survival). Assume the lifetime tail is regular in the sense that for some $\beta \ge 0$

$$\lim_{t \to \infty} \frac{\mathbb P(T > t + a)}{\mathbb P(T > t)} = e^{-\beta a} \qquad \text{for all } a \ge 0.$$

In the genealogical tree up to time $t$, with birth and death times $b_u, d_u$, let $M^{\mathrm p}_t = \max_{u \text{ alive at } t}(t - b_u)$ be the longest pendant edge (oldest living individual) and $M^{\mathrm i}_t = \max_{u : d_u \le t}(d_u - b_u)$ the longest interior edge. Define the characteristic length

$$\ell_t = \inf\bigl\{\ell > 0 : e^{-\alpha \ell}\, \mathbb P(T > \ell) \le e^{-\alpha t}\bigr\}, \qquad \text{so } \lim_{t\to\infty} \frac{\ell_t}{t} = \frac{\alpha}{\alpha + \beta}.$$

**Theorem (growth rate).** Almost surely on survival, $M^{\mathrm p}_t / t \to \alpha/(\alpha + \beta)$, and if $\beta > 0$ also $M^{\mathrm i}_t / t \to \alpha/(\alpha + \beta)$.

**Theorem (extremal point processes).** Let $\mathcal E^{\mathrm p}_t = \sum_{u \text{ alive}} \delta_{(t - b_u) - \ell_t}$ and $\mathcal E^{\mathrm i}_t = \sum_{u : d_u \le t} \delta_{(d_u - b_u) - \ell_t}$. Then $(\mathcal E^{\mathrm p}_t, \mathcal E^{\mathrm i}_t)$ converges jointly in distribution, for vague convergence, to a pair that, conditionally on $Z_\infty$, consists of independent Poisson point processes on $\mathbb R$ with intensities

$$c_\star Z_\infty\, \alpha\, e^{-(\alpha+\beta)x}\, dx \quad \text{and} \quad c_\star Z_\infty\, \beta\, e^{-(\alpha+\beta)x}\, dx, \qquad c_\star = \mathbb E\bigl(\alpha T e^{-\alpha T} L\bigr)^{-1}.$$

In particular $(M^{\mathrm p}_t - \ell_t, M^{\mathrm i}_t - \ell_t)$ converges in distribution to the pair of rightmost atoms (Gumbel-type laws randomized by $Z_\infty$), and the longest edge in the tree is pendant with probability tending to $\alpha/(\alpha + \beta)$. For exponential lifetimes with rate $\beta$ independent of $L$ (a continuous-time Galton-Watson tree), $\ell_t = (1 - 1/\mathbb E L)\, t + o(t)$.

## Proof sketch

Branches of length about $\ell$ at time $t$ are mostly born near time $t - \ell$, when about $e^{\alpha(t - \ell)}$ individuals are born, each surviving to age $\ell$ with probability $\mathbb P(T > \ell)$; $\ell_t$ is the length at which the expected number of such branches is of order one. Under the regular-tail assumption, conditional on $T > \ell_t$ the residual lifetime is asymptotically exponential with rate $\beta$, so a long-lived individual is still alive at time $t$ with probability tending to $\alpha/(\alpha+\beta)$ and has already died otherwise, which splits a single Poisson cloud into the two independent clouds. The Poisson limit is proved by computing Laplace functionals conditionally on the population at an intermediate time, where Nerman's law of large numbers $e^{-\alpha t}\#\{\text{alive}\} \to Z_\infty (1 - \mathbb E e^{-\alpha T})/\mathbb E(\alpha T e^{-\alpha T} L)$ supplies the random intensity; first and second moment bounds give the almost sure growth rates.

## Sources

- Sergey Bocharov, Simon C. Harris and Bastien Mallein, "The longest branches in a non-Markovian phylogenetic tree", to appear in *Branching Processes and Related Fields*, Springer. Preprint version: arXiv:2410.02444 (2024), Theorems 1.1 and 1.2 with Remarks 1.3-1.5, Lemmas 2.1 and 2.2, Remark 2.3, Proposition 2.4, <https://doi.org/10.48550/arXiv.2410.02444>.
