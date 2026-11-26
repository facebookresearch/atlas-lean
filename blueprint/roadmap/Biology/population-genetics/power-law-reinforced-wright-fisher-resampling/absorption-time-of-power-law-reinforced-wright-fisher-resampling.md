# Absorption time of power-law reinforced Wright-Fisher resampling

**Model.** Fix $n\ge2$ and $\alpha>0$. The chain $\mathbf{X}_k=(\mathbf{X}_k^{(1)},\dots,\mathbf{X}_k^{(n)})$ on $\Omega_n=\{\mathbf{x}\in\mathbb{Z}_{\ge0}^n:\sum_i\mathbf{x}_i=n\}$ starts at $\mathbf{X}_0=(1,\dots,1)$ ($n$ distinct types, one copy each). Given $\mathbf{X}_{k-1}=a$, each of the $n$ individuals of generation $k$ independently chooses type $i$ with probability

$$\frac{a_i^{\alpha}}{\sum_{l=1}^na_l^{\alpha}},$$

and $\mathbf{X}_k^{(i)}$ is the number choosing $i$. For $\alpha=1$ this is the neutral Wright-Fisher model, and its genealogy is Kingman's $n$-coalescent. The absorbing states have one type at count $n$; let $\mathcal{T}$ be the absorption (fixation) time and $\mathcal{W}$ the fixed type. Let $\lambda_k=2^{1/k}$ for $k\ge1$ and $\lambda_0=+\infty$, and let $\mathfrak{L}_k$ be the set of types with maximal count at time $k$ ($\mathfrak{L}_0=\emptyset$).

**Statements.**
1. *(Neutral case.)* For $\alpha=1$, $\mathcal{T}$ is typically of order $n$.
2. *(Superlinear reinforcement.)* If $k\ge2$ and $\alpha\in(\lambda_k,\lambda_{k-1}]$, then for every $\epsilon>0$

$$\lim_{n\to\infty}\mathbb{P}\Big(\Big|\frac{\log(\alpha)\,\mathcal{T}}{2\log\log n}-1\Big|<\epsilon\Big)=1 .$$

For $\alpha>2$ the same holds conditionally on the event $E$ that the first-generation counts have a unique maximum, while on $E^c$ the normalization $2\log\log n$ is replaced by $(1+\tfrac{\alpha}{2})\log\log n$. Hence for every $\alpha>1$ the absorption time is of order $\log\log n$.
3. *(Sublinear weights.)* For $0<\alpha<1$ and every $M\in\mathbb{Z}_{>0}$, $\mathbb{P}(\mathcal{T}>M)\ge(1-e^{-C(\alpha)n})^M$, so $\mathcal{T}\ge\exp(\Omega_\alpha(n))$ with probability $1-o(1)$.
4. *(Predictability of the winner.)* For $k\ge1$ and $\alpha\in(\lambda_k,\lambda_{k-1})$, $\mathbb{P}(\mathcal{W}\in\mathfrak{L}_k)=1-o(1)$ and $\mathbb{P}(\mathcal{W}\in\mathfrak{L}_{k-1})=o(1)$: the winner is determined by the leaders after exactly $k$ rounds and not before.

## Depends on

- [Absorption time of the Wright-Fisher diffusion](../diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/absorption-time.md)

## Expansion

From the uniform start, the first-round counts are approximately i.i.d. Poisson$(1)$, whose maximum is about $\log n/\log\log n$. With weights $a^\alpha$, a leader with count $m$ against a bulk of typical counts receives a share that grows like $m^{\alpha}$ relative to its competitors, so the ratio of the leader's count to the bulk is raised roughly to the power $\alpha$ each round; the leader's dominance $1-\delta$ therefore improves doubly exponentially, $\log(1/\delta_t)\approx\alpha^t$, and reaching $\delta\approx 1/n$ starting from $\delta\approx 1/\log n$ takes about $\log\log n/\log\alpha$ further rounds, giving the $2\log\log n/\log\alpha$ total once the early rounds are included. The thresholds $\alpha^k=2$ mark when the Poisson fluctuations of the leading counts stop being able to reshuffle the leader, which yields the all-or-nothing transition. For $\alpha<1$ the weights favour rare types, so the uniform-ish configuration is metastable and every round has probability $1-e^{-Cn}$ of not absorbing.

## Sources

- Itai Benjamini, Zhenhao Cai, Guanyi Chen, Shuyang Gong, "The Conclave Process", arXiv:2607.22324 (2026), Definition 1.1, Theorems 1.3, 1.5 and 1.6, <https://doi.org/10.48550/arXiv.2607.22324>.
