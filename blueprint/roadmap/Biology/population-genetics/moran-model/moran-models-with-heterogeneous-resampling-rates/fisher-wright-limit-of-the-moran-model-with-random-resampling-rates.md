# Fisher–Wright limit of the Moran model with random resampling rates

**Model.** A population of $N$ individuals carries two types, $1$ and $0$. Individual $i$ is assigned a resampling rate $R_i$, drawn i.i.d. from a discrete law $\mathbb P=\sum_k\mu_k\delta_{r_k}$ on $(0,\infty)$; the rates are frozen (a quenched environment). At rate $R_i$, individual $i$ adopts the type of an individual chosen uniformly at random from the population. With $\tau_i(t)$ the type of individual $i$ at time $t$, let

$$Y^N(t)=\frac1N\sum_{i=1}^N \mathbf 1_{\{\tau_i(Nt)=1\}}\,\delta_{R_i}$$

be the empirical measure on $\mathbb R_+$ of the rates of the type-$1$ individuals at the rescaled time $Nt$ (time sped up by the population size), so $Y^N(t)(\mathbb R_+)$ is the frequency of type $1$ at time $Nt$. Assume:

1. $\sum_k\mu_k r_k^{-1}<\infty$;
2. with $R_1,R_2,\dots$ i.i.d. from $\mathbb P$ and $N_R=\{k: R_i=r_k\text{ for some }i\le N\}$ the set of rate classes present among the first $N$ individuals,

    $$\lim_{N\to\infty}\frac{\big(\sum_{k\in N_R}r_k\big)\big(\sum_{k\in N_R}r_k^{-2}\big)}{N\,\min_{k\in N_R}r_k}=0\qquad \mathbb P^{\otimes\mathbb N}\text{-almost surely}.$$

Condition 2 holds whenever $\mathbb P$ has finite support; for infinite support it follows from suitable power-law tail conditions on $(\mu_k)$ together with moment conditions $\sum_k\mu_kr_k^{-\alpha}<\infty$ and $\sum_k\mu_kr_k^{\beta}<\infty$ for large enough $\alpha,\beta$ (Corollary 2.2 of the source).

**Theorem.** If $Y^N(0)\to\nu$, then for $\mathbb P^{\otimes\mathbb N}$-almost every realization of the rates,

$$\mathcal L[Y^N]\to\mathcal L[Y]\qquad\text{in the Meyer–Zheng topology},$$

where $Y(t)=S(t)\,\mathbb P$ and $S$ is the Fisher–Wright diffusion

$$dS(t)=\sqrt{D\,S(t)(1-S(t))}\,dW(t),\qquad S(0)=\nu(\mathbb R_+),\qquad \frac1D=\int_{\mathbb R_+}\frac1r\,\mathbb P(dr).$$

## Depends on

- [Backward generator of the Wright–Fisher diffusion with selection](../../diffusion-theory/wright-fisher-diffusion/generator.md)

## Expansion

The limit says two things. First, for $t>0$ the type-$1$ frequency is the same within every rate class, so the rate profile of type $1$ is $S(t)\,\mathbb P$, whatever the initial profile $\nu$. In the original (unscaled) time, within-class frequencies equilibrate on a time scale of order $1$, much faster than drift, which acts on time scale $N$; this is why $Y^N$ is read at time $Nt$. Second, the common frequency performs Fisher–Wright drift with an effective rate given by the harmonic mean $D=\big(\int r^{-1}d\mathbb P\big)^{-1}$. An individual of rate $r$ keeps its type for a mean time $1/r$, so slow resamplers carry the population's memory and dominate drift. This mirrors how the effective population size of a fluctuating population is a harmonic mean. The initial equilibration is instantaneous in the limit, so the convergence holds in the Meyer–Zheng (pseudo-path) topology and not in Skorokhod's. The proof splits the error into four approximation terms by a triangle inequality, controlling the last by a coupling with $S$, and applies a generator-convergence criterion of Ethier and Kurtz.

## Sources

- Siva Athreya, Frank den Hollander and Adrian Röllin, "The Moran model with random resampling rates", *The Annals of Applied Probability* 35 (2025), 1852–1868, <https://doi.org/10.1214/25-aap2159>. Numbering as in the preprint arXiv:2402.01333v2, <https://arxiv.org/abs/2402.01333v2>: Assumption 1.1 and Theorem 1.2 (Fisher–Wright limit with harmonic-mean diffusion constant), Lemma 2.1 and Corollary 2.2 (conditions on $\mathbb P$ implying the main assumption), Section 3, Lemmas 3.1 and 3.3 (approximation steps and generator convergence).
