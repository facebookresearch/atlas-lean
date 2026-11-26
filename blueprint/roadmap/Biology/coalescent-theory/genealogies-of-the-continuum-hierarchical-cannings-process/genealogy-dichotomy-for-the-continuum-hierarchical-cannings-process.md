# Genealogy dichotomy for the continuum hierarchical Cannings process

**Geographic space.** For $N\ge2$ let $Z_N=\{0,\dots,N-1\}$ be the cyclic group. The hierarchical group is $\Omega_N=\oplus_{k\ge0}Z_N$, its $L$-refinement is $\Omega_N^L=\oplus_{k\ge-L}Z_N$, and the *continuum hierarchical group* $\Omega_N^\infty$ is the closure of the set of two-sided sequences in $Z_N^{\mathbb{Z}}$ that vanish above some finite index, with the hierarchical ultrametric (two points are at distance determined by the highest index where they differ). It carries a Haar measure $\mathfrak{h}$.

**Dynamics.** A multitype population (types in a Polish space $\mathbb{K}$, many individuals per site) evolves on $\Omega_N^L$ by

- *migration*: jumps of hierarchical size $k$ at rate $c_k$;
- *block resampling with reshuffling*: at rate $\lambda_k$ a $k$-ball undergoes $\Lambda_k$-Cannings resampling, after which the offspring are reshuffled uniformly over the ball;
- *single-site resampling*: $\Lambda_0$-Cannings and Fleming–Viot (Moran) resampling at rate $d$.

The dual is a spatial coalescent: lineages migrate, coalesce pairwise at rate $d$ when co-located (Kingman), and coalesce in blocks according to $\Lambda_k$ during $k$-ball events. A single lineage performs an effective Lévy process on $\Omega_N^\infty$ driven by $(c_k)$ and $(\lambda_k)$. The continuum process is defined as the $L\to\infty$ limit of the $L$-truncated models, whose parameters for levels below $-L$ are switched off and replaced by site resampling at the bottom level.

**Theorem (regime dichotomy).** Let

$$\Sigma=\sum_{k=0}^{\infty}\frac{1}{c_k}\sum_{\ell=0}^{k}\lambda_\ell .$$

1. *Regime A ($\Sigma=\infty$, stochastic).* The laws of the truncated genealogy processes $\mathfrak{U}^L$ (marked ultrametric measure spaces with marks in $\Omega_N^\infty\times\mathbb{K}$) converge as $L\to\infty$ to the law of a unique strong Markov, Feller process $\mathfrak{U}$ with càdlàg paths, jumping only at block-resampling events. For every $t>0$ and $h\in(0,t]$, the population at time $t$ splits into finitely or countably many depth-$h$ families (disjoint $2h$-balls in genealogical distance); each depth-$t$ family is monotype and covers, up to $\mathfrak{h}$-null sets, a random union of balls in $\Omega_N^\infty$. Locally, the population descends from a single ancestor.
2. *Regime B ($\Sigma<\infty$, deterministic).* No limiting genealogy process exists: for every $t>0$, the probability that two sampled individuals have a common ancestor within time $t$ tends to $0$ as $L\to\infty$, so the genealogy fragments into dust of single-ancestor lines performing independent effective Lévy motions, and the type-frequency process becomes deterministic, equal to $\mathfrak{h}\otimes\theta$ for $t>0$ ($\theta$ the initial mean type distribution).

In regime A, the process $\mathfrak{U}$ is dual to the spatial coalescent with block coalescence, $\mathbb{E}[H(\mathfrak{U}_t,\mathfrak{Y}_0)]=\mathbb{E}[H(\mathfrak{U}_0,\mathfrak{Y}_t)]$ for duality functions $H$ built from polynomials (sample averages over Haar-distributed locations), and it is the unique solution of a well-posed martingale problem. From a translation-invariant ergodic initial state it converges in law to a unique shift-ergodic equilibrium with mean type intensity $\theta$; the equilibrium genealogy is that of the dual coalescent started from one particle at each site of a countable dense subgroup.

## Expansion

$\Sigma$ compares how fast block resampling at levels up to $k$ produces common ancestry with how fast migration at level $k$ spreads lineages out. Two dual lineages started close together coalesce with positive probability, uniformly in $L$, exactly when the effective Lévy motion is recurrent enough relative to the accumulated block-coalescence rates; this is the condition $\Sigma=\infty$. Then sampled individuals share ancestors and the type field clusters into monotype patches with a non-trivial genealogy. When $\Sigma<\infty$, lineages escape before coalescing: the continuum limit has infinitely many ancestors per ball and both genealogy and type frequencies become trivial (a law of large numbers). The construction goes through the dual: convergence of the finite spatial coalescents as $L\to\infty$ gives convergence of all moment functionals of $\mathfrak{U}^L$, which determine the laws.

## Sources

- A. Greven, F. den Hollander, "Continuum space hierarchical Cannings process: II. Genealogies and ancestral web", arXiv:2611.17017 (2026), Section 1.2 (model) and Theorems 2.1, 2.3, 2.5 and 2.7 (Section 2.1). <https://doi.org/10.48550/arXiv.2611.17017>
