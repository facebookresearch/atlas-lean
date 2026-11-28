# Stochastic Farris transform and the locus-number requirement without a molecular clock

**Model (MSC-JC$(m,k)$).** A species phylogeny $S = (V_s, E_s; r, \vec\tau, \vec\mu)$ is a rooted binary tree on leaves $L = \{1, \dots, n\}$ with edge lengths $\tau_e > 0$ (coalescent units) and edge mutation rates $\mu_e > 0$; no molecular clock is assumed, so the weighted root-to-leaf distances $\mu_{rx} = \sum_{e \in \pi(r,x)} \tau_e \mu_e$ may differ across leaves. Independently for each locus $i \in [m]$ a gene tree $G^{(i)}$ is drawn from the multispecies coalescent on $S$ (with rate-weighted branch lengths $\delta^{(i)}_e$), and a sequence of length $k$ evolves on $G^{(i)}$ under the Jukes–Cantor model: a site changes on edge $e$ with probability $p(\delta^{(i)}_e)$, where $p(x) = \tfrac34(1 - e^{-4x/3})$, to a uniformly chosen other state.

**Stochastic Farris transform.** For three species $\mathcal{X} = \{1,2,3\}$ let $\Delta_{xy} = \mu_{rx} - \mu_{ry}$ and assume $\mu_{r1} \ge \max\{\mu_{r2}, \mu_{r3}\}$. Encode states as $\{0,1,2,3\}$ and replace each sequence $\xi^i_x$ by $\xi^i_{x,N} = \xi^i_x \oplus \epsilon^i_x$ (addition mod $4$), where the $\epsilon^{ij}_x$ are independent with $\epsilon^{ij}_x = 0$ with probability $1 - p(\Delta_{1x})$ and equal to each of $1, 2, 3$ with probability $p(\Delta_{1x})/3$. Adding Jukes–Cantor noise of length $\Delta_{1x}$ to leaf $x$ makes all three root-to-leaf distances equal, so the transformed data look as if generated under a molecular clock.

**Theorem (data requirement).** Let mutation rates lie in $(\mu_L, \mu_U)$, leaf-edge lengths in $(f', g')$ and internal-edge lengths in $(f, g)$, and suppose $k \gtrsim f^{-C}$ for some $C > 0$. Then a two-stage algorithm (estimate the $\Delta_{xy}$ on a reserved set of loci, apply the stochastic Farris transform, then compare quantiles of the transformed pairwise distances) recovers the rooted topology of $S$ restricted to $\{1,2,3\}$ with probability at least $95\%$ provided

$$
m \gtrsim \frac{1}{f} \vee \frac{1}{\sqrt{k}\, f^2}.
$$

This matches, up to constants, the locus-number versus sequence-length trade-off $m \asymp 1/(f^2 \sqrt{k})$ previously known only under the molecular clock, plus the unavoidable $1/f$ term. A general version allows any failure probability $\varepsilon$ with explicit sizes for the four groups of loci used by the two stages.

## Depends on

- [Jukes–Cantor distance](../../../jukes-cantor-model/jc-distance.md)
- [Species tree](../../../../coalescent-theory/multispecies-coalescent/species-tree.md)

## Expansion

The weighted species metric $\mu_{ab}$ is ultrametric exactly when all root-to-leaf distances $\mu_{ra}$ agree, and earlier quantile-based reconstruction (comparing low empirical quantiles of pairwise sequence distances across loci) is only guaranteed in that ultrametric case. The reduction step estimates the offsets $\Delta_{xy}$ to precision $\phi = \Theta(f/\log f^{-1})$ using $m' \gtrsim 1 \vee 1/(k f^2)$ loci (Theorem 2); the stochastic Farris transform then adds independent Jukes–Cantor noise to the shorter leaves so that the transformed data are approximately those of an ultrametric phylogeny, and the quantile test is run on the remaining loci. Because the transform only adds noise, it costs a constant factor in signal, which is why the clock-case rate survives.

## Sources

- G. Dasarathy, E. Mossel, R. Nowak, S. Roch, "Coalescent-based species tree estimation: a stochastic Farris transform", arXiv:1707.04300 (2017): Definitions 1–4 (species phylogeny, gene trees, weighted species and gene metrics), Section 1 (MSC-JC$(m,k)$ process), Theorem 1 (data requirement), Theorem 2 (ultrametric reduction), Definition 5 (stochastic Farris transform), Proposition 3 (general version). <https://doi.org/10.48550/arXiv.1707.04300> Published version: Journal of Mathematical Biology (2022), <https://doi.org/10.1007/s00285-022-01731-5>.
