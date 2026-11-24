# Forward-time clocks for diffusion limits of Moran and Cannings models

In a two-type Cannings model with population size $N$ and exchangeable offspring numbers $\nu^{(N)}_1, \dots, \nu^{(N)}_N$, let $c_N = E[\nu_1(\nu_1 - 1)]/(N - 1) = \mathrm{Var}[\nu_1]/(N - 1)$ be the pair-coalescence probability and $d_N$ the triple-coalescence probability. Birkner's lecture notes (Section 1.7.2) rescale the type count $X_r$ as $Z^{(N)}_t = X_{\lfloor t/c_N\rfloor}/N$, so that one unit of time is $1/c_N$ generations. Given $Z^{(N)}_t = z$, the increment over one generation has mean $0$ and variance $c_Nz(1 - z)$ (Observation 1.7.11); if $c_N \to 0$ and $d_N/c_N \to 0$, its third and fourth moments are $o(c_N)$ uniformly (Lemma 1.7.13), the rescaled generator converges to $\frac12z(1 - z)f''(z)$, and the rescaled paths converge in distribution to the Wright–Fisher diffusion (Theorem 1.7.12). For the Wright–Fisher model $1/c_N = N$; if $\mathrm{Var}[\nu^{(N)}_1] \to \sigma^2 \in (0, \infty)$ and the fourth moments stay bounded, the clock $1/c_N = (N - 1)/\mathrm{Var}[\nu_1]$ is asymptotic to $N/\sigma^2$ generations and the third and fourth moments are $O(1/N^2)$ (equation (1.75)). For the continuous-time Moran model with $N$ individuals, time must be sped up by the factor $N/2$ to obtain the Wright–Fisher diffusion (Remark 1.3.3). If $\liminf d_N/c_N > 0$, triple mergers have non-vanishing probability in the genealogy of three individuals, which is impossible for Kingman's coalescent (Remark 1.7.6).

## Depends on

- [Cannings model of a haploid population](../../../../Biology/coalescent-theory/multiple-merger-coalescents/cannings-models/cannings-model.md)
- [Pair-coalescence probability of a Cannings model](../../../../Biology/coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/pair-coalescence.md)
- [Möhle–Sagitov conditions for a Kingman genealogy limit](../../../../Biology/coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/mohle-sagitov.md)
- [Wright–Fisher diffusion limit, generator form](../../../../Biology/population-genetics/diffusion-theory/diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md)
- [Diffusion limit of the Moran fixation probability](../../../../Biology/population-genetics/moran-model/tendsto-moran-fixation-diffusion.md)

## Expansion

1. The type-count chain of a two-type Cannings model and its one-generation mean and variance.
2. The moment bounds of Lemma 1.7.13 and the generator convergence on the clock $1/c_N$.
3. Convergence of the rescaled paths to the Wright–Fisher diffusion.
4. The clocks $N$ for the Wright–Fisher model, about $N/\sigma^2$ under bounded offspring moments, and $N/2$ for the continuous-time Moran model.
5. The regime $\liminf d_N/c_N > 0$, where the forward limit has jumps, as a separate statement with its own source.

## Sources

- M. Birkner, Stochastic population models, lecture notes, Johannes Gutenberg-Universität Mainz, winter 2025/26, Section 1.3 (Remark 1.3.3) and Section 1.7.2 (Theorem 1.7.5, Remark 1.7.6, Observation 1.7.11, Theorem 1.7.12, Lemma 1.7.13).
