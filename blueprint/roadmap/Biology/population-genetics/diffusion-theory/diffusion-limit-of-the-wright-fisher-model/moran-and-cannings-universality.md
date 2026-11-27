# Forward-time clocks for diffusion limits of Moran and Cannings models

In a two-type Cannings model with population size $N \ge 2$ and exchangeable offspring numbers $\nu^{(N)}_1, \dots, \nu^{(N)}_N$, let $c_N = E[\nu_1(\nu_1 - 1)]/(N - 1) = \mathrm{Var}[\nu_1]/(N - 1)$ be the pair-coalescence probability and $d_N$ the triple-coalescence probability; assume $c_N > 0$, so that the clock $1/c_N$ is finite (if every parent has exactly one child, $c_N = 0$ and the type count never moves). Following Möhle (2001), rescale the type count $X_r$ as $Z^{(N)}_t = X_{\lfloor t/c_N\rfloor}/N$, so that one unit of time is $1/c_N$ generations. Given $Z^{(N)}_t = z$, the increment over one generation has mean $0$ and variance $c_Nz(1 - z)$; if $c_N \to 0$ and $d_N/c_N \to 0$, the rescaled generator converges to $\frac12z(1 - z)f''(z)$ (Möhle 2001, where the forward Wright–Fisher limit is shown to hold exactly when the genealogy converges to Kingman's coalescent; by Möhle and Sagitov 2001 the latter holds exactly when $d_N/c_N \to 0$). If in addition the starting frequencies converge, $Z^{(N)}_0 = z_N \to z \in (0,1)$, the rescaled paths converge in distribution to the Wright–Fisher diffusion started at $z$ (Möhle 2001; for the Wright–Fisher model, Ethier and Kurtz 1986, Chapter 10, Section 1). The initial condition is needed: in the Wright–Fisher model the starting frequencies can tend to $1/4$ along even $N$ and to $3/4$ along odd $N$ while every offspring-moment condition holds, and then the paths have no limit. For the Wright–Fisher model $1/c_N = N$; if $\mathrm{Var}[\nu^{(N)}_1] \to \sigma^2 \in (0, \infty)$ and the fourth moments stay bounded, the clock $1/c_N = (N - 1)/\mathrm{Var}[\nu_1]$ (finite since $\mathrm{Var}[\nu_1] > 0$ for large $N$) is asymptotic to $N/\sigma^2$ generations, and $d_N = O(1/N^2)$, so $d_N/c_N \to 0$ (from the definitions). For the continuous-time Moran model with $N$ individuals, time must be sped up by the factor $N/2$ to obtain the Wright–Fisher diffusion (Durrett 2008, Chapter 1). If $\liminf d_N/c_N > 0$, triple mergers have non-vanishing probability in the genealogy of three individuals, which is impossible for Kingman's coalescent (Möhle and Sagitov 2001).

## Depends on

- [Cannings model of a haploid population](../../../../Biology/coalescent-theory/multiple-merger-coalescents/cannings-models/cannings-model.md)
- [Pair-coalescence probability of a Cannings model](../../../../Biology/coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/pair-coalescence.md)
- [Möhle–Sagitov conditions for a Kingman genealogy limit](../../../../Biology/coalescent-theory/multiple-merger-coalescents/kingman-limit-of-cannings-models/mohle-sagitov.md)
- [Wright–Fisher diffusion limit, generator form](../../../../Biology/population-genetics/diffusion-theory/diffusion-limit-of-the-wright-fisher-model/tendsto-wf-generator.md)
- [Diffusion limit of the Moran fixation probability](../../../../Biology/population-genetics/moran-model/tendsto-moran-fixation-diffusion.md)
- [Moran and Cannings models: generator limits and effective size](../../../../Biology/population-genetics/moran-model/moran-and-cannings-models-generator-limits-and-e.md)

## Expansion

1. The type-count chain of a two-type Cannings model and its one-generation mean and variance.
2. The generator convergence on the clock $1/c_N$, for $c_N > 0$, under $c_N \to 0$ and $d_N/c_N \to 0$.
3. Convergence of the rescaled paths, started from $z_N \to z \in (0,1)$, to the Wright–Fisher diffusion started at $z$.
4. The clocks $N$ for the Wright–Fisher model, about $N/\sigma^2$ under bounded offspring moments, and $N/2$ for the continuous-time Moran model.
5. The regime $\liminf d_N/c_N > 0$, where the forward limit has jumps, as a separate statement with its own source.

## Sources

- M. Möhle, Forward and backward diffusion approximations for haploid exchangeable population models, Stochastic Process. Appl. 95 (2001), 133–149. <https://doi.org/10.1016/S0304-4149(01)00093-X>
- M. Möhle and S. Sagitov, A classification of coalescent processes for haploid exchangeable population models, Ann. Probab. 29 (2001), 1547–1562.
- M. Möhle, Total variation distances and rates of convergence for ancestral coalescent processes in exchangeable population models, Adv. Appl. Probab. 32 (2000), 983–993.
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), Chapter 10, Section 1.
- R. Durrett, *Probability Models for DNA Sequence Evolution*, 2nd ed., Springer (2008), Chapter 1.
