# Wright–Fisher martingale-problem solutions under the usual augmentation

Let $T>0$ and let $X$ be a process with continuous paths that, with respect to its natural filtration $(\mathcal F^X_t)_{t\in[0,T]}$, solves on $[0,T]$ one of the Wright–Fisher martingale problems: the [Wright–Fisher diffusion with selection](../../../Biology/population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md) on $[0,1]$, the [Wright–Fisher diffusion with selection and two-way mutation](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md) on $[0,1]$, or the problem on the simplex for the [K-allele Wright–Fisher generator](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md), with test functions $f\in C^2$. Because the state space is compact, each pair $(f,Lf)$ restricted to it is bounded and continuous. Then, by [the preservation of martingale problems under the usual augmentation](martingales-and-martingale-problems-are-preserve.md), $X$ solves the same martingale problem with respect to the usual augmentation $(\mathcal F^{X,\mathrm{aug}}_t)_{t\in[0,T]}$, and the [hitting times of closed sets](../../markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-times-of-closed-sets-by-continuous-adapt.md) by $X$, such as fixation times and exit times of $[a,1-a]$, remain stopping times for the augmentation.

## Depends on

- [Martingales and martingale problems are preserved by the usual augmentation](martingales-and-martingale-problems-are-preserve.md)
- [Hitting times of closed sets by continuous adapted processes are stopping times (continuous time)](../../markov-chains/finite-continuous-time-markov-chains/hitting-times-of-finite-continuous-time-markov-c/hitting-times-of-closed-sets-by-continuous-adapt.md)
- [Martingale problem for the Wright–Fisher diffusion](../../../Biology/population-genetics/diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
- [Martingale problem for the Wright–Fisher diffusion with selection and two-way mutation](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-mutation/two-way-mutation-and-selection-wright-fisher-mar.md)
- [Generator of the K-allele Wright–Fisher diffusion with mutation and genic selection](../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion-with-selection-and-mutat/k-allele-wright-fisher-generator-on-the-simplex.md)

## Expansion

A full page matches each hypothesis of the general theorem: continuity of paths, the finite horizon (the Wright–Fisher pages are stated on $[0,\infty)$ and are restricted to $[0,T]$), and boundedness and continuity of $(f,Lf)$ on the compact state space. It does not repeat the proof of the general theorem.

## Sources

- I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991, <https://doi.org/10.1007/978-1-4612-0949-2>, usual augmentation (Ch. 1, topic level).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, filtrations, Ch. 2 and Ch. 4 (topic level).
