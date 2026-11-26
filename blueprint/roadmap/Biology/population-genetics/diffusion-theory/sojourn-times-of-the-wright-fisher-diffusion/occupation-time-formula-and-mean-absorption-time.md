# Occupation times and mean absorption time of the Wright–Fisher diffusion with selection

Let $X$ solve the [martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md) with genic selection $\alpha$ and no mutation, started at $p \in (0, 1)$; a solution exists for every $\alpha$, the [canonical process under $P^\alpha$](../wright-fisher-diffusion-with-selection-and-mutat/under-p-alpha-the-canonical-process-solves-the-s.md). Here $a(x) = x(1 - x)$, $b(x) = \alpha x(1 - x)$, the scale density is $s'(x) = e^{-2\alpha x}$, and $m(dy) = 2\, dy / (a(y)\, s'(y))$.

This is a special case of [the Green function and occupation times of a one-dimensional diffusion](../selection-duality-and-general-one-dimensional-di/green-function-occupation-times-and-mean-exit-ti.md): its almost sure hitting hypothesis holds by [absorption in finite time](../fixation-and-absorption-in-the-wright-fisher-dif/ae-exists-absorbed.md), and its weighted integrability $\int_0^1 s(y)(s(1) - s(y))\, m(dy) < \infty$ holds, since $s(y) \sim y$ and $m(dy) \sim 2\, dy / y$ near $0$, and symmetrically near $1$.

With the normalization that the density $G_D(p, y)$ of [the Dirichlet Green's function](../selection-duality-and-general-one-dimensional-di/green-function.md) is the Green kernel $G(p, y)$ times the speed density $m(y)$, for every bounded measurable $g$,

$$\mathbb{E}_p \int_0^\tau g(X_t)\, dt = \int_0^1 G_D(p, y)\, g(y)\, dy,$$

and $\mathbb{E}_p \tau = T_\alpha(p) < \infty$, the [mean absorption time under selection](selection-mean-absorption-time.md).

## Depends on

- [Green function, occupation times and mean exit times of a one-dimensional diffusion](../selection-duality-and-general-one-dimensional-di/green-function-occupation-times-and-mean-exit-ti.md)
- [Absorption in finite time](../fixation-and-absorption-in-the-wright-fisher-dif/ae-exists-absorbed.md)
- [Dirichlet Green's function of a one-dimensional diffusion](../selection-duality-and-general-one-dimensional-di/green-function.md)
- [Mean absorption time of the Wright–Fisher diffusion with selection](selection-mean-absorption-time.md)
- [Martingale problem for the Wright–Fisher diffusion](../fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
- [Under the selection path measure the canonical process solves the selection martingale problem](../wright-fisher-diffusion-with-selection-and-mutat/under-p-alpha-the-canonical-process-solves-the-s.md)

## Expansion

1. The normalization check: $G(p, y)\, m(y)$ reproduces $2 S(\min)(S(1) - S(\max))/(S(1)\, a\, \psi)$ of [the Dirichlet Green's function](../selection-duality-and-general-one-dimensional-di/green-function.md).
2. $g = 1$ gives $T_\alpha$, and $\alpha = 0$ gives the mean absorption time of Kimura and Ohta.

## Sources

- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer (2004), <https://doi.org/10.1007/978-0-387-21822-9>, Chapter 4 (sojourn times).
- S. Karlin and H. M. Taylor, *A Second Course in Stochastic Processes*, Academic Press (1981), Chapter 15.
- M. Kimura and T. Ohta, The average number of generations until fixation of a mutant gene in a finite population, *Genetics* 61 (1969), 763–771, <https://pmc.ncbi.nlm.nih.gov/articles/PMC1212239/> (mean time with selection).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10 (background).
