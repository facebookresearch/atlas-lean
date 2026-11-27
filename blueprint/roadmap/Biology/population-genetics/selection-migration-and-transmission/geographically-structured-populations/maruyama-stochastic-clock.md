# A random clock for the total allele frequency in a structured population

In the neutral structured diffusion with conservative migration, a connected migration graph (the rate matrix $Q = (q_{ij})$ irreducible, as in the invariance of fixation probabilities) and census weights $w_i = \kappa_i/K$ (generator as in the invariance of fixation probabilities with $\alpha = 0$), the total frequency $\bar x = \sum_iw_ix_i$ is a continuous martingale whose quadratic variation grows at rate $H(x)/K$, where $H(x) = \sum_iw_ix_i(1 - x_i)$. By concavity of $y \mapsto y(1 - y)$, $H(x) \le \bar x(1 - \bar x)$, with equality exactly when all demes have the same frequency. Define the nondecreasing random clock

$$A(t) = \int_0^{t \wedge \tau}\frac{H(x(s))}{\bar x(s)(1 - \bar x(s))}\,ds \le t \wedge \tau,$$

with $\tau$ the absorption time, and $Y_v = \bar x(A^{-1}(v))$ for its right-continuous inverse $A^{-1}$. Then $Y$ is a continuous martingale on $[0, 1]$ with $d\langle Y\rangle_v = Y_v(1 - Y_v)\,dv/K$, so by Itô's formula it solves the martingale problem for the neutral Wright–Fisher generator $\frac{1}{2K}y(1 - y)\partial_y^2$; this martingale problem is well posed (Epstein and Pop 2019, Theorem 1.3, for generalized Kimura operators), so $Y$ is the neutral Wright–Fisher diffusion of a panmictic population of $K$ times the reference size, run up to its absorption time $A(\tau)$. Two consequences follow: the fixation probability is $\bar x(0)$, as for a panmictic population, and since $A(t) \le t$ the absorption time satisfies $\tau \ge A(\tau)$, so the mean absorption time of the structured population is at least the panmictic mean, with the deficit of the clock measuring the differentiation $\bar x(1 - \bar x) - H$ among demes. In physical time $\bar x$ is not in general a one-dimensional Markov process, since its quadratic-variation rate depends on how the allele is spread among demes and not only on $\bar x$.

## Depends on

- [Invariance of fixation probabilities under conservative migration](../../../../Biology/population-genetics/selection-migration-and-transmission/geographically-structured-populations/maruyama-fixation-invariance.md)
- [Kimura–Ohta mean absorption time of a neutral allele](../../../../Biology/population-genetics/diffusion-theory/wright-fisher-diffusion/mean-absorption-time.md)
- [Martingale problem for the Wright–Fisher diffusion](../../diffusion-theory/fixation-and-absorption-in-the-wright-fisher-dif/is-wright-fisher-solution.md)
- [Uniqueness in law for the neutral Wright–Fisher martingale problem](../../diffusion-theory/neutral-wright-fisher-martingale-problem/uniqueness-in-law-for-the-neutral-martingale-pro.md)

## Proof depends on

- [Itô's formula for continuous semimartingales with bounded derivatives](../../../../Probability/stochastic-calculus/it-s-formula/ito-formula-for-continuous-semimartingales-bound.md)

## Expansion

1. The semimartingale decomposition of $\bar x$, its quadratic variation $H/K$, and the bound $H \le \bar x(1 - \bar x)$.
2. The random time change by $A$, the identification of $Y$ through the neutral Wright–Fisher martingale problem, and the treatment of intervals on which $H = 0$.
3. Two configurations with the same $\bar x$ and different laws of the future, showing that $\bar x$ is not Markov in physical time.
4. The comparison of absorption times, $\tau \ge A(\tau)$, and the resulting lower bound on the mean absorption time.

## Sources

- C. L. Epstein and C. A. Pop, Transition probabilities for degenerate diffusions arising in population genetics, Probab. Theory Related Fields 173 (2019), 537–603; Theorem 1.3 in the numbering of the arXiv version, arXiv:1608.02119v2. <https://doi.org/10.1007/s00440-018-0840-2>
- Original result: T. Maruyama, A Markov process of gene frequency change in a geographically structured population, Genetics 76 (1974), 367–377, abstract (the stochastic clock and the structure-independence of the fixation probability).
