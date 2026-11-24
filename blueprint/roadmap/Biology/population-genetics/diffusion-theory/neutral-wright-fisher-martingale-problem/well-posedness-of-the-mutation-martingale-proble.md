# Well-posedness of the Wright–Fisher martingale problem with mutation

Let $\theta_1, \theta_2 \ge 0$, $\theta = \theta_1 + \theta_2$, and

$$\mathcal{L}_{0, \theta} f(x) = \frac{1}{2} x(1 - x) f''(x) + \frac{1}{2}\bigl(\theta_1 (1 - x) - \theta_2 x\bigr) f'(x).$$

The martingale problem for $(\mathcal{L}_{0, \theta}, C^2[0, 1])$ is well posed:

- existence holds by [the mutation realization](mutation-realization-solves-the-mutation-marting.md);
- uniqueness in law holds for every initial law, because $\mathcal{L}_{0, \theta}$ is triangular on polynomials,

$$\mathcal{L}_{0, \theta}\, x^n = \binom{n}{2}\bigl(x^{n-1} - x^n\bigr) + \frac{n \theta_1}{2}\, x^{n-1} - \frac{n \theta}{2}\, x^n,$$

so [the conditional polynomial-semigroup identity](conditional-polynomial-semigroup-identity-for-ma.md) and [its upgrade to the Markov property](conditional-polynomial-identity-implies-markov-p.md) identify the law through the semigroup $P^{\theta}_t$ of [the mutation Feller semigroup](../wright-fisher-semigroup-and-moment-duality/mutation-wf-feller-semigroup-via-polynomial-dual.md).

Remark, not used in the proof: at a regular boundary, as at $0$ when $0 < \theta_1 < 1$, the domain $C^2[0, 1]$ selects the instantaneously reflecting solution.

## Depends on

- [Conditional polynomial-semigroup identity for martingale-problem solutions with triangular generators](conditional-polynomial-semigroup-identity-for-ma.md)
- [Conditional polynomial identity implies Markov property and uniqueness in law](conditional-polynomial-identity-implies-markov-p.md)
- [Mutation Wright–Fisher Feller semigroup via polynomial duality and chain limits](../wright-fisher-semigroup-and-moment-duality/mutation-wf-feller-semigroup-via-polynomial-dual.md)
- [Mutation realization solves the mutation martingale problem](mutation-realization-solves-the-mutation-marting.md)

## Expansion

1. The triangularity identity above.
2. Existence and uniqueness from the pages cited.

## Sources

- S. N. Ethier, A class of degenerate diffusion processes occurring in population genetics, *Comm. Pure Appl. Math.* 29 (1976), 483–493, <https://doi.org/10.1002/cpa.3160290503> (well-posedness).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 10.
- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Springer (1979) (martingale problems).
