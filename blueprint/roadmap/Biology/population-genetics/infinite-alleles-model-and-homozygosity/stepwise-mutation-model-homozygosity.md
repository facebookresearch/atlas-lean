# Identity in state under the stepwise mutation model

Let allelic states be integers and let each gene copy mutate at rate $u$ per generation by $\pm 1$ with probability $\tfrac12$
each. In the coalescent limit of a neutral population of $N$ diploids with $\theta = 4Nu$ held fixed, two gene copies
[coalesce at rate $1$](../../coalescent-theory/pairwise-differences-under-poisson-mutation/has-law-pair-coal-time-kingman-genealogy.md) (time in units of $2N$ generations) and, before that, their state difference performs a
continuous-time symmetric $\pm 1$ random walk at total rate $\theta$. Since the coalescence time $T$ is $\mathrm{Exp}(1)$ and the
difference at time $t$ has characteristic function $e^{-\theta t (1 - \cos\omega)}$, the probability that the two copies are in
the same state is

$$F = \frac{1}{2\pi} \int_0^{2\pi} \frac{d\omega}{1 + \theta (1 - \cos \omega)} = \frac{1}{\sqrt{1 + 2\theta}},$$

using $\int_0^{2\pi} d\omega / (\alpha - \beta \cos\omega) = 2\pi / \sqrt{\alpha^2 - \beta^2}$ for $\alpha > |\beta|$. For $\theta > 0$ this exceeds the
[infinite-alleles homozygosity](eq-homozygosity.md) in the same limit, $1/(1 + \theta)$, because stepwise mutation can return to a previous state.

## Depends on

- [Equilibrium homozygosity in the infinite-alleles model](eq-homozygosity.md)

## Proof depends on

- [Coalescence time of a pair in the Kingman genealogy is Exp(1)](../../coalescent-theory/pairwise-differences-under-poisson-mutation/has-law-pair-coal-time-kingman-genealogy.md)

## Sources

- T. Ohta and M. Kimura, "A model of mutation appropriate to estimate the number of electrophoretically detectable alleles in a finite population", Genetical Research 22 (1973), 201–204, <https://doi.org/10.1017/S0016672300012994>. The formula is derived above in the coalescent limit; a finite-$N$ recursion is not stated.
