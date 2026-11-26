# Canonical equation of adaptive dynamics from a logistic birth–death–mutation process

Consider an asexual population in which each individual carries a one-dimensional trait $x$ in an interval $\mathcal X$. An individual with trait $x$ gives birth at rate $b(x)$ and dies at rate $d(x) + \sum_{j} \alpha(x, x_j)/K$, the sum running over the individuals present, where $K$ scales the carrying capacity and $\alpha > 0$ is the competition kernel. A birth produces a mutant with probability $\mu(x)$, whose trait is $x + h$ with $h$ drawn from a density $m(x, h)$ of mean zero and variance $\sigma^2(x)$; otherwise the offspring is a clone. Assume $b(x) > d(x)$ and $b$, $d$, $\alpha$ smooth.

**Monomorphic equilibrium and invasion fitness.** As $K \to \infty$ without mutation, the density $n_t$ (population size divided by $K$) of a monomorphic population with trait $x$ follows the logistic equation $\dot n = n\,(b(x) - d(x) - \alpha(x,x)\,n)$, with stable equilibrium

$$\bar n(x) = \frac{b(x) - d(x)}{\alpha(x,x)}.$$

A rare mutant $y$ in this resident population has invasion fitness $f(y; x) = b(y) - d(y) - \alpha(y, x)\,\bar n(x)$, so $f(x; x) = 0$.

**Trait substitution sequence.** When mutations are rare enough that each mutant's fate is decided before the next mutant appears and $K \to \infty$, the resident trait jumps from $x$ to $x + h$ at rate

$$\mu(x)\, b(x)\, \bar n(x)\, \frac{[f(x+h; x)]_+}{b(x+h)}\, m(x,h)\, dh,$$

the rate of mutant births times the survival probability $[f]_+/b$ of the supercritical branching process started by one mutant, provided invasion implies fixation.

**Canonical equation.** In the further limit of small mutation steps, after rescaling time by the squared step size, the trait follows

$$\frac{dx}{dt} = \mu(x)\,\bar n(x) \int h\,[h\,\partial_1 f(x; x)]_+\, m(x,h)\, dh,$$

which for symmetric $m(x, \cdot)$ becomes

$$\frac{dx}{dt} = \frac12\,\mu(x)\,\sigma^2(x)\,\bar n(x)\,\partial_1 f(x; x).$$

Its rest points are the evolutionarily singular strategies, where the fitness gradient $\partial_1 f(x;x)$ vanishes.

## Depends on

- [Fitness Gradient](fitness-gradient.md)
- [Is Singular](is-singular.md)

## Expansion

The logistic limit is the law of large numbers for the density process. For the jump rate, mutants are born at rate $\mu(x) b(x) K \bar n(x)$ per unit time, the mutant line is initially a linear birth–death process with rates $b(y)$ and $d(y) + \alpha(y, x)\bar n(x)$, and such a process survives with probability $[f(y;x)]_+/b(y)$; the factor $K$ disappears under the rare-mutation time scaling. For small $h$, $f(x+h; x) \approx h\,\partial_1 f(x;x)$ and $b(x+h) \approx b(x)$, so the mean jump per unit time is the displayed integral; with a symmetric kernel, $\int h[h a]_+ m\,dh = \tfrac12 a\sigma^2$, giving the classical Dieckmann–Law form. The trait climbs the fitness gradient at a speed proportional to the mutation rate, the mutational variance and the equilibrium population size.

## Sources

- N. Champagnat, R. Ferrière and S. Méléard, "Unifying evolutionary dynamics: From individual stochastic processes to macroscopic models", Theoretical Population Biology 69 (2006), 297–321, <https://doi.org/10.1016/j.tpb.2005.10.004>.
- U. Dieckmann and R. Law, "The dynamical theory of coevolution: a derivation from stochastic ecological processes", Journal of Mathematical Biology 34 (1996), 579–612, <https://doi.org/10.1007/BF02409751>.
