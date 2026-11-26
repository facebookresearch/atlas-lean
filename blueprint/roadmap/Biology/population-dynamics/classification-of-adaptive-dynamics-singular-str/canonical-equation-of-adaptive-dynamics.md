# Canonical equation of adaptive dynamics from a logistic birth–death–mutation process

Consider an asexual population in which each individual carries a one-dimensional trait $x$ in an interval $\mathcal X$. An individual with trait $x$ gives birth at rate $b(x)$ and dies at rate $d(x) + \sum_{j} \alpha(x, x_j)/K$, the sum running over the individuals present, where $K$ scales the carrying capacity and $\alpha > 0$ is the competition kernel. A birth produces a mutant with probability $u_K\,\mu(x)$, where $\mu(x) \in [0, 1]$ is a trait-dependent factor and $u_K \in (0, 1]$ is a scale parameter that tends to $0$ as $K \to \infty$; the mutant's trait is $x + h$ with $h$ drawn from a density $m(x, h)$ of mean zero and variance $\sigma^2(x)$; otherwise the offspring is a clone. Assume $b(x) > d(x)$ and $b$, $d$, $\alpha$ smooth.

**Monomorphic equilibrium and invasion fitness.** As $K \to \infty$ without mutation, the density $n_t$ (population size divided by $K$) of a monomorphic population with trait $x$ follows the logistic equation $\dot n = n\,(b(x) - d(x) - \alpha(x,x)\,n)$, with stable equilibrium

$$\bar n(x) = \frac{b(x) - d(x)}{\alpha(x,x)}.$$

A rare mutant $y$ in this resident population has invasion fitness $f(y; x) = b(y) - d(y) - \alpha(y, x)\,\bar n(x)$, so $f(x; x) = 0$.

**Trait substitution sequence.** Let $K \to \infty$ and $u_K \to 0$ jointly, with

$$e^{-CK} \ll u_K \ll \frac{1}{K \log K} \qquad \text{for every } C > 0,$$

start from a monomorphic population of trait $x_0$ whose density converges to $\bar n(x_0)$, and observe the process on the mutation time scale $t/(K u_K)$. Then the resident trait converges, in the sense of finite-dimensional distributions, to the Markov jump process that jumps from $x$ to $x + h$ at rate

$$\mu(x)\, b(x)\, \bar n(x)\, \frac{[f(x+h; x)]_+}{b(x+h)}\, m(x,h)\, dh,$$

the rate of mutant births times the survival probability $[f]_+/b$ of the supercritical branching process started by one mutant, provided invasion implies fixation. The lower bound on $u_K$ keeps the resident near $\bar n$ until the next mutation, and the upper bound lets each mutant's fate be decided first. Holding the mutation probability fixed while $K \to \infty$ gives no such separation: the number of mutant births per unit time then grows like $K$.

**Canonical equation.** Replace $m(x, h)$ by $m_\varepsilon(x, h) = \varepsilon^{-1} m(x, h/\varepsilon)$ and let $\varepsilon \to 0$ after the limit above. On the time scale $t/\varepsilon^2$ the trait substitution sequence converges to the solution of

$$\frac{dx}{dt} = \mu(x)\,\bar n(x) \int h\,[h\,\partial_1 f(x; x)]_+\, m(x,h)\, dh,$$

which for symmetric $m(x, \cdot)$ becomes

$$\frac{dx}{dt} = \frac12\,\mu(x)\,\sigma^2(x)\,\bar n(x)\,\partial_1 f(x; x).$$

Since $b > d$, $\bar n(x) > 0$. Where $\mu(x) > 0$ and $\sigma^2(x) > 0$ (positive mutation supply and nondegenerate mutational variance), the rest points of the symmetric equation are exactly the evolutionarily singular strategies, where the fitness gradient $\partial_1 f(x;x)$ vanishes. Where $\mu(x)\sigma^2(x) = 0$ the right-hand side vanishes whatever the fitness gradient.

## Depends on

- [Fitness Gradient](fitness-gradient.md)
- [Is Singular](is-singular.md)

## Proof depends on

- [Limiting extinction probability in the supercritical case](../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-lt.md)
- [Certain extinction in the critical and subcritical cases](../../../Probability/branching-processes/linear-birth-death-process/tendsto-extinction-prob-of-le.md)

## Expansion

The logistic limit is the law of large numbers for the density process. For the jump rate, mutants are born at rate $u_K \mu(x) b(x) K \bar n(x)$ per unit time, the mutant line is initially a linear birth–death process with rates $b(y)$ and $d(y) + \alpha(y, x)\bar n(x)$, and such a process survives with probability $[f(y;x)]_+/b(y)$; the factor $K u_K$ disappears under the time scaling $t/(K u_K)$. A mutant's fate is decided in time of order $\log K$, which is short compared with the mean waiting time $1/(K u_K)$ between mutations by the upper bound on $u_K$, while the resident leaves a neighbourhood of $\bar n$ only after a time exponential in $K$, which is long by the lower bound. For small $h$, $f(x+h; x) \approx h\,\partial_1 f(x;x)$ and $b(x+h) \approx b(x)$, so the mean jump per unit time is the displayed integral; with a symmetric kernel, $\int h[h a]_+ m\,dh = \tfrac12 a\sigma^2$, giving the classical Dieckmann–Law form. The trait climbs the fitness gradient at a speed proportional to the mutation rate, the mutational variance and the equilibrium population size.

## Sources

- N. Champagnat, R. Ferrière and S. Méléard, "Unifying evolutionary dynamics: From individual stochastic processes to macroscopic models", Theoretical Population Biology 69 (2006), 297–321, <https://doi.org/10.1016/j.tpb.2005.10.004>. Section 5.1, Equations (5.3)–(5.5) (joint limit and time scale of the trait substitution sequence).
- U. Dieckmann and R. Law, "The dynamical theory of coevolution: a derivation from stochastic ecological processes", Journal of Mathematical Biology 34 (1996), 579–612, <https://doi.org/10.1007/BF02409751>.
