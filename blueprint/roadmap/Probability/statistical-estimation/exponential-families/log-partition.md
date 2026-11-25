# Log-partition (cumulant) function of a finite exponential family

Let $X$ be a finite set, $E$ a real inner product space and $\phi : X \to E$ a sufficient statistic. The log-partition, or cumulant, function is

$$
A(\theta) = \log \sum_{x \in X} \exp\langle\phi(x), \theta\rangle = \log Z(\theta), \qquad \theta \in E .
$$

This is (3.40) of Wainwright and Jordan with the counting measure as base measure; for nonempty finite $X$, $A$ is finite everywhere and $p_\theta(x) = \exp(\langle\phi(x), \theta\rangle - A(\theta))$ is a regular
family of probability distributions with domain $\Omega = E$. When $X$ is empty the sum is $0$ and the convention
$\log 0 = 0$ gives $A = 0$, which defines no probability family; the results below assume $X$ nonempty.

## Related topics

- [Log-partition function of an exponential family with base weights](log-partition-2.md): the form with base weights $h$ and a statistic in $\mathbb{R}^\iota$, instead of the counting base measure and a statistic in an inner product space.

## Sources

- M. J. Wainwright and M. I. Jordan, *Graphical models, exponential families, and variational inference*, Found. Trends Mach. Learn. 1(1–2) (2008) 1–305, equation (3.40).
