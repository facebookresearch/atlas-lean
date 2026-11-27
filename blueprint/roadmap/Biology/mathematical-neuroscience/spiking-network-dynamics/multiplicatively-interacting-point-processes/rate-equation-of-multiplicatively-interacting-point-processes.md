# Rate equation of multiplicatively interacting point processes

**Model.** Let $A$ index neurons and let $W = (w_{aa'})$ be a positive coupling matrix. Neuron $a$ fires as a Cox process with rate

$$
\lambda_a(t) = \lambda_a(0)\exp\Bigl(\sum_{a' \in A} N_{a'}(t^-)\log w_{aa'}\Bigr),
$$

where $N_{a'}(t)$ counts the spikes of neuron $a'$ up to time $t$. Each spike of $a'$ thus multiplies the rate of $a$ by $w_{aa'}$: excitation if $w_{aa'} > 1$, inhibition if $w_{aa'} < 1$, with no positivity constraint on the inhibitory strength (unlike the linear Hawkes process). Writing $\ell_{aa'} = \log w_{aa'}$, the expected rates satisfy

$$
\frac{d}{dt}\mathbb{E}\lambda_a = \sum_{a'} \ell_{aa'}\bigl(\mathbb{E}\lambda_a\,\mathbb{E}\lambda_{a'} + \operatorname{Cov}(\lambda_a, \lambda_{a'})\bigr).
$$

**Rate equation.** Neglecting covariances gives the Lotka–Volterra-type system

$$
\dot y_a = y_a \sum_{a' \in A} \ell_{aa'}\, y_{a'}, \qquad y_a(0) = \mathbb{E}\lambda_a(0).
$$

Separating constant-rate Poisson inputs $P \subset A$ (with $\ell_{pa'} = 0$, rates $i_p$) from the recurrent population $R$ gives $\dot y_r = y_r\bigl((\mathcal{L}_R y)_r + (\mathcal{L}_P i)_r\bigr)$.

**Results.**
1. The positive cone of $\mathbb{R}^{|A|}$ is invariant under the rate equation.
2. Every equilibrium has, for each $r$, either $y_r = 0$ or $(\mathcal{L}_R y + \mathcal{L}_P i)_r = 0$; with $\mathcal{L}_R$ invertible, the interior equilibrium is $y = -\mathcal{L}_R^{-1}\mathcal{L}_P i$, which need not be positive.
3. If $\mathcal{L}_R$ is negative definite, then all positive solutions are bounded.

## Proof sketch

Because rates are exponentials of linear functionals of the spike counts, a spike of $a'$ changes $\lambda_a$ by the factor $w_{aa'}$, i.e. by $(w_{aa'} - 1)\lambda_a$ in absolute terms, and the expected increment per unit time is $\lambda_{a'}(w_{aa'} - 1)\lambda_a \approx \ell_{aa'}\lambda_a\lambda_{a'}$ for weak couplings, which is the quadratic structure of the rate equation. The resulting equation is the replicator / Lotka–Volterra form, so its faces $\{y_a = 0\}$ are invariant and its equilibria are found face by face. Boundedness follows from the energy $z = \sum_a y_a$: $\dot z = \mathcal{L}_R y \cdot y + e \cdot y$ for a vector $e$ built from the inputs, which is negative for large $\|y\|$ when $\mathcal{L}_R$ is negative definite. The model connects to the generalized linear (log-link) models used to fit spike trains, and supports winner-takes-all circuits built from mutual inhibition.

## Related topics

- [Lotka–Volterra predator–prey model](../../../population-dynamics/lotka-volterra-predator-prey-model/README.md)

## Sources

- Stefano Cardanobile and Stefan Rotter, "Multiplicatively interacting point processes and applications to neural modeling", *Journal of Computational Neuroscience* 28 (2010), 267–284, <https://doi.org/10.1007/s10827-009-0204-0>. Preprint version: arXiv:0904.1505 (2009), definition of multiplicatively interacting processes, definition of the rate equation, Propositions 10–12, <https://doi.org/10.48550/arXiv.0904.1505>.
